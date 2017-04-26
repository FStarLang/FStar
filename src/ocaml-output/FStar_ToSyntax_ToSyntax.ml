
open Prims

let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun uu___199_5 -> (match (uu___199_5) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Syntax_Syntax.Equality)
end
| uu____8 -> begin
None
end))


let trans_qual : FStar_Range.range  ->  FStar_Ident.lident Prims.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun r maybe_effect_id uu___200_19 -> (match (uu___200_19) with
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


let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun uu___201_25 -> (match (uu___201_25) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end
| FStar_Parser_AST.LightOff -> begin
FStar_Syntax_Syntax.LightOff
end))


let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun uu___202_32 -> (match (uu___202_32) with
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


let op_as_term = (fun env arity rng op -> (

let r = (fun l dd -> (

let uu____166 = (

let uu____167 = (FStar_Syntax_Syntax.lid_as_fv (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd None)
in (FStar_All.pipe_right uu____167 FStar_Syntax_Syntax.fv_to_tm))
in Some (uu____166)))
in (

let fallback = (fun uu____172 -> (match ((FStar_Ident.text_of_id op)) with
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

let uu____174 = (FStar_Options.ml_ish ())
in (match (uu____174) with
| true -> begin
(r FStar_Syntax_Const.list_append_lid FStar_Syntax_Syntax.Delta_equational)
end
| uu____176 -> begin
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
| uu____177 -> begin
None
end))
in (

let uu____178 = (

let uu____182 = (compile_op_lid arity op.FStar_Ident.idText op.FStar_Ident.idRange)
in (FStar_ToSyntax_Env.try_lookup_lid env uu____182))
in (match (uu____178) with
| Some (t) -> begin
Some ((Prims.fst t))
end
| uu____189 -> begin
(fallback ())
end)))))


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (

let uu____199 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) uu____199)))


let rec free_type_vars_b : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_ToSyntax_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (uu____224) -> begin
((env), ([]))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____227 = (FStar_ToSyntax_Env.push_bv env x)
in (match (uu____227) with
| (env1, uu____234) -> begin
((env1), ((x)::[]))
end))
end
| FStar_Parser_AST.Annotated (uu____236, term) -> begin
(

let uu____238 = (free_type_vars env term)
in ((env), (uu____238)))
end
| FStar_Parser_AST.TAnnotated (id, uu____242) -> begin
(

let uu____243 = (FStar_ToSyntax_Env.push_bv env id)
in (match (uu____243) with
| (env1, uu____250) -> begin
((env1), ([]))
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____253 = (free_type_vars env t)
in ((env), (uu____253)))
end))
and free_type_vars : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (

let uu____258 = (

let uu____259 = (unparen t)
in uu____259.FStar_Parser_AST.tm)
in (match (uu____258) with
| FStar_Parser_AST.Labeled (uu____261) -> begin
(failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____267 = (FStar_ToSyntax_Env.try_lookup_id env a)
in (match (uu____267) with
| None -> begin
(a)::[]
end
| uu____274 -> begin
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
| FStar_Parser_AST.Construct (uu____300, ts) -> begin
(FStar_List.collect (fun uu____310 -> (match (uu____310) with
| (t1, uu____315) -> begin
(free_type_vars env t1)
end)) ts)
end
| FStar_Parser_AST.Op (uu____316, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, uu____322) -> begin
(

let uu____323 = (free_type_vars env t1)
in (

let uu____325 = (free_type_vars env t2)
in (FStar_List.append uu____323 uu____325)))
end
| FStar_Parser_AST.Refine (b, t1) -> begin
(

let uu____329 = (free_type_vars_b env b)
in (match (uu____329) with
| (env1, f) -> begin
(

let uu____338 = (free_type_vars env1 t1)
in (FStar_List.append f uu____338))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(

let uu____346 = (FStar_List.fold_left (fun uu____353 binder -> (match (uu____353) with
| (env1, free) -> begin
(

let uu____365 = (free_type_vars_b env1 binder)
in (match (uu____365) with
| (env2, f) -> begin
((env2), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (uu____346) with
| (env1, free) -> begin
(

let uu____383 = (free_type_vars env1 body)
in (FStar_List.append free uu____383))
end))
end
| FStar_Parser_AST.Project (t1, uu____386) -> begin
(free_type_vars env t1)
end
| FStar_Parser_AST.Attributes (cattributes) -> begin
(FStar_List.collect (free_type_vars env) cattributes)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Bind (_)) | (FStar_Parser_AST.Seq (_)) -> begin
[]
end)))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (

let rec aux = (fun args t1 -> (

let uu____426 = (

let uu____427 = (unparen t1)
in uu____427.FStar_Parser_AST.tm)
in (match (uu____426) with
| FStar_Parser_AST.App (t2, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t2)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t1.FStar_Parser_AST.range; FStar_Parser_AST.level = t1.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| uu____451 -> begin
((t1), (args))
end)))
in (aux [] t)))


let close : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (

let uu____465 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv uu____465))
in (match (((FStar_List.length ftv) = (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____471 -> begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (

let uu____477 = (

let uu____478 = (

let uu____481 = (tm_type x.FStar_Ident.idRange)
in ((x), (uu____481)))
in FStar_Parser_AST.TAnnotated (uu____478))
in (FStar_Parser_AST.mk_binder uu____477 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end)))


let close_fun : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (

let uu____492 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv uu____492))
in (match (((FStar_List.length ftv) = (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____498 -> begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (

let uu____504 = (

let uu____505 = (

let uu____508 = (tm_type x.FStar_Ident.idRange)
in ((x), (uu____508)))
in FStar_Parser_AST.TAnnotated (uu____505))
in (FStar_Parser_AST.mk_binder uu____504 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (Some (FStar_Parser_AST.Implicit)))))))
in (

let t1 = (

let uu____510 = (

let uu____511 = (unparen t)
in uu____511.FStar_Parser_AST.tm)
in (match (uu____510) with
| FStar_Parser_AST.Product (uu____512) -> begin
t
end
| uu____516 -> begin
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
| uu____537 -> begin
((bs), (t))
end))


let rec is_var_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatWild) | (FStar_Parser_AST.PatTvar (_, _)) | (FStar_Parser_AST.PatVar (_, _)) -> begin
true
end
| FStar_Parser_AST.PatAscribed (p1, uu____549) -> begin
(is_var_pattern p1)
end
| uu____550 -> begin
false
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p1, uu____555) -> begin
(is_app_pattern p1)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____556); FStar_Parser_AST.prange = uu____557}, uu____558) -> begin
true
end
| uu____564 -> begin
false
end))


let replace_unit_pattern : FStar_Parser_AST.pattern  ->  FStar_Parser_AST.pattern = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatConst (FStar_Const.Const_unit) -> begin
(FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatAscribed ((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)), (unit_ty)))) p.FStar_Parser_AST.prange)
end
| uu____568 -> begin
p
end))


let rec destruct_app_pattern : FStar_ToSyntax_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level1 p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p1, t) -> begin
(

let uu____594 = (destruct_app_pattern env is_top_level1 p1)
in (match (uu____594) with
| (name, args, uu____611) -> begin
((name), (args), (Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, uu____625); FStar_Parser_AST.prange = uu____626}, args) when is_top_level1 -> begin
(

let uu____632 = (

let uu____635 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (uu____635))
in ((uu____632), (args), (None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, uu____641); FStar_Parser_AST.prange = uu____642}, args) -> begin
((FStar_Util.Inl (id)), (args), (None))
end
| uu____652 -> begin
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
| FStar_Parser_AST.PatVar (x, uu____687) -> begin
(FStar_Util.set_add x acc)
end
| (FStar_Parser_AST.PatList (pats)) | (FStar_Parser_AST.PatTuple (pats, _)) | (FStar_Parser_AST.PatOr (pats)) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatRecord (guarded_pats) -> begin
(

let uu____700 = (FStar_List.map Prims.snd guarded_pats)
in (gather_pattern_bound_vars_from_list uu____700))
end
| FStar_Parser_AST.PatAscribed (pat, uu____705) -> begin
(gather_pattern_bound_vars_maybe_top acc pat)
end)))


let gather_pattern_bound_vars : FStar_Parser_AST.pattern  ->  FStar_Ident.ident FStar_Util.set = (

let acc = (FStar_Util.new_set (fun id1 id2 -> (match ((id1.FStar_Ident.idText = id2.FStar_Ident.idText)) with
| true -> begin
(Prims.parse_int "0")
end
| uu____713 -> begin
(Prims.parse_int "1")
end)) (fun uu____714 -> (Prims.parse_int "0")))
in (fun p -> (gather_pattern_bound_vars_maybe_top acc p)))

type bnd =
| LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * FStar_Syntax_Syntax.term)


let uu___is_LocalBinder : bnd  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LocalBinder (_0) -> begin
true
end
| uu____732 -> begin
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
| uu____752 -> begin
false
end))


let __proj__LetBinder__item___0 : bnd  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| LetBinder (_0) -> begin
_0
end))


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun uu___203_770 -> (match (uu___203_770) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| uu____775 -> begin
(failwith "Impossible")
end))


let as_binder : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_ToSyntax_Env.env) = (fun env imp uu___204_792 -> (match (uu___204_792) with
| (None, k) -> begin
(

let uu____801 = (FStar_Syntax_Syntax.null_binder k)
in ((uu____801), (env)))
end
| (Some (a), k) -> begin
(

let uu____805 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____805) with
| (env1, a1) -> begin
(((((

let uu___225_816 = a1
in {FStar_Syntax_Syntax.ppname = uu___225_816.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___225_816.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), ((trans_aqual imp)))), (env1))
end))
end))


type env_t =
FStar_ToSyntax_Env.env


type lenv_t =
FStar_Syntax_Syntax.bv Prims.list


let mk_lb : ((FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax * (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  FStar_Syntax_Syntax.letbinding = (fun uu____829 -> (match (uu____829) with
| (n1, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n1; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))


let no_annot_abs : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t None))


let mk_ref_read = (fun tm -> (

let tm' = (

let uu____879 = (

let uu____889 = (

let uu____890 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm uu____890))
in (

let uu____891 = (

let uu____897 = (

let uu____902 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (uu____902)))
in (uu____897)::[])
in ((uu____889), (uu____891))))
in FStar_Syntax_Syntax.Tm_app (uu____879))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_alloc = (fun tm -> (

let tm' = (

let uu____936 = (

let uu____946 = (

let uu____947 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm uu____947))
in (

let uu____948 = (

let uu____954 = (

let uu____959 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (uu____959)))
in (uu____954)::[])
in ((uu____946), (uu____948))))
in FStar_Syntax_Syntax.Tm_app (uu____936))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_assign = (fun t1 t2 pos -> (

let tm = (

let uu____1007 = (

let uu____1017 = (

let uu____1018 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm uu____1018))
in (

let uu____1019 = (

let uu____1025 = (

let uu____1030 = (FStar_Syntax_Syntax.as_implicit false)
in ((t1), (uu____1030)))
in (

let uu____1033 = (

let uu____1039 = (

let uu____1044 = (FStar_Syntax_Syntax.as_implicit false)
in ((t2), (uu____1044)))
in (uu____1039)::[])
in (uu____1025)::uu____1033))
in ((uu____1017), (uu____1019))))
in FStar_Syntax_Syntax.Tm_app (uu____1007))
in (FStar_Syntax_Syntax.mk tm None pos)))


let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun uu___205_1070 -> (match (uu___205_1070) with
| ("repr") | ("post") | ("pre") | ("wp") -> begin
true
end
| uu____1071 -> begin
false
end))


let rec sum_to_universe : FStar_Syntax_Syntax.universe  ->  Prims.int  ->  FStar_Syntax_Syntax.universe = (fun u n1 -> (match ((n1 = (Prims.parse_int "0"))) with
| true -> begin
u
end
| uu____1078 -> begin
(

let uu____1079 = (sum_to_universe u (n1 - (Prims.parse_int "1")))
in FStar_Syntax_Syntax.U_succ (uu____1079))
end))


let int_to_universe : Prims.int  ->  FStar_Syntax_Syntax.universe = (fun n1 -> (sum_to_universe FStar_Syntax_Syntax.U_zero n1))


let rec desugar_maybe_non_constant_universe : FStar_Parser_AST.term  ->  (Prims.int, FStar_Syntax_Syntax.universe) FStar_Util.either = (fun t -> (

let uu____1090 = (

let uu____1091 = (unparen t)
in uu____1091.FStar_Parser_AST.tm)
in (match (uu____1090) with
| FStar_Parser_AST.Wild -> begin
(

let uu____1094 = (

let uu____1095 = (FStar_Unionfind.fresh None)
in FStar_Syntax_Syntax.U_unif (uu____1095))
in FStar_Util.Inr (uu____1094))
end
| FStar_Parser_AST.Uvar (u) -> begin
FStar_Util.Inr (FStar_Syntax_Syntax.U_name (u))
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (repr, uu____1101)) -> begin
(

let n1 = (FStar_Util.int_of_string repr)
in ((match ((n1 < (Prims.parse_int "0"))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Negative universe constant  are not supported : " repr)), (t.FStar_Parser_AST.range)))))
end
| uu____1110 -> begin
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

let uu____1144 = (sum_to_universe u n1)
in FStar_Util.Inr (uu____1144))
end
| (FStar_Util.Inr (u11), FStar_Util.Inr (u21)) -> begin
(

let uu____1151 = (

let uu____1152 = (

let uu____1155 = (

let uu____1156 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "This universe might contain a sum of two universe variables " uu____1156))
in ((uu____1155), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____1152))
in (Prims.raise uu____1151))
end)))
end
| FStar_Parser_AST.App (uu____1159) -> begin
(

let rec aux = (fun t1 univargs -> (

let uu____1178 = (

let uu____1179 = (unparen t1)
in uu____1179.FStar_Parser_AST.tm)
in (match (uu____1178) with
| FStar_Parser_AST.App (t2, targ, uu____1184) -> begin
(

let uarg = (desugar_maybe_non_constant_universe targ)
in (aux t2 ((uarg)::univargs)))
end
| FStar_Parser_AST.Var (max_lid1) -> begin
(match ((FStar_List.existsb (fun uu___206_1196 -> (match (uu___206_1196) with
| FStar_Util.Inr (uu____1199) -> begin
true
end
| uu____1200 -> begin
false
end)) univargs)) with
| true -> begin
(

let uu____1203 = (

let uu____1204 = (FStar_List.map (fun uu___207_1208 -> (match (uu___207_1208) with
| FStar_Util.Inl (n1) -> begin
(int_to_universe n1)
end
| FStar_Util.Inr (u) -> begin
u
end)) univargs)
in FStar_Syntax_Syntax.U_max (uu____1204))
in FStar_Util.Inr (uu____1203))
end
| uu____1213 -> begin
(

let nargs = (FStar_List.map (fun uu___208_1218 -> (match (uu___208_1218) with
| FStar_Util.Inl (n1) -> begin
n1
end
| FStar_Util.Inr (uu____1222) -> begin
(failwith "impossible")
end)) univargs)
in (

let uu____1223 = (FStar_List.fold_left (fun m n1 -> (match ((m > n1)) with
| true -> begin
m
end
| uu____1226 -> begin
n1
end)) (Prims.parse_int "0") nargs)
in FStar_Util.Inl (uu____1223)))
end)
end
| uu____1227 -> begin
(

let uu____1228 = (

let uu____1229 = (

let uu____1232 = (

let uu____1233 = (

let uu____1234 = (FStar_Parser_AST.term_to_string t1)
in (Prims.strcat uu____1234 " in universe context"))
in (Prims.strcat "Unexpected term " uu____1233))
in ((uu____1232), (t1.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____1229))
in (Prims.raise uu____1228))
end)))
in (aux t []))
end
| uu____1239 -> begin
(

let uu____1240 = (

let uu____1241 = (

let uu____1244 = (

let uu____1245 = (

let uu____1246 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat uu____1246 " in universe context"))
in (Prims.strcat "Unexpected term " uu____1245))
in ((uu____1244), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____1241))
in (Prims.raise uu____1240))
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

let uu____1280 = (FStar_List.hd fields)
in (match (uu____1280) with
| (f, uu____1286) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f);
(

let record = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f)
in (

let check_field = (fun uu____1294 -> (match (uu____1294) with
| (f', uu____1298) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f');
(

let uu____1300 = (FStar_ToSyntax_Env.belongs_to_record env f' record)
in (match (uu____1300) with
| true -> begin
()
end
| uu____1301 -> begin
(

let msg = (FStar_Util.format3 "Field %s belongs to record type %s, whereas field %s does not" f.FStar_Ident.str record.FStar_ToSyntax_Env.typename.FStar_Ident.str f'.FStar_Ident.str)
in (Prims.raise (FStar_Errors.Error (((msg), (rg))))))
end));
)
end))
in ((

let uu____1304 = (FStar_List.tl fields)
in (FStar_List.iter check_field uu____1304));
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
| FStar_Syntax_Syntax.Pat_cons (uu____1464, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out uu____1486 -> (match (uu____1486) with
| (p3, uu____1492) -> begin
(

let uu____1493 = (pat_vars p3)
in (FStar_Util.set_union out uu____1493))
end)) FStar_Syntax_Syntax.no_names))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd1)::tl1) -> begin
(

let xs = (pat_vars hd1)
in (

let uu____1507 = (

let uu____1508 = (FStar_Util.for_all (fun p3 -> (

let ys = (pat_vars p3)
in ((FStar_Util.set_is_subset_of xs ys) && (FStar_Util.set_is_subset_of ys xs)))) tl1)
in (not (uu____1508)))
in (match (uu____1507) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Disjunctive pattern binds different variables in each case"), (p2.FStar_Syntax_Syntax.p)))))
end
| uu____1511 -> begin
xs
end)))
end))
in (pat_vars p1)))
in ((match (((is_mut), (p.FStar_Parser_AST.pat))) with
| ((false, _)) | ((true, FStar_Parser_AST.PatVar (_))) -> begin
()
end
| (true, uu____1515) -> begin
(Prims.raise (FStar_Errors.Error ((("let-mutable is for variables only"), (p.FStar_Parser_AST.prange)))))
end);
(

let push_bv_maybe_mut = (match (is_mut) with
| true -> begin
FStar_ToSyntax_Env.push_bv_mutable
end
| uu____1529 -> begin
FStar_ToSyntax_Env.push_bv
end)
in (

let resolvex = (fun l e x -> (

let uu____1543 = (FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText))))
in (match (uu____1543) with
| Some (y) -> begin
((l), (e), (y))
end
| uu____1551 -> begin
(

let uu____1553 = (push_bv_maybe_mut e x)
in (match (uu____1553) with
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

let uu____1602 = (

let uu____1603 = (

let uu____1604 = (

let uu____1608 = (

let uu____1609 = (

let uu____1612 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") op.FStar_Ident.idText)
in ((uu____1612), (op.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____1609))
in ((uu____1608), (None)))
in FStar_Parser_AST.PatVar (uu____1604))
in {FStar_Parser_AST.pat = uu____1603; FStar_Parser_AST.prange = p1.FStar_Parser_AST.prange})
in (aux loc env1 uu____1602))
end
| FStar_Parser_AST.PatOr ([]) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.PatOr ((p2)::ps) -> begin
(

let uu____1624 = (aux loc env1 p2)
in (match (uu____1624) with
| (loc1, env2, var, p3, uu____1643) -> begin
(

let uu____1648 = (FStar_List.fold_left (fun uu____1661 p4 -> (match (uu____1661) with
| (loc2, env3, ps1) -> begin
(

let uu____1684 = (aux loc2 env3 p4)
in (match (uu____1684) with
| (loc3, env4, uu____1700, p5, uu____1702) -> begin
((loc3), (env4), ((p5)::ps1))
end))
end)) ((loc1), (env2), ([])) ps)
in (match (uu____1648) with
| (loc2, env3, ps1) -> begin
(

let pat = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_disj ((p3)::(FStar_List.rev ps1))))
in ((loc2), (env3), (var), (pat), (false)))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p2, t) -> begin
(

let uu____1746 = (aux loc env1 p2)
in (match (uu____1746) with
| (loc1, env', binder, p3, imp) -> begin
(

let binder1 = (match (binder) with
| LetBinder (uu____1771) -> begin
(failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t1 = (

let uu____1777 = (close_fun env1 t)
in (desugar_term env1 uu____1777))
in ((match ((match (x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
false
end
| uu____1779 -> begin
true
end)) with
| true -> begin
(

let uu____1780 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____1781 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____1782 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3_warning "Multiple ascriptions for %s in pattern, type %s was shadowed by %s" uu____1780 uu____1781 uu____1782))))
end
| uu____1783 -> begin
()
end);
LocalBinder ((((

let uu___226_1784 = x
in {FStar_Syntax_Syntax.ppname = uu___226_1784.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___226_1784.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})), (aq)));
))
end)
in ((loc1), (env'), (binder1), (p3), (imp)))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____1788 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env1), (LocalBinder (((x), (None)))), (uu____1788), (false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____1798 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env1), (LocalBinder (((x), (None)))), (uu____1798), (false))))
end
| (FStar_Parser_AST.PatTvar (x, aq)) | (FStar_Parser_AST.PatVar (x, aq)) -> begin
(

let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (

let aq1 = (trans_aqual aq)
in (

let uu____1816 = (resolvex loc env1 x)
in (match (uu____1816) with
| (loc1, env2, xbv) -> begin
(

let uu____1830 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc1), (env2), (LocalBinder (((xbv), (aq1)))), (uu____1830), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l1 = (FStar_ToSyntax_Env.fail_or env1 (FStar_ToSyntax_Env.try_lookup_datacon env1) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____1841 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), ([])))))
in ((loc), (env1), (LocalBinder (((x), (None)))), (uu____1841), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = uu____1859}, args) -> begin
(

let uu____1863 = (FStar_List.fold_right (fun arg uu____1881 -> (match (uu____1881) with
| (loc1, env2, args1) -> begin
(

let uu____1911 = (aux loc1 env2 arg)
in (match (uu____1911) with
| (loc2, env3, uu____1929, arg1, imp) -> begin
((loc2), (env3), ((((arg1), (imp)))::args1))
end))
end)) args ((loc), (env1), ([])))
in (match (uu____1863) with
| (loc1, env2, args1) -> begin
(

let l1 = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_datacon env2) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____1978 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args1)))))
in ((loc1), (env2), (LocalBinder (((x), (None)))), (uu____1978), (false)))))
end))
end
| FStar_Parser_AST.PatApp (uu____1991) -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected pattern"), (p1.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____2004 = (FStar_List.fold_right (fun pat uu____2018 -> (match (uu____2018) with
| (loc1, env2, pats1) -> begin
(

let uu____2040 = (aux loc1 env2 pat)
in (match (uu____2040) with
| (loc2, env3, uu____2056, pat1, uu____2058) -> begin
((loc2), (env3), ((pat1)::pats1))
end))
end)) pats ((loc), (env1), ([])))
in (match (uu____2004) with
| (loc1, env2, pats1) -> begin
(

let pat = (

let uu____2092 = (

let uu____2095 = (

let uu____2100 = (FStar_Range.end_range p1.FStar_Parser_AST.prange)
in (pos_r uu____2100))
in (

let uu____2101 = (

let uu____2102 = (

let uu____2110 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____2110), ([])))
in FStar_Syntax_Syntax.Pat_cons (uu____2102))
in (FStar_All.pipe_left uu____2095 uu____2101)))
in (FStar_List.fold_right (fun hd1 tl1 -> (

let r = (FStar_Range.union_ranges hd1.FStar_Syntax_Syntax.p tl1.FStar_Syntax_Syntax.p)
in (

let uu____2133 = (

let uu____2134 = (

let uu____2142 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____2142), ((((hd1), (false)))::(((tl1), (false)))::[])))
in FStar_Syntax_Syntax.Pat_cons (uu____2134))
in (FStar_All.pipe_left (pos_r r) uu____2133)))) pats1 uu____2092))
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc1), (env2), (LocalBinder (((x), (None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep1) -> begin
(

let uu____2174 = (FStar_List.fold_left (fun uu____2191 p2 -> (match (uu____2191) with
| (loc1, env2, pats) -> begin
(

let uu____2222 = (aux loc1 env2 p2)
in (match (uu____2222) with
| (loc2, env3, uu____2240, pat, uu____2242) -> begin
((loc2), (env3), ((((pat), (false)))::pats))
end))
end)) ((loc), (env1), ([])) args)
in (match (uu____2174) with
| (loc1, env2, args1) -> begin
(

let args2 = (FStar_List.rev args1)
in (

let l = (match (dep1) with
| true -> begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end
| uu____2305 -> begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end)
in (

let uu____2313 = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_lid env2) l)
in (match (uu____2313) with
| (constr, uu____2326) -> begin
(

let l1 = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____2329 -> begin
(failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____2331 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args2)))))
in ((loc1), (env2), (LocalBinder (((x), (None)))), (uu____2331), (false)))))
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

let fields1 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____2372 -> (match (uu____2372) with
| (f, p2) -> begin
((f.FStar_Ident.ident), (p2))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____2387 -> (match (uu____2387) with
| (f, uu____2391) -> begin
(

let uu____2392 = (FStar_All.pipe_right fields1 (FStar_List.tryFind (fun uu____2404 -> (match (uu____2404) with
| (g, uu____2408) -> begin
(f.FStar_Ident.idText = g.FStar_Ident.idText)
end))))
in (match (uu____2392) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p1.FStar_Parser_AST.prange)
end
| Some (uu____2411, p2) -> begin
p2
end))
end))))
in (

let app = (

let uu____2416 = (

let uu____2417 = (

let uu____2421 = (

let uu____2422 = (

let uu____2423 = (FStar_Ident.lid_of_ids (FStar_List.append record.FStar_ToSyntax_Env.typename.FStar_Ident.ns ((record.FStar_ToSyntax_Env.constrname)::[])))
in FStar_Parser_AST.PatName (uu____2423))
in (FStar_Parser_AST.mk_pattern uu____2422 p1.FStar_Parser_AST.prange))
in ((uu____2421), (args)))
in FStar_Parser_AST.PatApp (uu____2417))
in (FStar_Parser_AST.mk_pattern uu____2416 p1.FStar_Parser_AST.prange))
in (

let uu____2425 = (aux loc env1 app)
in (match (uu____2425) with
| (env2, e, b, p2, uu____2444) -> begin
(

let p3 = (match (p2.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args1) -> begin
(

let uu____2466 = (

let uu____2467 = (

let uu____2475 = (

let uu___227_2476 = fv
in (

let uu____2477 = (

let uu____2479 = (

let uu____2480 = (

let uu____2484 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_ToSyntax_Env.typename), (uu____2484)))
in FStar_Syntax_Syntax.Record_ctor (uu____2480))
in Some (uu____2479))
in {FStar_Syntax_Syntax.fv_name = uu___227_2476.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = uu___227_2476.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu____2477}))
in ((uu____2475), (args1)))
in FStar_Syntax_Syntax.Pat_cons (uu____2467))
in (FStar_All.pipe_left pos uu____2466))
end
| uu____2503 -> begin
p2
end)
in ((env2), (e), (b), (p3), (false)))
end))))))
end))))
in (

let uu____2506 = (aux [] env p)
in (match (uu____2506) with
| (uu____2517, env1, b, p1, uu____2521) -> begin
((

let uu____2527 = (check_linear_pattern_variables p1)
in (FStar_All.pipe_left Prims.ignore uu____2527));
((env1), (b), (p1));
)
end)))));
)))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p is_mut -> (

let mklet = (fun x -> (

let uu____2546 = (

let uu____2547 = (

let uu____2550 = (FStar_ToSyntax_Env.qualify env x)
in ((uu____2550), (FStar_Syntax_Syntax.tun)))
in LetBinder (uu____2547))
in ((env), (uu____2546), (None))))
in (match (top) with
| true -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(

let uu____2561 = (

let uu____2562 = (

let uu____2565 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") x.FStar_Ident.idText)
in ((uu____2565), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____2562))
in (mklet uu____2561))
end
| FStar_Parser_AST.PatVar (x, uu____2567) -> begin
(mklet x)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____2571); FStar_Parser_AST.prange = uu____2572}, t) -> begin
(

let uu____2576 = (

let uu____2577 = (

let uu____2580 = (FStar_ToSyntax_Env.qualify env x)
in (

let uu____2581 = (desugar_term env t)
in ((uu____2580), (uu____2581))))
in LetBinder (uu____2577))
in ((env), (uu____2576), (None)))
end
| uu____2583 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end
| uu____2588 -> begin
(

let uu____2589 = (desugar_data_pat env p is_mut)
in (match (uu____2589) with
| (env1, binder, p1) -> begin
(

let p2 = (match (p1.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| uu____2605 -> begin
Some (p1)
end)
in ((env1), (binder), (p2)))
end))
end)))
and desugar_binding_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun uu____2609 env pat -> (

let uu____2612 = (desugar_data_pat env pat false)
in (match (uu____2612) with
| (env1, uu____2619, pat1) -> begin
((env1), (pat1))
end)))
and desugar_match_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env1 = (FStar_ToSyntax_Env.set_expect_typ env false)
in (desugar_term_maybe_top false env1 e)))
and desugar_typ : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env1 = (FStar_ToSyntax_Env.set_expect_typ env true)
in (desugar_term_maybe_top false env1 e)))
and desugar_machine_integer : FStar_ToSyntax_Env.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env repr uu____2631 range -> (match (uu____2631) with
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

let uu____2642 = (FStar_ToSyntax_Env.try_lookup_lid env lid1)
in (match (uu____2642) with
| Some (lid2) -> begin
(Prims.fst lid2)
end
| None -> begin
(

let uu____2653 = (FStar_Util.format1 "%s not in scope\n" (FStar_Ident.text_of_lid lid1))
in (failwith uu____2653))
end))
in (

let repr1 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (None)))))) None range)
in (

let uu____2670 = (

let uu____2673 = (

let uu____2674 = (

let uu____2684 = (

let uu____2690 = (

let uu____2695 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr1), (uu____2695)))
in (uu____2690)::[])
in ((lid2), (uu____2684)))
in FStar_Syntax_Syntax.Tm_app (uu____2674))
in (FStar_Syntax_Syntax.mk uu____2673))
in (uu____2670 None range))))))
end))
and desugar_name : (FStar_Syntax_Syntax.term'  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env_t  ->  Prims.bool  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.term = (fun mk1 setpos env resolve l -> (

let uu____2730 = (FStar_ToSyntax_Env.fail_or env ((match (resolve) with
| true -> begin
FStar_ToSyntax_Env.try_lookup_lid
end
| uu____2742 -> begin
FStar_ToSyntax_Env.try_lookup_lid_no_resolve
end) env) l)
in (match (uu____2730) with
| (tm, mut) -> begin
(

let tm1 = (setpos tm)
in (match (mut) with
| true -> begin
(

let uu____2748 = (

let uu____2749 = (

let uu____2754 = (mk_ref_read tm1)
in ((uu____2754), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval))))
in FStar_Syntax_Syntax.Tm_meta (uu____2749))
in (FStar_All.pipe_left mk1 uu____2748))
end
| uu____2759 -> begin
tm1
end))
end)))
and desugar_attributes : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun env cattributes -> (

let desugar_attribute = (fun t -> (

let uu____2768 = (

let uu____2769 = (unparen t)
in uu____2769.FStar_Parser_AST.tm)
in (match (uu____2768) with
| FStar_Parser_AST.Var ({FStar_Ident.ns = uu____2770; FStar_Ident.ident = uu____2771; FStar_Ident.nsstr = uu____2772; FStar_Ident.str = "cps"}) -> begin
FStar_Syntax_Syntax.CPS
end
| uu____2774 -> begin
(

let uu____2775 = (

let uu____2776 = (

let uu____2779 = (

let uu____2780 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "Unknown attribute " uu____2780))
in ((uu____2779), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____2776))
in (Prims.raise uu____2775))
end)))
in (FStar_List.map desugar_attribute cattributes)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (

let mk1 = (fun e -> ((FStar_Syntax_Syntax.mk e) None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let uu___228_2808 = e
in {FStar_Syntax_Syntax.n = uu___228_2808.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___228_2808.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___228_2808.FStar_Syntax_Syntax.vars}))
in (

let uu____2815 = (

let uu____2816 = (unparen top)
in uu____2816.FStar_Parser_AST.tm)
in (match (uu____2815) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (uu____2817) -> begin
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
| FStar_Parser_AST.Op ({FStar_Ident.idText = "=!="; FStar_Ident.idRange = r}, args) -> begin
(

let e = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Op ((((FStar_Ident.mk_ident (("=="), (r)))), (args)))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Op ((((FStar_Ident.mk_ident (("~"), (r)))), ((e)::[])))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))
end
| FStar_Parser_AST.Op (op_star, (uu____2849)::(uu____2850)::[]) when (((FStar_Ident.text_of_id op_star) = "*") && (

let uu____2852 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range op_star)
in (FStar_All.pipe_right uu____2852 FStar_Option.isNone))) -> begin
(

let rec flatten1 = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____2861}, (t1)::(t2)::[]) -> begin
(

let uu____2865 = (flatten1 t1)
in (FStar_List.append uu____2865 ((t2)::[])))
end
| uu____2867 -> begin
(t)::[]
end))
in (

let targs = (

let uu____2870 = (

let uu____2872 = (unparen top)
in (flatten1 uu____2872))
in (FStar_All.pipe_right uu____2870 (FStar_List.map (fun t -> (

let uu____2876 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg uu____2876))))))
in (

let uu____2877 = (

let uu____2880 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) uu____2880))
in (match (uu____2877) with
| (tup, uu____2887) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____2890 = (

let uu____2893 = (FStar_ToSyntax_Env.fail_or2 (FStar_ToSyntax_Env.try_lookup_id env) a)
in (Prims.fst uu____2893))
in (FStar_All.pipe_left setpos uu____2890))
end
| FStar_Parser_AST.Uvar (u) -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected universe variable " (Prims.strcat (FStar_Ident.text_of_id u) " in non-universe context"))), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(

let uu____2907 = (op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)
in (match (uu____2907) with
| None -> begin
(Prims.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected or unbound operator: " (FStar_Ident.text_of_id s))), (top.FStar_Parser_AST.range)))))
end
| Some (op) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let args1 = (FStar_All.pipe_right args (FStar_List.map (fun t -> (

let uu____2929 = (desugar_term env t)
in ((uu____2929), (None))))))
in (mk1 (FStar_Syntax_Syntax.Tm_app (((op), (args1))))))
end
| uu____2935 -> begin
op
end)
end))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2936; FStar_Ident.ident = uu____2937; FStar_Ident.nsstr = uu____2938; FStar_Ident.str = "Type0"}) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2940; FStar_Ident.ident = uu____2941; FStar_Ident.nsstr = uu____2942; FStar_Ident.str = "Type"}) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Construct ({FStar_Ident.ns = uu____2944; FStar_Ident.ident = uu____2945; FStar_Ident.nsstr = uu____2946; FStar_Ident.str = "Type"}, ((t, FStar_Parser_AST.UnivApp))::[]) -> begin
(

let uu____2956 = (

let uu____2957 = (desugar_universe t)
in FStar_Syntax_Syntax.Tm_type (uu____2957))
in (mk1 uu____2956))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2958; FStar_Ident.ident = uu____2959; FStar_Ident.nsstr = uu____2960; FStar_Ident.str = "Effect"}) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2962; FStar_Ident.ident = uu____2963; FStar_Ident.nsstr = uu____2964; FStar_Ident.str = "True"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant None)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____2966; FStar_Ident.ident = uu____2967; FStar_Ident.nsstr = uu____2968; FStar_Ident.str = "False"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant None)
end
| FStar_Parser_AST.Projector (eff_name, {FStar_Ident.idText = txt; FStar_Ident.idRange = uu____2972}) when ((is_special_effect_combinator txt) && (FStar_ToSyntax_Env.is_effect_name env eff_name)) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name);
(

let uu____2974 = (FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name)
in (match (uu____2974) with
| Some (ed) -> begin
(

let uu____2977 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" txt))) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.fvar uu____2977 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None))
end
| None -> begin
(

let uu____2978 = (FStar_Util.format2 "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)" (FStar_Ident.text_of_lid eff_name) txt)
in (failwith uu____2978))
end));
)
end
| FStar_Parser_AST.Assign (ident, t2) -> begin
(

let t21 = (desugar_term env t2)
in (

let uu____2982 = (FStar_ToSyntax_Env.fail_or2 (FStar_ToSyntax_Env.try_lookup_id env) ident)
in (match (uu____2982) with
| (t1, mut) -> begin
((match ((not (mut))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Can only assign to mutable values"), (top.FStar_Parser_AST.range)))))
end
| uu____2990 -> begin
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

let uu____3000 = (FStar_ToSyntax_Env.try_lookup_datacon env l)
in (match (uu____3000) with
| Some (uu____3005) -> begin
Some (((true), (l)))
end
| None -> begin
(

let uu____3008 = (FStar_ToSyntax_Env.try_lookup_root_effect_name env l)
in (match (uu____3008) with
| Some (new_name) -> begin
Some (((false), (new_name)))
end
| uu____3016 -> begin
None
end))
end))
in (match (name) with
| Some (resolve, new_name) -> begin
(

let uu____3024 = (FStar_Syntax_Util.mk_field_projector_name_from_ident new_name i)
in (desugar_name mk1 setpos env resolve uu____3024))
end
| uu____3025 -> begin
(

let uu____3029 = (

let uu____3030 = (

let uu____3033 = (FStar_Util.format1 "Data constructor or effect %s not found" l.FStar_Ident.str)
in ((uu____3033), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____3030))
in (Prims.raise uu____3029))
end));
)
end
| FStar_Parser_AST.Discrim (lid) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid);
(

let uu____3036 = (FStar_ToSyntax_Env.try_lookup_datacon env lid)
in (match (uu____3036) with
| None -> begin
(

let uu____3038 = (

let uu____3039 = (

let uu____3042 = (FStar_Util.format1 "Data constructor %s not found" lid.FStar_Ident.str)
in ((uu____3042), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____3039))
in (Prims.raise uu____3038))
end
| uu____3043 -> begin
(

let lid' = (FStar_Syntax_Util.mk_discriminator lid)
in (desugar_name mk1 setpos env true lid'))
end));
)
end
| FStar_Parser_AST.Construct (l, args) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l);
(

let uu____3055 = (FStar_ToSyntax_Env.try_lookup_datacon env l)
in (match (uu____3055) with
| Some (head1) -> begin
(

let uu____3058 = (

let uu____3063 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (head1)))
in ((uu____3063), (true)))
in (match (uu____3058) with
| (head2, is_data) -> begin
(match (args) with
| [] -> begin
head2
end
| uu____3076 -> begin
(

let uu____3080 = (FStar_Util.take (fun uu____3091 -> (match (uu____3091) with
| (uu____3094, imp) -> begin
(imp = FStar_Parser_AST.UnivApp)
end)) args)
in (match (uu____3080) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun x -> (desugar_universe (Prims.fst x))) universes)
in (

let args2 = (FStar_List.map (fun uu____3127 -> (match (uu____3127) with
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
| uu____3142 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_uinst (((head2), (universes1)))))
end)
in (

let app = (mk1 (FStar_Syntax_Syntax.Tm_app (((head3), (args2)))))
in (match (is_data) with
| true -> begin
(mk1 (FStar_Syntax_Syntax.Tm_meta (((app), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end
| uu____3157 -> begin
app
end)))))
end))
end)
end))
end
| None -> begin
(

let error_msg = (

let uu____3159 = (FStar_ToSyntax_Env.try_lookup_effect_name env l)
in (match (uu____3159) with
| None -> begin
(Prims.strcat "Constructor " (Prims.strcat l.FStar_Ident.str " not found"))
end
| Some (uu____3161) -> begin
(Prims.strcat "Effect " (Prims.strcat l.FStar_Ident.str " used at an unexpected position"))
end))
in (Prims.raise (FStar_Errors.Error (((error_msg), (top.FStar_Parser_AST.range))))))
end));
)
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let uu____3166 = (FStar_List.fold_left (fun uu____3183 b -> (match (uu____3183) with
| (env1, tparams, typs) -> begin
(

let uu____3214 = (desugar_binder env1 b)
in (match (uu____3214) with
| (xopt, t1) -> begin
(

let uu____3230 = (match (xopt) with
| None -> begin
(

let uu____3235 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env1), (uu____3235)))
end
| Some (x) -> begin
(FStar_ToSyntax_Env.push_bv env1 x)
end)
in (match (uu____3230) with
| (env2, x) -> begin
(

let uu____3247 = (

let uu____3249 = (

let uu____3251 = (

let uu____3252 = (no_annot_abs tparams t1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3252))
in (uu____3251)::[])
in (FStar_List.append typs uu____3249))
in ((env2), ((FStar_List.append tparams (((((

let uu___229_3265 = x
in {FStar_Syntax_Syntax.ppname = uu___229_3265.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___229_3265.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})), (None)))::[]))), (uu____3247)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type_level None))::[])))
in (match (uu____3166) with
| (env1, uu____3278, targs) -> begin
(

let uu____3290 = (

let uu____3293 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_ToSyntax_Env.fail_or env1 (FStar_ToSyntax_Env.try_lookup_lid env1) uu____3293))
in (match (uu____3290) with
| (tup, uu____3300) -> begin
(FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let uu____3308 = (uncurry binders t)
in (match (uu____3308) with
| (bs, t1) -> begin
(

let rec aux = (fun env1 bs1 uu___209_3331 -> (match (uu___209_3331) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range env1 t1)
in (

let uu____3341 = (FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod)
in (FStar_All.pipe_left setpos uu____3341)))
end
| (hd1)::tl1 -> begin
(

let bb = (desugar_binder env1 hd1)
in (

let uu____3357 = (as_binder env1 hd1.FStar_Parser_AST.aqual bb)
in (match (uu____3357) with
| (b, env2) -> begin
(aux env2 ((b)::bs1) tl1)
end)))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(

let uu____3368 = (desugar_binder env b)
in (match (uu____3368) with
| (None, uu____3372) -> begin
(failwith "Missing binder in refinement")
end
| b1 -> begin
(

let uu____3378 = (as_binder env None b1)
in (match (uu____3378) with
| ((x, uu____3382), env1) -> begin
(

let f1 = (desugar_formula env1 f)
in (

let uu____3387 = (FStar_Syntax_Util.refine x f1)
in (FStar_All.pipe_left setpos uu____3387)))
end))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let binders1 = (FStar_All.pipe_right binders (FStar_List.map replace_unit_pattern))
in (

let uu____3402 = (FStar_List.fold_left (fun uu____3409 pat -> (match (uu____3409) with
| (env1, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (uu____3424, t) -> begin
(

let uu____3426 = (

let uu____3428 = (free_type_vars env1 t)
in (FStar_List.append uu____3428 ftvs))
in ((env1), (uu____3426)))
end
| uu____3431 -> begin
((env1), (ftvs))
end)
end)) ((env), ([])) binders1)
in (match (uu____3402) with
| (uu____3434, ftv) -> begin
(

let ftv1 = (sort_ftv ftv)
in (

let binders2 = (

let uu____3442 = (FStar_All.pipe_right ftv1 (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append uu____3442 binders1))
in (

let rec aux = (fun env1 bs sc_pat_opt uu___210_3471 -> (match (uu___210_3471) with
| [] -> begin
(

let body1 = (desugar_term env1 body)
in (

let body2 = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(

let body2 = (

let uu____3500 = (

let uu____3501 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right uu____3501 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close uu____3500 body1))
in ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (None), (body2)))::[]))))) None body2.FStar_Syntax_Syntax.pos))
end
| None -> begin
body1
end)
in (

let uu____3543 = (no_annot_abs (FStar_List.rev bs) body2)
in (setpos uu____3543))))
end
| (p)::rest -> begin
(

let uu____3551 = (desugar_binding_pat env1 p)
in (match (uu____3551) with
| (env2, b, pat) -> begin
(

let uu____3563 = (match (b) with
| LetBinder (uu____3582) -> begin
(failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt1 = (match (((pat), (sc_pat_opt))) with
| (None, uu____3613) -> begin
sc_pat_opt
end
| (Some (p1), None) -> begin
(

let uu____3636 = (

let uu____3639 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____3639), (p1)))
in Some (uu____3636))
end
| (Some (p1), Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (uu____3664), uu____3665) -> begin
(

let tup2 = (

let uu____3667 = (FStar_Syntax_Util.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____3667 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____3671 = (

let uu____3674 = (

let uu____3675 = (

let uu____3685 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (

let uu____3688 = (

let uu____3690 = (FStar_Syntax_Syntax.as_arg sc)
in (

let uu____3691 = (

let uu____3693 = (

let uu____3694 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3694))
in (uu____3693)::[])
in (uu____3690)::uu____3691))
in ((uu____3685), (uu____3688))))
in FStar_Syntax_Syntax.Tm_app (uu____3675))
in (FStar_Syntax_Syntax.mk uu____3674))
in (uu____3671 None top.FStar_Parser_AST.range))
in (

let p2 = (

let uu____3709 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p1), (false)))::[])))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n uu____3709))
in Some (((sc1), (p2))))))
end
| (FStar_Syntax_Syntax.Tm_app (uu____3729, args), FStar_Syntax_Syntax.Pat_cons (uu____3731, pats)) -> begin
(

let tupn = (

let uu____3758 = (FStar_Syntax_Util.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____3758 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____3768 = (

let uu____3769 = (

let uu____3779 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (

let uu____3782 = (

let uu____3788 = (

let uu____3794 = (

let uu____3795 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____3795))
in (uu____3794)::[])
in (FStar_List.append args uu____3788))
in ((uu____3779), (uu____3782))))
in FStar_Syntax_Syntax.Tm_app (uu____3769))
in (mk1 uu____3768))
in (

let p2 = (

let uu____3810 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p1), (false)))::[])))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n uu____3810))
in Some (((sc1), (p2))))))
end
| uu____3834 -> begin
(failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt1)))
end)
in (match (uu____3563) with
| (b1, sc_pat_opt1) -> begin
(aux env2 ((b1)::bs) sc_pat_opt1 rest)
end))
end))
end))
in (aux env [] None binders2))))
end)))
end
| FStar_Parser_AST.App (uu____3875, uu____3876, FStar_Parser_AST.UnivApp) -> begin
(

let rec aux = (fun universes e -> (

let uu____3888 = (

let uu____3889 = (unparen e)
in uu____3889.FStar_Parser_AST.tm)
in (match (uu____3888) with
| FStar_Parser_AST.App (e1, t, FStar_Parser_AST.UnivApp) -> begin
(

let univ_arg = (desugar_universe t)
in (aux ((univ_arg)::universes) e1))
end
| uu____3895 -> begin
(

let head1 = (desugar_term env e)
in (mk1 (FStar_Syntax_Syntax.Tm_uinst (((head1), (universes))))))
end)))
in (aux [] top))
end
| FStar_Parser_AST.App (uu____3898) -> begin
(

let rec aux = (fun args e -> (

let uu____3919 = (

let uu____3920 = (unparen e)
in uu____3920.FStar_Parser_AST.tm)
in (match (uu____3919) with
| FStar_Parser_AST.App (e1, t, imp) when (imp <> FStar_Parser_AST.UnivApp) -> begin
(

let arg = (

let uu____3930 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) uu____3930))
in (aux ((arg)::args) e1))
end
| uu____3937 -> begin
(

let head1 = (desugar_term env e)
in (mk1 (FStar_Syntax_Syntax.Tm_app (((head1), (args))))))
end)))
in (aux [] top))
end
| FStar_Parser_AST.Bind (x, t1, t2) -> begin
(

let xpat = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (None)))) x.FStar_Ident.idRange)
in (

let k = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ((((xpat)::[]), (t2)))) t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level)
in (

let bind1 = (

let uu____3954 = (

let uu____3955 = (FStar_Ident.lid_of_path (("bind")::[]) x.FStar_Ident.idRange)
in FStar_Parser_AST.Var (uu____3955))
in (FStar_Parser_AST.mk_term uu____3954 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let uu____3956 = (FStar_Parser_AST.mkExplicitApp bind1 ((t1)::(k)::[]) top.FStar_Parser_AST.range)
in (desugar_term env uu____3956)))))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(

let uu____3959 = (

let uu____3960 = (

let uu____3965 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((uu____3965), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))
in FStar_Syntax_Syntax.Tm_meta (uu____3960))
in (mk1 uu____3959))
end
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(

let env1 = (FStar_ToSyntax_Env.push_namespace env lid)
in (

let uu____3976 = (

let uu____3981 = (FStar_ToSyntax_Env.expect_typ env1)
in (match (uu____3981) with
| true -> begin
desugar_typ
end
| uu____3986 -> begin
desugar_term
end))
in (uu____3976 env1 e)))
end
| FStar_Parser_AST.Let (qual1, ((pat, _snd))::_tl, body) -> begin
(

let is_rec = (qual1 = FStar_Parser_AST.Rec)
in (

let ds_let_rec_or_app = (fun uu____4006 -> (

let bindings = (((pat), (_snd)))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun uu____4048 -> (match (uu____4048) with
| (p, def) -> begin
(

let uu____4062 = (is_app_pattern p)
in (match (uu____4062) with
| true -> begin
(

let uu____4072 = (destruct_app_pattern env top_level p)
in ((uu____4072), (def)))
end
| uu____4087 -> begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p1, def1) -> begin
(

let uu____4101 = (destruct_app_pattern env top_level p1)
in ((uu____4101), (def1)))
end
| uu____4116 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, uu____4130); FStar_Parser_AST.prange = uu____4131}, t) -> begin
(match (top_level) with
| true -> begin
(

let uu____4144 = (

let uu____4152 = (

let uu____4155 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (uu____4155))
in ((uu____4152), ([]), (Some (t))))
in ((uu____4144), (def)))
end
| uu____4167 -> begin
((((FStar_Util.Inl (id)), ([]), (Some (t)))), (def))
end)
end
| FStar_Parser_AST.PatVar (id, uu____4180) -> begin
(match (top_level) with
| true -> begin
(

let uu____4192 = (

let uu____4200 = (

let uu____4203 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (uu____4203))
in ((uu____4200), ([]), (None)))
in ((uu____4192), (def)))
end
| uu____4215 -> begin
((((FStar_Util.Inl (id)), ([]), (None))), (def))
end)
end
| uu____4227 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end))
end))))
in (

let uu____4237 = (FStar_List.fold_left (fun uu____4261 uu____4262 -> (match (((uu____4261), (uu____4262))) with
| ((env1, fnames, rec_bindings), ((f, uu____4306, uu____4307), uu____4308)) -> begin
(

let uu____4348 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let uu____4362 = (FStar_ToSyntax_Env.push_bv env1 x)
in (match (uu____4362) with
| (env2, xx) -> begin
(

let uu____4373 = (

let uu____4375 = (FStar_Syntax_Syntax.mk_binder xx)
in (uu____4375)::rec_bindings)
in ((env2), (FStar_Util.Inl (xx)), (uu____4373)))
end))
end
| FStar_Util.Inr (l) -> begin
(

let uu____4380 = (FStar_ToSyntax_Env.push_top_level_rec_binding env1 l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in ((uu____4380), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (uu____4348) with
| (env2, lbname, rec_bindings1) -> begin
((env2), ((lbname)::fnames), (rec_bindings1))
end))
end)) ((env), ([]), ([])) funs)
in (match (uu____4237) with
| (env', fnames, rec_bindings) -> begin
(

let fnames1 = (FStar_List.rev fnames)
in (

let rec_bindings1 = (FStar_List.rev rec_bindings)
in (

let desugar_one_def = (fun env1 lbname uu____4453 -> (match (uu____4453) with
| ((uu____4465, args, result_t), def) -> begin
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

let uu____4491 = (is_comp_type env1 t)
in (match (uu____4491) with
| true -> begin
((

let uu____4493 = (FStar_All.pipe_right args1 (FStar_List.tryFind (fun x -> (

let uu____4498 = (is_var_pattern x)
in (not (uu____4498))))))
in (match (uu____4493) with
| None -> begin
()
end
| Some (p) -> begin
(Prims.raise (FStar_Errors.Error ((("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable"), (p.FStar_Parser_AST.prange)))))
end));
t;
)
end
| uu____4500 -> begin
(

let uu____4501 = (((FStar_Options.ml_ish ()) && (

let uu____4502 = (FStar_ToSyntax_Env.try_lookup_effect_name env1 FStar_Syntax_Const.effect_ML_lid)
in (FStar_Option.isSome uu____4502))) && ((not (is_rec)) || ((FStar_List.length args1) <> (Prims.parse_int "0"))))
in (match (uu____4501) with
| true -> begin
(FStar_Parser_AST.ml_comp t)
end
| uu____4506 -> begin
(FStar_Parser_AST.tot_comp t)
end))
end))
in (

let uu____4507 = (FStar_Range.union_ranges t1.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t1), (None)))) uu____4507 FStar_Parser_AST.Expr)))
end)
in (

let def2 = (match (args1) with
| [] -> begin
def1
end
| uu____4510 -> begin
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

let uu____4520 = (

let uu____4521 = (FStar_Syntax_Util.incr_delta_qualifier body1)
in (FStar_Syntax_Syntax.lid_as_fv l uu____4521 None))
in FStar_Util.Inr (uu____4520))
end)
in (

let body2 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.close rec_bindings1 body1)
end
| uu____4523 -> begin
body1
end)
in (mk_lb ((lbname1), (FStar_Syntax_Syntax.tun), (body2)))))))))
end))
in (

let lbs = (FStar_List.map2 (desugar_one_def (match (is_rec) with
| true -> begin
env'
end
| uu____4539 -> begin
env
end)) fnames1 funs)
in (

let body1 = (desugar_term env' body)
in (

let uu____4541 = (

let uu____4542 = (

let uu____4550 = (FStar_Syntax_Subst.close rec_bindings1 body1)
in ((((is_rec), (lbs))), (uu____4550)))
in FStar_Syntax_Syntax.Tm_let (uu____4542))
in (FStar_All.pipe_left mk1 uu____4541)))))))
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
| uu____4576 -> begin
t11
end)
in (

let uu____4577 = (desugar_binding_pat_maybe_top top_level env pat1 is_mutable)
in (match (uu____4577) with
| (env1, binder, pat2) -> begin
(

let tm = (match (binder) with
| LetBinder (l, t) -> begin
(

let body1 = (desugar_term env1 t2)
in (

let fv = (

let uu____4598 = (FStar_Syntax_Util.incr_delta_qualifier t12)
in (FStar_Syntax_Syntax.lid_as_fv l uu____4598 None))
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_let (((((false), (({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t12})::[]))), (body1)))))))
end
| LocalBinder (x, uu____4606) -> begin
(

let body1 = (desugar_term env1 t2)
in (

let body2 = (match (pat2) with
| (None) | (Some ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (_); FStar_Syntax_Syntax.ty = _; FStar_Syntax_Syntax.p = _})) -> begin
body1
end
| Some (pat3) -> begin
(

let uu____4615 = (

let uu____4618 = (

let uu____4619 = (

let uu____4635 = (FStar_Syntax_Syntax.bv_to_name x)
in (

let uu____4636 = (

let uu____4638 = (FStar_Syntax_Util.branch ((pat3), (None), (body1)))
in (uu____4638)::[])
in ((uu____4635), (uu____4636))))
in FStar_Syntax_Syntax.Tm_match (uu____4619))
in (FStar_Syntax_Syntax.mk uu____4618))
in (uu____4615 None body1.FStar_Syntax_Syntax.pos))
end)
in (

let uu____4653 = (

let uu____4654 = (

let uu____4662 = (

let uu____4663 = (

let uu____4664 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____4664)::[])
in (FStar_Syntax_Subst.close uu____4663 body2))
in ((((false), (((mk_lb ((FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t12))))::[]))), (uu____4662)))
in FStar_Syntax_Syntax.Tm_let (uu____4654))
in (FStar_All.pipe_left mk1 uu____4653))))
end)
in (match (is_mutable) with
| true -> begin
(FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((tm), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc))))))
end
| uu____4683 -> begin
tm
end))
end))))))
in (

let uu____4684 = (is_rec || (is_app_pattern pat))
in (match (uu____4684) with
| true -> begin
(ds_let_rec_or_app ())
end
| uu____4685 -> begin
(ds_non_rec pat _snd body)
end)))))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (

let uu____4690 = (

let uu____4691 = (

let uu____4707 = (desugar_term env t1)
in (

let uu____4708 = (

let uu____4718 = (

let uu____4727 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (

let uu____4730 = (desugar_term env t2)
in ((uu____4727), (None), (uu____4730))))
in (

let uu____4738 = (

let uu____4748 = (

let uu____4757 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (

let uu____4760 = (desugar_term env t3)
in ((uu____4757), (None), (uu____4760))))
in (uu____4748)::[])
in (uu____4718)::uu____4738))
in ((uu____4707), (uu____4708))))
in FStar_Syntax_Syntax.Tm_match (uu____4691))
in (mk1 uu____4690)))
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

let desugar_branch = (fun uu____4846 -> (match (uu____4846) with
| (pat, wopt, b) -> begin
(

let uu____4856 = (desugar_match_pat env pat)
in (match (uu____4856) with
| (env1, pat1) -> begin
(

let wopt1 = (match (wopt) with
| None -> begin
None
end
| Some (e1) -> begin
(

let uu____4865 = (desugar_term env1 e1)
in Some (uu____4865))
end)
in (

let b1 = (desugar_term env1 b)
in (FStar_Syntax_Util.branch ((pat1), (wopt1), (b1)))))
end))
end))
in (

let uu____4868 = (

let uu____4869 = (

let uu____4885 = (desugar_term env e)
in (

let uu____4886 = (FStar_List.map desugar_branch branches)
in ((uu____4885), (uu____4886))))
in FStar_Syntax_Syntax.Tm_match (uu____4869))
in (FStar_All.pipe_left mk1 uu____4868)))
end
| FStar_Parser_AST.Ascribed (e, t, tac_opt) -> begin
(

let annot = (

let uu____4905 = (is_comp_type env t)
in (match (uu____4905) with
| true -> begin
(

let uu____4910 = (desugar_comp t.FStar_Parser_AST.range env t)
in FStar_Util.Inr (uu____4910))
end
| uu____4915 -> begin
(

let uu____4916 = (desugar_term env t)
in FStar_Util.Inl (uu____4916))
end))
in (

let tac_opt1 = (FStar_Util.map_opt tac_opt (desugar_term env))
in (

let uu____4921 = (

let uu____4922 = (

let uu____4940 = (desugar_term env e)
in ((uu____4940), (((annot), (tac_opt1))), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____4922))
in (FStar_All.pipe_left mk1 uu____4921))))
end
| FStar_Parser_AST.Record (uu____4956, []) -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let record = (check_fields env fields top.FStar_Parser_AST.range)
in (

let user_ns = (

let uu____4977 = (FStar_List.hd fields)
in (match (uu____4977) with
| (f, uu____4984) -> begin
f.FStar_Ident.ns
end))
in (

let get_field = (fun xopt f -> (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun uu____5008 -> (match (uu____5008) with
| (g, uu____5012) -> begin
(f.FStar_Ident.idText = g.FStar_Ident.ident.FStar_Ident.idText)
end))))
in (

let fn = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((f)::[])))
in (match (found) with
| Some (uu____5016, e) -> begin
((fn), (e))
end
| None -> begin
(match (xopt) with
| None -> begin
(

let uu____5024 = (

let uu____5025 = (

let uu____5028 = (FStar_Util.format2 "Field %s of record type %s is missing" f.FStar_Ident.idText record.FStar_ToSyntax_Env.typename.FStar_Ident.str)
in ((uu____5028), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____5025))
in (Prims.raise uu____5024))
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

let uu____5034 = (

let uu____5040 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____5054 -> (match (uu____5054) with
| (f, uu____5060) -> begin
(

let uu____5061 = (

let uu____5062 = (get_field None f)
in (FStar_All.pipe_left Prims.snd uu____5062))
in ((uu____5061), (FStar_Parser_AST.Nothing)))
end))))
in ((user_constrname), (uu____5040)))
in FStar_Parser_AST.Construct (uu____5034))
end
| Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (

let uu____5073 = (

let uu____5074 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____5074))
in (FStar_Parser_AST.mk_term uu____5073 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record1 = (

let uu____5076 = (

let uu____5083 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____5097 -> (match (uu____5097) with
| (f, uu____5103) -> begin
(get_field (Some (xterm)) f)
end))))
in ((None), (uu____5083)))
in FStar_Parser_AST.Record (uu____5076))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record1 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm1 = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_term env recterm1)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____5119; FStar_Syntax_Syntax.pos = uu____5120; FStar_Syntax_Syntax.vars = uu____5121}, args); FStar_Syntax_Syntax.tk = uu____5123; FStar_Syntax_Syntax.pos = uu____5124; FStar_Syntax_Syntax.vars = uu____5125}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(

let e1 = (

let uu____5147 = (

let uu____5148 = (

let uu____5158 = (

let uu____5159 = (

let uu____5161 = (

let uu____5162 = (

let uu____5166 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_ToSyntax_Env.typename), (uu____5166)))
in FStar_Syntax_Syntax.Record_ctor (uu____5162))
in Some (uu____5161))
in (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant uu____5159))
in ((uu____5158), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____5148))
in (FStar_All.pipe_left mk1 uu____5147))
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((e1), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))))))
end
| uu____5190 -> begin
e
end))))))))
end
| FStar_Parser_AST.Project (e, f) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f);
(

let uu____5194 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f)
in (match (uu____5194) with
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
| uu____5206 -> begin
None
end)
in (

let uu____5207 = (

let uu____5208 = (

let uu____5218 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projname (FStar_Ident.range_of_lid f)) FStar_Syntax_Syntax.Delta_equational qual1)
in (

let uu____5219 = (

let uu____5221 = (FStar_Syntax_Syntax.as_arg e1)
in (uu____5221)::[])
in ((uu____5218), (uu____5219))))
in FStar_Syntax_Syntax.Tm_app (uu____5208))
in (FStar_All.pipe_left mk1 uu____5207)))))
end));
)
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| uu____5227 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| uu____5228 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Let (uu____5229, uu____5230, uu____5231) -> begin
(failwith "Not implemented yet")
end
| FStar_Parser_AST.QForall (uu____5238, uu____5239, uu____5240) -> begin
(failwith "Not implemented yet")
end
| FStar_Parser_AST.QExists (uu____5247, uu____5248, uu____5249) -> begin
(failwith "Not implemented yet")
end)))))
and desugar_args : FStar_ToSyntax_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____5273 -> (match (uu____5273) with
| (a, imp) -> begin
(

let uu____5281 = (desugar_term env a)
in (arg_withimp_e imp uu____5281))
end)))))
and desugar_comp : FStar_Range.range  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r env t -> (

let fail = (fun msg -> (Prims.raise (FStar_Errors.Error (((msg), (r))))))
in (

let is_requires = (fun uu____5298 -> (match (uu____5298) with
| (t1, uu____5302) -> begin
(

let uu____5303 = (

let uu____5304 = (unparen t1)
in uu____5304.FStar_Parser_AST.tm)
in (match (uu____5303) with
| FStar_Parser_AST.Requires (uu____5305) -> begin
true
end
| uu____5309 -> begin
false
end))
end))
in (

let is_ensures = (fun uu____5315 -> (match (uu____5315) with
| (t1, uu____5319) -> begin
(

let uu____5320 = (

let uu____5321 = (unparen t1)
in uu____5321.FStar_Parser_AST.tm)
in (match (uu____5320) with
| FStar_Parser_AST.Ensures (uu____5322) -> begin
true
end
| uu____5326 -> begin
false
end))
end))
in (

let is_app = (fun head1 uu____5335 -> (match (uu____5335) with
| (t1, uu____5339) -> begin
(

let uu____5340 = (

let uu____5341 = (unparen t1)
in uu____5341.FStar_Parser_AST.tm)
in (match (uu____5340) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = uu____5343; FStar_Parser_AST.level = uu____5344}, uu____5345, uu____5346) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head1)
end
| uu____5347 -> begin
false
end))
end))
in (

let is_smt_pat = (fun uu____5353 -> (match (uu____5353) with
| (t1, uu____5357) -> begin
(

let uu____5358 = (

let uu____5359 = (unparen t1)
in uu____5359.FStar_Parser_AST.tm)
in (match (uu____5358) with
| FStar_Parser_AST.Construct (cons1, (({FStar_Parser_AST.tm = FStar_Parser_AST.Construct (smtpat, uu____5362); FStar_Parser_AST.range = uu____5363; FStar_Parser_AST.level = uu____5364}, uu____5365))::(uu____5366)::[]) -> begin
((FStar_Ident.lid_equals cons1 FStar_Syntax_Const.cons_lid) && (FStar_Util.for_some (fun s -> (smtpat.FStar_Ident.str = s)) (("SMTPat")::("SMTPatT")::("SMTPatOr")::[])))
end
| uu____5385 -> begin
false
end))
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t1 -> (

let uu____5403 = (head_and_args t1)
in (match (uu____5403) with
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

let uu____5620 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes env) l)
in ((uu____5620), (args)))
end
| FStar_Parser_AST.Name (l) when ((

let uu____5634 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals uu____5634 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head1.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when ((

let uu____5643 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals uu____5643 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head1.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when (((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head1.FStar_Parser_AST.range)), ([]))), ((((t1), (FStar_Parser_AST.Nothing)))::[]))
end
| uu____5663 -> begin
(

let default_effect = (

let uu____5665 = (FStar_Options.ml_ish ())
in (match (uu____5665) with
| true -> begin
FStar_Syntax_Const.effect_ML_lid
end
| uu____5666 -> begin
((

let uu____5668 = (FStar_Options.warn_default_effects ())
in (match (uu____5668) with
| true -> begin
(FStar_Errors.warn head1.FStar_Parser_AST.range "Using default effect Tot")
end
| uu____5669 -> begin
()
end));
FStar_Syntax_Const.effect_Tot_lid;
)
end))
in (((((FStar_Ident.set_lid_range default_effect head1.FStar_Parser_AST.range)), ([]))), ((((t1), (FStar_Parser_AST.Nothing)))::[])))
end)
end)))
in (

let uu____5681 = (pre_process_comp_typ t)
in (match (uu____5681) with
| ((eff, cattributes), args) -> begin
((match (((FStar_List.length args) = (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5711 = (

let uu____5712 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" uu____5712))
in (fail uu____5711))
end
| uu____5713 -> begin
()
end);
(

let is_universe = (fun uu____5719 -> (match (uu____5719) with
| (uu____5722, imp) -> begin
(imp = FStar_Parser_AST.UnivApp)
end))
in (

let uu____5724 = (FStar_Util.take is_universe args)
in (match (uu____5724) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun uu____5755 -> (match (uu____5755) with
| (u, imp) -> begin
(desugar_universe u)
end)) universes)
in (

let uu____5760 = (

let uu____5768 = (FStar_List.hd args1)
in (

let uu____5773 = (FStar_List.tl args1)
in ((uu____5768), (uu____5773))))
in (match (uu____5760) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (Prims.fst result_arg))
in (

let rest1 = (desugar_args env rest)
in (

let uu____5804 = (

let is_decrease = (fun uu____5827 -> (match (uu____5827) with
| (t1, uu____5834) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = uu____5842; FStar_Syntax_Syntax.pos = uu____5843; FStar_Syntax_Syntax.vars = uu____5844}, (uu____5845)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| uu____5867 -> begin
false
end)
end))
in (FStar_All.pipe_right rest1 (FStar_List.partition is_decrease)))
in (match (uu____5804) with
| (dec, rest2) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun uu____5933 -> (match (uu____5933) with
| (t1, uu____5940) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____5947, ((arg, uu____5949))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| uu____5971 -> begin
(failwith "impos")
end)
end))))
in (

let no_additional_args = (

let is_empty = (fun l -> (match (l) with
| [] -> begin
true
end
| uu____5983 -> begin
false
end))
in ((((is_empty decreases_clause) && (is_empty rest2)) && (is_empty cattributes)) && (is_empty universes1)))
in (match ((no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid))) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end
| uu____5992 -> begin
(match ((no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid))) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end
| uu____5995 -> begin
(

let flags = (match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid)) with
| true -> begin
(FStar_Syntax_Syntax.LEMMA)::[]
end
| uu____5999 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____6001 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_ML_lid)) with
| true -> begin
(FStar_Syntax_Syntax.MLEFFECT)::[]
end
| uu____6003 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____6005 -> begin
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

let uu____6075 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.mk_Tm_uinst uu____6075 ((FStar_Syntax_Syntax.U_zero)::[])))
in ((FStar_Syntax_Syntax.mk_Tm_app nil ((((pattern), (Some (FStar_Syntax_Syntax.imp_tag))))::[])) None pat.FStar_Syntax_Syntax.pos)))
end
| uu____6087 -> begin
pat
end)
in (

let uu____6088 = (

let uu____6095 = (

let uu____6102 = (

let uu____6108 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat1), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)))))) None pat1.FStar_Syntax_Syntax.pos)
in ((uu____6108), (aq)))
in (uu____6102)::[])
in (ens)::uu____6095)
in (req)::uu____6088))
end
| uu____6144 -> begin
rest2
end)
end
| uu____6151 -> begin
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
| uu____6160 -> begin
None
end))
in (

let mk1 = (fun t -> ((FStar_Syntax_Syntax.mk t) None f.FStar_Parser_AST.range))
in (

let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let uu___230_6201 = t
in {FStar_Syntax_Syntax.n = uu___230_6201.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = uu___230_6201.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___230_6201.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let uu___231_6231 = b
in {FStar_Parser_AST.b = uu___231_6231.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___231_6231.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___231_6231.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env1 pats1 -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (

let uu____6264 = (desugar_term env1 e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) uu____6264)))))) pats1))
in (match (tk) with
| (Some (a), k) -> begin
(

let uu____6273 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____6273) with
| (env1, a1) -> begin
(

let a2 = (

let uu___232_6281 = a1
in {FStar_Syntax_Syntax.ppname = uu___232_6281.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___232_6281.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats1 = (desugar_pats env1 pats)
in (

let body1 = (desugar_formula env1 body)
in (

let body2 = (match (pats1) with
| [] -> begin
body1
end
| uu____6294 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_meta (((body1), (FStar_Syntax_Syntax.Meta_pattern (pats1))))))
end)
in (

let body3 = (

let uu____6303 = (

let uu____6306 = (

let uu____6307 = (FStar_Syntax_Syntax.mk_binder a2)
in (uu____6307)::[])
in (no_annot_abs uu____6306 body2))
in (FStar_All.pipe_left setpos uu____6303))
in (

let uu____6312 = (

let uu____6313 = (

let uu____6323 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (

let uu____6324 = (

let uu____6326 = (FStar_Syntax_Syntax.as_arg body3)
in (uu____6326)::[])
in ((uu____6323), (uu____6324))))
in FStar_Syntax_Syntax.Tm_app (uu____6313))
in (FStar_All.pipe_left mk1 uu____6312)))))))
end))
end
| uu____6330 -> begin
(failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body1 = (

let uu____6379 = (q ((rest), (pats), (body)))
in (

let uu____6383 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term uu____6379 uu____6383 FStar_Parser_AST.Formula)))
in (

let uu____6384 = (q (((b)::[]), ([]), (body1)))
in (FStar_Parser_AST.mk_term uu____6384 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| uu____6389 -> begin
(failwith "impossible")
end))
in (

let uu____6391 = (

let uu____6392 = (unparen f)
in uu____6392.FStar_Parser_AST.tm)
in (match (uu____6391) with
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

let uu____6422 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env uu____6422)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____6443 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env uu____6443)))
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
| uu____6468 -> begin
(desugar_term env f)
end)))))))))
and typars_of_binders : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_ToSyntax_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (

let uu____6472 = (FStar_List.fold_left (fun uu____6485 b -> (match (uu____6485) with
| (env1, out) -> begin
(

let tk = (desugar_binder env1 (

let uu___233_6513 = b
in {FStar_Parser_AST.b = uu___233_6513.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___233_6513.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___233_6513.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(

let uu____6523 = (FStar_ToSyntax_Env.push_bv env1 a)
in (match (uu____6523) with
| (env2, a1) -> begin
(

let a2 = (

let uu___234_6535 = a1
in {FStar_Syntax_Syntax.ppname = uu___234_6535.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___234_6535.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in ((env2), ((((a2), ((trans_aqual b.FStar_Parser_AST.aqual))))::out)))
end))
end
| uu____6544 -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (uu____6472) with
| (env1, tpars) -> begin
((env1), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(

let uu____6594 = (desugar_typ env t)
in ((Some (x)), (uu____6594)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____6597 = ((FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown))) None x.FStar_Ident.idRange)
in ((Some (x)), (uu____6597)))
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____6612 = (desugar_typ env t)
in ((None), (uu____6612)))
end
| FStar_Parser_AST.Variable (x) -> begin
((Some (x)), (FStar_Syntax_Syntax.tun))
end))


let mk_data_discriminators = (fun quals env t tps k datas -> (

let quals1 = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___211_6661 -> (match (uu___211_6661) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| uu____6662 -> begin
false
end))))
in (

let quals2 = (fun q -> (

let uu____6670 = ((

let uu____6671 = (FStar_ToSyntax_Env.iface env)
in (not (uu____6671))) || (FStar_ToSyntax_Env.admitted_iface env))
in (match (uu____6670) with
| true -> begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals1)
end
| uu____6673 -> begin
(FStar_List.append q quals1)
end)))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (

let uu____6678 = (

let uu____6679 = (

let uu____6685 = (quals2 ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in ((disc_name), ([]), (FStar_Syntax_Syntax.tun), (uu____6685)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____6679))
in {FStar_Syntax_Syntax.sigel = uu____6678; FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid disc_name)}))))))))


let mk_indexed_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  FStar_ToSyntax_Env.env  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq env lid fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let uu____6710 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____6720 -> (match (uu____6720) with
| (x, uu____6725) -> begin
(

let uu____6726 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____6726) with
| (field_name, uu____6731) -> begin
(

let only_decl = (((

let uu____6733 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid uu____6733)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (

let uu____6734 = (

let uu____6735 = (FStar_ToSyntax_Env.current_module env)
in uu____6735.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____6734)))
in (

let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____6745 = (FStar_List.filter (fun uu___212_6747 -> (match (uu___212_6747) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____6748 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____6745)
end
| uu____6749 -> begin
q
end))
in (

let quals1 = (

let iquals1 = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___213_6756 -> (match (uu___213_6756) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| uu____6757 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals1)))
in (

let decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), ([]), (FStar_Syntax_Syntax.tun), (quals1))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid field_name)}
in (match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____6762 -> begin
(

let dd = (

let uu____6764 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____6764) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____6766 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lb = (

let uu____6768 = (

let uu____6771 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (uu____6771))
in {FStar_Syntax_Syntax.lbname = uu____6768; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = FStar_Syntax_Syntax.tun})
in (

let impl = (

let uu____6773 = (

let uu____6774 = (

let uu____6782 = (

let uu____6784 = (

let uu____6785 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____6785 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____6784)::[])
in ((((false), ((lb)::[]))), (uu____6782), (quals1), ([])))
in FStar_Syntax_Syntax.Sig_let (uu____6774))
in {FStar_Syntax_Syntax.sigel = uu____6773; FStar_Syntax_Syntax.sigrng = p})
in (match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____6801 -> begin
(decl)::(impl)::[]
end))))
end))))))
end))
end))))
in (FStar_All.pipe_right uu____6710 FStar_List.flatten))))


let mk_data_projector_names = (fun iquals env uu____6825 -> (match (uu____6825) with
| (inductive_tps, se) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____6833, t, uu____6835, n1, quals, uu____6838) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let uu____6843 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____6843) with
| (formals, uu____6853) -> begin
(match (formals) with
| [] -> begin
[]
end
| uu____6867 -> begin
(

let filter_records = (fun uu___214_6875 -> (match (uu___214_6875) with
| FStar_Syntax_Syntax.RecordConstructor (uu____6877, fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| uu____6884 -> begin
None
end))
in (

let fv_qual = (

let uu____6886 = (FStar_Util.find_map quals filter_records)
in (match (uu____6886) with
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
| uu____6892 -> begin
iquals
end)
in (

let uu____6893 = (FStar_Util.first_N n1 formals)
in (match (uu____6893) with
| (uu____6905, rest) -> begin
(mk_indexed_projector_names iquals1 fv_qual env lid rest)
end)))))
end)
end))
end
| uu____6919 -> begin
[]
end)
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (

let dd = (

let uu____6957 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____6957) with
| true -> begin
(

let uu____6959 = (FStar_Syntax_Util.incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (uu____6959))
end
| uu____6960 -> begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end))
in (

let lb = (

let uu____6962 = (

let uu____6965 = (FStar_Syntax_Syntax.lid_as_fv lid dd None)
in FStar_Util.Inr (uu____6965))
in (

let uu____6966 = (

let uu____6969 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars uu____6969))
in (

let uu____6972 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = uu____6962; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____6966; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____6972})))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (lids), (quals), ([]))); FStar_Syntax_Syntax.sigrng = rng})))


let rec desugar_tycon : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d quals tcs -> (

let rng = d.FStar_Parser_AST.drange
in (

let tycon_id = (fun uu___215_7006 -> (match (uu___215_7006) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(

let uu____7045 = (

let uu____7046 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____7046))
in (FStar_Parser_AST.mk_term uu____7045 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
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
| uu____7068 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (

let uu____7071 = (

let uu____7072 = (

let uu____7076 = (binder_to_term b)
in ((out), (uu____7076), ((imp_of_aqual b))))
in FStar_Parser_AST.App (uu____7072))
in (FStar_Parser_AST.mk_term uu____7071 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun uu___216_7083 -> (match (uu___216_7083) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun uu____7112 -> (match (uu____7112) with
| (x, t, uu____7119) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Syntax_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (

let result = (

let uu____7123 = (

let uu____7124 = (

let uu____7125 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (uu____7125))
in (FStar_Parser_AST.mk_term uu____7124 id.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____7123 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type_level)
in (

let uu____7128 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____7140 -> (match (uu____7140) with
| (x, uu____7146, uu____7147) -> begin
(FStar_Syntax_Util.unmangle_field_name x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (Some (constrTyp)), (None), (false)))::[])))), (uu____7128)))))))
end
| uu____7174 -> begin
(failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals1 _env mutuals uu___217_7196 -> (match (uu___217_7196) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let uu____7210 = (typars_of_binders _env binders)
in (match (uu____7210) with
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

let uu____7238 = (

let uu____7239 = (

let uu____7240 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (uu____7240))
in (FStar_Parser_AST.mk_term uu____7239 id.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____7238 binders))
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
| uu____7251 -> begin
(failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env1 bs -> (

let uu____7277 = (FStar_List.fold_left (fun uu____7293 uu____7294 -> (match (((uu____7293), (uu____7294))) with
| ((env2, tps), (x, imp)) -> begin
(

let uu____7342 = (FStar_ToSyntax_Env.push_bv env2 x.FStar_Syntax_Syntax.ppname)
in (match (uu____7342) with
| (env3, y) -> begin
((env3), ((((y), (imp)))::tps))
end))
end)) ((env1), ([])) bs)
in (match (uu____7277) with
| (env2, bs1) -> begin
((env2), ((FStar_List.rev bs1)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id, bs, kopt))::[] -> begin
(

let kopt1 = (match (kopt) with
| None -> begin
(

let uu____7403 = (tm_type_z id.FStar_Ident.idRange)
in Some (uu____7403))
end
| uu____7404 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id), (bs), (kopt1)))
in (

let uu____7409 = (desugar_abstract_tc quals env [] tc)
in (match (uu____7409) with
| (uu____7416, uu____7417, se, uu____7419) -> begin
(

let se1 = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, uu____7422, typars, k, [], [], quals1) -> begin
(

let quals2 = (

let uu____7432 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Assumption))
in (match (uu____7432) with
| true -> begin
quals1
end
| uu____7435 -> begin
((

let uu____7437 = (FStar_Range.string_of_range se.FStar_Syntax_Syntax.sigrng)
in (

let uu____7438 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" uu____7437 uu____7438)));
(FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals1;
)
end))
in (

let t = (match (typars) with
| [] -> begin
k
end
| uu____7442 -> begin
(

let uu____7443 = (

let uu____7446 = (

let uu____7447 = (

let uu____7455 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (uu____7455)))
in FStar_Syntax_Syntax.Tm_arrow (uu____7447))
in (FStar_Syntax_Syntax.mk uu____7446))
in (uu____7443 None se.FStar_Syntax_Syntax.sigrng))
end)
in (

let uu___235_7464 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t), (quals2))); FStar_Syntax_Syntax.sigrng = uu___235_7464.FStar_Syntax_Syntax.sigrng})))
end
| uu____7467 -> begin
(failwith "Impossible")
end)
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env se1)
in (

let env2 = (

let uu____7470 = (FStar_ToSyntax_Env.qualify env1 id)
in (FStar_ToSyntax_Env.push_doc env1 uu____7470 d.FStar_Parser_AST.doc))
in ((env2), ((se1)::[])))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let uu____7480 = (typars_of_binders env binders)
in (match (uu____7480) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
(

let uu____7500 = (FStar_Util.for_some (fun uu___218_7501 -> (match (uu___218_7501) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| uu____7502 -> begin
false
end)) quals)
in (match (uu____7500) with
| true -> begin
FStar_Syntax_Syntax.teff
end
| uu____7503 -> begin
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

let uu____7508 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___219_7510 -> (match (uu___219_7510) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| uu____7511 -> begin
false
end))))
in (match (uu____7508) with
| true -> begin
quals
end
| uu____7513 -> begin
(match ((t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula)) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals
end
| uu____7515 -> begin
quals
end)
end))
in (

let qlid = (FStar_ToSyntax_Env.qualify env id)
in (

let se = (

let uu____7518 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Effect))
in (match (uu____7518) with
| true -> begin
(

let uu____7520 = (

let uu____7524 = (

let uu____7525 = (unparen t)
in uu____7525.FStar_Parser_AST.tm)
in (match (uu____7524) with
| FStar_Parser_AST.Construct (head1, args) -> begin
(

let uu____7537 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____7553))::args_rev -> begin
(

let uu____7560 = (

let uu____7561 = (unparen last_arg)
in uu____7561.FStar_Parser_AST.tm)
in (match (uu____7560) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____7576 -> begin
(([]), (args))
end))
end
| uu____7581 -> begin
(([]), (args))
end)
in (match (uu____7537) with
| (cattributes, args1) -> begin
(

let uu____7602 = (desugar_attributes env cattributes)
in (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((head1), (args1)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (uu____7602)))
end))
end
| uu____7608 -> begin
((t), ([]))
end))
in (match (uu____7520) with
| (t1, cattributes) -> begin
(

let c = (desugar_comp t1.FStar_Parser_AST.range env' t1)
in (

let typars1 = (FStar_Syntax_Subst.close_binders typars)
in (

let c1 = (FStar_Syntax_Subst.close_comp typars1 c)
in (

let uu____7619 = (

let uu____7620 = (

let uu____7629 = (FStar_All.pipe_right quals1 (FStar_List.filter (fun uu___220_7633 -> (match (uu___220_7633) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| uu____7634 -> begin
true
end))))
in ((qlid), ([]), (typars1), (c1), (uu____7629), ((FStar_List.append cattributes (FStar_Syntax_Util.comp_flags c1)))))
in FStar_Syntax_Syntax.Sig_effect_abbrev (uu____7620))
in {FStar_Syntax_Syntax.sigel = uu____7619; FStar_Syntax_Syntax.sigrng = rng}))))
end))
end
| uu____7638 -> begin
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
| (FStar_Parser_AST.TyconRecord (uu____7643))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let uu____7656 = (tycon_record_as_variant trec)
in (match (uu____7656) with
| (t, fs) -> begin
(

let uu____7666 = (

let uu____7668 = (

let uu____7669 = (

let uu____7674 = (

let uu____7676 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.ids_of_lid uu____7676))
in ((uu____7674), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____7669))
in (uu____7668)::quals)
in (desugar_tycon env d uu____7666 ((t)::[])))
end)))
end
| (uu____7679)::uu____7680 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals1 et tc -> (

let uu____7767 = et
in (match (uu____7767) with
| (env1, tcs1) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (uu____7881) -> begin
(

let trec = tc
in (

let uu____7894 = (tycon_record_as_variant trec)
in (match (uu____7894) with
| (t, fs) -> begin
(

let uu____7925 = (

let uu____7927 = (

let uu____7928 = (

let uu____7933 = (

let uu____7935 = (FStar_ToSyntax_Env.current_module env1)
in (FStar_Ident.ids_of_lid uu____7935))
in ((uu____7933), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____7928))
in (uu____7927)::quals1)
in (collect_tcs uu____7925 ((env1), (tcs1)) t))
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let uu____7981 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (uu____7981) with
| (env2, uu____8012, se, tconstr) -> begin
((env2), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals1))))::tcs1))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let uu____8090 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (uu____8090) with
| (env2, uu____8121, se, tconstr) -> begin
((env2), ((FStar_Util.Inr (((se), (binders), (t), (quals1))))::tcs1))
end))
end
| uu____8185 -> begin
(failwith "Unrecognized mutual type definition")
end)
end)))
in (

let uu____8209 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (uu____8209) with
| (env1, tcs1) -> begin
(

let tcs2 = (FStar_List.rev tcs1)
in (

let docs_tps_sigelts = (FStar_All.pipe_right tcs2 (FStar_List.collect (fun uu___222_8459 -> (match (uu___222_8459) with
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, uu____8495, uu____8496, uu____8497); FStar_Syntax_Syntax.sigrng = uu____8498}, binders, t, quals1) -> begin
(

let t1 = (

let uu____8531 = (typars_of_binders env1 binders)
in (match (uu____8531) with
| (env2, tpars1) -> begin
(

let uu____8548 = (push_tparams env2 tpars1)
in (match (uu____8548) with
| (env_tps, tpars2) -> begin
(

let t1 = (desugar_typ env_tps t)
in (

let tpars3 = (FStar_Syntax_Subst.close_binders tpars2)
in (FStar_Syntax_Subst.close tpars3 t1)))
end))
end))
in (

let uu____8567 = (

let uu____8578 = (mk_typ_abbrev id uvs tpars k t1 ((id)::[]) quals1 rng)
in ((((id), (d.FStar_Parser_AST.doc))), ([]), (uu____8578)))
in (uu____8567)::[]))
end
| FStar_Util.Inl ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals1, uu____8615, tags); FStar_Syntax_Syntax.sigrng = uu____8617}, constrs, tconstr, quals1) -> begin
(

let mk_tot = (fun t -> (

let tot1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((tot1), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)))
in (

let tycon = ((tname), (tpars), (k))
in (

let uu____8670 = (push_tparams env1 tpars)
in (match (uu____8670) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun uu____8709 -> (match (uu____8709) with
| (x, uu____8717) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let tot_tconstr = (mk_tot tconstr)
in (

let uu____8722 = (

let uu____8737 = (FStar_All.pipe_right constrs (FStar_List.map (fun uu____8789 -> (match (uu____8789) with
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
| uu____8819 -> begin
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

let uu____8822 = (close env_tps t)
in (desugar_term env_tps uu____8822))
in (

let name = (FStar_ToSyntax_Env.qualify env1 id)
in (

let quals2 = (FStar_All.pipe_right tags (FStar_List.collect (fun uu___221_8828 -> (match (uu___221_8828) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| uu____8835 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (

let uu____8841 = (

let uu____8852 = (

let uu____8853 = (

let uu____8854 = (

let uu____8864 = (

let uu____8867 = (

let uu____8870 = (FStar_All.pipe_right t1 FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total uu____8870))
in (FStar_Syntax_Util.arrow data_tpars uu____8867))
in ((name), (univs), (uu____8864), (tname), (ntps), (quals2), (mutuals1)))
in FStar_Syntax_Syntax.Sig_datacon (uu____8854))
in {FStar_Syntax_Syntax.sigel = uu____8853; FStar_Syntax_Syntax.sigrng = rng})
in ((((name), (doc1))), (tps), (uu____8852)))
in ((name), (uu____8841))))))))
end))))
in (FStar_All.pipe_left FStar_List.split uu____8737))
in (match (uu____8722) with
| (constrNames, constrs1) -> begin
(((((tname), (d.FStar_Parser_AST.doc))), ([]), ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs), (tpars), (k), (mutuals1), (constrNames), (tags))); FStar_Syntax_Syntax.sigrng = rng})))::constrs1
end))))
end))))
end
| uu____8995 -> begin
(failwith "impossible")
end))))
in (

let name_docs = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.map (fun uu____9060 -> (match (uu____9060) with
| (name_doc, uu____9075, uu____9076) -> begin
name_doc
end))))
in (

let sigelts = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.map (fun uu____9115 -> (match (uu____9115) with
| (uu____9126, uu____9127, se) -> begin
se
end))))
in (

let uu____9143 = (

let uu____9147 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle sigelts quals uu____9147 rng))
in (match (uu____9143) with
| (bundle, abbrevs) -> begin
(

let env2 = (FStar_ToSyntax_Env.push_sigelt env0 bundle)
in (

let env3 = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2 abbrevs)
in (

let data_ops = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.collect (fun uu____9181 -> (match (uu____9181) with
| (uu____9193, tps, se) -> begin
(mk_data_projector_names quals env3 ((tps), (se)))
end))))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, uu____9225, tps, k, uu____9228, constrs, quals1) when ((FStar_List.length constrs) > (Prims.parse_int "1")) -> begin
(

let quals2 = (match ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals1)) with
| true -> begin
(FStar_Syntax_Syntax.Private)::quals1
end
| uu____9243 -> begin
quals1
end)
in (mk_data_discriminators quals2 env3 tname tps k constrs))
end
| uu____9244 -> begin
[]
end))))
in (

let ops = (FStar_List.append discs data_ops)
in (

let env4 = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env3 ops)
in (

let env5 = (FStar_List.fold_left (fun acc uu____9253 -> (match (uu____9253) with
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

let uu____9275 = (FStar_List.fold_left (fun uu____9282 b -> (match (uu____9282) with
| (env1, binders1) -> begin
(

let uu____9294 = (desugar_binder env1 b)
in (match (uu____9294) with
| (Some (a), k) -> begin
(

let uu____9304 = (as_binder env1 b.FStar_Parser_AST.aqual ((Some (a)), (k)))
in (match (uu____9304) with
| (binder, env2) -> begin
((env2), ((binder)::binders1))
end))
end
| uu____9314 -> begin
(Prims.raise (FStar_Errors.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) binders)
in (match (uu____9275) with
| (env1, binders1) -> begin
((env1), ((FStar_List.rev binders1)))
end)))


let rec desugar_effect : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_typ eff_decls -> (

let env0 = env
in (

let monad_env = (FStar_ToSyntax_Env.enter_monad_scope env eff_name)
in (

let uu____9392 = (desugar_binders monad_env eff_binders)
in (match (uu____9392) with
| (env1, binders) -> begin
(

let eff_t = (desugar_term env1 eff_typ)
in (

let for_free = (

let uu____9405 = (

let uu____9406 = (

let uu____9410 = (FStar_Syntax_Util.arrow_formals eff_t)
in (Prims.fst uu____9410))
in (FStar_List.length uu____9406))
in (uu____9405 = (Prims.parse_int "1")))
in (

let mandatory_members = (

let rr_members = ("repr")::("return")::("bind")::[]
in (match (for_free) with
| true -> begin
rr_members
end
| uu____9433 -> begin
(FStar_List.append rr_members (("return_wp")::("bind_wp")::("if_then_else")::("ite_wp")::("stronger")::("close_wp")::("assert_p")::("assume_p")::("null_wp")::("trivial")::[]))
end))
in (

let name_of_eff_decl = (fun decl -> (match (decl.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____9438, ((FStar_Parser_AST.TyconAbbrev (name, uu____9440, uu____9441, uu____9442), uu____9443))::[]) -> begin
(FStar_Ident.text_of_id name)
end
| uu____9460 -> begin
(failwith "Malformed effect member declaration.")
end))
in (

let uu____9461 = (FStar_List.partition (fun decl -> (

let uu____9467 = (name_of_eff_decl decl)
in (FStar_List.mem uu____9467 mandatory_members))) eff_decls)
in (match (uu____9461) with
| (mandatory_members_decls, actions) -> begin
(

let uu____9477 = (FStar_All.pipe_right mandatory_members_decls (FStar_List.fold_left (fun uu____9488 decl -> (match (uu____9488) with
| (env2, out) -> begin
(

let uu____9500 = (desugar_decl env2 decl)
in (match (uu____9500) with
| (env3, ses) -> begin
(

let uu____9508 = (

let uu____9510 = (FStar_List.hd ses)
in (uu____9510)::out)
in ((env3), (uu____9508)))
end))
end)) ((env1), ([]))))
in (match (uu____9477) with
| (env2, decls) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (

let actions_docs = (FStar_All.pipe_right actions (FStar_List.map (fun d1 -> (match (d1.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____9538, ((FStar_Parser_AST.TyconAbbrev (name, action_params, uu____9541, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (uu____9542, ((def, uu____9544))::((cps_type, uu____9546))::[]); FStar_Parser_AST.range = uu____9547; FStar_Parser_AST.level = uu____9548}), doc1))::[]) when (not (for_free)) -> begin
(

let uu____9575 = (desugar_binders env2 action_params)
in (match (uu____9575) with
| (env3, action_params1) -> begin
(

let action_params2 = (FStar_Syntax_Subst.close_binders action_params1)
in (

let uu____9587 = (

let uu____9588 = (FStar_ToSyntax_Env.qualify env3 name)
in (

let uu____9589 = (

let uu____9590 = (desugar_term env3 def)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____9590))
in (

let uu____9593 = (

let uu____9594 = (desugar_typ env3 cps_type)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____9594))
in {FStar_Syntax_Syntax.action_name = uu____9588; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = action_params2; FStar_Syntax_Syntax.action_defn = uu____9589; FStar_Syntax_Syntax.action_typ = uu____9593})))
in ((uu____9587), (doc1))))
end))
end
| FStar_Parser_AST.Tycon (uu____9598, ((FStar_Parser_AST.TyconAbbrev (name, action_params, uu____9601, defn), doc1))::[]) when for_free -> begin
(

let uu____9620 = (desugar_binders env2 action_params)
in (match (uu____9620) with
| (env3, action_params1) -> begin
(

let action_params2 = (FStar_Syntax_Subst.close_binders action_params1)
in (

let uu____9632 = (

let uu____9633 = (FStar_ToSyntax_Env.qualify env3 name)
in (

let uu____9634 = (

let uu____9635 = (desugar_term env3 defn)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____9635))
in {FStar_Syntax_Syntax.action_name = uu____9633; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = action_params2; FStar_Syntax_Syntax.action_defn = uu____9634; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
in ((uu____9632), (doc1))))
end))
end
| uu____9639 -> begin
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

let uu____9658 = (

let uu____9659 = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_definition env2) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders1) uu____9659))
in (([]), (uu____9658)))))
in (

let mname = (FStar_ToSyntax_Env.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange (Some (mname))) quals)
in (

let se = (match (for_free) with
| true -> begin
(

let dummy_tscheme = (

let uu____9671 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (([]), (uu____9671)))
in (

let uu____9681 = (

let uu____9682 = (

let uu____9683 = (

let uu____9684 = (lookup "repr")
in (Prims.snd uu____9684))
in (

let uu____9689 = (lookup "return")
in (

let uu____9690 = (lookup "bind")
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = eff_t1; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = uu____9683; FStar_Syntax_Syntax.return_repr = uu____9689; FStar_Syntax_Syntax.bind_repr = uu____9690; FStar_Syntax_Syntax.actions = actions1})))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____9682))
in {FStar_Syntax_Syntax.sigel = uu____9681; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange}))
end
| uu____9691 -> begin
(

let rr = (FStar_Util.for_some (fun uu___223_9693 -> (match (uu___223_9693) with
| (FStar_Syntax_Syntax.Reifiable) | (FStar_Syntax_Syntax.Reflectable (_)) -> begin
true
end
| uu____9695 -> begin
false
end)) qualifiers)
in (

let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in (

let uu____9701 = (

let uu____9702 = (

let uu____9703 = (lookup "return_wp")
in (

let uu____9704 = (lookup "bind_wp")
in (

let uu____9705 = (lookup "if_then_else")
in (

let uu____9706 = (lookup "ite_wp")
in (

let uu____9707 = (lookup "stronger")
in (

let uu____9708 = (lookup "close_wp")
in (

let uu____9709 = (lookup "assert_p")
in (

let uu____9710 = (lookup "assume_p")
in (

let uu____9711 = (lookup "null_wp")
in (

let uu____9712 = (lookup "trivial")
in (

let uu____9713 = (match (rr) with
| true -> begin
(

let uu____9714 = (lookup "repr")
in (FStar_All.pipe_left Prims.snd uu____9714))
end
| uu____9722 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let uu____9723 = (match (rr) with
| true -> begin
(lookup "return")
end
| uu____9724 -> begin
un_ts
end)
in (

let uu____9725 = (match (rr) with
| true -> begin
(lookup "bind")
end
| uu____9726 -> begin
un_ts
end)
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = eff_t1; FStar_Syntax_Syntax.ret_wp = uu____9703; FStar_Syntax_Syntax.bind_wp = uu____9704; FStar_Syntax_Syntax.if_then_else = uu____9705; FStar_Syntax_Syntax.ite_wp = uu____9706; FStar_Syntax_Syntax.stronger = uu____9707; FStar_Syntax_Syntax.close_wp = uu____9708; FStar_Syntax_Syntax.assert_p = uu____9709; FStar_Syntax_Syntax.assume_p = uu____9710; FStar_Syntax_Syntax.null_wp = uu____9711; FStar_Syntax_Syntax.trivial = uu____9712; FStar_Syntax_Syntax.repr = uu____9713; FStar_Syntax_Syntax.return_repr = uu____9723; FStar_Syntax_Syntax.bind_repr = uu____9725; FStar_Syntax_Syntax.actions = actions1})))))))))))))
in FStar_Syntax_Syntax.Sig_new_effect (uu____9702))
in {FStar_Syntax_Syntax.sigel = uu____9701; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange})))
end)
in (

let env3 = (FStar_ToSyntax_Env.push_sigelt env0 se)
in (

let env4 = (FStar_ToSyntax_Env.push_doc env3 mname d.FStar_Parser_AST.doc)
in (

let env5 = (FStar_All.pipe_right actions_docs (FStar_List.fold_left (fun env5 uu____9738 -> (match (uu____9738) with
| (a, doc1) -> begin
(

let env6 = (

let uu____9747 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_ToSyntax_Env.push_sigelt env5 uu____9747))
in (FStar_ToSyntax_Env.push_doc env6 a.FStar_Syntax_Syntax.action_name doc1))
end)) env4))
in (

let env6 = (

let uu____9749 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____9749) with
| true -> begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_ToSyntax_Env.qualify monad_env))
in (

let refl_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange}
in (FStar_ToSyntax_Env.push_sigelt env5 refl_decl)))
end
| uu____9754 -> begin
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

let uu____9773 = (desugar_binders env1 eff_binders)
in (match (uu____9773) with
| (env2, binders) -> begin
(

let uu____9784 = (

let uu____9794 = (head_and_args defn)
in (match (uu____9794) with
| (head1, args) -> begin
(

let lid = (match (head1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
l
end
| uu____9819 -> begin
(

let uu____9820 = (

let uu____9821 = (

let uu____9824 = (

let uu____9825 = (

let uu____9826 = (FStar_Parser_AST.term_to_string head1)
in (Prims.strcat uu____9826 " not found"))
in (Prims.strcat "Effect " uu____9825))
in ((uu____9824), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____9821))
in (Prims.raise uu____9820))
end)
in (

let ed = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_effect_defn env2) lid)
in (

let uu____9828 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____9844))::args_rev -> begin
(

let uu____9851 = (

let uu____9852 = (unparen last_arg)
in uu____9852.FStar_Parser_AST.tm)
in (match (uu____9851) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____9867 -> begin
(([]), (args))
end))
end
| uu____9872 -> begin
(([]), (args))
end)
in (match (uu____9828) with
| (cattributes, args1) -> begin
(

let uu____9899 = (desugar_args env2 args1)
in (

let uu____9904 = (desugar_attributes env2 cattributes)
in ((lid), (ed), (uu____9899), (uu____9904))))
end))))
end))
in (match (uu____9784) with
| (ed_lid, ed, args, cattributes) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (

let sub1 = (fun uu____9938 -> (match (uu____9938) with
| (uu____9945, x) -> begin
(

let uu____9949 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (uu____9949) with
| (edb, x1) -> begin
((match (((FStar_List.length args) <> (FStar_List.length edb))) with
| true -> begin
(Prims.raise (FStar_Errors.Error ((("Unexpected number of arguments to effect constructor"), (defn.FStar_Parser_AST.range)))))
end
| uu____9967 -> begin
()
end);
(

let s = (FStar_Syntax_Util.subst_of_list edb args)
in (

let uu____9969 = (

let uu____9970 = (FStar_Syntax_Subst.subst s x1)
in (FStar_Syntax_Subst.close binders1 uu____9970))
in (([]), (uu____9969))));
)
end))
end))
in (

let mname = (FStar_ToSyntax_Env.qualify env0 eff_name)
in (

let ed1 = (

let uu____9974 = (

let uu____9976 = (trans_qual1 (Some (mname)))
in (FStar_List.map uu____9976 quals))
in (

let uu____9979 = (

let uu____9980 = (sub1 (([]), (ed.FStar_Syntax_Syntax.signature)))
in (Prims.snd uu____9980))
in (

let uu____9986 = (sub1 ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____9987 = (sub1 ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____9988 = (sub1 ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____9989 = (sub1 ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____9990 = (sub1 ed.FStar_Syntax_Syntax.stronger)
in (

let uu____9991 = (sub1 ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____9992 = (sub1 ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____9993 = (sub1 ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____9994 = (sub1 ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____9995 = (sub1 ed.FStar_Syntax_Syntax.trivial)
in (

let uu____9996 = (

let uu____9997 = (sub1 (([]), (ed.FStar_Syntax_Syntax.repr)))
in (Prims.snd uu____9997))
in (

let uu____10003 = (sub1 ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____10004 = (sub1 ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____10005 = (FStar_List.map (fun action -> (

let uu____10008 = (FStar_ToSyntax_Env.qualify env2 action.FStar_Syntax_Syntax.action_unqualified_name)
in (

let uu____10009 = (

let uu____10010 = (sub1 (([]), (action.FStar_Syntax_Syntax.action_defn)))
in (Prims.snd uu____10010))
in (

let uu____10016 = (

let uu____10017 = (sub1 (([]), (action.FStar_Syntax_Syntax.action_typ)))
in (Prims.snd uu____10017))
in {FStar_Syntax_Syntax.action_name = uu____10008; FStar_Syntax_Syntax.action_unqualified_name = action.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = action.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = uu____10009; FStar_Syntax_Syntax.action_typ = uu____10016})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = uu____9974; FStar_Syntax_Syntax.cattributes = cattributes; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = uu____9979; FStar_Syntax_Syntax.ret_wp = uu____9986; FStar_Syntax_Syntax.bind_wp = uu____9987; FStar_Syntax_Syntax.if_then_else = uu____9988; FStar_Syntax_Syntax.ite_wp = uu____9989; FStar_Syntax_Syntax.stronger = uu____9990; FStar_Syntax_Syntax.close_wp = uu____9991; FStar_Syntax_Syntax.assert_p = uu____9992; FStar_Syntax_Syntax.assume_p = uu____9993; FStar_Syntax_Syntax.null_wp = uu____9994; FStar_Syntax_Syntax.trivial = uu____9995; FStar_Syntax_Syntax.repr = uu____9996; FStar_Syntax_Syntax.return_repr = uu____10003; FStar_Syntax_Syntax.bind_repr = uu____10004; FStar_Syntax_Syntax.actions = uu____10005}))))))))))))))))
in (

let se = (

let for_free = (

let uu____10025 = (

let uu____10026 = (

let uu____10030 = (FStar_Syntax_Util.arrow_formals ed1.FStar_Syntax_Syntax.signature)
in (Prims.fst uu____10030))
in (FStar_List.length uu____10026))
in (uu____10025 = (Prims.parse_int "1")))
in {FStar_Syntax_Syntax.sigel = (match (for_free) with
| true -> begin
FStar_Syntax_Syntax.Sig_new_effect_for_free (ed1)
end
| uu____10048 -> begin
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

let uu____10059 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_ToSyntax_Env.push_sigelt env5 uu____10059))
in (FStar_ToSyntax_Env.push_doc env6 a.FStar_Syntax_Syntax.action_name doc1)))) env4))
in (

let env6 = (

let uu____10061 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____10061) with
| true -> begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_ToSyntax_Env.qualify monad_env))
in (

let refl_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange}
in (FStar_ToSyntax_Env.push_sigelt env5 refl_decl)))
end
| uu____10067 -> begin
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
| uu____10085 -> begin
()
end);
((env), ((se)::[]));
))
end
| FStar_Parser_AST.Fsdoc (uu____10087) -> begin
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

let uu____10099 = (FStar_ToSyntax_Env.push_module_abbrev env x l)
in ((uu____10099), ([])))
end
| FStar_Parser_AST.Tycon (is_effect, tcs) -> begin
(

let quals = (match (is_effect) with
| true -> begin
(FStar_Parser_AST.Effect_qual)::d.FStar_Parser_AST.quals
end
| uu____10114 -> begin
d.FStar_Parser_AST.quals
end)
in (

let tcs1 = (FStar_List.map (fun uu____10120 -> (match (uu____10120) with
| (x, uu____10125) -> begin
x
end)) tcs)
in (

let uu____10128 = (FStar_List.map (trans_qual1 None) quals)
in (desugar_tycon env d uu____10128 tcs1))))
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
| ((p, uu____10167))::[] -> begin
(

let uu____10172 = (is_app_pattern p)
in (not (uu____10172)))
end
| uu____10173 -> begin
false
end))
in (match ((not (expand_toplevel_pattern))) with
| true -> begin
(

let as_inner_let = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)
in (

let ds_lets = (desugar_term_maybe_top true env as_inner_let)
in (

let uu____10184 = (

let uu____10185 = (FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets)
in uu____10185.FStar_Syntax_Syntax.n)
in (match (uu____10184) with
| FStar_Syntax_Syntax.Tm_let (lbs, uu____10191) -> begin
(

let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals1 = (match (quals) with
| (uu____10211)::uu____10212 -> begin
(FStar_List.map (trans_qual1 None) quals)
end
| uu____10214 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun uu___224_10218 -> (match (uu___224_10218) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (uu____10220); FStar_Syntax_Syntax.lbunivs = uu____10221; FStar_Syntax_Syntax.lbtyp = uu____10222; FStar_Syntax_Syntax.lbeff = uu____10223; FStar_Syntax_Syntax.lbdef = uu____10224} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____10231; FStar_Syntax_Syntax.lbtyp = uu____10232; FStar_Syntax_Syntax.lbeff = uu____10233; FStar_Syntax_Syntax.lbdef = uu____10234} -> begin
(FStar_ToSyntax_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals2 = (

let uu____10246 = (FStar_All.pipe_right lets (FStar_Util.for_some (fun uu____10252 -> (match (uu____10252) with
| (uu____10255, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end))))
in (match (uu____10246) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals1
end
| uu____10258 -> begin
quals1
end))
in (

let lbs1 = (

let uu____10263 = (FStar_All.pipe_right quals2 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____10263) with
| true -> begin
(

let uu____10268 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu___236_10275 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let uu___237_10276 = fv
in {FStar_Syntax_Syntax.fv_name = uu___237_10276.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = uu___237_10276.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = uu___236_10275.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___236_10275.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___236_10275.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___236_10275.FStar_Syntax_Syntax.lbdef})))))
in (((Prims.fst lbs)), (uu____10268)))
end
| uu____10282 -> begin
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
| uu____10304 -> begin
(failwith "Desugaring a let did not produce a let")
end))))
end
| uu____10307 -> begin
(

let uu____10308 = (match (lets) with
| ((pat, body))::[] -> begin
((pat), (body))
end
| uu____10319 -> begin
(failwith "expand_toplevel_pattern should only allow single definition lets")
end)
in (match (uu____10308) with
| (pat, body) -> begin
(

let fresh_toplevel_name = (FStar_Ident.gen FStar_Range.dummyRange)
in (

let fresh_pat = (

let var_pat = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((fresh_toplevel_name), (None)))) FStar_Range.dummyRange)
in (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat1, ty) -> begin
(

let uu___238_10335 = pat1
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed (((var_pat), (ty))); FStar_Parser_AST.prange = uu___238_10335.FStar_Parser_AST.prange})
end
| uu____10336 -> begin
var_pat
end))
in (

let main_let = (desugar_decl env (

let uu___239_10340 = d
in {FStar_Parser_AST.d = FStar_Parser_AST.TopLevelLet (((isrec), ((((fresh_pat), (body)))::[]))); FStar_Parser_AST.drange = uu___239_10340.FStar_Parser_AST.drange; FStar_Parser_AST.doc = uu___239_10340.FStar_Parser_AST.doc; FStar_Parser_AST.quals = (FStar_Parser_AST.Private)::d.FStar_Parser_AST.quals; FStar_Parser_AST.attrs = uu___239_10340.FStar_Parser_AST.attrs}))
in (

let build_projection = (fun uu____10359 id -> (match (uu____10359) with
| (env1, ses) -> begin
(

let main = (

let uu____10372 = (

let uu____10373 = (FStar_Ident.lid_of_ids ((fresh_toplevel_name)::[]))
in FStar_Parser_AST.Var (uu____10373))
in (FStar_Parser_AST.mk_term uu____10372 FStar_Range.dummyRange FStar_Parser_AST.Expr))
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

let uu____10401 = (desugar_decl env1 id_decl)
in (match (uu____10401) with
| (env2, ses') -> begin
((env2), ((FStar_List.append ses ses')))
end))))))))
end))
in (

let bvs = (

let uu____10412 = (gather_pattern_bound_vars pat)
in (FStar_All.pipe_right uu____10412 FStar_Util.set_elements))
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

let uu____10434 = (close_fun env t)
in (desugar_term env uu____10434))
in (

let quals1 = (

let uu____10437 = ((FStar_ToSyntax_Env.iface env) && (FStar_ToSyntax_Env.admitted_iface env))
in (match (uu____10437) with
| true -> begin
(FStar_Parser_AST.Assumption)::quals
end
| uu____10439 -> begin
quals
end))
in (

let lid = (FStar_ToSyntax_Env.qualify env id)
in (

let se = (

let uu____10442 = (

let uu____10443 = (

let uu____10449 = (FStar_List.map (trans_qual1 None) quals1)
in ((lid), ([]), (t1), (uu____10449)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____10443))
in {FStar_Syntax_Syntax.sigel = uu____10442; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange})
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env se)
in (

let env2 = (FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc)
in ((env2), ((se)::[])))))))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(

let uu____10458 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (match (uu____10458) with
| (t, uu____10466) -> begin
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

let uu____10494 = (

let uu____10498 = (FStar_Syntax_Syntax.null_binder t)
in (uu____10498)::[])
in (

let uu____10499 = (

let uu____10502 = (

let uu____10503 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (Prims.fst uu____10503))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____10502))
in (FStar_Syntax_Util.arrow uu____10494 uu____10499)))
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

let uu____10550 = (FStar_ToSyntax_Env.try_lookup_effect_name env l1)
in (match (uu____10550) with
| None -> begin
(

let uu____10552 = (

let uu____10553 = (

let uu____10556 = (

let uu____10557 = (

let uu____10558 = (FStar_Syntax_Print.lid_to_string l1)
in (Prims.strcat uu____10558 " not found"))
in (Prims.strcat "Effect name " uu____10557))
in ((uu____10556), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____10553))
in (Prims.raise uu____10552))
end
| Some (l2) -> begin
l2
end)))
in (

let src = (lookup l.FStar_Parser_AST.msource)
in (

let dst = (lookup l.FStar_Parser_AST.mdest)
in (

let uu____10562 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(

let uu____10584 = (

let uu____10589 = (

let uu____10593 = (desugar_term env t)
in (([]), (uu____10593)))
in Some (uu____10589))
in ((uu____10584), (None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(

let uu____10611 = (

let uu____10616 = (

let uu____10620 = (desugar_term env wp)
in (([]), (uu____10620)))
in Some (uu____10616))
in (

let uu____10625 = (

let uu____10630 = (

let uu____10634 = (desugar_term env t)
in (([]), (uu____10634)))
in Some (uu____10630))
in ((uu____10611), (uu____10625))))
end
| FStar_Parser_AST.LiftForFree (t) -> begin
(

let uu____10648 = (

let uu____10653 = (

let uu____10657 = (desugar_term env t)
in (([]), (uu____10657)))
in Some (uu____10653))
in ((None), (uu____10648)))
end)
in (match (uu____10562) with
| (lift_wp, lift) -> begin
(

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect ({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift}); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange}
in ((env), ((se)::[])))
end)))))
end)))


let desugar_decls : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun uu____10708 d -> (match (uu____10708) with
| (env1, sigelts) -> begin
(

let uu____10720 = (desugar_decl env1 d)
in (match (uu____10720) with
| (env2, se) -> begin
((env2), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls))


let open_prims_all : (FStar_Parser_AST.decoration Prims.list  ->  FStar_Parser_AST.decl) Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.all_lid)) FStar_Range.dummyRange))::[]


let desugar_modul_common : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let env1 = (match (((curmod), (m))) with
| (None, uu____10762) -> begin
env
end
| (Some ({FStar_Syntax_Syntax.name = prev_lid; FStar_Syntax_Syntax.declarations = uu____10765; FStar_Syntax_Syntax.exports = uu____10766; FStar_Syntax_Syntax.is_interface = uu____10767}), FStar_Parser_AST.Module (current_lid, uu____10769)) when ((FStar_Ident.lid_equals prev_lid current_lid) && (FStar_Options.interactive ())) -> begin
env
end
| (Some (prev_mod), uu____10774) -> begin
(FStar_ToSyntax_Env.finish_module_or_interface env prev_mod)
end)
in (

let uu____10776 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(

let uu____10796 = (FStar_ToSyntax_Env.prepare_module_or_interface true admitted env1 mname)
in ((uu____10796), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(

let uu____10806 = (FStar_ToSyntax_Env.prepare_module_or_interface false false env1 mname)
in ((uu____10806), (mname), (decls), (false)))
end)
in (match (uu____10776) with
| ((env2, pop_when_done), mname, decls, intf) -> begin
(

let uu____10824 = (desugar_decls env2 decls)
in (match (uu____10824) with
| (env3, sigelts) -> begin
(

let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in ((env3), (modul), (pop_when_done)))
end))
end))))


let as_interface : FStar_Parser_AST.modul  ->  FStar_Parser_AST.modul = (fun m -> (match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface (((mname), (decls), (true)))
end
| i -> begin
i
end))


let desugar_partial_modul : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (

let m1 = (

let uu____10858 = ((FStar_Options.interactive ()) && (

let uu____10859 = (

let uu____10860 = (

let uu____10861 = (FStar_Options.file_list ())
in (FStar_List.hd uu____10861))
in (FStar_Util.get_file_extension uu____10860))
in (uu____10859 = "fsti")))
in (match (uu____10858) with
| true -> begin
(as_interface m)
end
| uu____10863 -> begin
m
end))
in (

let uu____10864 = (desugar_modul_common curmod env m1)
in (match (uu____10864) with
| (x, y, pop_when_done) -> begin
((match (pop_when_done) with
| true -> begin
(

let uu____10874 = (FStar_ToSyntax_Env.pop ())
in ())
end
| uu____10875 -> begin
()
end);
((x), (y));
)
end))))


let desugar_modul : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul) = (fun env m -> (

let uu____10886 = (desugar_modul_common None env m)
in (match (uu____10886) with
| (env1, modul, pop_when_done) -> begin
(

let env2 = (FStar_ToSyntax_Env.finish_module_or_interface env1 modul)
in ((

let uu____10897 = (FStar_Options.dump_module modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____10897) with
| true -> begin
(

let uu____10898 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" uu____10898))
end
| uu____10899 -> begin
()
end));
(

let uu____10900 = (match (pop_when_done) with
| true -> begin
(FStar_ToSyntax_Env.export_interface modul.FStar_Syntax_Syntax.name env2)
end
| uu____10901 -> begin
env2
end)
in ((uu____10900), (modul)));
))
end)))


let desugar_file : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (

let uu____10911 = (FStar_List.fold_left (fun uu____10918 m -> (match (uu____10918) with
| (env1, mods) -> begin
(

let uu____10930 = (desugar_modul env1 m)
in (match (uu____10930) with
| (env2, m1) -> begin
((env2), ((m1)::mods))
end))
end)) ((env), ([])) f)
in (match (uu____10911) with
| (env1, mods) -> begin
((env1), ((FStar_List.rev mods)))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_ToSyntax_Env.env  ->  FStar_ToSyntax_Env.env = (fun m en -> (

let uu____10954 = (FStar_ToSyntax_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (uu____10954) with
| (en1, pop_when_done) -> begin
(

let en2 = (

let uu____10960 = (FStar_ToSyntax_Env.set_current_module en1 m.FStar_Syntax_Syntax.name)
in (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____10960 m.FStar_Syntax_Syntax.exports))
in (

let env = (FStar_ToSyntax_Env.finish_module_or_interface en2 m)
in (match (pop_when_done) with
| true -> begin
(FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name env)
end
| uu____10962 -> begin
env
end)))
end)))




