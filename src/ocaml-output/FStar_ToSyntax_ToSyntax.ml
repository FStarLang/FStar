
open Prims
open FStar_Pervasives

let desugar_disjunctive_pattern : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.branch Prims.list = (fun pats when_opt branch1 -> (FStar_All.pipe_right pats (FStar_List.map (fun pat -> (FStar_Syntax_Util.branch ((pat), (when_opt), (branch1)))))))


let trans_aqual : FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option = (fun uu___85_66 -> (match (uu___85_66) with
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)
end
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality)
end
| uu____71 -> begin
FStar_Pervasives_Native.None
end))


let trans_qual : FStar_Range.range  ->  FStar_Ident.lident FStar_Pervasives_Native.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun r maybe_effect_id q -> (match (q) with
| FStar_Parser_AST.Logic -> begin
((FStar_Errors.log_issue r ((FStar_Errors.Warning_DeprecatedDefinition), ("The \'logic\' qualifier is deprecated and redundant; please remove it")));
[];
)
end
| uu____98 -> begin
(

let uu____99 = (match (q) with
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
((FStar_Errors.log_issue r ((FStar_Errors.Warning_DeprecatedOpaqueQualifier), ("The \'opaque\' qualifier is deprecated since its use was strangely schizophrenic. There were two overloaded uses: (1) Given \'opaque val f : t\', the behavior was to exclude the definition of \'f\' to the SMT solver. This corresponds roughly to the new \'irreducible\' qualifier. (2) Given \'opaque type t = t\'\', the behavior was to provide the definition of \'t\' to the SMT solver, but not to inline it, unless absolutely required for unification. This corresponds roughly to the behavior of \'unfoldable\' (which is currently the default).")));
FStar_Syntax_Syntax.Visible_default;
)
end
| FStar_Parser_AST.Reflectable -> begin
(match (maybe_effect_id) with
| FStar_Pervasives_Native.None -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ReflectOnlySupportedOnEffects), ("Qualifier reflect only supported on effects")) r)
end
| FStar_Pervasives_Native.Some (effect_id) -> begin
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
(FStar_Errors.raise_error ((FStar_Errors.Fatal_DefaultQualifierNotAllowedOnEffects), ("The \'default\' qualifier on effects is no longer supported")) r)
end
| FStar_Parser_AST.Inline -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnsupportedQualifier), ("Unsupported qualifier")) r)
end
| FStar_Parser_AST.Visible -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnsupportedQualifier), ("Unsupported qualifier")) r)
end
| FStar_Parser_AST.Logic -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnsupportedQualifier), ("Unsupported qualifier")) r)
end)
in (uu____99)::[])
end))


let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun uu___86_106 -> (match (uu___86_106) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end
| FStar_Parser_AST.LightOff -> begin
FStar_Syntax_Syntax.LightOff
end))


let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option = (fun uu___87_117 -> (match (uu___87_117) with
| FStar_Parser_AST.Hash -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)
end
| uu____120 -> begin
FStar_Pervasives_Native.None
end))


let arg_withimp_e : 'Auu____127 . FStar_Parser_AST.imp  ->  'Auu____127  ->  ('Auu____127 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) = (fun imp t -> ((t), ((as_imp imp))))


let arg_withimp_t : 'Auu____152 . FStar_Parser_AST.imp  ->  'Auu____152  ->  ('Auu____152 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
((t), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end
| uu____171 -> begin
((t), (FStar_Pervasives_Native.None))
end))


let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (uu____188) -> begin
true
end
| uu____193 -> begin
false
end)))))


let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t1) -> begin
(unparen t1)
end
| uu____200 -> begin
t
end))


let tm_type_z : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (

let uu____206 = (

let uu____207 = (FStar_Ident.lid_of_path (("Type0")::[]) r)
in FStar_Parser_AST.Name (uu____207))
in (FStar_Parser_AST.mk_term uu____206 r FStar_Parser_AST.Kind)))


let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (

let uu____213 = (

let uu____214 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (uu____214))
in (FStar_Parser_AST.mk_term uu____213 r FStar_Parser_AST.Kind)))


let rec is_comp_type : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> (

let uu____225 = (

let uu____226 = (unparen t)
in uu____226.FStar_Parser_AST.tm)
in (match (uu____225) with
| FStar_Parser_AST.Name (l) -> begin
(

let uu____228 = (FStar_Syntax_DsEnv.try_lookup_effect_name env l)
in (FStar_All.pipe_right uu____228 FStar_Option.isSome))
end
| FStar_Parser_AST.Construct (l, uu____234) -> begin
(

let uu____247 = (FStar_Syntax_DsEnv.try_lookup_effect_name env l)
in (FStar_All.pipe_right uu____247 FStar_Option.isSome))
end
| FStar_Parser_AST.App (head1, uu____253, uu____254) -> begin
(is_comp_type env head1)
end
| FStar_Parser_AST.Paren (t1) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.Ascribed (t1, uu____257, uu____258) -> begin
(is_comp_type env t1)
end
| FStar_Parser_AST.LetOpen (uu____263, t1) -> begin
(is_comp_type env t1)
end
| uu____265 -> begin
false
end)))


let unit_ty : FStar_Parser_AST.term = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.unit_lid)) FStar_Range.dummyRange FStar_Parser_AST.Type_level)


let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n1 s r -> (

let uu____281 = (

let uu____284 = (

let uu____285 = (

let uu____290 = (FStar_Parser_AST.compile_op n1 s r)
in ((uu____290), (r)))
in (FStar_Ident.mk_ident uu____285))
in (uu____284)::[])
in (FStar_All.pipe_right uu____281 FStar_Ident.lid_of_ids)))


let op_as_term : 'Auu____303 . FStar_Syntax_DsEnv.env  ->  Prims.int  ->  'Auu____303  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env arity rng op -> (

let r = (fun l dd -> (

let uu____339 = (

let uu____340 = (

let uu____341 = (FStar_Ident.set_lid_range l op.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____341 dd FStar_Pervasives_Native.None))
in (FStar_All.pipe_right uu____340 FStar_Syntax_Syntax.fv_to_tm))
in FStar_Pervasives_Native.Some (uu____339)))
in (

let fallback = (fun uu____349 -> (

let uu____350 = (FStar_Ident.text_of_id op)
in (match (uu____350) with
| "=" -> begin
(r FStar_Parser_Const.op_Eq FStar_Syntax_Syntax.delta_equational)
end
| ":=" -> begin
(r FStar_Parser_Const.write_lid FStar_Syntax_Syntax.delta_equational)
end
| "<" -> begin
(r FStar_Parser_Const.op_LT FStar_Syntax_Syntax.delta_equational)
end
| "<=" -> begin
(r FStar_Parser_Const.op_LTE FStar_Syntax_Syntax.delta_equational)
end
| ">" -> begin
(r FStar_Parser_Const.op_GT FStar_Syntax_Syntax.delta_equational)
end
| ">=" -> begin
(r FStar_Parser_Const.op_GTE FStar_Syntax_Syntax.delta_equational)
end
| "&&" -> begin
(r FStar_Parser_Const.op_And FStar_Syntax_Syntax.delta_equational)
end
| "||" -> begin
(r FStar_Parser_Const.op_Or FStar_Syntax_Syntax.delta_equational)
end
| "+" -> begin
(r FStar_Parser_Const.op_Addition FStar_Syntax_Syntax.delta_equational)
end
| "-" when (Prims.op_Equality arity (Prims.parse_int "1")) -> begin
(r FStar_Parser_Const.op_Minus FStar_Syntax_Syntax.delta_equational)
end
| "-" -> begin
(r FStar_Parser_Const.op_Subtraction FStar_Syntax_Syntax.delta_equational)
end
| "/" -> begin
(r FStar_Parser_Const.op_Division FStar_Syntax_Syntax.delta_equational)
end
| "%" -> begin
(r FStar_Parser_Const.op_Modulus FStar_Syntax_Syntax.delta_equational)
end
| "!" -> begin
(r FStar_Parser_Const.read_lid FStar_Syntax_Syntax.delta_equational)
end
| "@" -> begin
(

let uu____353 = (FStar_Options.ml_ish ())
in (match (uu____353) with
| true -> begin
(r FStar_Parser_Const.list_append_lid FStar_Syntax_Syntax.delta_equational)
end
| uu____356 -> begin
(r FStar_Parser_Const.list_tot_append_lid FStar_Syntax_Syntax.delta_equational)
end))
end
| "^" -> begin
(r FStar_Parser_Const.strcat_lid FStar_Syntax_Syntax.delta_equational)
end
| "|>" -> begin
(r FStar_Parser_Const.pipe_right_lid FStar_Syntax_Syntax.delta_equational)
end
| "<|" -> begin
(r FStar_Parser_Const.pipe_left_lid FStar_Syntax_Syntax.delta_equational)
end
| "<>" -> begin
(r FStar_Parser_Const.op_notEq FStar_Syntax_Syntax.delta_equational)
end
| "~" -> begin
(r FStar_Parser_Const.not_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "2"))))
end
| "==" -> begin
(r FStar_Parser_Const.eq2_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "2"))))
end
| "<<" -> begin
(r FStar_Parser_Const.precedes_lid FStar_Syntax_Syntax.delta_constant)
end
| "/\\" -> begin
(r FStar_Parser_Const.and_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))))
end
| "\\/" -> begin
(r FStar_Parser_Const.or_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))))
end
| "==>" -> begin
(r FStar_Parser_Const.imp_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))))
end
| "<==>" -> begin
(r FStar_Parser_Const.iff_lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "2"))))
end
| uu____357 -> begin
FStar_Pervasives_Native.None
end)))
in (

let uu____358 = (

let uu____365 = (compile_op_lid arity op.FStar_Ident.idText op.FStar_Ident.idRange)
in (FStar_Syntax_DsEnv.try_lookup_lid env uu____365))
in (match (uu____358) with
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some ((FStar_Pervasives_Native.fst t))
end
| uu____377 -> begin
(fallback ())
end)))))


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (

let uu____395 = (FStar_Util.remove_dups (fun x y -> (Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) uu____395)))


let rec free_type_vars_b : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (uu____442) -> begin
((env), ([]))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____446 = (FStar_Syntax_DsEnv.push_bv env x)
in (match (uu____446) with
| (env1, uu____458) -> begin
((env1), ((x)::[]))
end))
end
| FStar_Parser_AST.Annotated (uu____461, term) -> begin
(

let uu____463 = (free_type_vars env term)
in ((env), (uu____463)))
end
| FStar_Parser_AST.TAnnotated (id1, uu____469) -> begin
(

let uu____470 = (FStar_Syntax_DsEnv.push_bv env id1)
in (match (uu____470) with
| (env1, uu____482) -> begin
((env1), ([]))
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____486 = (free_type_vars env t)
in ((env), (uu____486)))
end))
and free_type_vars : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (

let uu____493 = (

let uu____494 = (unparen t)
in uu____494.FStar_Parser_AST.tm)
in (match (uu____493) with
| FStar_Parser_AST.Labeled (uu____497) -> begin
(failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____507 = (FStar_Syntax_DsEnv.try_lookup_id env a)
in (match (uu____507) with
| FStar_Pervasives_Native.None -> begin
(a)::[]
end
| uu____520 -> begin
[]
end))
end
| FStar_Parser_AST.Wild -> begin
[]
end
| FStar_Parser_AST.Const (uu____527) -> begin
[]
end
| FStar_Parser_AST.Uvar (uu____528) -> begin
[]
end
| FStar_Parser_AST.Var (uu____529) -> begin
[]
end
| FStar_Parser_AST.Projector (uu____530) -> begin
[]
end
| FStar_Parser_AST.Discrim (uu____535) -> begin
[]
end
| FStar_Parser_AST.Name (uu____536) -> begin
[]
end
| FStar_Parser_AST.Requires (t1, uu____538) -> begin
(free_type_vars env t1)
end
| FStar_Parser_AST.Ensures (t1, uu____544) -> begin
(free_type_vars env t1)
end
| FStar_Parser_AST.NamedTyp (uu____549, t1) -> begin
(free_type_vars env t1)
end
| FStar_Parser_AST.Paren (t1) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.Ascribed (t1, t', tacopt) -> begin
(

let ts = (t1)::(t')::(match (tacopt) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (t2) -> begin
(t2)::[]
end)
in (FStar_List.collect (free_type_vars env) ts))
end
| FStar_Parser_AST.Construct (uu____567, ts) -> begin
(FStar_List.collect (fun uu____588 -> (match (uu____588) with
| (t1, uu____596) -> begin
(free_type_vars env t1)
end)) ts)
end
| FStar_Parser_AST.Op (uu____597, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, uu____605) -> begin
(

let uu____606 = (free_type_vars env t1)
in (

let uu____609 = (free_type_vars env t2)
in (FStar_List.append uu____606 uu____609)))
end
| FStar_Parser_AST.Refine (b, t1) -> begin
(

let uu____614 = (free_type_vars_b env b)
in (match (uu____614) with
| (env1, f) -> begin
(

let uu____629 = (free_type_vars env1 t1)
in (FStar_List.append f uu____629))
end))
end
| FStar_Parser_AST.Product (binders, body) -> begin
(

let uu____638 = (FStar_List.fold_left (fun uu____658 binder -> (match (uu____658) with
| (env1, free) -> begin
(

let uu____678 = (free_type_vars_b env1 binder)
in (match (uu____678) with
| (env2, f) -> begin
((env2), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (uu____638) with
| (env1, free) -> begin
(

let uu____709 = (free_type_vars env1 body)
in (FStar_List.append free uu____709))
end))
end
| FStar_Parser_AST.Sum (binders, body) -> begin
(

let uu____718 = (FStar_List.fold_left (fun uu____738 binder -> (match (uu____738) with
| (env1, free) -> begin
(

let uu____758 = (free_type_vars_b env1 binder)
in (match (uu____758) with
| (env2, f) -> begin
((env2), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (uu____718) with
| (env1, free) -> begin
(

let uu____789 = (free_type_vars env1 body)
in (FStar_List.append free uu____789))
end))
end
| FStar_Parser_AST.Project (t1, uu____793) -> begin
(free_type_vars env t1)
end
| FStar_Parser_AST.Attributes (cattributes) -> begin
(FStar_List.collect (free_type_vars env) cattributes)
end
| FStar_Parser_AST.Abs (uu____797) -> begin
[]
end
| FStar_Parser_AST.Let (uu____804) -> begin
[]
end
| FStar_Parser_AST.LetOpen (uu____825) -> begin
[]
end
| FStar_Parser_AST.If (uu____830) -> begin
[]
end
| FStar_Parser_AST.QForall (uu____837) -> begin
[]
end
| FStar_Parser_AST.QExists (uu____850) -> begin
[]
end
| FStar_Parser_AST.Record (uu____863) -> begin
[]
end
| FStar_Parser_AST.Match (uu____876) -> begin
[]
end
| FStar_Parser_AST.TryWith (uu____891) -> begin
[]
end
| FStar_Parser_AST.Bind (uu____906) -> begin
[]
end
| FStar_Parser_AST.Quote (uu____913) -> begin
[]
end
| FStar_Parser_AST.VQuote (uu____918) -> begin
[]
end
| FStar_Parser_AST.Antiquote (uu____919) -> begin
[]
end
| FStar_Parser_AST.Seq (uu____924) -> begin
[]
end)))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (

let rec aux = (fun args t1 -> (

let uu____977 = (

let uu____978 = (unparen t1)
in uu____978.FStar_Parser_AST.tm)
in (match (uu____977) with
| FStar_Parser_AST.App (t2, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t2)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t1.FStar_Parser_AST.range; FStar_Parser_AST.level = t1.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| uu____1020 -> begin
((t1), (args))
end)))
in (aux [] t)))


let close : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (

let uu____1044 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv uu____1044))
in (match ((Prims.op_Equality (FStar_List.length ftv) (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____1051 -> begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (

let uu____1062 = (

let uu____1063 = (

let uu____1068 = (tm_type x.FStar_Ident.idRange)
in ((x), (uu____1068)))
in FStar_Parser_AST.TAnnotated (uu____1063))
in (FStar_Parser_AST.mk_binder uu____1062 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end)))


let close_fun : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (

let uu____1085 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv uu____1085))
in (match ((Prims.op_Equality (FStar_List.length ftv) (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____1092 -> begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (

let uu____1103 = (

let uu____1104 = (

let uu____1109 = (tm_type x.FStar_Ident.idRange)
in ((x), (uu____1109)))
in FStar_Parser_AST.TAnnotated (uu____1104))
in (FStar_Parser_AST.mk_binder uu____1103 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))))))
in (

let t1 = (

let uu____1111 = (

let uu____1112 = (unparen t)
in uu____1112.FStar_Parser_AST.tm)
in (match (uu____1111) with
| FStar_Parser_AST.Product (uu____1113) -> begin
t
end
| uu____1120 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t1)))) t1.FStar_Parser_AST.range t1.FStar_Parser_AST.level)
in result)))
end)))


let rec uncurry : FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term) = (fun bs t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (binders, t1) -> begin
(uncurry (FStar_List.append bs binders) t1)
end
| uu____1156 -> begin
((bs), (t))
end))


let rec is_var_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatWild -> begin
true
end
| FStar_Parser_AST.PatTvar (uu____1164, uu____1165) -> begin
true
end
| FStar_Parser_AST.PatVar (uu____1170, uu____1171) -> begin
true
end
| FStar_Parser_AST.PatAscribed (p1, uu____1177) -> begin
(is_var_pattern p1)
end
| uu____1190 -> begin
false
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p1, uu____1197) -> begin
(is_app_pattern p1)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____1210); FStar_Parser_AST.prange = uu____1211}, uu____1212) -> begin
true
end
| uu____1223 -> begin
false
end))


let replace_unit_pattern : FStar_Parser_AST.pattern  ->  FStar_Parser_AST.pattern = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatConst (FStar_Const.Const_unit) -> begin
(FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatAscribed ((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)), (((unit_ty), (FStar_Pervasives_Native.None)))))) p.FStar_Parser_AST.prange)
end
| uu____1237 -> begin
p
end))


let rec destruct_app_pattern : FStar_Syntax_DsEnv.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * (FStar_Parser_AST.term * FStar_Parser_AST.term FStar_Pervasives_Native.option) FStar_Pervasives_Native.option) = (fun env is_top_level1 p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p1, t) -> begin
(

let uu____1307 = (destruct_app_pattern env is_top_level1 p1)
in (match (uu____1307) with
| (name, args, uu____1350) -> begin
((name), (args), (FStar_Pervasives_Native.Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id1, uu____1400); FStar_Parser_AST.prange = uu____1401}, args) when is_top_level1 -> begin
(

let uu____1411 = (

let uu____1416 = (FStar_Syntax_DsEnv.qualify env id1)
in FStar_Util.Inr (uu____1416))
in ((uu____1411), (args), (FStar_Pervasives_Native.None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id1, uu____1438); FStar_Parser_AST.prange = uu____1439}, args) -> begin
((FStar_Util.Inl (id1)), (args), (FStar_Pervasives_Native.None))
end
| uu____1469 -> begin
(failwith "Not an app pattern")
end))


let rec gather_pattern_bound_vars_maybe_top : FStar_Ident.ident FStar_Util.set  ->  FStar_Parser_AST.pattern  ->  FStar_Ident.ident FStar_Util.set = (fun acc p -> (

let gather_pattern_bound_vars_from_list = (FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc)
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatWild -> begin
acc
end
| FStar_Parser_AST.PatConst (uu____1519) -> begin
acc
end
| FStar_Parser_AST.PatVar (uu____1520, FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)) -> begin
acc
end
| FStar_Parser_AST.PatName (uu____1523) -> begin
acc
end
| FStar_Parser_AST.PatTvar (uu____1524) -> begin
acc
end
| FStar_Parser_AST.PatOp (uu____1531) -> begin
acc
end
| FStar_Parser_AST.PatApp (phead, pats) -> begin
(gather_pattern_bound_vars_from_list ((phead)::pats))
end
| FStar_Parser_AST.PatVar (x, uu____1539) -> begin
(FStar_Util.set_add x acc)
end
| FStar_Parser_AST.PatList (pats) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatTuple (pats, uu____1548) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatOr (pats) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatRecord (guarded_pats) -> begin
(

let uu____1563 = (FStar_List.map FStar_Pervasives_Native.snd guarded_pats)
in (gather_pattern_bound_vars_from_list uu____1563))
end
| FStar_Parser_AST.PatAscribed (pat, uu____1571) -> begin
(gather_pattern_bound_vars_maybe_top acc pat)
end)))


let gather_pattern_bound_vars : FStar_Parser_AST.pattern  ->  FStar_Ident.ident FStar_Util.set = (

let acc = (FStar_Util.new_set (fun id1 id2 -> (match ((Prims.op_Equality id1.FStar_Ident.idText id2.FStar_Ident.idText)) with
| true -> begin
(Prims.parse_int "0")
end
| uu____1597 -> begin
(Prims.parse_int "1")
end)))
in (fun p -> (gather_pattern_bound_vars_maybe_top acc p)))

type bnd =
| LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option))


let uu___is_LocalBinder : bnd  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LocalBinder (_0) -> begin
true
end
| uu____1633 -> begin
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
| uu____1669 -> begin
false
end))


let __proj__LetBinder__item___0 : bnd  ->  (FStar_Ident.lident * (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)) = (fun projectee -> (match (projectee) with
| LetBinder (_0) -> begin
_0
end))


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun uu___88_1715 -> (match (uu___88_1715) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| uu____1722 -> begin
(failwith "Impossible")
end))


let as_binder : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  (FStar_Ident.ident FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_DsEnv.env) = (fun env imp uu___89_1753 -> (match (uu___89_1753) with
| (FStar_Pervasives_Native.None, k) -> begin
(

let uu____1769 = (FStar_Syntax_Syntax.null_binder k)
in ((uu____1769), (env)))
end
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____1774 = (FStar_Syntax_DsEnv.push_bv env a)
in (match (uu____1774) with
| (env1, a1) -> begin
(((((

let uu___112_1794 = a1
in {FStar_Syntax_Syntax.ppname = uu___112_1794.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___112_1794.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), ((trans_aqual imp)))), (env1))
end))
end))


type env_t =
FStar_Syntax_DsEnv.env


type lenv_t =
FStar_Syntax_Syntax.bv Prims.list


let mk_lb : (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list * (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)  ->  FStar_Syntax_Syntax.letbinding = (fun uu____1823 -> (match (uu____1823) with
| (attrs, n1, t, e, pos) -> begin
{FStar_Syntax_Syntax.lbname = n1; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = attrs; FStar_Syntax_Syntax.lbpos = pos}
end))


let no_annot_abs : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t FStar_Pervasives_Native.None))


let mk_ref_read : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun tm -> (

let tm' = (

let uu____1897 = (

let uu____1912 = (

let uu____1913 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____1913))
in (

let uu____1914 = (

let uu____1923 = (

let uu____1930 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (uu____1930)))
in (uu____1923)::[])
in ((uu____1912), (uu____1914))))
in FStar_Syntax_Syntax.Tm_app (uu____1897))
in (FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_alloc : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun tm -> (

let tm' = (

let uu____1965 = (

let uu____1980 = (

let uu____1981 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____1981))
in (

let uu____1982 = (

let uu____1991 = (

let uu____1998 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (uu____1998)))
in (uu____1991)::[])
in ((uu____1980), (uu____1982))))
in FStar_Syntax_Syntax.Tm_app (uu____1965))
in (FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_assign : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t1 t2 pos -> (

let tm = (

let uu____2047 = (

let uu____2062 = (

let uu____2063 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____2063))
in (

let uu____2064 = (

let uu____2073 = (

let uu____2080 = (FStar_Syntax_Syntax.as_implicit false)
in ((t1), (uu____2080)))
in (

let uu____2083 = (

let uu____2092 = (

let uu____2099 = (FStar_Syntax_Syntax.as_implicit false)
in ((t2), (uu____2099)))
in (uu____2092)::[])
in (uu____2073)::uu____2083))
in ((uu____2062), (uu____2064))))
in FStar_Syntax_Syntax.Tm_app (uu____2047))
in (FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos)))


let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun uu___90_2132 -> (match (uu___90_2132) with
| "repr" -> begin
true
end
| "post" -> begin
true
end
| "pre" -> begin
true
end
| "wp" -> begin
true
end
| uu____2133 -> begin
false
end))


let rec sum_to_universe : FStar_Syntax_Syntax.universe  ->  Prims.int  ->  FStar_Syntax_Syntax.universe = (fun u n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
u
end
| uu____2144 -> begin
(

let uu____2145 = (sum_to_universe u (n1 - (Prims.parse_int "1")))
in FStar_Syntax_Syntax.U_succ (uu____2145))
end))


let int_to_universe : Prims.int  ->  FStar_Syntax_Syntax.universe = (fun n1 -> (sum_to_universe FStar_Syntax_Syntax.U_zero n1))


let rec desugar_maybe_non_constant_universe : FStar_Parser_AST.term  ->  (Prims.int, FStar_Syntax_Syntax.universe) FStar_Util.either = (fun t -> (

let uu____2164 = (

let uu____2165 = (unparen t)
in uu____2165.FStar_Parser_AST.tm)
in (match (uu____2164) with
| FStar_Parser_AST.Wild -> begin
(

let uu____2170 = (

let uu____2171 = (FStar_Syntax_Unionfind.univ_fresh ())
in FStar_Syntax_Syntax.U_unif (uu____2171))
in FStar_Util.Inr (uu____2170))
end
| FStar_Parser_AST.Uvar (u) -> begin
FStar_Util.Inr (FStar_Syntax_Syntax.U_name (u))
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (repr, uu____2182)) -> begin
(

let n1 = (FStar_Util.int_of_string repr)
in ((match ((n1 < (Prims.parse_int "0"))) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_NegativeUniverseConstFatal_NotSupported), ((Prims.strcat "Negative universe constant  are not supported : " repr))) t.FStar_Parser_AST.range)
end
| uu____2197 -> begin
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
| (FStar_Util.Inl (n1), FStar_Util.Inr (u)) -> begin
(

let uu____2247 = (sum_to_universe u n1)
in FStar_Util.Inr (uu____2247))
end
| (FStar_Util.Inr (u), FStar_Util.Inl (n1)) -> begin
(

let uu____2258 = (sum_to_universe u n1)
in FStar_Util.Inr (uu____2258))
end
| (FStar_Util.Inr (u11), FStar_Util.Inr (u21)) -> begin
(

let uu____2269 = (

let uu____2274 = (

let uu____2275 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "This universe might contain a sum of two universe variables " uu____2275))
in ((FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars), (uu____2274)))
in (FStar_Errors.raise_error uu____2269 t.FStar_Parser_AST.range))
end)))
end
| FStar_Parser_AST.App (uu____2280) -> begin
(

let rec aux = (fun t1 univargs -> (

let uu____2314 = (

let uu____2315 = (unparen t1)
in uu____2315.FStar_Parser_AST.tm)
in (match (uu____2314) with
| FStar_Parser_AST.App (t2, targ, uu____2322) -> begin
(

let uarg = (desugar_maybe_non_constant_universe targ)
in (aux t2 ((uarg)::univargs)))
end
| FStar_Parser_AST.Var (max_lid1) -> begin
(match ((FStar_List.existsb (fun uu___91_2345 -> (match (uu___91_2345) with
| FStar_Util.Inr (uu____2350) -> begin
true
end
| uu____2351 -> begin
false
end)) univargs)) with
| true -> begin
(

let uu____2356 = (

let uu____2357 = (FStar_List.map (fun uu___92_2366 -> (match (uu___92_2366) with
| FStar_Util.Inl (n1) -> begin
(int_to_universe n1)
end
| FStar_Util.Inr (u) -> begin
u
end)) univargs)
in FStar_Syntax_Syntax.U_max (uu____2357))
in FStar_Util.Inr (uu____2356))
end
| uu____2373 -> begin
(

let nargs = (FStar_List.map (fun uu___93_2383 -> (match (uu___93_2383) with
| FStar_Util.Inl (n1) -> begin
n1
end
| FStar_Util.Inr (uu____2389) -> begin
(failwith "impossible")
end)) univargs)
in (

let uu____2390 = (FStar_List.fold_left (fun m n1 -> (match ((m > n1)) with
| true -> begin
m
end
| uu____2395 -> begin
n1
end)) (Prims.parse_int "0") nargs)
in FStar_Util.Inl (uu____2390)))
end)
end
| uu____2396 -> begin
(

let uu____2397 = (

let uu____2402 = (

let uu____2403 = (

let uu____2404 = (FStar_Parser_AST.term_to_string t1)
in (Prims.strcat uu____2404 " in universe context"))
in (Prims.strcat "Unexpected term " uu____2403))
in ((FStar_Errors.Fatal_UnexpectedTermInUniverse), (uu____2402)))
in (FStar_Errors.raise_error uu____2397 t1.FStar_Parser_AST.range))
end)))
in (aux t []))
end
| uu____2413 -> begin
(

let uu____2414 = (

let uu____2419 = (

let uu____2420 = (

let uu____2421 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat uu____2421 " in universe context"))
in (Prims.strcat "Unexpected term " uu____2420))
in ((FStar_Errors.Fatal_UnexpectedTermInUniverse), (uu____2419)))
in (FStar_Errors.raise_error uu____2414 t.FStar_Parser_AST.range))
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


let check_no_aq : FStar_Syntax_Syntax.antiquotations  ->  unit = (fun aq -> (match (aq) with
| [] -> begin
()
end
| ((bv, b, e))::uu____2454 -> begin
(

let uu____2477 = (

let uu____2482 = (

let uu____2483 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected antiquotation: %s(%s)" (match (b) with
| true -> begin
"`@"
end
| uu____2484 -> begin
"`#"
end) uu____2483))
in ((FStar_Errors.Fatal_UnexpectedAntiquotation), (uu____2482)))
in (FStar_Errors.raise_error uu____2477 e.FStar_Syntax_Syntax.pos))
end))


let check_fields : 'Auu____2493 . FStar_Syntax_DsEnv.env  ->  (FStar_Ident.lident * 'Auu____2493) Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_DsEnv.record_or_dc = (fun env fields rg -> (

let uu____2521 = (FStar_List.hd fields)
in (match (uu____2521) with
| (f, uu____2531) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f);
(

let record = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f)
in (

let check_field = (fun uu____2543 -> (match (uu____2543) with
| (f', uu____2549) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f');
(

let uu____2551 = (FStar_Syntax_DsEnv.belongs_to_record env f' record)
in (match (uu____2551) with
| true -> begin
()
end
| uu____2552 -> begin
(

let msg = (FStar_Util.format3 "Field %s belongs to record type %s, whereas field %s does not" f.FStar_Ident.str record.FStar_Syntax_DsEnv.typename.FStar_Ident.str f'.FStar_Ident.str)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_FieldsNotBelongToSameRecordType), (msg)) rg))
end));
)
end))
in ((

let uu____2555 = (FStar_List.tl fields)
in (FStar_List.iter check_field uu____2555));
(match (()) with
| () -> begin
record
end);
)));
)
end)))


let rec desugar_data_pat : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.list) = (fun env p is_mut -> (

let check_linear_pattern_variables = (fun pats r -> (

let rec pat_vars = (fun p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____2910) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_wild (uu____2917) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_constant (uu____2918) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (uu____2920, pats1) -> begin
(

let aux = (fun out uu____2958 -> (match (uu____2958) with
| (p2, uu____2970) -> begin
(

let intersection = (

let uu____2978 = (pat_vars p2)
in (FStar_Util.set_intersect uu____2978 out))
in (

let uu____2981 = (FStar_Util.set_is_empty intersection)
in (match (uu____2981) with
| true -> begin
(

let uu____2984 = (pat_vars p2)
in (FStar_Util.set_union out uu____2984))
end
| uu____2987 -> begin
(

let duplicate_bv = (

let uu____2989 = (FStar_Util.set_elements intersection)
in (FStar_List.hd uu____2989))
in (

let uu____2992 = (

let uu____2997 = (FStar_Util.format1 "Non-linear patterns are not permitted. %s appears more than once in this pattern." duplicate_bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in ((FStar_Errors.Fatal_NonLinearPatternNotPermitted), (uu____2997)))
in (FStar_Errors.raise_error uu____2992 r)))
end)))
end))
in (FStar_List.fold_left aux FStar_Syntax_Syntax.no_names pats1))
end))
in (match (pats) with
| [] -> begin
()
end
| (p1)::[] -> begin
(

let uu____3017 = (pat_vars p1)
in (FStar_All.pipe_right uu____3017 (fun a239 -> ())))
end
| (p1)::ps -> begin
(

let pvars = (pat_vars p1)
in (

let aux = (fun p2 -> (

let uu____3039 = (

let uu____3040 = (pat_vars p2)
in (FStar_Util.set_eq pvars uu____3040))
in (match (uu____3039) with
| true -> begin
()
end
| uu____3043 -> begin
(

let nonlinear_vars = (

let uu____3047 = (pat_vars p2)
in (FStar_Util.set_symmetric_difference pvars uu____3047))
in (

let first_nonlinear_var = (

let uu____3051 = (FStar_Util.set_elements nonlinear_vars)
in (FStar_List.hd uu____3051))
in (

let uu____3054 = (

let uu____3059 = (FStar_Util.format1 "Patterns in this match are incoherent, variable %s is bound in some but not all patterns." first_nonlinear_var.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in ((FStar_Errors.Fatal_IncoherentPatterns), (uu____3059)))
in (FStar_Errors.raise_error uu____3054 r))))
end)))
in (FStar_List.iter aux ps)))
end)))
in ((match (((is_mut), (p.FStar_Parser_AST.pat))) with
| (false, uu____3063) -> begin
()
end
| (true, FStar_Parser_AST.PatVar (uu____3064)) -> begin
()
end
| (true, uu____3071) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_LetMutableForVariablesOnly), ("let-mutable is for variables only")) p.FStar_Parser_AST.prange)
end);
(

let resolvex = (fun l e x -> (

let uu____3094 = (FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (Prims.op_Equality y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText x.FStar_Ident.idText))))
in (match (uu____3094) with
| FStar_Pervasives_Native.Some (y) -> begin
((l), (e), (y))
end
| uu____3108 -> begin
(

let uu____3111 = (match (is_mut) with
| true -> begin
(FStar_Syntax_DsEnv.push_bv_mutable e x)
end
| uu____3120 -> begin
(FStar_Syntax_DsEnv.push_bv e x)
end)
in (match (uu____3111) with
| (e1, x1) -> begin
(((x1)::l), (e1), (x1))
end))
end)))
in (

let rec aux' = (fun top loc env1 p1 -> (

let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange))
in (

let pos_r = (fun r q -> (FStar_Syntax_Syntax.withinfo q r))
in (

let orig = p1
in (match (p1.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (uu____3223) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.PatOp (op) -> begin
(

let uu____3239 = (

let uu____3240 = (

let uu____3241 = (

let uu____3248 = (

let uu____3249 = (

let uu____3254 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") op.FStar_Ident.idText op.FStar_Ident.idRange)
in ((uu____3254), (op.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____3249))
in ((uu____3248), (FStar_Pervasives_Native.None)))
in FStar_Parser_AST.PatVar (uu____3241))
in {FStar_Parser_AST.pat = uu____3240; FStar_Parser_AST.prange = p1.FStar_Parser_AST.prange})
in (aux loc env1 uu____3239))
end
| FStar_Parser_AST.PatAscribed (p2, (t, tacopt)) -> begin
((match (tacopt) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (uu____3271) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly), ("Type ascriptions within patterns are cannot be associated with a tactic")) orig.FStar_Parser_AST.prange)
end);
(

let uu____3272 = (aux loc env1 p2)
in (match (uu____3272) with
| (loc1, env', binder, p3, imp) -> begin
(

let annot_pat_var = (fun p4 t1 -> (match (p4.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu___113_3330 = p4
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var ((

let uu___114_3335 = x
in {FStar_Syntax_Syntax.ppname = uu___114_3335.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___114_3335.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})); FStar_Syntax_Syntax.p = uu___113_3330.FStar_Syntax_Syntax.p})
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu___115_3337 = p4
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild ((

let uu___116_3342 = x
in {FStar_Syntax_Syntax.ppname = uu___116_3342.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___116_3342.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})); FStar_Syntax_Syntax.p = uu___115_3337.FStar_Syntax_Syntax.p})
end
| uu____3343 when top -> begin
p4
end
| uu____3344 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly), ("Type ascriptions within patterns are only allowed on variables")) orig.FStar_Parser_AST.prange)
end))
in (

let uu____3347 = (match (binder) with
| LetBinder (uu____3360) -> begin
(failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t1 = (

let uu____3380 = (close_fun env1 t)
in (desugar_term env1 uu____3380))
in ((match ((match (x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
false
end
| uu____3382 -> begin
true
end)) with
| true -> begin
(

let uu____3383 = (

let uu____3388 = (

let uu____3389 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____3390 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____3391 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n" uu____3389 uu____3390 uu____3391))))
in ((FStar_Errors.Warning_MultipleAscriptions), (uu____3388)))
in (FStar_Errors.log_issue orig.FStar_Parser_AST.prange uu____3383))
end
| uu____3392 -> begin
()
end);
(

let uu____3393 = (annot_pat_var p3 t1)
in ((uu____3393), (LocalBinder ((((

let uu___117_3399 = x
in {FStar_Syntax_Syntax.ppname = uu___117_3399.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___117_3399.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})), (aq))))));
))
end)
in (match (uu____3347) with
| (p4, binder1) -> begin
((loc1), (env'), (binder1), (p4), (imp))
end)))
end));
)
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____3421 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3421), (false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____3432 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3432), (false))))
end
| FStar_Parser_AST.PatTvar (x, aq) -> begin
(

let imp = (Prims.op_Equality aq (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))
in (

let aq1 = (trans_aqual aq)
in (

let uu____3453 = (resolvex loc env1 x)
in (match (uu____3453) with
| (loc1, env2, xbv) -> begin
(

let uu____3475 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc1), (env2), (LocalBinder (((xbv), (aq1)))), (uu____3475), (imp)))
end))))
end
| FStar_Parser_AST.PatVar (x, aq) -> begin
(

let imp = (Prims.op_Equality aq (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))
in (

let aq1 = (trans_aqual aq)
in (

let uu____3496 = (resolvex loc env1 x)
in (match (uu____3496) with
| (loc1, env2, xbv) -> begin
(

let uu____3518 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc1), (env2), (LocalBinder (((xbv), (aq1)))), (uu____3518), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l1 = (FStar_Syntax_DsEnv.fail_or env1 (FStar_Syntax_DsEnv.try_lookup_datacon env1) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____3530 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), ([])))))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3530), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = uu____3554}, args) -> begin
(

let uu____3560 = (FStar_List.fold_right (fun arg uu____3601 -> (match (uu____3601) with
| (loc1, env2, args1) -> begin
(

let uu____3649 = (aux loc1 env2 arg)
in (match (uu____3649) with
| (loc2, env3, uu____3678, arg1, imp) -> begin
((loc2), (env3), ((((arg1), (imp)))::args1))
end))
end)) args ((loc), (env1), ([])))
in (match (uu____3560) with
| (loc1, env2, args1) -> begin
(

let l1 = (FStar_Syntax_DsEnv.fail_or env2 (FStar_Syntax_DsEnv.try_lookup_datacon env2) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____3748 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args1)))))
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3748), (false)))))
end))
end
| FStar_Parser_AST.PatApp (uu____3765) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedPattern), ("Unexpected pattern")) p1.FStar_Parser_AST.prange)
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____3787 = (FStar_List.fold_right (fun pat uu____3820 -> (match (uu____3820) with
| (loc1, env2, pats1) -> begin
(

let uu____3852 = (aux loc1 env2 pat)
in (match (uu____3852) with
| (loc2, env3, uu____3877, pat1, uu____3879) -> begin
((loc2), (env3), ((pat1)::pats1))
end))
end)) pats ((loc), (env1), ([])))
in (match (uu____3787) with
| (loc1, env2, pats1) -> begin
(

let pat = (

let uu____3922 = (

let uu____3925 = (

let uu____3932 = (FStar_Range.end_range p1.FStar_Parser_AST.prange)
in (pos_r uu____3932))
in (

let uu____3933 = (

let uu____3934 = (

let uu____3947 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.nil_lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____3947), ([])))
in FStar_Syntax_Syntax.Pat_cons (uu____3934))
in (FStar_All.pipe_left uu____3925 uu____3933)))
in (FStar_List.fold_right (fun hd1 tl1 -> (

let r = (FStar_Range.union_ranges hd1.FStar_Syntax_Syntax.p tl1.FStar_Syntax_Syntax.p)
in (

let uu____3979 = (

let uu____3980 = (

let uu____3993 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.cons_lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____3993), ((((hd1), (false)))::(((tl1), (false)))::[])))
in FStar_Syntax_Syntax.Pat_cons (uu____3980))
in (FStar_All.pipe_left (pos_r r) uu____3979)))) pats1 uu____3922))
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep1) -> begin
(

let uu____4037 = (FStar_List.fold_left (fun uu____4077 p2 -> (match (uu____4077) with
| (loc1, env2, pats) -> begin
(

let uu____4126 = (aux loc1 env2 p2)
in (match (uu____4126) with
| (loc2, env3, uu____4155, pat, uu____4157) -> begin
((loc2), (env3), ((((pat), (false)))::pats))
end))
end)) ((loc), (env1), ([])) args)
in (match (uu____4037) with
| (loc1, env2, args1) -> begin
(

let args2 = (FStar_List.rev args1)
in (

let l = (match (dep1) with
| true -> begin
(FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end
| uu____4245 -> begin
(FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end)
in (

let uu____4252 = (FStar_Syntax_DsEnv.fail_or env2 (FStar_Syntax_DsEnv.try_lookup_lid env2) l)
in (match (uu____4252) with
| (constr, uu____4274) -> begin
(

let l1 = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____4277 -> begin
(failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____4279 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args2)))))
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____4279), (false)))))
end))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedPattern), ("Unexpected pattern")) p1.FStar_Parser_AST.prange)
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(

let record = (check_fields env1 fields p1.FStar_Parser_AST.prange)
in (

let fields1 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____4350 -> (match (uu____4350) with
| (f, p2) -> begin
((f.FStar_Ident.ident), (p2))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map (fun uu____4380 -> (match (uu____4380) with
| (f, uu____4386) -> begin
(

let uu____4387 = (FStar_All.pipe_right fields1 (FStar_List.tryFind (fun uu____4413 -> (match (uu____4413) with
| (g, uu____4419) -> begin
(Prims.op_Equality f.FStar_Ident.idText g.FStar_Ident.idText)
end))))
in (match (uu____4387) with
| FStar_Pervasives_Native.None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p1.FStar_Parser_AST.prange)
end
| FStar_Pervasives_Native.Some (uu____4424, p2) -> begin
p2
end))
end))))
in (

let app = (

let uu____4431 = (

let uu____4432 = (

let uu____4439 = (

let uu____4440 = (

let uu____4441 = (FStar_Ident.lid_of_ids (FStar_List.append record.FStar_Syntax_DsEnv.typename.FStar_Ident.ns ((record.FStar_Syntax_DsEnv.constrname)::[])))
in FStar_Parser_AST.PatName (uu____4441))
in (FStar_Parser_AST.mk_pattern uu____4440 p1.FStar_Parser_AST.prange))
in ((uu____4439), (args)))
in FStar_Parser_AST.PatApp (uu____4432))
in (FStar_Parser_AST.mk_pattern uu____4431 p1.FStar_Parser_AST.prange))
in (

let uu____4444 = (aux loc env1 app)
in (match (uu____4444) with
| (env2, e, b, p2, uu____4473) -> begin
(

let p3 = (match (p2.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args1) -> begin
(

let uu____4501 = (

let uu____4502 = (

let uu____4515 = (

let uu___118_4516 = fv
in (

let uu____4517 = (

let uu____4520 = (

let uu____4521 = (

let uu____4528 = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map FStar_Pervasives_Native.fst))
in ((record.FStar_Syntax_DsEnv.typename), (uu____4528)))
in FStar_Syntax_Syntax.Record_ctor (uu____4521))
in FStar_Pervasives_Native.Some (uu____4520))
in {FStar_Syntax_Syntax.fv_name = uu___118_4516.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = uu___118_4516.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu____4517}))
in ((uu____4515), (args1)))
in FStar_Syntax_Syntax.Pat_cons (uu____4502))
in (FStar_All.pipe_left pos uu____4501))
end
| uu____4555 -> begin
p2
end)
in ((env2), (e), (b), (p3), (false)))
end))))))
end)))))
and aux = (fun loc env1 p1 -> (aux' false loc env1 p1))
in (

let aux_maybe_or = (fun env1 p1 -> (

let loc = []
in (match (p1.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr ([]) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.PatOr ((p2)::ps) -> begin
(

let uu____4609 = (aux' true loc env1 p2)
in (match (uu____4609) with
| (loc1, env2, var, p3, uu____4636) -> begin
(

let uu____4641 = (FStar_List.fold_left (fun uu____4673 p4 -> (match (uu____4673) with
| (loc2, env3, ps1) -> begin
(

let uu____4706 = (aux' true loc2 env3 p4)
in (match (uu____4706) with
| (loc3, env4, uu____4731, p5, uu____4733) -> begin
((loc3), (env4), ((p5)::ps1))
end))
end)) ((loc1), (env2), ([])) ps)
in (match (uu____4641) with
| (loc2, env3, ps1) -> begin
(

let pats = (p3)::(FStar_List.rev ps1)
in ((env3), (var), (pats)))
end))
end))
end
| uu____4784 -> begin
(

let uu____4785 = (aux' true loc env1 p1)
in (match (uu____4785) with
| (loc1, env2, vars, pat, b) -> begin
((env2), (vars), ((pat)::[]))
end))
end)))
in (

let uu____4825 = (aux_maybe_or env p)
in (match (uu____4825) with
| (env1, b, pats) -> begin
((check_linear_pattern_variables pats p.FStar_Parser_AST.prange);
((env1), (b), (pats));
)
end)))));
)))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.list) = (fun top env p is_mut -> (

let mklet = (fun x -> (

let uu____4886 = (

let uu____4887 = (

let uu____4898 = (FStar_Syntax_DsEnv.qualify env x)
in ((uu____4898), (((FStar_Syntax_Syntax.tun), (FStar_Pervasives_Native.None)))))
in LetBinder (uu____4887))
in ((env), (uu____4886), ([]))))
in (match (top) with
| true -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(

let uu____4926 = (

let uu____4927 = (

let uu____4932 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") x.FStar_Ident.idText x.FStar_Ident.idRange)
in ((uu____4932), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____4927))
in (mklet uu____4926))
end
| FStar_Parser_AST.PatVar (x, uu____4934) -> begin
(mklet x)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____4940); FStar_Parser_AST.prange = uu____4941}, (t, tacopt)) -> begin
(

let tacopt1 = (FStar_Util.map_opt tacopt (desugar_term env))
in (

let uu____4961 = (

let uu____4962 = (

let uu____4973 = (FStar_Syntax_DsEnv.qualify env x)
in (

let uu____4974 = (

let uu____4981 = (desugar_term env t)
in ((uu____4981), (tacopt1)))
in ((uu____4973), (uu____4974))))
in LetBinder (uu____4962))
in ((env), (uu____4961), ([]))))
end
| uu____4992 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedPattern), ("Unexpected pattern at the top-level")) p.FStar_Parser_AST.prange)
end)
end
| uu____5001 -> begin
(

let uu____5002 = (desugar_data_pat env p is_mut)
in (match (uu____5002) with
| (env1, binder, p1) -> begin
(

let p2 = (match (p1) with
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (uu____5031); FStar_Syntax_Syntax.p = uu____5032})::[] -> begin
[]
end
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (uu____5037); FStar_Syntax_Syntax.p = uu____5038})::[] -> begin
[]
end
| uu____5043 -> begin
p1
end)
in ((env1), (binder), (p2)))
end))
end)))
and desugar_binding_pat : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.list) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat Prims.list) = (fun uu____5050 env pat -> (

let uu____5053 = (desugar_data_pat env pat false)
in (match (uu____5053) with
| (env1, uu____5069, pat1) -> begin
((env1), (pat1))
end)))
and desugar_match_pat : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat Prims.list) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term_aq : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations) = (fun env e -> (

let env1 = (FStar_Syntax_DsEnv.set_expect_typ env false)
in (desugar_term_maybe_top false env1 e)))
and desugar_term : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let uu____5088 = (desugar_term_aq env e)
in (match (uu____5088) with
| (t, aq) -> begin
((check_no_aq aq);
t;
)
end)))
and desugar_typ_aq : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations) = (fun env e -> (

let env1 = (FStar_Syntax_DsEnv.set_expect_typ env true)
in (desugar_term_maybe_top false env1 e)))
and desugar_typ : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let uu____5105 = (desugar_typ_aq env e)
in (match (uu____5105) with
| (t, aq) -> begin
((check_no_aq aq);
t;
)
end)))
and desugar_machine_integer : FStar_Syntax_DsEnv.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun env repr uu____5115 range -> (match (uu____5115) with
| (signedness, width) -> begin
(

let tnm = (Prims.strcat "FStar." (Prims.strcat (match (signedness) with
| FStar_Const.Unsigned -> begin
"U"
end
| FStar_Const.Signed -> begin
""
end) (Prims.strcat "Int" (match (width) with
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
end))))
in ((

let uu____5125 = (

let uu____5126 = (FStar_Const.within_bounds repr signedness width)
in (not (uu____5126)))
in (match (uu____5125) with
| true -> begin
(

let uu____5127 = (

let uu____5132 = (FStar_Util.format2 "%s is not in the expected range for %s" repr tnm)
in ((FStar_Errors.Error_OutOfRange), (uu____5132)))
in (FStar_Errors.log_issue range uu____5127))
end
| uu____5133 -> begin
()
end));
(

let private_intro_nm = (Prims.strcat tnm (Prims.strcat ".__" (Prims.strcat (match (signedness) with
| FStar_Const.Unsigned -> begin
"u"
end
| FStar_Const.Signed -> begin
""
end) "int_to_t")))
in (

let intro_nm = (Prims.strcat tnm (Prims.strcat "." (Prims.strcat (match (signedness) with
| FStar_Const.Unsigned -> begin
"u"
end
| FStar_Const.Signed -> begin
""
end) "int_to_t")))
in (

let lid = (

let uu____5137 = (FStar_Ident.path_of_text intro_nm)
in (FStar_Ident.lid_of_path uu____5137 range))
in (

let lid1 = (

let uu____5141 = (FStar_Syntax_DsEnv.try_lookup_lid env lid)
in (match (uu____5141) with
| FStar_Pervasives_Native.Some (intro_term, uu____5151) -> begin
(match (intro_term.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let private_lid = (

let uu____5160 = (FStar_Ident.path_of_text private_intro_nm)
in (FStar_Ident.lid_of_path uu____5160 range))
in (

let private_fv = (

let uu____5162 = (FStar_Syntax_Util.incr_delta_depth fv.FStar_Syntax_Syntax.fv_delta)
in (FStar_Syntax_Syntax.lid_as_fv private_lid uu____5162 fv.FStar_Syntax_Syntax.fv_qual))
in (

let uu___119_5163 = intro_term
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (private_fv); FStar_Syntax_Syntax.pos = uu___119_5163.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___119_5163.FStar_Syntax_Syntax.vars})))
end
| uu____5164 -> begin
(failwith (Prims.strcat "Unexpected non-fvar for " intro_nm))
end)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5171 = (

let uu____5176 = (FStar_Util.format1 "Unexpected numeric literal.  Restart F* to load %s." tnm)
in ((FStar_Errors.Fatal_UnexpectedNumericLiteral), (uu____5176)))
in (FStar_Errors.raise_error uu____5171 range))
end))
in (

let repr1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (FStar_Pervasives_Native.None))))) FStar_Pervasives_Native.None range)
in (

let uu____5192 = (

let uu____5199 = (

let uu____5200 = (

let uu____5215 = (

let uu____5224 = (

let uu____5231 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr1), (uu____5231)))
in (uu____5224)::[])
in ((lid1), (uu____5215)))
in FStar_Syntax_Syntax.Tm_app (uu____5200))
in (FStar_Syntax_Syntax.mk uu____5199))
in (uu____5192 FStar_Pervasives_Native.None range)))))));
))
end))
and desugar_name : (FStar_Syntax_Syntax.term'  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  env_t  ->  Prims.bool  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.term = (fun mk1 setpos env resolve l -> (

let uu____5270 = (FStar_Syntax_DsEnv.fail_or env ((match (resolve) with
| true -> begin
FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
end
| uu____5287 -> begin
FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve
end) env) l)
in (match (uu____5270) with
| (tm, mut, attrs) -> begin
(

let warn_if_deprecated = (fun attrs1 -> (FStar_List.iter (fun a -> (match (a.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____5319; FStar_Syntax_Syntax.vars = uu____5320}, args) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v FStar_Parser_Const.deprecated_attr) -> begin
(

let msg = (

let uu____5343 = (FStar_Syntax_Print.term_to_string tm)
in (Prims.strcat uu____5343 " is deprecated"))
in (

let msg1 = (match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5351 = (

let uu____5352 = (

let uu____5355 = (FStar_List.hd args)
in (FStar_Pervasives_Native.fst uu____5355))
in uu____5352.FStar_Syntax_Syntax.n)
in (match (uu____5351) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____5371)) when (not ((Prims.op_Equality (FStar_Util.trim_string s) ""))) -> begin
(Prims.strcat msg (Prims.strcat ", use " (Prims.strcat s " instead")))
end
| uu____5372 -> begin
msg
end))
end
| uu____5373 -> begin
msg
end)
in (

let uu____5374 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.log_issue uu____5374 ((FStar_Errors.Warning_DeprecatedDefinition), (msg1))))))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v FStar_Parser_Const.deprecated_attr) -> begin
(

let msg = (

let uu____5377 = (FStar_Syntax_Print.term_to_string tm)
in (Prims.strcat uu____5377 " is deprecated"))
in (

let uu____5378 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.log_issue uu____5378 ((FStar_Errors.Warning_DeprecatedDefinition), (msg)))))
end
| uu____5379 -> begin
()
end)) attrs1))
in ((warn_if_deprecated attrs);
(

let tm1 = (setpos tm)
in (match (mut) with
| true -> begin
(

let uu____5384 = (

let uu____5385 = (

let uu____5392 = (mk_ref_read tm1)
in ((uu____5392), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval))))
in FStar_Syntax_Syntax.Tm_meta (uu____5385))
in (FStar_All.pipe_left mk1 uu____5384))
end
| uu____5397 -> begin
tm1
end));
))
end)))
and desugar_attributes : env_t  ->  FStar_Parser_AST.term Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun env cattributes -> (

let desugar_attribute = (fun t -> (

let uu____5410 = (

let uu____5411 = (unparen t)
in uu____5411.FStar_Parser_AST.tm)
in (match (uu____5410) with
| FStar_Parser_AST.Var ({FStar_Ident.ns = uu____5412; FStar_Ident.ident = uu____5413; FStar_Ident.nsstr = uu____5414; FStar_Ident.str = "cps"}) -> begin
FStar_Syntax_Syntax.CPS
end
| uu____5417 -> begin
(

let uu____5418 = (

let uu____5423 = (

let uu____5424 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "Unknown attribute " uu____5424))
in ((FStar_Errors.Fatal_UnknownAttribute), (uu____5423)))
in (FStar_Errors.raise_error uu____5418 t.FStar_Parser_AST.range))
end)))
in (FStar_List.map desugar_attribute cattributes)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations) = (fun top_level env top -> (

let mk1 = (fun e -> (FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
in (

let noaqs = []
in (

let join_aqs = (fun aqs -> (FStar_List.flatten aqs))
in (

let setpos = (fun e -> (

let uu___120_5519 = e
in {FStar_Syntax_Syntax.n = uu___120_5519.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___120_5519.FStar_Syntax_Syntax.vars}))
in (

let uu____5522 = (

let uu____5523 = (unparen top)
in uu____5523.FStar_Parser_AST.tm)
in (match (uu____5522) with
| FStar_Parser_AST.Wild -> begin
(((setpos FStar_Syntax_Syntax.tun)), (noaqs))
end
| FStar_Parser_AST.Labeled (uu____5540) -> begin
(

let uu____5547 = (desugar_formula env top)
in ((uu____5547), (noaqs)))
end
| FStar_Parser_AST.Requires (t, lopt) -> begin
(

let uu____5564 = (desugar_formula env t)
in ((uu____5564), (noaqs)))
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(

let uu____5581 = (desugar_formula env t)
in ((uu____5581), (noaqs)))
end
| FStar_Parser_AST.Attributes (ts) -> begin
(failwith "Attributes should not be desugared by desugar_term_maybe_top")
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (i, FStar_Pervasives_Native.Some (size))) -> begin
(

let uu____5615 = (desugar_machine_integer env i size top.FStar_Parser_AST.range)
in ((uu____5615), (noaqs)))
end
| FStar_Parser_AST.Const (c) -> begin
(

let uu____5627 = (mk1 (FStar_Syntax_Syntax.Tm_constant (c)))
in ((uu____5627), (noaqs)))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "=!="; FStar_Ident.idRange = r}, args) -> begin
(

let e = (

let uu____5649 = (

let uu____5650 = (

let uu____5657 = (FStar_Ident.mk_ident (("=="), (r)))
in ((uu____5657), (args)))
in FStar_Parser_AST.Op (uu____5650))
in (FStar_Parser_AST.mk_term uu____5649 top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
in (

let uu____5660 = (

let uu____5661 = (

let uu____5662 = (

let uu____5669 = (FStar_Ident.mk_ident (("~"), (r)))
in ((uu____5669), ((e)::[])))
in FStar_Parser_AST.Op (uu____5662))
in (FStar_Parser_AST.mk_term uu____5661 top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
in (desugar_term_aq env uu____5660)))
end
| FStar_Parser_AST.Op (op_star, (uu____5673)::(uu____5674)::[]) when ((

let uu____5679 = (FStar_Ident.text_of_id op_star)
in (Prims.op_Equality uu____5679 "*")) && (

let uu____5681 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range op_star)
in (FStar_All.pipe_right uu____5681 FStar_Option.isNone))) -> begin
(

let rec flatten1 = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____5696}, (t1)::(t2)::[]) -> begin
(

let uu____5701 = (flatten1 t1)
in (FStar_List.append uu____5701 ((t2)::[])))
end
| uu____5704 -> begin
(t)::[]
end))
in (

let uu____5705 = (

let uu____5714 = (

let uu____5721 = (

let uu____5724 = (unparen top)
in (flatten1 uu____5724))
in (FStar_All.pipe_right uu____5721 (FStar_List.map (fun t -> (

let uu____5743 = (desugar_typ_aq env t)
in (match (uu____5743) with
| (t', aq) -> begin
(

let uu____5754 = (FStar_Syntax_Syntax.as_arg t')
in ((uu____5754), (aq)))
end))))))
in (FStar_All.pipe_right uu____5714 FStar_List.unzip))
in (match (uu____5705) with
| (targs, aqs) -> begin
(

let uu____5783 = (

let uu____5788 = (FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_lid env) uu____5788))
in (match (uu____5783) with
| (tup, uu____5798) -> begin
(

let uu____5799 = (mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
in ((uu____5799), ((join_aqs aqs))))
end))
end)))
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____5817 = (

let uu____5820 = (

let uu____5823 = (FStar_Syntax_DsEnv.fail_or2 (FStar_Syntax_DsEnv.try_lookup_id env) a)
in (FStar_Pervasives_Native.fst uu____5823))
in (FStar_All.pipe_left setpos uu____5820))
in ((uu____5817), (noaqs)))
end
| FStar_Parser_AST.Uvar (u) -> begin
(

let uu____5849 = (

let uu____5854 = (

let uu____5855 = (

let uu____5856 = (FStar_Ident.text_of_id u)
in (Prims.strcat uu____5856 " in non-universe context"))
in (Prims.strcat "Unexpected universe variable " uu____5855))
in ((FStar_Errors.Fatal_UnexpectedUniverseVariable), (uu____5854)))
in (FStar_Errors.raise_error uu____5849 top.FStar_Parser_AST.range))
end
| FStar_Parser_AST.Op (s, args) -> begin
(

let uu____5867 = (op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)
in (match (uu____5867) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5874 = (

let uu____5879 = (

let uu____5880 = (FStar_Ident.text_of_id s)
in (Prims.strcat "Unexpected or unbound operator: " uu____5880))
in ((FStar_Errors.Fatal_UnepxectedOrUnboundOperator), (uu____5879)))
in (FStar_Errors.raise_error uu____5874 top.FStar_Parser_AST.range))
end
| FStar_Pervasives_Native.Some (op) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5890 = (

let uu____5905 = (FStar_All.pipe_right args (FStar_List.map (fun t -> (

let uu____5947 = (desugar_term_aq env t)
in (match (uu____5947) with
| (t', s1) -> begin
((((t'), (FStar_Pervasives_Native.None))), (s1))
end)))))
in (FStar_All.pipe_right uu____5905 FStar_List.unzip))
in (match (uu____5890) with
| (args1, aqs) -> begin
(

let uu____6030 = (mk1 (FStar_Syntax_Syntax.Tm_app (((op), (args1)))))
in ((uu____6030), ((join_aqs aqs))))
end))
end
| uu____6053 -> begin
((op), (noaqs))
end)
end))
end
| FStar_Parser_AST.Construct (n1, ((a, uu____6066))::[]) when (Prims.op_Equality n1.FStar_Ident.str "SMTPat") -> begin
(

let uu____6081 = (

let uu___121_6082 = top
in (

let uu____6083 = (

let uu____6084 = (

let uu____6091 = (

let uu___122_6092 = top
in (

let uu____6093 = (

let uu____6094 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____6094))
in {FStar_Parser_AST.tm = uu____6093; FStar_Parser_AST.range = uu___122_6092.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___122_6092.FStar_Parser_AST.level}))
in ((uu____6091), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____6084))
in {FStar_Parser_AST.tm = uu____6083; FStar_Parser_AST.range = uu___121_6082.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___121_6082.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____6081))
end
| FStar_Parser_AST.Construct (n1, ((a, uu____6097))::[]) when (Prims.op_Equality n1.FStar_Ident.str "SMTPatT") -> begin
((FStar_Errors.log_issue top.FStar_Parser_AST.range ((FStar_Errors.Warning_SMTPatTDeprecated), ("SMTPatT is deprecated; please just use SMTPat")));
(

let uu____6113 = (

let uu___123_6114 = top
in (

let uu____6115 = (

let uu____6116 = (

let uu____6123 = (

let uu___124_6124 = top
in (

let uu____6125 = (

let uu____6126 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____6126))
in {FStar_Parser_AST.tm = uu____6125; FStar_Parser_AST.range = uu___124_6124.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___124_6124.FStar_Parser_AST.level}))
in ((uu____6123), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____6116))
in {FStar_Parser_AST.tm = uu____6115; FStar_Parser_AST.range = uu___123_6114.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___123_6114.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____6113));
)
end
| FStar_Parser_AST.Construct (n1, ((a, uu____6129))::[]) when (Prims.op_Equality n1.FStar_Ident.str "SMTPatOr") -> begin
(

let uu____6144 = (

let uu___125_6145 = top
in (

let uu____6146 = (

let uu____6147 = (

let uu____6154 = (

let uu___126_6155 = top
in (

let uu____6156 = (

let uu____6157 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat_or")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____6157))
in {FStar_Parser_AST.tm = uu____6156; FStar_Parser_AST.range = uu___126_6155.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___126_6155.FStar_Parser_AST.level}))
in ((uu____6154), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____6147))
in {FStar_Parser_AST.tm = uu____6146; FStar_Parser_AST.range = uu___125_6145.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___125_6145.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____6144))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____6158; FStar_Ident.ident = uu____6159; FStar_Ident.nsstr = uu____6160; FStar_Ident.str = "Type0"}) -> begin
(

let uu____6163 = (mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
in ((uu____6163), (noaqs)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____6178; FStar_Ident.ident = uu____6179; FStar_Ident.nsstr = uu____6180; FStar_Ident.str = "Type"}) -> begin
(

let uu____6183 = (mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
in ((uu____6183), (noaqs)))
end
| FStar_Parser_AST.Construct ({FStar_Ident.ns = uu____6198; FStar_Ident.ident = uu____6199; FStar_Ident.nsstr = uu____6200; FStar_Ident.str = "Type"}, ((t, FStar_Parser_AST.UnivApp))::[]) -> begin
(

let uu____6218 = (

let uu____6221 = (

let uu____6222 = (desugar_universe t)
in FStar_Syntax_Syntax.Tm_type (uu____6222))
in (mk1 uu____6221))
in ((uu____6218), (noaqs)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____6235; FStar_Ident.ident = uu____6236; FStar_Ident.nsstr = uu____6237; FStar_Ident.str = "Effect"}) -> begin
(

let uu____6240 = (mk1 (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
in ((uu____6240), (noaqs)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____6255; FStar_Ident.ident = uu____6256; FStar_Ident.nsstr = uu____6257; FStar_Ident.str = "True"}) -> begin
(

let uu____6260 = (

let uu____6261 = (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar uu____6261 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))
in ((uu____6260), (noaqs)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____6272; FStar_Ident.ident = uu____6273; FStar_Ident.nsstr = uu____6274; FStar_Ident.str = "False"}) -> begin
(

let uu____6277 = (

let uu____6278 = (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar uu____6278 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))
in ((uu____6277), (noaqs)))
end
| FStar_Parser_AST.Projector (eff_name, {FStar_Ident.idText = txt; FStar_Ident.idRange = uu____6291}) when ((is_special_effect_combinator txt) && (FStar_Syntax_DsEnv.is_effect_name env eff_name)) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name);
(

let uu____6293 = (FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name)
in (match (uu____6293) with
| FStar_Pervasives_Native.Some (ed) -> begin
(

let lid = (FStar_Syntax_Util.dm4f_lid ed txt)
in (

let uu____6302 = (FStar_Syntax_Syntax.fvar lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in ((uu____6302), (noaqs))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____6313 = (

let uu____6314 = (FStar_Ident.text_of_lid eff_name)
in (FStar_Util.format2 "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)" uu____6314 txt))
in (failwith uu____6313))
end));
)
end
| FStar_Parser_AST.Var (l) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l);
(

let uu____6321 = (desugar_name mk1 setpos env true l)
in ((uu____6321), (noaqs)));
)
end
| FStar_Parser_AST.Name (l) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l);
(

let uu____6334 = (desugar_name mk1 setpos env true l)
in ((uu____6334), (noaqs)));
)
end
| FStar_Parser_AST.Projector (l, i) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l);
(

let name = (

let uu____6355 = (FStar_Syntax_DsEnv.try_lookup_datacon env l)
in (match (uu____6355) with
| FStar_Pervasives_Native.Some (uu____6364) -> begin
FStar_Pervasives_Native.Some (((true), (l)))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____6369 = (FStar_Syntax_DsEnv.try_lookup_root_effect_name env l)
in (match (uu____6369) with
| FStar_Pervasives_Native.Some (new_name) -> begin
FStar_Pervasives_Native.Some (((false), (new_name)))
end
| uu____6383 -> begin
FStar_Pervasives_Native.None
end))
end))
in (match (name) with
| FStar_Pervasives_Native.Some (resolve, new_name) -> begin
(

let uu____6400 = (

let uu____6401 = (FStar_Syntax_Util.mk_field_projector_name_from_ident new_name i)
in (desugar_name mk1 setpos env resolve uu____6401))
in ((uu____6400), (noaqs)))
end
| uu____6412 -> begin
(

let uu____6419 = (

let uu____6424 = (FStar_Util.format1 "Data constructor or effect %s not found" l.FStar_Ident.str)
in ((FStar_Errors.Fatal_EffectNotFound), (uu____6424)))
in (FStar_Errors.raise_error uu____6419 top.FStar_Parser_AST.range))
end));
)
end
| FStar_Parser_AST.Discrim (lid) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid);
(

let uu____6431 = (FStar_Syntax_DsEnv.try_lookup_datacon env lid)
in (match (uu____6431) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6438 = (

let uu____6443 = (FStar_Util.format1 "Data constructor %s not found" lid.FStar_Ident.str)
in ((FStar_Errors.Fatal_DataContructorNotFound), (uu____6443)))
in (FStar_Errors.raise_error uu____6438 top.FStar_Parser_AST.range))
end
| uu____6448 -> begin
(

let lid' = (FStar_Syntax_Util.mk_discriminator lid)
in (

let uu____6452 = (desugar_name mk1 setpos env true lid')
in ((uu____6452), (noaqs))))
end));
)
end
| FStar_Parser_AST.Construct (l, args) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l);
(

let uu____6478 = (FStar_Syntax_DsEnv.try_lookup_datacon env l)
in (match (uu____6478) with
| FStar_Pervasives_Native.Some (head1) -> begin
(

let head2 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (head1)))
in (match (args) with
| [] -> begin
((head2), (noaqs))
end
| uu____6509 -> begin
(

let uu____6516 = (FStar_Util.take (fun uu____6540 -> (match (uu____6540) with
| (uu____6545, imp) -> begin
(Prims.op_Equality imp FStar_Parser_AST.UnivApp)
end)) args)
in (match (uu____6516) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun x -> (desugar_universe (FStar_Pervasives_Native.fst x))) universes)
in (

let uu____6590 = (

let uu____6605 = (FStar_List.map (fun uu____6638 -> (match (uu____6638) with
| (t, imp) -> begin
(

let uu____6655 = (desugar_term_aq env t)
in (match (uu____6655) with
| (te, aq) -> begin
(((arg_withimp_e imp te)), (aq))
end))
end)) args1)
in (FStar_All.pipe_right uu____6605 FStar_List.unzip))
in (match (uu____6590) with
| (args2, aqs) -> begin
(

let head3 = (match ((Prims.op_Equality universes1 [])) with
| true -> begin
head2
end
| uu____6743 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_uinst (((head2), (universes1)))))
end)
in (

let uu____6748 = (mk1 (FStar_Syntax_Syntax.Tm_app (((head3), (args2)))))
in ((uu____6748), ((join_aqs aqs)))))
end)))
end))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let err = (

let uu____6778 = (FStar_Syntax_DsEnv.try_lookup_effect_name env l)
in (match (uu____6778) with
| FStar_Pervasives_Native.None -> begin
((FStar_Errors.Fatal_ConstructorNotFound), ((Prims.strcat "Constructor " (Prims.strcat l.FStar_Ident.str " not found"))))
end
| FStar_Pervasives_Native.Some (uu____6785) -> begin
((FStar_Errors.Fatal_UnexpectedEffect), ((Prims.strcat "Effect " (Prims.strcat l.FStar_Ident.str " used at an unexpected position"))))
end))
in (FStar_Errors.raise_error err top.FStar_Parser_AST.range))
end));
)
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let uu____6796 = (FStar_List.fold_left (fun uu____6841 b -> (match (uu____6841) with
| (env1, tparams, typs) -> begin
(

let uu____6898 = (desugar_binder env1 b)
in (match (uu____6898) with
| (xopt, t1) -> begin
(

let uu____6927 = (match (xopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6936 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env1), (uu____6936)))
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_DsEnv.push_bv env1 x)
end)
in (match (uu____6927) with
| (env2, x) -> begin
(

let uu____6956 = (

let uu____6959 = (

let uu____6962 = (

let uu____6963 = (no_annot_abs tparams t1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____6963))
in (uu____6962)::[])
in (FStar_List.append typs uu____6959))
in ((env2), ((FStar_List.append tparams (((((

let uu___127_6989 = x
in {FStar_Syntax_Syntax.ppname = uu___127_6989.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___127_6989.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})), (FStar_Pervasives_Native.None)))::[]))), (uu____6956)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type_level FStar_Pervasives_Native.None))::[])))
in (match (uu____6796) with
| (env1, uu____7017, targs) -> begin
(

let uu____7039 = (

let uu____7044 = (FStar_Parser_Const.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Syntax_DsEnv.fail_or env1 (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____7044))
in (match (uu____7039) with
| (tup, uu____7054) -> begin
(

let uu____7055 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
in ((uu____7055), (noaqs)))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let uu____7080 = (uncurry binders t)
in (match (uu____7080) with
| (bs, t1) -> begin
(

let rec aux = (fun env1 bs1 uu___94_7122 -> (match (uu___94_7122) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range env1 t1)
in (

let uu____7136 = (FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod)
in (FStar_All.pipe_left setpos uu____7136)))
end
| (hd1)::tl1 -> begin
(

let bb = (desugar_binder env1 hd1)
in (

let uu____7158 = (as_binder env1 hd1.FStar_Parser_AST.aqual bb)
in (match (uu____7158) with
| (b, env2) -> begin
(aux env2 ((b)::bs1) tl1)
end)))
end))
in (

let uu____7167 = (aux env [] bs)
in ((uu____7167), (noaqs))))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(

let uu____7188 = (desugar_binder env b)
in (match (uu____7188) with
| (FStar_Pervasives_Native.None, uu____7199) -> begin
(failwith "Missing binder in refinement")
end
| b1 -> begin
(

let uu____7213 = (as_binder env FStar_Pervasives_Native.None b1)
in (match (uu____7213) with
| (x, env1) -> begin
(

let f1 = (desugar_formula env1 f)
in (

let t = (

let uu____7228 = (FStar_Syntax_Util.refine (FStar_Pervasives_Native.fst x) f1)
in (FStar_All.pipe_left setpos uu____7228))
in ((t), (noaqs))))
end))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let binders1 = (FStar_All.pipe_right binders (FStar_List.map replace_unit_pattern))
in (

let uu____7260 = (FStar_List.fold_left (fun uu____7280 pat -> (match (uu____7280) with
| (env1, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (uu____7306, (t, FStar_Pervasives_Native.None)) -> begin
(

let uu____7316 = (

let uu____7319 = (free_type_vars env1 t)
in (FStar_List.append uu____7319 ftvs))
in ((env1), (uu____7316)))
end
| FStar_Parser_AST.PatAscribed (uu____7324, (t, FStar_Pervasives_Native.Some (tac))) -> begin
(

let uu____7335 = (

let uu____7338 = (free_type_vars env1 t)
in (

let uu____7341 = (

let uu____7344 = (free_type_vars env1 tac)
in (FStar_List.append uu____7344 ftvs))
in (FStar_List.append uu____7338 uu____7341)))
in ((env1), (uu____7335)))
end
| uu____7349 -> begin
((env1), (ftvs))
end)
end)) ((env), ([])) binders1)
in (match (uu____7260) with
| (uu____7358, ftv) -> begin
(

let ftv1 = (sort_ftv ftv)
in (

let binders2 = (

let uu____7370 = (FStar_All.pipe_right ftv1 (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append uu____7370 binders1))
in (

let rec aux = (fun env1 bs sc_pat_opt uu___95_7423 -> (match (uu___95_7423) with
| [] -> begin
(

let uu____7446 = (desugar_term_aq env1 body)
in (match (uu____7446) with
| (body1, aq) -> begin
(

let body2 = (match (sc_pat_opt) with
| FStar_Pervasives_Native.Some (sc, pat) -> begin
(

let body2 = (

let uu____7477 = (

let uu____7478 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right uu____7478 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close uu____7477 body1))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (FStar_Pervasives_Native.None), (body2)))::[])))) FStar_Pervasives_Native.None body2.FStar_Syntax_Syntax.pos))
end
| FStar_Pervasives_Native.None -> begin
body1
end)
in (

let uu____7531 = (

let uu____7534 = (no_annot_abs (FStar_List.rev bs) body2)
in (setpos uu____7534))
in ((uu____7531), (aq))))
end))
end
| (p)::rest -> begin
(

let uu____7547 = (desugar_binding_pat env1 p)
in (match (uu____7547) with
| (env2, b, pat) -> begin
(

let pat1 = (match (pat) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (p1)::[] -> begin
FStar_Pervasives_Native.Some (p1)
end
| uu____7575 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnsupportedDisjuctivePatterns), ("Disjunctive patterns are not supported in abstractions")) p.FStar_Parser_AST.prange)
end)
in (

let uu____7580 = (match (b) with
| LetBinder (uu____7613) -> begin
(failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt1 = (match (((pat1), (sc_pat_opt))) with
| (FStar_Pervasives_Native.None, uu____7669) -> begin
sc_pat_opt
end
| (FStar_Pervasives_Native.Some (p1), FStar_Pervasives_Native.None) -> begin
(

let uu____7705 = (

let uu____7710 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____7710), (p1)))
in FStar_Pervasives_Native.Some (uu____7705))
end
| (FStar_Pervasives_Native.Some (p1), FStar_Pervasives_Native.Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (uu____7746), uu____7747) -> begin
(

let tup2 = (

let uu____7749 = (FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____7749 FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____7753 = (

let uu____7760 = (

let uu____7761 = (

let uu____7776 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (

let uu____7779 = (

let uu____7782 = (FStar_Syntax_Syntax.as_arg sc)
in (

let uu____7783 = (

let uu____7786 = (

let uu____7787 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____7787))
in (uu____7786)::[])
in (uu____7782)::uu____7783))
in ((uu____7776), (uu____7779))))
in FStar_Syntax_Syntax.Tm_app (uu____7761))
in (FStar_Syntax_Syntax.mk uu____7760))
in (uu____7753 FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
in (

let p2 = (

let uu____7798 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p1), (false)))::[])))) uu____7798))
in FStar_Pervasives_Native.Some (((sc1), (p2))))))
end
| (FStar_Syntax_Syntax.Tm_app (uu____7829, args), FStar_Syntax_Syntax.Pat_cons (uu____7831, pats)) -> begin
(

let tupn = (

let uu____7870 = (FStar_Parser_Const.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____7870 FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____7880 = (

let uu____7881 = (

let uu____7896 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (

let uu____7899 = (

let uu____7908 = (

let uu____7917 = (

let uu____7918 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____7918))
in (uu____7917)::[])
in (FStar_List.append args uu____7908))
in ((uu____7896), (uu____7899))))
in FStar_Syntax_Syntax.Tm_app (uu____7881))
in (mk1 uu____7880))
in (

let p2 = (

let uu____7938 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p1), (false)))::[])))))) uu____7938))
in FStar_Pervasives_Native.Some (((sc1), (p2))))))
end
| uu____7973 -> begin
(failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt1)))
end)
in (match (uu____7580) with
| (b1, sc_pat_opt1) -> begin
(aux env2 ((b1)::bs) sc_pat_opt1 rest)
end)))
end))
end))
in (aux env [] FStar_Pervasives_Native.None binders2))))
end)))
end
| FStar_Parser_AST.App (uu____8044, uu____8045, FStar_Parser_AST.UnivApp) -> begin
(

let rec aux = (fun universes e -> (

let uu____8067 = (

let uu____8068 = (unparen e)
in uu____8068.FStar_Parser_AST.tm)
in (match (uu____8067) with
| FStar_Parser_AST.App (e1, t, FStar_Parser_AST.UnivApp) -> begin
(

let univ_arg = (desugar_universe t)
in (aux ((univ_arg)::universes) e1))
end
| uu____8078 -> begin
(

let uu____8079 = (desugar_term_aq env e)
in (match (uu____8079) with
| (head1, aq) -> begin
(

let uu____8092 = (mk1 (FStar_Syntax_Syntax.Tm_uinst (((head1), (universes)))))
in ((uu____8092), (aq)))
end))
end)))
in (aux [] top))
end
| FStar_Parser_AST.App (uu____8099) -> begin
(

let rec aux = (fun args aqs e -> (

let uu____8158 = (

let uu____8159 = (unparen e)
in uu____8159.FStar_Parser_AST.tm)
in (match (uu____8158) with
| FStar_Parser_AST.App (e1, t, imp) when (Prims.op_disEquality imp FStar_Parser_AST.UnivApp) -> begin
(

let uu____8179 = (desugar_term_aq env t)
in (match (uu____8179) with
| (t1, aq) -> begin
(

let arg = (arg_withimp_e imp t1)
in (aux ((arg)::args) ((aq)::aqs) e1))
end))
end
| uu____8215 -> begin
(

let uu____8216 = (desugar_term_aq env e)
in (match (uu____8216) with
| (head1, aq) -> begin
(

let uu____8239 = (mk1 (FStar_Syntax_Syntax.Tm_app (((head1), (args)))))
in ((uu____8239), ((join_aqs ((aq)::aqs)))))
end))
end)))
in (aux [] [] top))
end
| FStar_Parser_AST.Bind (x, t1, t2) -> begin
(

let xpat = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (FStar_Pervasives_Native.None)))) x.FStar_Ident.idRange)
in (

let k = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ((((xpat)::[]), (t2)))) t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level)
in (

let bind_lid = (FStar_Ident.lid_of_path (("bind")::[]) x.FStar_Ident.idRange)
in (

let bind1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (bind_lid)) x.FStar_Ident.idRange FStar_Parser_AST.Expr)
in (

let uu____8279 = (FStar_Parser_AST.mkExplicitApp bind1 ((t1)::(k)::[]) top.FStar_Parser_AST.range)
in (desugar_term_aq env uu____8279))))))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(

let t = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), ((((FStar_Pervasives_Native.None), ((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
in (

let uu____8331 = (desugar_term_aq env t)
in (match (uu____8331) with
| (tm, s) -> begin
(

let uu____8342 = (mk1 (FStar_Syntax_Syntax.Tm_meta (((tm), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))))
in ((uu____8342), (s)))
end)))
end
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(

let env1 = (FStar_Syntax_DsEnv.push_namespace env lid)
in (

let uu____8350 = (

let uu____8363 = (FStar_Syntax_DsEnv.expect_typ env1)
in (match (uu____8363) with
| true -> begin
desugar_typ_aq
end
| uu____8374 -> begin
desugar_term_aq
end))
in (uu____8350 env1 e)))
end
| FStar_Parser_AST.Let (qual, lbs, body) -> begin
(

let is_rec = (Prims.op_Equality qual FStar_Parser_AST.Rec)
in (

let ds_let_rec_or_app = (fun uu____8418 -> (

let bindings = lbs
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun uu____8561 -> (match (uu____8561) with
| (attr_opt, (p, def)) -> begin
(

let uu____8619 = (is_app_pattern p)
in (match (uu____8619) with
| true -> begin
(

let uu____8650 = (destruct_app_pattern env top_level p)
in ((attr_opt), (uu____8650), (def)))
end
| uu____8695 -> begin
(match ((FStar_Parser_AST.un_function p def)) with
| FStar_Pervasives_Native.Some (p1, def1) -> begin
(

let uu____8732 = (destruct_app_pattern env top_level p1)
in ((attr_opt), (uu____8732), (def1)))
end
| uu____8777 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id1, uu____8815); FStar_Parser_AST.prange = uu____8816}, t) -> begin
(match (top_level) with
| true -> begin
(

let uu____8864 = (

let uu____8885 = (

let uu____8890 = (FStar_Syntax_DsEnv.qualify env id1)
in FStar_Util.Inr (uu____8890))
in ((uu____8885), ([]), (FStar_Pervasives_Native.Some (t))))
in ((attr_opt), (uu____8864), (def)))
end
| uu____8935 -> begin
((attr_opt), (((FStar_Util.Inl (id1)), ([]), (FStar_Pervasives_Native.Some (t)))), (def))
end)
end
| FStar_Parser_AST.PatVar (id1, uu____8981) -> begin
(match (top_level) with
| true -> begin
(

let uu____9016 = (

let uu____9037 = (

let uu____9042 = (FStar_Syntax_DsEnv.qualify env id1)
in FStar_Util.Inr (uu____9042))
in ((uu____9037), ([]), (FStar_Pervasives_Native.None)))
in ((attr_opt), (uu____9016), (def)))
end
| uu____9087 -> begin
((attr_opt), (((FStar_Util.Inl (id1)), ([]), (FStar_Pervasives_Native.None))), (def))
end)
end
| uu____9132 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedLetBinding), ("Unexpected let binding")) p.FStar_Parser_AST.prange)
end)
end)
end))
end))))
in (

let uu____9163 = (FStar_List.fold_left (fun uu____9236 uu____9237 -> (match (((uu____9236), (uu____9237))) with
| ((env1, fnames, rec_bindings), (_attr_opt, (f, uu____9345, uu____9346), uu____9347)) -> begin
(

let uu____9464 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let uu____9490 = (FStar_Syntax_DsEnv.push_bv env1 x)
in (match (uu____9490) with
| (env2, xx) -> begin
(

let uu____9509 = (

let uu____9512 = (FStar_Syntax_Syntax.mk_binder xx)
in (uu____9512)::rec_bindings)
in ((env2), (FStar_Util.Inl (xx)), (uu____9509)))
end))
end
| FStar_Util.Inr (l) -> begin
(

let uu____9520 = (FStar_Syntax_DsEnv.push_top_level_rec_binding env1 l.FStar_Ident.ident FStar_Syntax_Syntax.delta_equational)
in ((uu____9520), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (uu____9464) with
| (env2, lbname, rec_bindings1) -> begin
((env2), ((lbname)::fnames), (rec_bindings1))
end))
end)) ((env), ([]), ([])) funs)
in (match (uu____9163) with
| (env', fnames, rec_bindings) -> begin
(

let fnames1 = (FStar_List.rev fnames)
in (

let rec_bindings1 = (FStar_List.rev rec_bindings)
in (

let desugar_one_def = (fun env1 lbname uu____9668 -> (match (uu____9668) with
| (attrs_opt, (uu____9704, args, result_t), def) -> begin
(

let args1 = (FStar_All.pipe_right args (FStar_List.map replace_unit_pattern))
in (

let pos = def.FStar_Parser_AST.range
in (

let def1 = (match (result_t) with
| FStar_Pervasives_Native.None -> begin
def
end
| FStar_Pervasives_Native.Some (t, tacopt) -> begin
(

let t1 = (

let uu____9792 = (is_comp_type env1 t)
in (match (uu____9792) with
| true -> begin
((

let uu____9794 = (FStar_All.pipe_right args1 (FStar_List.tryFind (fun x -> (

let uu____9804 = (is_var_pattern x)
in (not (uu____9804))))))
in (match (uu____9794) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (p) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ComputationTypeNotAllowed), ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")) p.FStar_Parser_AST.prange)
end));
t;
)
end
| uu____9806 -> begin
(

let uu____9807 = (((FStar_Options.ml_ish ()) && (

let uu____9809 = (FStar_Syntax_DsEnv.try_lookup_effect_name env1 FStar_Parser_Const.effect_ML_lid)
in (FStar_Option.isSome uu____9809))) && ((not (is_rec)) || (Prims.op_disEquality (FStar_List.length args1) (Prims.parse_int "0"))))
in (match (uu____9807) with
| true -> begin
(FStar_Parser_AST.ml_comp t)
end
| uu____9812 -> begin
(FStar_Parser_AST.tot_comp t)
end))
end))
in (

let uu____9813 = (FStar_Range.union_ranges t1.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t1), (tacopt)))) uu____9813 FStar_Parser_AST.Expr)))
end)
in (

let def2 = (match (args1) with
| [] -> begin
def1
end
| uu____9817 -> begin
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

let uu____9832 = (

let uu____9833 = (FStar_Syntax_Util.incr_delta_qualifier body1)
in (FStar_Syntax_Syntax.lid_as_fv l uu____9833 FStar_Pervasives_Native.None))
in FStar_Util.Inr (uu____9832))
end)
in (

let body2 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.close rec_bindings1 body1)
end
| uu____9835 -> begin
body1
end)
in (

let attrs = (match (attrs_opt) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (l) -> begin
(FStar_List.map (desugar_term env1) l)
end)
in (mk_lb ((attrs), (lbname1), (FStar_Syntax_Syntax.tun), (body2), (pos)))))))))))
end))
in (

let lbs1 = (FStar_List.map2 (desugar_one_def (match (is_rec) with
| true -> begin
env'
end
| uu____9891 -> begin
env
end)) fnames1 funs)
in (

let uu____9892 = (desugar_term_aq env' body)
in (match (uu____9892) with
| (body1, aq) -> begin
(

let uu____9905 = (

let uu____9908 = (

let uu____9909 = (

let uu____9922 = (FStar_Syntax_Subst.close rec_bindings1 body1)
in ((((is_rec), (lbs1))), (uu____9922)))
in FStar_Syntax_Syntax.Tm_let (uu____9909))
in (FStar_All.pipe_left mk1 uu____9908))
in ((uu____9905), (aq)))
end))))))
end)))))
in (

let ds_non_rec = (fun attrs_opt pat t1 t2 -> (

let attrs = (match (attrs_opt) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (l) -> begin
(FStar_List.map (desugar_term env) l)
end)
in (

let t11 = (desugar_term env t1)
in (

let is_mutable = (Prims.op_Equality qual FStar_Parser_AST.Mutable)
in (

let t12 = (match (is_mutable) with
| true -> begin
(mk_ref_alloc t11)
end
| uu____9989 -> begin
t11
end)
in (

let uu____9990 = (desugar_binding_pat_maybe_top top_level env pat is_mutable)
in (match (uu____9990) with
| (env1, binder, pat1) -> begin
(

let uu____10012 = (match (binder) with
| LetBinder (l, (t, _tacopt)) -> begin
(

let uu____10038 = (desugar_term_aq env1 t2)
in (match (uu____10038) with
| (body1, aq) -> begin
(

let fv = (

let uu____10052 = (FStar_Syntax_Util.incr_delta_qualifier t12)
in (FStar_Syntax_Syntax.lid_as_fv l uu____10052 FStar_Pervasives_Native.None))
in (

let uu____10053 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_let (((((false), (((mk_lb ((attrs), (FStar_Util.Inr (fv)), (t), (t12), (t12.FStar_Syntax_Syntax.pos))))::[]))), (body1)))))
in ((uu____10053), (aq))))
end))
end
| LocalBinder (x, uu____10077) -> begin
(

let uu____10078 = (desugar_term_aq env1 t2)
in (match (uu____10078) with
| (body1, aq) -> begin
(

let body2 = (match (pat1) with
| [] -> begin
body1
end
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (uu____10092); FStar_Syntax_Syntax.p = uu____10093})::[] -> begin
body1
end
| uu____10098 -> begin
(

let uu____10101 = (

let uu____10108 = (

let uu____10109 = (

let uu____10132 = (FStar_Syntax_Syntax.bv_to_name x)
in (

let uu____10133 = (desugar_disjunctive_pattern pat1 FStar_Pervasives_Native.None body1)
in ((uu____10132), (uu____10133))))
in FStar_Syntax_Syntax.Tm_match (uu____10109))
in (FStar_Syntax_Syntax.mk uu____10108))
in (uu____10101 FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
end)
in (

let uu____10143 = (

let uu____10146 = (

let uu____10147 = (

let uu____10160 = (

let uu____10161 = (

let uu____10162 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____10162)::[])
in (FStar_Syntax_Subst.close uu____10161 body2))
in ((((false), (((mk_lb ((attrs), (FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t12), (t12.FStar_Syntax_Syntax.pos))))::[]))), (uu____10160)))
in FStar_Syntax_Syntax.Tm_let (uu____10147))
in (FStar_All.pipe_left mk1 uu____10146))
in ((uu____10143), (aq))))
end))
end)
in (match (uu____10012) with
| (tm, aq) -> begin
(match (is_mutable) with
| true -> begin
(

let uu____10203 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((tm), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc))))))
in ((uu____10203), (aq)))
end
| uu____10212 -> begin
((tm), (aq))
end)
end))
end)))))))
in (

let uu____10215 = (FStar_List.hd lbs)
in (match (uu____10215) with
| (attrs, (head_pat, defn)) -> begin
(

let uu____10259 = (is_rec || (is_app_pattern head_pat))
in (match (uu____10259) with
| true -> begin
(ds_let_rec_or_app ())
end
| uu____10264 -> begin
(ds_non_rec attrs head_pat defn body)
end))
end)))))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (

let t_bool1 = (

let uu____10272 = (

let uu____10273 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in FStar_Syntax_Syntax.Tm_fvar (uu____10273))
in (mk1 uu____10272))
in (

let uu____10274 = (desugar_term_aq env t1)
in (match (uu____10274) with
| (t1', aq1) -> begin
(

let uu____10285 = (desugar_term_aq env t2)
in (match (uu____10285) with
| (t2', aq2) -> begin
(

let uu____10296 = (desugar_term_aq env t3)
in (match (uu____10296) with
| (t3', aq3) -> begin
(

let uu____10307 = (

let uu____10310 = (

let uu____10311 = (

let uu____10334 = (FStar_Syntax_Util.ascribe t1' ((FStar_Util.Inl (t_bool1)), (FStar_Pervasives_Native.None)))
in (

let uu____10355 = (

let uu____10370 = (

let uu____10383 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) t2.FStar_Parser_AST.range)
in ((uu____10383), (FStar_Pervasives_Native.None), (t2')))
in (

let uu____10394 = (

let uu____10409 = (

let uu____10422 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) t3.FStar_Parser_AST.range)
in ((uu____10422), (FStar_Pervasives_Native.None), (t3')))
in (uu____10409)::[])
in (uu____10370)::uu____10394))
in ((uu____10334), (uu____10355))))
in FStar_Syntax_Syntax.Tm_match (uu____10311))
in (mk1 uu____10310))
in ((uu____10307), ((join_aqs ((aq1)::(aq2)::(aq3)::[])))))
end))
end))
end))))
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(

let r = top.FStar_Parser_AST.range
in (

let handler = (FStar_Parser_AST.mk_function branches r r)
in (

let body = (FStar_Parser_AST.mk_function (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatConst (FStar_Const.Const_unit)) r)), (FStar_Pervasives_Native.None), (e)))::[]) r r)
in (

let a1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (FStar_Parser_Const.try_with_lid)) r top.FStar_Parser_AST.level)), (body), (FStar_Parser_AST.Nothing)))) r top.FStar_Parser_AST.level)
in (

let a2 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((a1), (handler), (FStar_Parser_AST.Nothing)))) r top.FStar_Parser_AST.level)
in (desugar_term_aq env a2))))))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(

let desugar_branch = (fun uu____10583 -> (match (uu____10583) with
| (pat, wopt, b) -> begin
(

let uu____10605 = (desugar_match_pat env pat)
in (match (uu____10605) with
| (env1, pat1) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (e1) -> begin
(

let uu____10630 = (desugar_term env1 e1)
in FStar_Pervasives_Native.Some (uu____10630))
end)
in (

let uu____10631 = (desugar_term_aq env1 b)
in (match (uu____10631) with
| (b1, aq) -> begin
(

let uu____10644 = (desugar_disjunctive_pattern pat1 wopt1 b1)
in ((uu____10644), (aq)))
end)))
end))
end))
in (

let uu____10649 = (desugar_term_aq env e)
in (match (uu____10649) with
| (e1, aq) -> begin
(

let uu____10660 = (

let uu____10669 = (

let uu____10680 = (FStar_List.map desugar_branch branches)
in (FStar_All.pipe_right uu____10680 FStar_List.unzip))
in (FStar_All.pipe_right uu____10669 (fun uu____10744 -> (match (uu____10744) with
| (x, y) -> begin
(((FStar_List.flatten x)), (y))
end))))
in (match (uu____10660) with
| (brs, aqs) -> begin
(

let uu____10795 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_match (((e1), (brs)))))
in ((uu____10795), ((join_aqs ((aq)::aqs)))))
end))
end)))
end
| FStar_Parser_AST.Ascribed (e, t, tac_opt) -> begin
(

let annot = (

let uu____10828 = (is_comp_type env t)
in (match (uu____10828) with
| true -> begin
(

let uu____10835 = (desugar_comp t.FStar_Parser_AST.range env t)
in FStar_Util.Inr (uu____10835))
end
| uu____10840 -> begin
(

let uu____10841 = (desugar_term env t)
in FStar_Util.Inl (uu____10841))
end))
in (

let tac_opt1 = (FStar_Util.map_opt tac_opt (desugar_term env))
in (

let uu____10847 = (desugar_term_aq env e)
in (match (uu____10847) with
| (e1, aq) -> begin
(

let uu____10858 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_ascribed (((e1), (((annot), (tac_opt1))), (FStar_Pervasives_Native.None)))))
in ((uu____10858), (aq)))
end))))
end
| FStar_Parser_AST.Record (uu____10887, []) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedEmptyRecord), ("Unexpected empty record")) top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let record = (check_fields env fields top.FStar_Parser_AST.range)
in (

let user_ns = (

let uu____10928 = (FStar_List.hd fields)
in (match (uu____10928) with
| (f, uu____10940) -> begin
f.FStar_Ident.ns
end))
in (

let get_field = (fun xopt f -> (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun uu____10986 -> (match (uu____10986) with
| (g, uu____10992) -> begin
(Prims.op_Equality f.FStar_Ident.idText g.FStar_Ident.ident.FStar_Ident.idText)
end))))
in (

let fn = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((f)::[])))
in (match (found) with
| FStar_Pervasives_Native.Some (uu____10998, e) -> begin
((fn), (e))
end
| FStar_Pervasives_Native.None -> begin
(match (xopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____11012 = (

let uu____11017 = (FStar_Util.format2 "Field %s of record type %s is missing" f.FStar_Ident.idText record.FStar_Syntax_DsEnv.typename.FStar_Ident.str)
in ((FStar_Errors.Fatal_MissingFieldInRecord), (uu____11017)))
in (FStar_Errors.raise_error uu____11012 top.FStar_Parser_AST.range))
end
| FStar_Pervasives_Native.Some (x) -> begin
((fn), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Project (((x), (fn)))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end))))
in (

let user_constrname = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((record.FStar_Syntax_DsEnv.constrname)::[])))
in (

let recterm = (match (eopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____11025 = (

let uu____11036 = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map (fun uu____11067 -> (match (uu____11067) with
| (f, uu____11077) -> begin
(

let uu____11078 = (

let uu____11079 = (get_field FStar_Pervasives_Native.None f)
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____11079))
in ((uu____11078), (FStar_Parser_AST.Nothing)))
end))))
in ((user_constrname), (uu____11036)))
in FStar_Parser_AST.Construct (uu____11025))
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (

let uu____11097 = (

let uu____11098 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____11098))
in (FStar_Parser_AST.mk_term uu____11097 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record1 = (

let uu____11100 = (

let uu____11113 = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map (fun uu____11143 -> (match (uu____11143) with
| (f, uu____11153) -> begin
(get_field (FStar_Pervasives_Native.Some (xterm)) f)
end))))
in ((FStar_Pervasives_Native.None), (uu____11113)))
in FStar_Parser_AST.Record (uu____11100))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), ((((FStar_Pervasives_Native.None), ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (FStar_Pervasives_Native.None)))) x.FStar_Ident.idRange)), (e)))))::[]), ((FStar_Parser_AST.mk_term record1 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm1 = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let uu____11213 = (desugar_term_aq env recterm1)
in (match (uu____11213) with
| (e, s) -> begin
(match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____11229; FStar_Syntax_Syntax.vars = uu____11230}, args) -> begin
(

let uu____11252 = (

let uu____11255 = (

let uu____11256 = (

let uu____11271 = (

let uu____11272 = (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos)
in (

let uu____11273 = (

let uu____11276 = (

let uu____11277 = (

let uu____11284 = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map FStar_Pervasives_Native.fst))
in ((record.FStar_Syntax_DsEnv.typename), (uu____11284)))
in FStar_Syntax_Syntax.Record_ctor (uu____11277))
in FStar_Pervasives_Native.Some (uu____11276))
in (FStar_Syntax_Syntax.fvar uu____11272 FStar_Syntax_Syntax.delta_constant uu____11273)))
in ((uu____11271), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____11256))
in (FStar_All.pipe_left mk1 uu____11255))
in ((uu____11252), (s)))
end
| uu____11313 -> begin
((e), (s))
end)
end))))))))
end
| FStar_Parser_AST.Project (e, f) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f);
(

let uu____11317 = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f)
in (match (uu____11317) with
| (constrname, is_rec) -> begin
(

let uu____11332 = (desugar_term_aq env e)
in (match (uu____11332) with
| (e1, s) -> begin
(

let projname = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname f.FStar_Ident.ident)
in (

let qual = (match (is_rec) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (((constrname), (f.FStar_Ident.ident))))
end
| uu____11349 -> begin
FStar_Pervasives_Native.None
end)
in (

let uu____11350 = (

let uu____11353 = (

let uu____11354 = (

let uu____11369 = (

let uu____11370 = (

let uu____11371 = (FStar_Ident.range_of_lid f)
in (FStar_Ident.set_lid_range projname uu____11371))
in (FStar_Syntax_Syntax.fvar uu____11370 FStar_Syntax_Syntax.delta_equational qual))
in (

let uu____11372 = (

let uu____11375 = (FStar_Syntax_Syntax.as_arg e1)
in (uu____11375)::[])
in ((uu____11369), (uu____11372))))
in FStar_Syntax_Syntax.Tm_app (uu____11354))
in (FStar_All.pipe_left mk1 uu____11353))
in ((uu____11350), (s)))))
end))
end));
)
end
| FStar_Parser_AST.NamedTyp (uu____11382, e) -> begin
(desugar_term_aq env e)
end
| FStar_Parser_AST.Paren (e) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.VQuote (e) -> begin
(

let tm = (desugar_term env e)
in (

let uu____11391 = (

let uu____11392 = (FStar_Syntax_Subst.compress tm)
in uu____11392.FStar_Syntax_Syntax.n)
in (match (uu____11391) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____11400 = (

let uu___128_11403 = (

let uu____11404 = (

let uu____11405 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____11405))
in (FStar_Syntax_Util.exp_string uu____11404))
in {FStar_Syntax_Syntax.n = uu___128_11403.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = e.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___128_11403.FStar_Syntax_Syntax.vars})
in ((uu____11400), (noaqs)))
end
| uu____11418 -> begin
(

let uu____11419 = (

let uu____11424 = (

let uu____11425 = (FStar_Syntax_Print.term_to_string tm)
in (Prims.strcat "VQuote, expected an fvar, got: " uu____11425))
in ((FStar_Errors.Fatal_UnexpectedTermVQuote), (uu____11424)))
in (FStar_Errors.raise_error uu____11419 top.FStar_Parser_AST.range))
end)))
end
| FStar_Parser_AST.Quote (e, FStar_Parser_AST.Static) -> begin
(

let uu____11431 = (desugar_term_aq env e)
in (match (uu____11431) with
| (tm, vts) -> begin
(

let qi = {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = vts}
in (

let uu____11443 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_quoted (((tm), (qi)))))
in ((uu____11443), (noaqs))))
end))
end
| FStar_Parser_AST.Antiquote (b, e) -> begin
(

let bv = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (

let uu____11463 = (FStar_Syntax_Syntax.bv_to_name bv)
in (

let uu____11464 = (

let uu____11473 = (

let uu____11480 = (desugar_term env e)
in ((bv), (b), (uu____11480)))
in (uu____11473)::[])
in ((uu____11463), (uu____11464)))))
end
| FStar_Parser_AST.Quote (e, FStar_Parser_AST.Dynamic) -> begin
(

let qi = {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = []}
in (

let uu____11511 = (

let uu____11514 = (

let uu____11515 = (

let uu____11522 = (desugar_term env e)
in ((uu____11522), (qi)))
in FStar_Syntax_Syntax.Tm_quoted (uu____11515))
in (FStar_All.pipe_left mk1 uu____11514))
in ((uu____11511), (noaqs))))
end
| uu____11537 when (Prims.op_Equality top.FStar_Parser_AST.level FStar_Parser_AST.Formula) -> begin
(

let uu____11538 = (desugar_formula env top)
in ((uu____11538), (noaqs)))
end
| uu____11549 -> begin
(

let uu____11550 = (

let uu____11555 = (

let uu____11556 = (FStar_Parser_AST.term_to_string top)
in (Prims.strcat "Unexpected term: " uu____11556))
in ((FStar_Errors.Fatal_UnexpectedTerm), (uu____11555)))
in (FStar_Errors.raise_error uu____11550 top.FStar_Parser_AST.range))
end)))))))
and not_ascribed : FStar_Parser_AST.term  ->  Prims.bool = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Ascribed (uu____11562) -> begin
false
end
| uu____11571 -> begin
true
end))
and is_synth_by_tactic : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun e t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (l, r, FStar_Parser_AST.Hash) -> begin
(is_synth_by_tactic e l)
end
| FStar_Parser_AST.Var (lid) -> begin
(

let uu____11577 = (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name e lid)
in (match (uu____11577) with
| FStar_Pervasives_Native.Some (lid1) -> begin
(FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid)
end
| FStar_Pervasives_Native.None -> begin
false
end))
end
| uu____11581 -> begin
false
end))
and desugar_args : FStar_Syntax_DsEnv.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____11618 -> (match (uu____11618) with
| (a, imp) -> begin
(

let uu____11631 = (desugar_term env a)
in (arg_withimp_e imp uu____11631))
end)))))
and desugar_comp : FStar_Range.range  ->  FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun r env t -> (

let fail1 = (fun err -> (FStar_Errors.raise_error err r))
in (

let is_requires = (fun uu____11663 -> (match (uu____11663) with
| (t1, uu____11669) -> begin
(

let uu____11670 = (

let uu____11671 = (unparen t1)
in uu____11671.FStar_Parser_AST.tm)
in (match (uu____11670) with
| FStar_Parser_AST.Requires (uu____11672) -> begin
true
end
| uu____11679 -> begin
false
end))
end))
in (

let is_ensures = (fun uu____11689 -> (match (uu____11689) with
| (t1, uu____11695) -> begin
(

let uu____11696 = (

let uu____11697 = (unparen t1)
in uu____11697.FStar_Parser_AST.tm)
in (match (uu____11696) with
| FStar_Parser_AST.Ensures (uu____11698) -> begin
true
end
| uu____11705 -> begin
false
end))
end))
in (

let is_app = (fun head1 uu____11720 -> (match (uu____11720) with
| (t1, uu____11726) -> begin
(

let uu____11727 = (

let uu____11728 = (unparen t1)
in uu____11728.FStar_Parser_AST.tm)
in (match (uu____11727) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = uu____11730; FStar_Parser_AST.level = uu____11731}, uu____11732, uu____11733) -> begin
(Prims.op_Equality d.FStar_Ident.ident.FStar_Ident.idText head1)
end
| uu____11734 -> begin
false
end))
end))
in (

let is_smt_pat = (fun uu____11744 -> (match (uu____11744) with
| (t1, uu____11750) -> begin
(

let uu____11751 = (

let uu____11752 = (unparen t1)
in uu____11752.FStar_Parser_AST.tm)
in (match (uu____11751) with
| FStar_Parser_AST.Construct (cons1, (({FStar_Parser_AST.tm = FStar_Parser_AST.Construct (smtpat, uu____11755); FStar_Parser_AST.range = uu____11756; FStar_Parser_AST.level = uu____11757}, uu____11758))::(uu____11759)::[]) -> begin
((FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid) && (FStar_Util.for_some (fun s -> (Prims.op_Equality smtpat.FStar_Ident.str s)) (("SMTPat")::("SMTPatT")::("SMTPatOr")::[])))
end
| FStar_Parser_AST.Construct (cons1, (({FStar_Parser_AST.tm = FStar_Parser_AST.Var (smtpat); FStar_Parser_AST.range = uu____11798; FStar_Parser_AST.level = uu____11799}, uu____11800))::(uu____11801)::[]) -> begin
((FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid) && (FStar_Util.for_some (fun s -> (Prims.op_Equality smtpat.FStar_Ident.str s)) (("smt_pat")::("smt_pat_or")::[])))
end
| uu____11826 -> begin
false
end))
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t1 -> (

let uu____11858 = (head_and_args t1)
in (match (uu____11858) with
| (head1, args) -> begin
(match (head1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (Prims.op_Equality lemma.FStar_Ident.ident.FStar_Ident.idText "Lemma") -> begin
(

let unit_tm = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.unit_lid)) t1.FStar_Parser_AST.range FStar_Parser_AST.Type_level)), (FStar_Parser_AST.Nothing))
in (

let nil_pat = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.nil_lid)) t1.FStar_Parser_AST.range FStar_Parser_AST.Expr)), (FStar_Parser_AST.Nothing))
in (

let req_true = (

let req = FStar_Parser_AST.Requires ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.true_lid)) t1.FStar_Parser_AST.range FStar_Parser_AST.Formula)), (FStar_Pervasives_Native.None)))
in (((FStar_Parser_AST.mk_term req t1.FStar_Parser_AST.range FStar_Parser_AST.Type_level)), (FStar_Parser_AST.Nothing)))
in (

let thunk_ens_ = (fun ens -> (

let wildpat = (FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild ens.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ((((wildpat)::[]), (ens)))) ens.FStar_Parser_AST.range FStar_Parser_AST.Expr)))
in (

let thunk_ens = (fun uu____11956 -> (match (uu____11956) with
| (e, i) -> begin
(

let uu____11967 = (thunk_ens_ e)
in ((uu____11967), (i)))
end))
in (

let fail_lemma = (fun uu____11979 -> (

let expected_one_of = ("Lemma post")::("Lemma (ensures post)")::("Lemma (requires pre) (ensures post)")::("Lemma post [SMTPat ...]")::("Lemma (ensures post) [SMTPat ...]")::("Lemma (ensures post) (decreases d)")::("Lemma (ensures post) (decreases d) [SMTPat ...]")::("Lemma (requires pre) (ensures post) (decreases d)")::("Lemma (requires pre) (ensures post) [SMTPat ...]")::("Lemma (requires pre) (ensures post) (decreases d) [SMTPat ...]")::[]
in (

let msg = (FStar_String.concat "\n\t" expected_one_of)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_InvalidLemmaArgument), ((Prims.strcat "Invalid arguments to \'Lemma\'; expected one of the following:\n\t" msg))) t1.FStar_Parser_AST.range))))
in (

let args1 = (match (args) with
| [] -> begin
(fail_lemma ())
end
| (req)::[] when (is_requires req) -> begin
(fail_lemma ())
end
| (smtpat)::[] when (is_smt_pat smtpat) -> begin
(fail_lemma ())
end
| (dec)::[] when (is_decreases dec) -> begin
(fail_lemma ())
end
| (ens)::[] -> begin
(

let uu____12059 = (

let uu____12066 = (

let uu____12073 = (thunk_ens ens)
in (uu____12073)::(nil_pat)::[])
in (req_true)::uu____12066)
in (unit_tm)::uu____12059)
end
| (req)::(ens)::[] when ((is_requires req) && (is_ensures ens)) -> begin
(

let uu____12120 = (

let uu____12127 = (

let uu____12134 = (thunk_ens ens)
in (uu____12134)::(nil_pat)::[])
in (req)::uu____12127)
in (unit_tm)::uu____12120)
end
| (ens)::(smtpat)::[] when ((((

let uu____12183 = (is_requires ens)
in (not (uu____12183))) && (

let uu____12185 = (is_smt_pat ens)
in (not (uu____12185)))) && (

let uu____12187 = (is_decreases ens)
in (not (uu____12187)))) && (is_smt_pat smtpat)) -> begin
(

let uu____12188 = (

let uu____12195 = (

let uu____12202 = (thunk_ens ens)
in (uu____12202)::(smtpat)::[])
in (req_true)::uu____12195)
in (unit_tm)::uu____12188)
end
| (ens)::(dec)::[] when ((is_ensures ens) && (is_decreases dec)) -> begin
(

let uu____12249 = (

let uu____12256 = (

let uu____12263 = (thunk_ens ens)
in (uu____12263)::(nil_pat)::(dec)::[])
in (req_true)::uu____12256)
in (unit_tm)::uu____12249)
end
| (ens)::(dec)::(smtpat)::[] when (((is_ensures ens) && (is_decreases dec)) && (is_smt_pat smtpat)) -> begin
(

let uu____12323 = (

let uu____12330 = (

let uu____12337 = (thunk_ens ens)
in (uu____12337)::(smtpat)::(dec)::[])
in (req_true)::uu____12330)
in (unit_tm)::uu____12323)
end
| (req)::(ens)::(dec)::[] when (((is_requires req) && (is_ensures ens)) && (is_decreases dec)) -> begin
(

let uu____12397 = (

let uu____12404 = (

let uu____12411 = (thunk_ens ens)
in (uu____12411)::(nil_pat)::(dec)::[])
in (req)::uu____12404)
in (unit_tm)::uu____12397)
end
| (req)::(ens)::(smtpat)::[] when (((is_requires req) && (is_ensures ens)) && (is_smt_pat smtpat)) -> begin
(

let uu____12471 = (

let uu____12478 = (

let uu____12485 = (thunk_ens ens)
in (uu____12485)::(smtpat)::[])
in (req)::uu____12478)
in (unit_tm)::uu____12471)
end
| (req)::(ens)::(dec)::(smtpat)::[] when ((((is_requires req) && (is_ensures ens)) && (is_smt_pat smtpat)) && (is_decreases dec)) -> begin
(

let uu____12550 = (

let uu____12557 = (

let uu____12564 = (thunk_ens ens)
in (uu____12564)::(dec)::(smtpat)::[])
in (req)::uu____12557)
in (unit_tm)::uu____12550)
end
| _other -> begin
(fail_lemma ())
end)
in (

let head_and_attributes = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes env) lemma)
in ((head_and_attributes), (args1))))))))))
end
| FStar_Parser_AST.Name (l) when (FStar_Syntax_DsEnv.is_effect_name env l) -> begin
(

let uu____12626 = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes env) l)
in ((uu____12626), (args)))
end
| FStar_Parser_AST.Name (l) when ((

let uu____12654 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Ident.lid_equals uu____12654 FStar_Parser_Const.prims_lid)) && (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Tot")) -> begin
(

let uu____12655 = (

let uu____12662 = (FStar_Ident.set_lid_range FStar_Parser_Const.effect_Tot_lid head1.FStar_Parser_AST.range)
in ((uu____12662), ([])))
in ((uu____12655), (args)))
end
| FStar_Parser_AST.Name (l) when ((

let uu____12680 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Ident.lid_equals uu____12680 FStar_Parser_Const.prims_lid)) && (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "GTot")) -> begin
(

let uu____12681 = (

let uu____12688 = (FStar_Ident.set_lid_range FStar_Parser_Const.effect_GTot_lid head1.FStar_Parser_AST.range)
in ((uu____12688), ([])))
in ((uu____12681), (args)))
end
| FStar_Parser_AST.Name (l) when (((Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Type") || (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Type0")) || (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Effect")) -> begin
(

let uu____12704 = (

let uu____12711 = (FStar_Ident.set_lid_range FStar_Parser_Const.effect_Tot_lid head1.FStar_Parser_AST.range)
in ((uu____12711), ([])))
in ((uu____12704), ((((t1), (FStar_Parser_AST.Nothing)))::[])))
end
| uu____12734 -> begin
(

let default_effect = (

let uu____12736 = (FStar_Options.ml_ish ())
in (match (uu____12736) with
| true -> begin
FStar_Parser_Const.effect_ML_lid
end
| uu____12737 -> begin
((

let uu____12739 = (FStar_Options.warn_default_effects ())
in (match (uu____12739) with
| true -> begin
(FStar_Errors.log_issue head1.FStar_Parser_AST.range ((FStar_Errors.Warning_UseDefaultEffect), ("Using default effect Tot")))
end
| uu____12740 -> begin
()
end));
FStar_Parser_Const.effect_Tot_lid;
)
end))
in (

let uu____12741 = (

let uu____12748 = (FStar_Ident.set_lid_range default_effect head1.FStar_Parser_AST.range)
in ((uu____12748), ([])))
in ((uu____12741), ((((t1), (FStar_Parser_AST.Nothing)))::[]))))
end)
end)))
in (

let uu____12771 = (pre_process_comp_typ t)
in (match (uu____12771) with
| ((eff, cattributes), args) -> begin
((match ((Prims.op_Equality (FStar_List.length args) (Prims.parse_int "0"))) with
| true -> begin
(

let uu____12820 = (

let uu____12825 = (

let uu____12826 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" uu____12826))
in ((FStar_Errors.Fatal_NotEnoughArgsToEffect), (uu____12825)))
in (fail1 uu____12820))
end
| uu____12827 -> begin
()
end);
(

let is_universe = (fun uu____12837 -> (match (uu____12837) with
| (uu____12842, imp) -> begin
(Prims.op_Equality imp FStar_Parser_AST.UnivApp)
end))
in (

let uu____12844 = (FStar_Util.take is_universe args)
in (match (uu____12844) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun uu____12903 -> (match (uu____12903) with
| (u, imp) -> begin
(desugar_universe u)
end)) universes)
in (

let uu____12910 = (

let uu____12925 = (FStar_List.hd args1)
in (

let uu____12934 = (FStar_List.tl args1)
in ((uu____12925), (uu____12934))))
in (match (uu____12910) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (FStar_Pervasives_Native.fst result_arg))
in (

let rest1 = (desugar_args env rest)
in (

let uu____12989 = (

let is_decrease = (fun uu____13027 -> (match (uu____13027) with
| (t1, uu____13037) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____13047; FStar_Syntax_Syntax.vars = uu____13048}, (uu____13049)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.decreases_lid)
end
| uu____13080 -> begin
false
end)
end))
in (FStar_All.pipe_right rest1 (FStar_List.partition is_decrease)))
in (match (uu____12989) with
| (dec, rest2) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun uu____13194 -> (match (uu____13194) with
| (t1, uu____13204) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____13213, ((arg, uu____13215))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| uu____13244 -> begin
(failwith "impos")
end)
end))))
in (

let no_additional_args = (

let is_empty = (fun l -> (match (l) with
| [] -> begin
true
end
| uu____13261 -> begin
false
end))
in ((((is_empty decreases_clause) && (is_empty rest2)) && (is_empty cattributes)) && (is_empty universes1)))
in (

let uu____13272 = (no_additional_args && (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid))
in (match (uu____13272) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end
| uu____13275 -> begin
(

let uu____13276 = (no_additional_args && (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid))
in (match (uu____13276) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end
| uu____13279 -> begin
(

let flags1 = (

let uu____13283 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Lemma_lid)
in (match (uu____13283) with
| true -> begin
(FStar_Syntax_Syntax.LEMMA)::[]
end
| uu____13286 -> begin
(

let uu____13287 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid)
in (match (uu____13287) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____13290 -> begin
(

let uu____13291 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_ML_lid)
in (match (uu____13291) with
| true -> begin
(FStar_Syntax_Syntax.MLEFFECT)::[]
end
| uu____13294 -> begin
(

let uu____13295 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid)
in (match (uu____13295) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____13298 -> begin
[]
end))
end))
end))
end))
in (

let flags2 = (FStar_List.append flags1 cattributes)
in (

let rest3 = (

let uu____13313 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Lemma_lid)
in (match (uu____13313) with
| true -> begin
(match (rest2) with
| (req)::(ens)::((pat, aq))::[] -> begin
(

let pat1 = (match (pat.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
(

let nil = (FStar_Syntax_Syntax.mk_Tm_uinst pat ((FStar_Syntax_Syntax.U_zero)::[]))
in (

let pattern = (

let uu____13402 = (FStar_Ident.set_lid_range FStar_Parser_Const.pattern_lid pat.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar uu____13402 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.mk_Tm_app nil ((((pattern), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::[]) FStar_Pervasives_Native.None pat.FStar_Syntax_Syntax.pos)))
end
| uu____13417 -> begin
pat
end)
in (

let uu____13418 = (

let uu____13429 = (

let uu____13440 = (

let uu____13449 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat1), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) FStar_Pervasives_Native.None pat1.FStar_Syntax_Syntax.pos)
in ((uu____13449), (aq)))
in (uu____13440)::[])
in (ens)::uu____13429)
in (req)::uu____13418))
end
| uu____13490 -> begin
rest2
end)
end
| uu____13501 -> begin
rest2
end))
in (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = universes1; FStar_Syntax_Syntax.effect_name = eff; FStar_Syntax_Syntax.result_typ = result_typ; FStar_Syntax_Syntax.effect_args = rest3; FStar_Syntax_Syntax.flags = (FStar_List.append flags2 decreases_clause)}))))
end))
end))))
end))))
end)))
end)));
)
end))))))))))
and desugar_formula : env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env f -> (

let connective = (fun s -> (match (s) with
| "/\\" -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.and_lid)
end
| "\\/" -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.or_lid)
end
| "==>" -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.imp_lid)
end
| "<==>" -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.iff_lid)
end
| "~" -> begin
FStar_Pervasives_Native.Some (FStar_Parser_Const.not_lid)
end
| uu____13514 -> begin
FStar_Pervasives_Native.None
end))
in (

let mk1 = (fun t -> (FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let uu___129_13535 = t
in {FStar_Syntax_Syntax.n = uu___129_13535.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___129_13535.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let uu___130_13577 = b
in {FStar_Parser_AST.b = uu___130_13577.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___130_13577.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___130_13577.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env1 pats1 -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (

let uu____13640 = (desugar_term env1 e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) uu____13640)))))) pats1))
in (match (tk) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____13653 = (FStar_Syntax_DsEnv.push_bv env a)
in (match (uu____13653) with
| (env1, a1) -> begin
(

let a2 = (

let uu___131_13663 = a1
in {FStar_Syntax_Syntax.ppname = uu___131_13663.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___131_13663.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats1 = (desugar_pats env1 pats)
in (

let body1 = (desugar_formula env1 body)
in (

let body2 = (match (pats1) with
| [] -> begin
body1
end
| uu____13685 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_meta (((body1), (FStar_Syntax_Syntax.Meta_pattern (pats1))))))
end)
in (

let body3 = (

let uu____13699 = (

let uu____13702 = (

let uu____13703 = (FStar_Syntax_Syntax.mk_binder a2)
in (uu____13703)::[])
in (no_annot_abs uu____13702 body2))
in (FStar_All.pipe_left setpos uu____13699))
in (

let uu____13708 = (

let uu____13709 = (

let uu____13724 = (

let uu____13725 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Syntax_Syntax.fvar uu____13725 (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None))
in (

let uu____13726 = (

let uu____13729 = (FStar_Syntax_Syntax.as_arg body3)
in (uu____13729)::[])
in ((uu____13724), (uu____13726))))
in FStar_Syntax_Syntax.Tm_app (uu____13709))
in (FStar_All.pipe_left mk1 uu____13708)))))))
end))
end
| uu____13734 -> begin
(failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body1 = (

let uu____13814 = (q ((rest), (pats), (body)))
in (

let uu____13821 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term uu____13814 uu____13821 FStar_Parser_AST.Formula)))
in (

let uu____13822 = (q (((b)::[]), ([]), (body1)))
in (FStar_Parser_AST.mk_term uu____13822 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| uu____13831 -> begin
(failwith "impossible")
end))
in (

let uu____13834 = (

let uu____13835 = (unparen f)
in uu____13835.FStar_Parser_AST.tm)
in (match (uu____13834) with
| FStar_Parser_AST.Labeled (f1, l, p) -> begin
(

let f2 = (desugar_formula env f1)
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((f2), (FStar_Syntax_Syntax.Meta_labeled (((l), (f2.FStar_Syntax_Syntax.pos), (p)))))))))
end
| FStar_Parser_AST.QForall ([], uu____13842, uu____13843) -> begin
(failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QExists ([], uu____13854, uu____13855) -> begin
(failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____13886 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env uu____13886)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____13922 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env uu____13922)))
end
| FStar_Parser_AST.QForall ((b)::[], pats, body) -> begin
(desugar_quant FStar_Parser_Const.forall_lid b pats body)
end
| FStar_Parser_AST.QExists ((b)::[], pats, body) -> begin
(desugar_quant FStar_Parser_Const.exists_lid b pats body)
end
| FStar_Parser_AST.Paren (f1) -> begin
(failwith "impossible")
end
| uu____13965 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list) = (fun env bs -> (

let uu____13970 = (FStar_List.fold_left (fun uu____14006 b -> (match (uu____14006) with
| (env1, out) -> begin
(

let tk = (desugar_binder env1 (

let uu___132_14058 = b
in {FStar_Parser_AST.b = uu___132_14058.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___132_14058.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___132_14058.FStar_Parser_AST.aqual}))
in (match (tk) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____14075 = (FStar_Syntax_DsEnv.push_bv env1 a)
in (match (uu____14075) with
| (env2, a1) -> begin
(

let a2 = (

let uu___133_14095 = a1
in {FStar_Syntax_Syntax.ppname = uu___133_14095.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___133_14095.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in ((env2), ((((a2), ((trans_aqual b.FStar_Parser_AST.aqual))))::out)))
end))
end
| uu____14112 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedBinder), ("Unexpected binder")) b.FStar_Parser_AST.brange)
end))
end)) ((env), ([])) bs)
in (match (uu____13970) with
| (env1, tpars) -> begin
((env1), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.TAnnotated (x, t) -> begin
(

let uu____14199 = (desugar_typ env t)
in ((FStar_Pervasives_Native.Some (x)), (uu____14199)))
end
| FStar_Parser_AST.Annotated (x, t) -> begin
(

let uu____14204 = (desugar_typ env t)
in ((FStar_Pervasives_Native.Some (x)), (uu____14204)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____14208 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) FStar_Pervasives_Native.None x.FStar_Ident.idRange)
in ((FStar_Pervasives_Native.Some (x)), (uu____14208)))
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____14216 = (desugar_typ env t)
in ((FStar_Pervasives_Native.None), (uu____14216)))
end
| FStar_Parser_AST.Variable (x) -> begin
((FStar_Pervasives_Native.Some (x)), (FStar_Syntax_Syntax.tun))
end))


let mk_data_discriminators : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_DsEnv.env  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun quals env datas -> (

let quals1 = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___96_14255 -> (match (uu___96_14255) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____14256 -> begin
false
end))))
in (

let quals2 = (fun q -> (

let uu____14269 = ((

let uu____14272 = (FStar_Syntax_DsEnv.iface env)
in (not (uu____14272))) || (FStar_Syntax_DsEnv.admitted_iface env))
in (match (uu____14269) with
| true -> begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals1)
end
| uu____14275 -> begin
(FStar_List.append q quals1)
end)))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (

let uu____14286 = (FStar_Ident.range_of_lid disc_name)
in (

let uu____14287 = (quals2 ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((disc_name), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = uu____14286; FStar_Syntax_Syntax.sigquals = uu____14287; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))))))))


let mk_indexed_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  FStar_Syntax_DsEnv.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq env lid fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let uu____14328 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____14358 -> (match (uu____14358) with
| (x, uu____14366) -> begin
(

let uu____14367 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____14367) with
| (field_name, uu____14375) -> begin
(

let only_decl = (((

let uu____14379 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____14379)) || (Prims.op_disEquality fvq FStar_Syntax_Syntax.Data_ctor)) || (

let uu____14381 = (

let uu____14382 = (FStar_Syntax_DsEnv.current_module env)
in uu____14382.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____14381)))
in (

let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____14398 = (FStar_List.filter (fun uu___97_14402 -> (match (uu___97_14402) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____14403 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____14398)
end
| uu____14404 -> begin
q
end))
in (

let quals1 = (

let iquals1 = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___98_14416 -> (match (uu___98_14416) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____14417 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals1)))
in (

let decl = (

let uu____14419 = (FStar_Ident.range_of_lid field_name)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = uu____14419; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____14424 -> begin
(

let dd = (

let uu____14426 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____14426) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.delta_equational)
end
| uu____14429 -> begin
FStar_Syntax_Syntax.delta_equational
end))
in (

let lb = (

let uu____14431 = (

let uu____14436 = (FStar_Syntax_Syntax.lid_as_fv field_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____14436))
in {FStar_Syntax_Syntax.lbname = uu____14431; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbattrs = []; FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange})
in (

let impl = (

let uu____14440 = (

let uu____14441 = (

let uu____14448 = (

let uu____14451 = (

let uu____14452 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____14452 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____14451)::[])
in ((((false), ((lb)::[]))), (uu____14448)))
in FStar_Syntax_Syntax.Sig_let (uu____14441))
in {FStar_Syntax_Syntax.sigel = uu____14440; FStar_Syntax_Syntax.sigrng = p; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____14471 -> begin
(decl)::(impl)::[]
end))))
end))))))
end))
end))))
in (FStar_All.pipe_right uu____14328 FStar_List.flatten))))


let mk_data_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____14502, t, uu____14504, n1, uu____14506) when (

let uu____14511 = (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
in (not (uu____14511))) -> begin
(

let uu____14512 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____14512) with
| (formals, uu____14528) -> begin
(match (formals) with
| [] -> begin
[]
end
| uu____14551 -> begin
(

let filter_records = (fun uu___99_14565 -> (match (uu___99_14565) with
| FStar_Syntax_Syntax.RecordConstructor (uu____14568, fns) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| uu____14580 -> begin
FStar_Pervasives_Native.None
end))
in (

let fv_qual = (

let uu____14582 = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals filter_records)
in (match (uu____14582) with
| FStar_Pervasives_Native.None -> begin
FStar_Syntax_Syntax.Data_ctor
end
| FStar_Pervasives_Native.Some (q) -> begin
q
end))
in (

let iquals1 = (match ((FStar_List.contains FStar_Syntax_Syntax.Abstract iquals)) with
| true -> begin
(FStar_Syntax_Syntax.Private)::iquals
end
| uu____14591 -> begin
iquals
end)
in (

let uu____14592 = (FStar_Util.first_N n1 formals)
in (match (uu____14592) with
| (uu____14615, rest) -> begin
(mk_indexed_projector_names iquals1 fv_qual env lid rest)
end)))))
end)
end))
end
| uu____14641 -> begin
[]
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (

let dd = (

let uu____14707 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____14707) with
| true -> begin
(

let uu____14710 = (FStar_Syntax_Util.incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (uu____14710))
end
| uu____14711 -> begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end))
in (

let lb = (

let uu____14713 = (

let uu____14718 = (FStar_Syntax_Syntax.lid_as_fv lid dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____14718))
in (

let uu____14719 = (

let uu____14722 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars uu____14722))
in (

let uu____14725 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = uu____14713; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____14719; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____14725; FStar_Syntax_Syntax.lbattrs = []; FStar_Syntax_Syntax.lbpos = rng})))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (lids))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))


let rec desugar_tycon : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.decl  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d quals tcs -> (

let rng = d.FStar_Parser_AST.drange
in (

let tycon_id = (fun uu___100_14782 -> (match (uu___100_14782) with
| FStar_Parser_AST.TyconAbstract (id1, uu____14784, uu____14785) -> begin
id1
end
| FStar_Parser_AST.TyconAbbrev (id1, uu____14795, uu____14796, uu____14797) -> begin
id1
end
| FStar_Parser_AST.TyconRecord (id1, uu____14807, uu____14808, uu____14809) -> begin
id1
end
| FStar_Parser_AST.TyconVariant (id1, uu____14839, uu____14840, uu____14841) -> begin
id1
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (x, uu____14885) -> begin
(

let uu____14886 = (

let uu____14887 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____14887))
in (FStar_Parser_AST.mk_term uu____14886 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| FStar_Parser_AST.Variable (x) -> begin
(

let uu____14889 = (

let uu____14890 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____14890))
in (FStar_Parser_AST.mk_term uu____14889 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| FStar_Parser_AST.TAnnotated (a, uu____14892) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar (a)) a.FStar_Ident.idRange FStar_Parser_AST.Type_level)
end
| FStar_Parser_AST.TVariable (a) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar (a)) a.FStar_Ident.idRange FStar_Parser_AST.Type_level)
end
| FStar_Parser_AST.NoName (t) -> begin
t
end))
in (

let tot = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.effect_Tot_lid)) rng FStar_Parser_AST.Expr)
in (

let with_constructor_effect = (fun t -> (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((tot), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level))
in (

let apply_binders = (fun t binders -> (

let imp_of_aqual = (fun b -> (match (b.FStar_Parser_AST.aqual) with
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit) -> begin
FStar_Parser_AST.Hash
end
| uu____14923 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (

let uu____14929 = (

let uu____14930 = (

let uu____14937 = (binder_to_term b)
in ((out), (uu____14937), ((imp_of_aqual b))))
in FStar_Parser_AST.App (uu____14930))
in (FStar_Parser_AST.mk_term uu____14929 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun uu___101_14949 -> (match (uu___101_14949) with
| FStar_Parser_AST.TyconRecord (id1, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id1.FStar_Ident.idText)), (id1.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun uu____15005 -> (match (uu____15005) with
| (x, t, uu____15016) -> begin
(

let uu____15021 = (

let uu____15022 = (

let uu____15027 = (FStar_Syntax_Util.mangle_field_name x)
in ((uu____15027), (t)))
in FStar_Parser_AST.Annotated (uu____15022))
in (FStar_Parser_AST.mk_binder uu____15021 x.FStar_Ident.idRange FStar_Parser_AST.Expr FStar_Pervasives_Native.None))
end)) fields)
in (

let result = (

let uu____15029 = (

let uu____15030 = (

let uu____15031 = (FStar_Ident.lid_of_ids ((id1)::[]))
in FStar_Parser_AST.Var (uu____15031))
in (FStar_Parser_AST.mk_term uu____15030 id1.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____15029 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id1.FStar_Ident.idRange FStar_Parser_AST.Type_level)
in (

let uu____15035 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____15062 -> (match (uu____15062) with
| (x, uu____15072, uu____15073) -> begin
(FStar_Syntax_Util.unmangle_field_name x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id1), (parms), (kopt), ((((constrName), (FStar_Pervasives_Native.Some (constrTyp)), (FStar_Pervasives_Native.None), (false)))::[])))), (uu____15035)))))))
end
| uu____15126 -> begin
(failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals1 _env mutuals uu___102_15165 -> (match (uu___102_15165) with
| FStar_Parser_AST.TyconAbstract (id1, binders, kopt) -> begin
(

let uu____15189 = (typars_of_binders _env binders)
in (match (uu____15189) with
| (_env', typars) -> begin
(

let k = (match (kopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Syntax_Util.ktype
end
| FStar_Pervasives_Native.Some (k) -> begin
(desugar_term _env' k)
end)
in (

let tconstr = (

let uu____15235 = (

let uu____15236 = (

let uu____15237 = (FStar_Ident.lid_of_ids ((id1)::[]))
in FStar_Parser_AST.Var (uu____15237))
in (FStar_Parser_AST.mk_term uu____15236 id1.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____15235 binders))
in (

let qlid = (FStar_Syntax_DsEnv.qualify _env id1)
in (

let typars1 = (FStar_Syntax_Subst.close_binders typars)
in (

let k1 = (FStar_Syntax_Subst.close typars1 k)
in (

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((qlid), ([]), (typars1), (k1), (mutuals), ([]))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (

let _env1 = (FStar_Syntax_DsEnv.push_top_level_rec_binding _env id1 FStar_Syntax_Syntax.delta_constant)
in (

let _env2 = (FStar_Syntax_DsEnv.push_top_level_rec_binding _env' id1 FStar_Syntax_Syntax.delta_constant)
in ((_env1), (_env2), (se), (tconstr))))))))))
end))
end
| uu____15250 -> begin
(failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env1 bs -> (

let uu____15298 = (FStar_List.fold_left (fun uu____15338 uu____15339 -> (match (((uu____15338), (uu____15339))) with
| ((env2, tps), (x, imp)) -> begin
(

let uu____15430 = (FStar_Syntax_DsEnv.push_bv env2 x.FStar_Syntax_Syntax.ppname)
in (match (uu____15430) with
| (env3, y) -> begin
((env3), ((((y), (imp)))::tps))
end))
end)) ((env1), ([])) bs)
in (match (uu____15298) with
| (env2, bs1) -> begin
((env2), ((FStar_List.rev bs1)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id1, bs, kopt))::[] -> begin
(

let kopt1 = (match (kopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____15543 = (tm_type_z id1.FStar_Ident.idRange)
in FStar_Pervasives_Native.Some (uu____15543))
end
| uu____15544 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id1), (bs), (kopt1)))
in (

let uu____15552 = (desugar_abstract_tc quals env [] tc)
in (match (uu____15552) with
| (uu____15565, uu____15566, se, uu____15568) -> begin
(

let se1 = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, uu____15571, typars, k, [], []) -> begin
(

let quals1 = se.FStar_Syntax_Syntax.sigquals
in (

let quals2 = (match ((FStar_List.contains FStar_Syntax_Syntax.Assumption quals1)) with
| true -> begin
quals1
end
| uu____15586 -> begin
((

let uu____15588 = (

let uu____15589 = (FStar_Options.ml_ish ())
in (not (uu____15589)))
in (match (uu____15588) with
| true -> begin
(

let uu____15590 = (

let uu____15595 = (

let uu____15596 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Adding an implicit \'assume new\' qualifier on %s" uu____15596))
in ((FStar_Errors.Warning_AddImplicitAssumeNewQualifier), (uu____15595)))
in (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng uu____15590))
end
| uu____15597 -> begin
()
end));
(FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals1;
)
end)
in (

let t = (match (typars) with
| [] -> begin
k
end
| uu____15603 -> begin
(

let uu____15604 = (

let uu____15611 = (

let uu____15612 = (

let uu____15625 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (uu____15625)))
in FStar_Syntax_Syntax.Tm_arrow (uu____15612))
in (FStar_Syntax_Syntax.mk uu____15611))
in (uu____15604 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
end)
in (

let uu___134_15629 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t))); FStar_Syntax_Syntax.sigrng = uu___134_15629.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = uu___134_15629.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___134_15629.FStar_Syntax_Syntax.sigattrs}))))
end
| uu____15632 -> begin
(failwith "Impossible")
end)
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se1)
in (

let env2 = (

let uu____15635 = (FStar_Syntax_DsEnv.qualify env1 id1)
in (FStar_Syntax_DsEnv.push_doc env1 uu____15635 d.FStar_Parser_AST.doc))
in ((env2), ((se1)::[])))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id1, binders, kopt, t))::[] -> begin
(

let uu____15650 = (typars_of_binders env binders)
in (match (uu____15650) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____15686 = (FStar_Util.for_some (fun uu___103_15688 -> (match (uu___103_15688) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| uu____15689 -> begin
false
end)) quals)
in (match (uu____15686) with
| true -> begin
FStar_Syntax_Syntax.teff
end
| uu____15690 -> begin
FStar_Syntax_Util.ktype
end))
end
| FStar_Pervasives_Native.Some (k) -> begin
(desugar_term env' k)
end)
in (

let t0 = t
in (

let qlid = (FStar_Syntax_DsEnv.qualify env id1)
in (

let se = (

let uu____15695 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Effect))
in (match (uu____15695) with
| true -> begin
(

let uu____15698 = (

let uu____15705 = (

let uu____15706 = (unparen t)
in uu____15706.FStar_Parser_AST.tm)
in (match (uu____15705) with
| FStar_Parser_AST.Construct (head1, args) -> begin
(

let uu____15727 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____15757))::args_rev -> begin
(

let uu____15769 = (

let uu____15770 = (unparen last_arg)
in uu____15770.FStar_Parser_AST.tm)
in (match (uu____15769) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____15798 -> begin
(([]), (args))
end))
end
| uu____15807 -> begin
(([]), (args))
end)
in (match (uu____15727) with
| (cattributes, args1) -> begin
(

let uu____15846 = (desugar_attributes env cattributes)
in (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((head1), (args1)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (uu____15846)))
end))
end
| uu____15857 -> begin
((t), ([]))
end))
in (match (uu____15698) with
| (t1, cattributes) -> begin
(

let c = (desugar_comp t1.FStar_Parser_AST.range env' t1)
in (

let typars1 = (FStar_Syntax_Subst.close_binders typars)
in (

let c1 = (FStar_Syntax_Subst.close_comp typars1 c)
in (

let quals1 = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___104_15879 -> (match (uu___104_15879) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| uu____15880 -> begin
true
end))))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((qlid), ([]), (typars1), (c1), ((FStar_List.append cattributes (FStar_Syntax_Util.comp_flags c1))))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))))
end))
end
| uu____15885 -> begin
(

let t1 = (desugar_typ env' t)
in (mk_typ_abbrev qlid [] typars k t1 ((qlid)::[]) quals rng))
end))
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se)
in (

let env2 = (FStar_Syntax_DsEnv.push_doc env1 qlid d.FStar_Parser_AST.doc)
in ((env2), ((se)::[]))))))))
end))
end
| (FStar_Parser_AST.TyconRecord (uu____15891))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let uu____15915 = (tycon_record_as_variant trec)
in (match (uu____15915) with
| (t, fs) -> begin
(

let uu____15932 = (

let uu____15935 = (

let uu____15936 = (

let uu____15945 = (

let uu____15948 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Ident.ids_of_lid uu____15948))
in ((uu____15945), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____15936))
in (uu____15935)::quals)
in (desugar_tycon env d uu____15932 ((t)::[])))
end)))
end
| (uu____15953)::uu____15954 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals1 et tc -> (

let uu____16121 = et
in (match (uu____16121) with
| (env1, tcs1) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (uu____16346) -> begin
(

let trec = tc
in (

let uu____16370 = (tycon_record_as_variant trec)
in (match (uu____16370) with
| (t, fs) -> begin
(

let uu____16429 = (

let uu____16432 = (

let uu____16433 = (

let uu____16442 = (

let uu____16445 = (FStar_Syntax_DsEnv.current_module env1)
in (FStar_Ident.ids_of_lid uu____16445))
in ((uu____16442), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____16433))
in (uu____16432)::quals1)
in (collect_tcs uu____16429 ((env1), (tcs1)) t))
end)))
end
| FStar_Parser_AST.TyconVariant (id1, binders, kopt, constructors) -> begin
(

let uu____16532 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id1), (binders), (kopt)))))
in (match (uu____16532) with
| (env2, uu____16592, se, tconstr) -> begin
((env2), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals1))))::tcs1))
end))
end
| FStar_Parser_AST.TyconAbbrev (id1, binders, kopt, t) -> begin
(

let uu____16741 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id1), (binders), (kopt)))))
in (match (uu____16741) with
| (env2, uu____16801, se, tconstr) -> begin
((env2), ((FStar_Util.Inr (((se), (binders), (t), (quals1))))::tcs1))
end))
end
| uu____16926 -> begin
(failwith "Unrecognized mutual type definition")
end)
end)))
in (

let uu____16973 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (uu____16973) with
| (env1, tcs1) -> begin
(

let tcs2 = (FStar_List.rev tcs1)
in (

let docs_tps_sigelts = (FStar_All.pipe_right tcs2 (FStar_List.collect (fun uu___106_17484 -> (match (uu___106_17484) with
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (id1, uvs, tpars, k, uu____17551, uu____17552); FStar_Syntax_Syntax.sigrng = uu____17553; FStar_Syntax_Syntax.sigquals = uu____17554; FStar_Syntax_Syntax.sigmeta = uu____17555; FStar_Syntax_Syntax.sigattrs = uu____17556}, binders, t, quals1) -> begin
(

let t1 = (

let uu____17617 = (typars_of_binders env1 binders)
in (match (uu____17617) with
| (env2, tpars1) -> begin
(

let uu____17648 = (push_tparams env2 tpars1)
in (match (uu____17648) with
| (env_tps, tpars2) -> begin
(

let t1 = (desugar_typ env_tps t)
in (

let tpars3 = (FStar_Syntax_Subst.close_binders tpars2)
in (FStar_Syntax_Subst.close tpars3 t1)))
end))
end))
in (

let uu____17681 = (

let uu____17702 = (mk_typ_abbrev id1 uvs tpars k t1 ((id1)::[]) quals1 rng)
in ((((id1), (d.FStar_Parser_AST.doc))), ([]), (uu____17702)))
in (uu____17681)::[]))
end
| FStar_Util.Inl ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs1, tpars, k, mutuals1, uu____17770); FStar_Syntax_Syntax.sigrng = uu____17771; FStar_Syntax_Syntax.sigquals = tname_quals; FStar_Syntax_Syntax.sigmeta = uu____17773; FStar_Syntax_Syntax.sigattrs = uu____17774}, constrs, tconstr, quals1) -> begin
(

let mk_tot = (fun t -> (

let tot1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((tot1), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)))
in (

let tycon = ((tname), (tpars), (k))
in (

let uu____17872 = (push_tparams env1 tpars)
in (match (uu____17872) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun uu____17949 -> (match (uu____17949) with
| (x, uu____17963) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let tot_tconstr = (mk_tot tconstr)
in (

let uu____17971 = (

let uu____18000 = (FStar_All.pipe_right constrs (FStar_List.map (fun uu____18114 -> (match (uu____18114) with
| (id1, topt, doc1, of_notation) -> begin
(

let t = (match (of_notation) with
| true -> begin
(match (topt) with
| FStar_Pervasives_Native.Some (t) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level FStar_Pervasives_Native.None))::[]), (tot_tconstr)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end
| FStar_Pervasives_Native.None -> begin
tconstr
end)
end
| uu____18167 -> begin
(match (topt) with
| FStar_Pervasives_Native.None -> begin
(failwith "Impossible")
end
| FStar_Pervasives_Native.Some (t) -> begin
t
end)
end)
in (

let t1 = (

let uu____18170 = (close env_tps t)
in (desugar_term env_tps uu____18170))
in (

let name = (FStar_Syntax_DsEnv.qualify env1 id1)
in (

let quals2 = (FStar_All.pipe_right tname_quals (FStar_List.collect (fun uu___105_18181 -> (match (uu___105_18181) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| uu____18193 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (

let uu____18201 = (

let uu____18222 = (

let uu____18223 = (

let uu____18224 = (

let uu____18239 = (

let uu____18242 = (

let uu____18245 = (FStar_All.pipe_right t1 FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total uu____18245))
in (FStar_Syntax_Util.arrow data_tpars uu____18242))
in ((name), (univs1), (uu____18239), (tname), (ntps), (mutuals1)))
in FStar_Syntax_Syntax.Sig_datacon (uu____18224))
in {FStar_Syntax_Syntax.sigel = uu____18223; FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in ((((name), (doc1))), (tps), (uu____18222)))
in ((name), (uu____18201))))))))
end))))
in (FStar_All.pipe_left FStar_List.split uu____18000))
in (match (uu____17971) with
| (constrNames, constrs1) -> begin
(((((tname), (d.FStar_Parser_AST.doc))), ([]), ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs1), (tpars), (k), (mutuals1), (constrNames))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = tname_quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))::constrs1
end))))
end))))
end
| uu____18484 -> begin
(failwith "impossible")
end))))
in (

let name_docs = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.map (fun uu____18616 -> (match (uu____18616) with
| (name_doc, uu____18644, uu____18645) -> begin
name_doc
end))))
in (

let sigelts = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.map (fun uu____18725 -> (match (uu____18725) with
| (uu____18746, uu____18747, se) -> begin
se
end))))
in (

let uu____18777 = (

let uu____18784 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle sigelts quals uu____18784 rng))
in (match (uu____18777) with
| (bundle, abbrevs) -> begin
(

let env2 = (FStar_Syntax_DsEnv.push_sigelt env0 bundle)
in (

let env3 = (FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env2 abbrevs)
in (

let data_ops = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.collect (fun uu____18850 -> (match (uu____18850) with
| (uu____18873, tps, se) -> begin
(mk_data_projector_names quals env3 se)
end))))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, uu____18924, tps, k, uu____18927, constrs) when ((FStar_List.length constrs) > (Prims.parse_int "1")) -> begin
(

let quals1 = se.FStar_Syntax_Syntax.sigquals
in (

let quals2 = (match ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals1)) with
| true -> begin
(FStar_Syntax_Syntax.Private)::quals1
end
| uu____18945 -> begin
quals1
end)
in (mk_data_discriminators quals2 env3 constrs)))
end
| uu____18946 -> begin
[]
end))))
in (

let ops = (FStar_List.append discs data_ops)
in (

let env4 = (FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env3 ops)
in (

let env5 = (FStar_List.fold_left (fun acc uu____18963 -> (match (uu____18963) with
| (lid, doc1) -> begin
(FStar_Syntax_DsEnv.push_doc env4 lid doc1)
end)) env4 name_docs)
in ((env5), ((FStar_List.append ((bundle)::[]) (FStar_List.append abbrevs ops)))))))))))
end))))))
end)))))
end
| [] -> begin
(failwith "impossible")
end)))))))))))


let desugar_binders : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.binder Prims.list) = (fun env binders -> (

let uu____19002 = (FStar_List.fold_left (fun uu____19025 b -> (match (uu____19025) with
| (env1, binders1) -> begin
(

let uu____19045 = (desugar_binder env1 b)
in (match (uu____19045) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____19062 = (as_binder env1 b.FStar_Parser_AST.aqual ((FStar_Pervasives_Native.Some (a)), (k)))
in (match (uu____19062) with
| (binder, env2) -> begin
((env2), ((binder)::binders1))
end))
end
| uu____19079 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_MissingNameInBinder), ("Missing name in binder")) b.FStar_Parser_AST.brange)
end))
end)) ((env), ([])) binders)
in (match (uu____19002) with
| (env1, binders1) -> begin
((env1), ((FStar_List.rev binders1)))
end)))


let push_reflect_effect : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lid  ->  FStar_Range.range  ->  FStar_Syntax_DsEnv.env = (fun env quals effect_name range -> (

let uu____19132 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___107_19137 -> (match (uu___107_19137) with
| FStar_Syntax_Syntax.Reflectable (uu____19138) -> begin
true
end
| uu____19139 -> begin
false
end))))
in (match (uu____19132) with
| true -> begin
(

let monad_env = (FStar_Syntax_DsEnv.enter_monad_scope env effect_name.FStar_Ident.ident)
in (

let reflect_lid = (

let uu____19142 = (FStar_Ident.id_of_text "reflect")
in (FStar_All.pipe_right uu____19142 (FStar_Syntax_DsEnv.qualify monad_env)))
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (effect_name))::[]
in (

let refl_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = range; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (FStar_Syntax_DsEnv.push_sigelt env refl_decl)))))
end
| uu____19149 -> begin
env
end)))


let get_fail_attr : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  Prims.int Prims.list FStar_Pervasives_Native.option = (fun warn at1 -> (

let uu____19168 = (FStar_Syntax_Util.head_and_args at1)
in (match (uu____19168) with
| (hd1, args) -> begin
(

let uu____19209 = (

let uu____19222 = (

let uu____19223 = (FStar_Syntax_Subst.compress hd1)
in uu____19223.FStar_Syntax_Syntax.n)
in ((uu____19222), (args)))
in (match (uu____19209) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((a1, uu____19240))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_errs_attr) -> begin
(

let uu____19265 = (

let uu____19270 = (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_int)
in (FStar_Syntax_Embeddings.unembed uu____19270 a1))
in (FStar_Util.map_opt uu____19265 (FStar_List.map FStar_BigInt.to_int_fs)))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____19282) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_errs_attr) -> begin
((match (warn) with
| true -> begin
(FStar_Errors.log_issue at1.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_UnappliedFail), ("Found ill-applied fail_errs, did you forget to use parentheses?")))
end
| uu____19300 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end
| uu____19303 -> begin
(

let uu____19316 = (FStar_Syntax_Util.attr_eq at1 FStar_Syntax_Util.fail_attr)
in (match (uu____19316) with
| true -> begin
FStar_Pervasives_Native.Some ([])
end
| uu____19323 -> begin
FStar_Pervasives_Native.None
end))
end))
end)))


let rec desugar_effect : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.term Prims.list  ->  (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_typ eff_decls attrs -> (

let env0 = env
in (

let monad_env = (FStar_Syntax_DsEnv.enter_monad_scope env eff_name)
in (

let uu____19464 = (desugar_binders monad_env eff_binders)
in (match (uu____19464) with
| (env1, binders) -> begin
(

let eff_t = (desugar_term env1 eff_typ)
in (

let for_free = (

let uu____19485 = (

let uu____19486 = (

let uu____19493 = (FStar_Syntax_Util.arrow_formals eff_t)
in (FStar_Pervasives_Native.fst uu____19493))
in (FStar_List.length uu____19486))
in (Prims.op_Equality uu____19485 (Prims.parse_int "1")))
in (

let mandatory_members = (

let rr_members = ("repr")::("return")::("bind")::[]
in (match (for_free) with
| true -> begin
rr_members
end
| uu____19530 -> begin
(FStar_List.append rr_members (("return_wp")::("bind_wp")::("if_then_else")::("ite_wp")::("stronger")::("close_wp")::("assert_p")::("assume_p")::("null_wp")::("trivial")::[]))
end))
in (

let name_of_eff_decl = (fun decl -> (match (decl.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____19537, ((FStar_Parser_AST.TyconAbbrev (name, uu____19539, uu____19540, uu____19541), uu____19542))::[]) -> begin
(FStar_Ident.text_of_id name)
end
| uu____19575 -> begin
(failwith "Malformed effect member declaration.")
end))
in (

let uu____19576 = (FStar_List.partition (fun decl -> (

let uu____19588 = (name_of_eff_decl decl)
in (FStar_List.mem uu____19588 mandatory_members))) eff_decls)
in (match (uu____19576) with
| (mandatory_members_decls, actions) -> begin
(

let uu____19605 = (FStar_All.pipe_right mandatory_members_decls (FStar_List.fold_left (fun uu____19634 decl -> (match (uu____19634) with
| (env2, out) -> begin
(

let uu____19654 = (desugar_decl env2 decl)
in (match (uu____19654) with
| (env3, ses) -> begin
(

let uu____19667 = (

let uu____19670 = (FStar_List.hd ses)
in (uu____19670)::out)
in ((env3), (uu____19667)))
end))
end)) ((env1), ([]))))
in (match (uu____19605) with
| (env2, decls) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (

let actions_docs = (FStar_All.pipe_right actions (FStar_List.map (fun d1 -> (match (d1.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____19738, ((FStar_Parser_AST.TyconAbbrev (name, action_params, uu____19741, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (uu____19742, ((def, uu____19744))::((cps_type, uu____19746))::[]); FStar_Parser_AST.range = uu____19747; FStar_Parser_AST.level = uu____19748}), doc1))::[]) when (not (for_free)) -> begin
(

let uu____19800 = (desugar_binders env2 action_params)
in (match (uu____19800) with
| (env3, action_params1) -> begin
(

let action_params2 = (FStar_Syntax_Subst.close_binders action_params1)
in (

let uu____19820 = (

let uu____19821 = (FStar_Syntax_DsEnv.qualify env3 name)
in (

let uu____19822 = (

let uu____19823 = (desugar_term env3 def)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____19823))
in (

let uu____19828 = (

let uu____19829 = (desugar_typ env3 cps_type)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____19829))
in {FStar_Syntax_Syntax.action_name = uu____19821; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = action_params2; FStar_Syntax_Syntax.action_defn = uu____19822; FStar_Syntax_Syntax.action_typ = uu____19828})))
in ((uu____19820), (doc1))))
end))
end
| FStar_Parser_AST.Tycon (uu____19836, ((FStar_Parser_AST.TyconAbbrev (name, action_params, uu____19839, defn), doc1))::[]) when for_free -> begin
(

let uu____19874 = (desugar_binders env2 action_params)
in (match (uu____19874) with
| (env3, action_params1) -> begin
(

let action_params2 = (FStar_Syntax_Subst.close_binders action_params1)
in (

let uu____19894 = (

let uu____19895 = (FStar_Syntax_DsEnv.qualify env3 name)
in (

let uu____19896 = (

let uu____19897 = (desugar_term env3 defn)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____19897))
in {FStar_Syntax_Syntax.action_name = uu____19895; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = action_params2; FStar_Syntax_Syntax.action_defn = uu____19896; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
in ((uu____19894), (doc1))))
end))
end
| uu____19904 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_MalformedActionDeclaration), ("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).")) d1.FStar_Parser_AST.drange)
end))))
in (

let actions1 = (FStar_List.map FStar_Pervasives_Native.fst actions_docs)
in (

let eff_t1 = (FStar_Syntax_Subst.close binders1 eff_t)
in (

let lookup1 = (fun s -> (

let l = (

let uu____19936 = (FStar_Ident.mk_ident ((s), (d.FStar_Parser_AST.drange)))
in (FStar_Syntax_DsEnv.qualify env2 uu____19936))
in (

let uu____19937 = (

let uu____19938 = (FStar_Syntax_DsEnv.fail_or env2 (FStar_Syntax_DsEnv.try_lookup_definition env2) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders1) uu____19938))
in (([]), (uu____19937)))))
in (

let mname = (FStar_Syntax_DsEnv.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.collect (trans_qual d.FStar_Parser_AST.drange (FStar_Pervasives_Native.Some (mname))) quals)
in (

let se = (match (for_free) with
| true -> begin
(

let dummy_tscheme = (

let uu____19955 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (([]), (uu____19955)))
in (

let uu____19962 = (

let uu____19963 = (

let uu____19964 = (

let uu____19965 = (lookup1 "repr")
in (FStar_Pervasives_Native.snd uu____19965))
in (

let uu____19974 = (lookup1 "return")
in (

let uu____19975 = (lookup1 "bind")
in (

let uu____19976 = (FStar_List.map (desugar_term env2) attrs)
in {FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = eff_t1; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = uu____19964; FStar_Syntax_Syntax.return_repr = uu____19974; FStar_Syntax_Syntax.bind_repr = uu____19975; FStar_Syntax_Syntax.actions = actions1; FStar_Syntax_Syntax.eff_attrs = uu____19976}))))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____19963))
in {FStar_Syntax_Syntax.sigel = uu____19962; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qualifiers; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))
end
| uu____19979 -> begin
(

let rr = (FStar_Util.for_some (fun uu___108_19982 -> (match (uu___108_19982) with
| FStar_Syntax_Syntax.Reifiable -> begin
true
end
| FStar_Syntax_Syntax.Reflectable (uu____19983) -> begin
true
end
| uu____19984 -> begin
false
end)) qualifiers)
in (

let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in (

let uu____19994 = (

let uu____19995 = (

let uu____19996 = (lookup1 "return_wp")
in (

let uu____19997 = (lookup1 "bind_wp")
in (

let uu____19998 = (lookup1 "if_then_else")
in (

let uu____19999 = (lookup1 "ite_wp")
in (

let uu____20000 = (lookup1 "stronger")
in (

let uu____20001 = (lookup1 "close_wp")
in (

let uu____20002 = (lookup1 "assert_p")
in (

let uu____20003 = (lookup1 "assume_p")
in (

let uu____20004 = (lookup1 "null_wp")
in (

let uu____20005 = (lookup1 "trivial")
in (

let uu____20006 = (match (rr) with
| true -> begin
(

let uu____20007 = (lookup1 "repr")
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____20007))
end
| uu____20022 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let uu____20023 = (match (rr) with
| true -> begin
(lookup1 "return")
end
| uu____20024 -> begin
un_ts
end)
in (

let uu____20025 = (match (rr) with
| true -> begin
(lookup1 "bind")
end
| uu____20026 -> begin
un_ts
end)
in (

let uu____20027 = (FStar_List.map (desugar_term env2) attrs)
in {FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = eff_t1; FStar_Syntax_Syntax.ret_wp = uu____19996; FStar_Syntax_Syntax.bind_wp = uu____19997; FStar_Syntax_Syntax.if_then_else = uu____19998; FStar_Syntax_Syntax.ite_wp = uu____19999; FStar_Syntax_Syntax.stronger = uu____20000; FStar_Syntax_Syntax.close_wp = uu____20001; FStar_Syntax_Syntax.assert_p = uu____20002; FStar_Syntax_Syntax.assume_p = uu____20003; FStar_Syntax_Syntax.null_wp = uu____20004; FStar_Syntax_Syntax.trivial = uu____20005; FStar_Syntax_Syntax.repr = uu____20006; FStar_Syntax_Syntax.return_repr = uu____20023; FStar_Syntax_Syntax.bind_repr = uu____20025; FStar_Syntax_Syntax.actions = actions1; FStar_Syntax_Syntax.eff_attrs = uu____20027}))))))))))))))
in FStar_Syntax_Syntax.Sig_new_effect (uu____19995))
in {FStar_Syntax_Syntax.sigel = uu____19994; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qualifiers; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))
end)
in (

let env3 = (FStar_Syntax_DsEnv.push_sigelt env0 se)
in (

let env4 = (FStar_Syntax_DsEnv.push_doc env3 mname d.FStar_Parser_AST.doc)
in (

let env5 = (FStar_All.pipe_right actions_docs (FStar_List.fold_left (fun env5 uu____20053 -> (match (uu____20053) with
| (a, doc1) -> begin
(

let env6 = (

let uu____20067 = (FStar_Syntax_Util.action_as_lb mname a a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_DsEnv.push_sigelt env5 uu____20067))
in (FStar_Syntax_DsEnv.push_doc env6 a.FStar_Syntax_Syntax.action_name doc1))
end)) env4))
in (

let env6 = (push_reflect_effect env5 qualifiers mname d.FStar_Parser_AST.drange)
in (

let env7 = (FStar_Syntax_DsEnv.push_doc env6 mname d.FStar_Parser_AST.doc)
in ((env7), ((se)::[])))))))))))))))
end))
end))))))
end)))))
and desugar_redefine_effect : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.decl  ->  (FStar_Ident.lident FStar_Pervasives_Native.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier Prims.list)  ->  FStar_Parser_AST.qualifier Prims.list  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d trans_qual1 quals eff_name eff_binders defn -> (

let env0 = env
in (

let env1 = (FStar_Syntax_DsEnv.enter_monad_scope env eff_name)
in (

let uu____20093 = (desugar_binders env1 eff_binders)
in (match (uu____20093) with
| (env2, binders) -> begin
(

let uu____20112 = (

let uu____20131 = (head_and_args defn)
in (match (uu____20131) with
| (head1, args) -> begin
(

let lid = (match (head1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
l
end
| uu____20176 -> begin
(

let uu____20177 = (

let uu____20182 = (

let uu____20183 = (

let uu____20184 = (FStar_Parser_AST.term_to_string head1)
in (Prims.strcat uu____20184 " not found"))
in (Prims.strcat "Effect " uu____20183))
in ((FStar_Errors.Fatal_EffectNotFound), (uu____20182)))
in (FStar_Errors.raise_error uu____20177 d.FStar_Parser_AST.drange))
end)
in (

let ed = (FStar_Syntax_DsEnv.fail_or env2 (FStar_Syntax_DsEnv.try_lookup_effect_defn env2) lid)
in (

let uu____20186 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____20216))::args_rev -> begin
(

let uu____20228 = (

let uu____20229 = (unparen last_arg)
in uu____20229.FStar_Parser_AST.tm)
in (match (uu____20228) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____20257 -> begin
(([]), (args))
end))
end
| uu____20266 -> begin
(([]), (args))
end)
in (match (uu____20186) with
| (cattributes, args1) -> begin
(

let uu____20317 = (desugar_args env2 args1)
in (

let uu____20326 = (desugar_attributes env2 cattributes)
in ((lid), (ed), (uu____20317), (uu____20326))))
end))))
end))
in (match (uu____20112) with
| (ed_lid, ed, args, cattributes) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in ((match ((Prims.op_disEquality (FStar_List.length args) (FStar_List.length ed.FStar_Syntax_Syntax.binders))) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ArgumentLengthMismatch), ("Unexpected number of arguments to effect constructor")) defn.FStar_Parser_AST.range)
end
| uu____20381 -> begin
()
end);
(

let uu____20382 = (FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit)
in (match (uu____20382) with
| (ed_binders, uu____20396, ed_binders_opening) -> begin
(

let sub1 = (fun uu____20409 -> (match (uu____20409) with
| (us, x) -> begin
(

let x1 = (

let uu____20423 = (FStar_Syntax_Subst.shift_subst (FStar_List.length us) ed_binders_opening)
in (FStar_Syntax_Subst.subst uu____20423 x))
in (

let s = (FStar_Syntax_Util.subst_of_list ed_binders args)
in (

let uu____20427 = (

let uu____20428 = (FStar_Syntax_Subst.subst s x1)
in ((us), (uu____20428)))
in (FStar_Syntax_Subst.close_tscheme binders1 uu____20427))))
end))
in (

let mname = (FStar_Syntax_DsEnv.qualify env0 eff_name)
in (

let ed1 = (

let uu____20433 = (

let uu____20434 = (sub1 (([]), (ed.FStar_Syntax_Syntax.signature)))
in (FStar_Pervasives_Native.snd uu____20434))
in (

let uu____20445 = (sub1 ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____20446 = (sub1 ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____20447 = (sub1 ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____20448 = (sub1 ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____20449 = (sub1 ed.FStar_Syntax_Syntax.stronger)
in (

let uu____20450 = (sub1 ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____20451 = (sub1 ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____20452 = (sub1 ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____20453 = (sub1 ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____20454 = (sub1 ed.FStar_Syntax_Syntax.trivial)
in (

let uu____20455 = (

let uu____20456 = (sub1 (([]), (ed.FStar_Syntax_Syntax.repr)))
in (FStar_Pervasives_Native.snd uu____20456))
in (

let uu____20467 = (sub1 ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____20468 = (sub1 ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____20469 = (FStar_List.map (fun action -> (

let uu____20477 = (FStar_Syntax_DsEnv.qualify env2 action.FStar_Syntax_Syntax.action_unqualified_name)
in (

let uu____20478 = (

let uu____20479 = (sub1 (([]), (action.FStar_Syntax_Syntax.action_defn)))
in (FStar_Pervasives_Native.snd uu____20479))
in (

let uu____20490 = (

let uu____20491 = (sub1 (([]), (action.FStar_Syntax_Syntax.action_typ)))
in (FStar_Pervasives_Native.snd uu____20491))
in {FStar_Syntax_Syntax.action_name = uu____20477; FStar_Syntax_Syntax.action_unqualified_name = action.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = action.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = uu____20478; FStar_Syntax_Syntax.action_typ = uu____20490})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = cattributes; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = ed.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = uu____20433; FStar_Syntax_Syntax.ret_wp = uu____20445; FStar_Syntax_Syntax.bind_wp = uu____20446; FStar_Syntax_Syntax.if_then_else = uu____20447; FStar_Syntax_Syntax.ite_wp = uu____20448; FStar_Syntax_Syntax.stronger = uu____20449; FStar_Syntax_Syntax.close_wp = uu____20450; FStar_Syntax_Syntax.assert_p = uu____20451; FStar_Syntax_Syntax.assume_p = uu____20452; FStar_Syntax_Syntax.null_wp = uu____20453; FStar_Syntax_Syntax.trivial = uu____20454; FStar_Syntax_Syntax.repr = uu____20455; FStar_Syntax_Syntax.return_repr = uu____20467; FStar_Syntax_Syntax.bind_repr = uu____20468; FStar_Syntax_Syntax.actions = uu____20469; FStar_Syntax_Syntax.eff_attrs = ed.FStar_Syntax_Syntax.eff_attrs})))))))))))))))
in (

let se = (

let for_free = (

let uu____20504 = (

let uu____20505 = (

let uu____20512 = (FStar_Syntax_Util.arrow_formals ed1.FStar_Syntax_Syntax.signature)
in (FStar_Pervasives_Native.fst uu____20512))
in (FStar_List.length uu____20505))
in (Prims.op_Equality uu____20504 (Prims.parse_int "1")))
in (

let uu____20541 = (

let uu____20544 = (trans_qual1 (FStar_Pervasives_Native.Some (mname)))
in (FStar_List.collect uu____20544 quals))
in {FStar_Syntax_Syntax.sigel = (match (for_free) with
| true -> begin
FStar_Syntax_Syntax.Sig_new_effect_for_free (ed1)
end
| uu____20551 -> begin
FStar_Syntax_Syntax.Sig_new_effect (ed1)
end); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = uu____20541; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))
in (

let monad_env = env2
in (

let env3 = (FStar_Syntax_DsEnv.push_sigelt env0 se)
in (

let env4 = (FStar_Syntax_DsEnv.push_doc env3 ed_lid d.FStar_Parser_AST.doc)
in (

let env5 = (FStar_All.pipe_right ed1.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun env5 a -> (

let doc1 = (FStar_Syntax_DsEnv.try_lookup_doc env5 a.FStar_Syntax_Syntax.action_name)
in (

let env6 = (

let uu____20568 = (FStar_Syntax_Util.action_as_lb mname a a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_DsEnv.push_sigelt env5 uu____20568))
in (FStar_Syntax_DsEnv.push_doc env6 a.FStar_Syntax_Syntax.action_name doc1)))) env4))
in (

let env6 = (

let uu____20570 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____20570) with
| true -> begin
(

let reflect_lid = (

let uu____20574 = (FStar_Ident.id_of_text "reflect")
in (FStar_All.pipe_right uu____20574 (FStar_Syntax_DsEnv.qualify monad_env)))
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]
in (

let refl_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (FStar_Syntax_DsEnv.push_sigelt env5 refl_decl))))
end
| uu____20581 -> begin
env5
end))
in (

let env7 = (FStar_Syntax_DsEnv.push_doc env6 mname d.FStar_Parser_AST.doc)
in ((env7), ((se)::[]))))))))))))
end));
))
end))
end)))))
and mk_comment_attr : FStar_Parser_AST.decl  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun d -> (

let uu____20586 = (match (d.FStar_Parser_AST.doc) with
| FStar_Pervasives_Native.None -> begin
((""), ([]))
end
| FStar_Pervasives_Native.Some (fsdoc) -> begin
fsdoc
end)
in (match (uu____20586) with
| (text, kv) -> begin
(

let summary = (match ((FStar_List.assoc "summary" kv)) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (s) -> begin
(Prims.strcat "  " (Prims.strcat s "\n"))
end)
in (

let pp = (match ((FStar_List.assoc "type" kv)) with
| FStar_Pervasives_Native.Some (uu____20637) -> begin
(

let uu____20638 = (

let uu____20639 = (FStar_Parser_ToDocument.signature_to_document d)
in (FStar_Pprint.pretty_string 0.950000 (Prims.parse_int "80") uu____20639))
in (Prims.strcat "\n  " uu____20638))
end
| uu____20640 -> begin
""
end)
in (

let other = (FStar_List.filter_map (fun uu____20653 -> (match (uu____20653) with
| (k, v1) -> begin
(match (((Prims.op_disEquality k "summary") && (Prims.op_disEquality k "type"))) with
| true -> begin
FStar_Pervasives_Native.Some ((Prims.strcat k (Prims.strcat ": " v1)))
end
| uu____20664 -> begin
FStar_Pervasives_Native.None
end)
end)) kv)
in (

let other1 = (match ((Prims.op_disEquality other [])) with
| true -> begin
(Prims.strcat (FStar_String.concat "\n" other) "\n")
end
| uu____20668 -> begin
""
end)
in (

let str = (Prims.strcat summary (Prims.strcat pp (Prims.strcat other1 text)))
in (

let fv = (

let uu____20671 = (FStar_Ident.lid_of_str "FStar.Pervasives.Comment")
in (FStar_Syntax_Syntax.fvar uu____20671 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))
in (

let arg = (FStar_Syntax_Util.exp_string str)
in (

let uu____20673 = (

let uu____20682 = (FStar_Syntax_Syntax.as_arg arg)
in (uu____20682)::[])
in (FStar_Syntax_Util.mk_app fv uu____20673)))))))))
end)))
and desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (

let uu____20689 = (desugar_decl_noattrs env d)
in (match (uu____20689) with
| (env1, sigelts) -> begin
(

let attrs = d.FStar_Parser_AST.attrs
in (

let attrs1 = (FStar_List.map (desugar_term env1) attrs)
in (

let attrs2 = (

let uu____20709 = (mk_comment_attr d)
in (uu____20709)::attrs1)
in (

let uu____20714 = (FStar_List.mapi (fun i sigelt -> (match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
(

let uu___135_20722 = sigelt
in {FStar_Syntax_Syntax.sigel = uu___135_20722.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___135_20722.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___135_20722.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___135_20722.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = attrs2})
end
| uu____20723 -> begin
(

let uu___136_20724 = sigelt
in (

let uu____20725 = (FStar_List.filter (fun at1 -> (

let uu____20731 = (get_fail_attr false at1)
in (FStar_Option.isNone uu____20731))) attrs2)
in {FStar_Syntax_Syntax.sigel = uu___136_20724.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___136_20724.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___136_20724.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___136_20724.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu____20725}))
end)) sigelts)
in ((env1), (uu____20714))))))
end)))
and desugar_decl_noattrs : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (

let trans_qual1 = (trans_qual d.FStar_Parser_AST.drange)
in (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_pragma ((trans_pragma p)); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in ((match ((Prims.op_Equality p FStar_Parser_AST.LightOff)) with
| true -> begin
(FStar_Options.set_ml_ish ())
end
| uu____20766 -> begin
()
end);
((env), ((se)::[]));
))
end
| FStar_Parser_AST.Fsdoc (uu____20769) -> begin
((env), ([]))
end
| FStar_Parser_AST.TopLevelModule (id1) -> begin
((env), ([]))
end
| FStar_Parser_AST.Open (lid) -> begin
(

let env1 = (FStar_Syntax_DsEnv.push_namespace env lid)
in ((env1), ([])))
end
| FStar_Parser_AST.Include (lid) -> begin
(

let env1 = (FStar_Syntax_DsEnv.push_include env lid)
in ((env1), ([])))
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(

let uu____20785 = (FStar_Syntax_DsEnv.push_module_abbrev env x l)
in ((uu____20785), ([])))
end
| FStar_Parser_AST.Tycon (is_effect, tcs) -> begin
(

let quals = (match (is_effect) with
| true -> begin
(FStar_Parser_AST.Effect_qual)::d.FStar_Parser_AST.quals
end
| uu____20811 -> begin
d.FStar_Parser_AST.quals
end)
in (

let tcs1 = (FStar_List.map (fun uu____20824 -> (match (uu____20824) with
| (x, uu____20832) -> begin
x
end)) tcs)
in (

let uu____20837 = (FStar_List.collect (trans_qual1 FStar_Pervasives_Native.None) quals)
in (desugar_tycon env d uu____20837 tcs1))))
end
| FStar_Parser_AST.TopLevelLet (isrec, lets) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let expand_toplevel_pattern = ((Prims.op_Equality isrec FStar_Parser_AST.NoLetQualifier) && (match (lets) with
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatOp (uu____20859); FStar_Parser_AST.prange = uu____20860}, uu____20861))::[] -> begin
false
end
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____20870); FStar_Parser_AST.prange = uu____20871}, uu____20872))::[] -> begin
false
end
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____20887); FStar_Parser_AST.prange = uu____20888}, uu____20889); FStar_Parser_AST.prange = uu____20890}, uu____20891))::[] -> begin
false
end
| ((p, uu____20919))::[] -> begin
(

let uu____20928 = (is_app_pattern p)
in (not (uu____20928)))
end
| uu____20929 -> begin
false
end))
in (match ((not (expand_toplevel_pattern))) with
| true -> begin
(

let lets1 = (FStar_List.map (fun x -> ((FStar_Pervasives_Native.None), (x))) lets)
in (

let as_inner_let = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets1), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)
in (

let uu____21002 = (desugar_term_maybe_top true env as_inner_let)
in (match (uu____21002) with
| (ds_lets, aq) -> begin
((check_no_aq aq);
(

let uu____21014 = (

let uu____21015 = (FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets)
in uu____21015.FStar_Syntax_Syntax.n)
in (match (uu____21014) with
| FStar_Syntax_Syntax.Tm_let (lbs, uu____21023) -> begin
(

let fvs = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals1 = (match (quals) with
| (uu____21056)::uu____21057 -> begin
(FStar_List.collect (trans_qual1 FStar_Pervasives_Native.None) quals)
end
| uu____21060 -> begin
(FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.collect (fun uu___109_21075 -> (match (uu___109_21075) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (uu____21078); FStar_Syntax_Syntax.lbunivs = uu____21079; FStar_Syntax_Syntax.lbtyp = uu____21080; FStar_Syntax_Syntax.lbeff = uu____21081; FStar_Syntax_Syntax.lbdef = uu____21082; FStar_Syntax_Syntax.lbattrs = uu____21083; FStar_Syntax_Syntax.lbpos = uu____21084} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____21096; FStar_Syntax_Syntax.lbtyp = uu____21097; FStar_Syntax_Syntax.lbeff = uu____21098; FStar_Syntax_Syntax.lbdef = uu____21099; FStar_Syntax_Syntax.lbattrs = uu____21100; FStar_Syntax_Syntax.lbpos = uu____21101} -> begin
(FStar_Syntax_DsEnv.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let lbs1 = (

let uu____21119 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____21119) with
| true -> begin
(

let uu____21128 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu___137_21142 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let uu___138_21144 = fv
in {FStar_Syntax_Syntax.fv_name = uu___138_21144.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = uu___138_21144.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = uu___137_21142.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___137_21142.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___137_21142.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___137_21142.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___137_21142.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___137_21142.FStar_Syntax_Syntax.lbpos})))))
in (((FStar_Pervasives_Native.fst lbs)), (uu____21128)))
end
| uu____21149 -> begin
lbs
end))
in (

let names1 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (

let attrs = (FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs)
in (

let s = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((lbs1), (names1))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = attrs}
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env s)
in (

let env2 = (FStar_List.fold_left (fun env2 id1 -> (FStar_Syntax_DsEnv.push_doc env2 id1 d.FStar_Parser_AST.doc)) env1 names1)
in ((env2), ((s)::[]))))))))))
end
| uu____21179 -> begin
(failwith "Desugaring a let did not produce a let")
end));
)
end))))
end
| uu____21184 -> begin
(

let uu____21185 = (match (lets) with
| ((pat, body))::[] -> begin
((pat), (body))
end
| uu____21204 -> begin
(failwith "expand_toplevel_pattern should only allow single definition lets")
end)
in (match (uu____21185) with
| (pat, body) -> begin
(

let fresh_toplevel_name = (FStar_Ident.gen FStar_Range.dummyRange)
in (

let fresh_pat = (

let var_pat = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((fresh_toplevel_name), (FStar_Pervasives_Native.None)))) FStar_Range.dummyRange)
in (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat1, ty) -> begin
(

let uu___139_21240 = pat1
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed (((var_pat), (ty))); FStar_Parser_AST.prange = uu___139_21240.FStar_Parser_AST.prange})
end
| uu____21247 -> begin
var_pat
end))
in (

let main_let = (desugar_decl env (

let uu___140_21254 = d
in {FStar_Parser_AST.d = FStar_Parser_AST.TopLevelLet (((isrec), ((((fresh_pat), (body)))::[]))); FStar_Parser_AST.drange = uu___140_21254.FStar_Parser_AST.drange; FStar_Parser_AST.doc = uu___140_21254.FStar_Parser_AST.doc; FStar_Parser_AST.quals = (FStar_Parser_AST.Private)::d.FStar_Parser_AST.quals; FStar_Parser_AST.attrs = uu___140_21254.FStar_Parser_AST.attrs}))
in (

let build_projection = (fun uu____21290 id1 -> (match (uu____21290) with
| (env1, ses) -> begin
(

let main = (

let uu____21311 = (

let uu____21312 = (FStar_Ident.lid_of_ids ((fresh_toplevel_name)::[]))
in FStar_Parser_AST.Var (uu____21312))
in (FStar_Parser_AST.mk_term uu____21311 FStar_Range.dummyRange FStar_Parser_AST.Expr))
in (

let lid = (FStar_Ident.lid_of_ids ((id1)::[]))
in (

let projectee = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (lid)) FStar_Range.dummyRange FStar_Parser_AST.Expr)
in (

let body1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Match (((main), ((((pat), (FStar_Pervasives_Native.None), (projectee)))::[])))) FStar_Range.dummyRange FStar_Parser_AST.Expr)
in (

let bv_pat = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((id1), (FStar_Pervasives_Native.None)))) FStar_Range.dummyRange)
in (

let id_decl = (FStar_Parser_AST.mk_decl (FStar_Parser_AST.TopLevelLet (((FStar_Parser_AST.NoLetQualifier), ((((bv_pat), (body1)))::[])))) FStar_Range.dummyRange [])
in (

let uu____21362 = (desugar_decl env1 id_decl)
in (match (uu____21362) with
| (env2, ses') -> begin
((env2), ((FStar_List.append ses ses')))
end))))))))
end))
in (

let bvs = (

let uu____21380 = (gather_pattern_bound_vars pat)
in (FStar_All.pipe_right uu____21380 FStar_Util.set_elements))
in (FStar_List.fold_left build_projection main_let bvs))))))
end))
end)))
end
| FStar_Parser_AST.Main (t) -> begin
(

let e = (desugar_term env t)
in (

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_main (e); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in ((env), ((se)::[]))))
end
| FStar_Parser_AST.Assume (id1, t) -> begin
(

let f = (desugar_formula env t)
in (

let lid = (FStar_Syntax_DsEnv.qualify env id1)
in (

let env1 = (FStar_Syntax_DsEnv.push_doc env lid d.FStar_Parser_AST.doc)
in ((env1), (({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_assume (((lid), ([]), (f))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})::[])))))
end
| FStar_Parser_AST.Val (id1, t) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let t1 = (

let uu____21411 = (close_fun env t)
in (desugar_term env uu____21411))
in (

let quals1 = (

let uu____21415 = ((FStar_Syntax_DsEnv.iface env) && (FStar_Syntax_DsEnv.admitted_iface env))
in (match (uu____21415) with
| true -> begin
(FStar_Parser_AST.Assumption)::quals
end
| uu____21418 -> begin
quals
end))
in (

let lid = (FStar_Syntax_DsEnv.qualify env id1)
in (

let se = (

let uu____21421 = (FStar_List.collect (trans_qual1 FStar_Pervasives_Native.None) quals1)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), ([]), (t1))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = uu____21421; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se)
in (

let env2 = (FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc)
in ((env2), ((se)::[])))))))))
end
| FStar_Parser_AST.Exception (id1, FStar_Pervasives_Native.None) -> begin
(

let uu____21433 = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_lid env) FStar_Parser_Const.exn_lid)
in (match (uu____21433) with
| (t, uu____21447) -> begin
(

let l = (FStar_Syntax_DsEnv.qualify env id1)
in (

let qual = (FStar_Syntax_Syntax.ExceptionConstructor)::[]
in (

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((l), ([]), (t), (FStar_Parser_Const.exn_lid), ((Prims.parse_int "0")), ((FStar_Parser_Const.exn_lid)::[]))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qual; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (

let se' = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((se)::[]), ((l)::[]))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qual; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se')
in (

let env2 = (FStar_Syntax_DsEnv.push_doc env1 l d.FStar_Parser_AST.doc)
in (

let data_ops = (mk_data_projector_names [] env2 se)
in (

let discs = (mk_data_discriminators [] env2 ((l)::[]))
in (

let env3 = (FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env2 (FStar_List.append discs data_ops))
in ((env3), ((FStar_List.append ((se')::discs) data_ops))))))))))))
end))
end
| FStar_Parser_AST.Exception (id1, FStar_Pervasives_Native.Some (term)) -> begin
(

let t = (desugar_term env term)
in (

let t1 = (

let uu____21481 = (

let uu____21488 = (FStar_Syntax_Syntax.null_binder t)
in (uu____21488)::[])
in (

let uu____21489 = (

let uu____21492 = (

let uu____21493 = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_lid env) FStar_Parser_Const.exn_lid)
in (FStar_Pervasives_Native.fst uu____21493))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____21492))
in (FStar_Syntax_Util.arrow uu____21481 uu____21489)))
in (

let l = (FStar_Syntax_DsEnv.qualify env id1)
in (

let qual = (FStar_Syntax_Syntax.ExceptionConstructor)::[]
in (

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((l), ([]), (t1), (FStar_Parser_Const.exn_lid), ((Prims.parse_int "0")), ((FStar_Parser_Const.exn_lid)::[]))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qual; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (

let se' = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((se)::[]), ((l)::[]))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qual; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se')
in (

let env2 = (FStar_Syntax_DsEnv.push_doc env1 l d.FStar_Parser_AST.doc)
in (

let data_ops = (mk_data_projector_names [] env2 se)
in (

let discs = (mk_data_discriminators [] env2 ((l)::[]))
in (

let env3 = (FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env2 (FStar_List.append discs data_ops))
in ((env3), ((FStar_List.append ((se')::discs) data_ops))))))))))))))
end
| FStar_Parser_AST.NewEffect (FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (desugar_redefine_effect env d trans_qual1 quals eff_name eff_binders defn))
end
| FStar_Parser_AST.NewEffect (FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_typ, eff_decls)) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let attrs = d.FStar_Parser_AST.attrs
in (desugar_effect env d quals eff_name eff_binders eff_typ eff_decls attrs)))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(

let lookup1 = (fun l1 -> (

let uu____21558 = (FStar_Syntax_DsEnv.try_lookup_effect_name env l1)
in (match (uu____21558) with
| FStar_Pervasives_Native.None -> begin
(

let uu____21561 = (

let uu____21566 = (

let uu____21567 = (

let uu____21568 = (FStar_Syntax_Print.lid_to_string l1)
in (Prims.strcat uu____21568 " not found"))
in (Prims.strcat "Effect name " uu____21567))
in ((FStar_Errors.Fatal_EffectNotFound), (uu____21566)))
in (FStar_Errors.raise_error uu____21561 d.FStar_Parser_AST.drange))
end
| FStar_Pervasives_Native.Some (l2) -> begin
l2
end)))
in (

let src = (lookup1 l.FStar_Parser_AST.msource)
in (

let dst = (lookup1 l.FStar_Parser_AST.mdest)
in (

let uu____21572 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(

let uu____21614 = (

let uu____21623 = (

let uu____21630 = (desugar_term env t)
in (([]), (uu____21630)))
in FStar_Pervasives_Native.Some (uu____21623))
in ((uu____21614), (FStar_Pervasives_Native.None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(

let uu____21663 = (

let uu____21672 = (

let uu____21679 = (desugar_term env wp)
in (([]), (uu____21679)))
in FStar_Pervasives_Native.Some (uu____21672))
in (

let uu____21688 = (

let uu____21697 = (

let uu____21704 = (desugar_term env t)
in (([]), (uu____21704)))
in FStar_Pervasives_Native.Some (uu____21697))
in ((uu____21663), (uu____21688))))
end
| FStar_Parser_AST.LiftForFree (t) -> begin
(

let uu____21730 = (

let uu____21739 = (

let uu____21746 = (desugar_term env t)
in (([]), (uu____21746)))
in FStar_Pervasives_Native.Some (uu____21739))
in ((FStar_Pervasives_Native.None), (uu____21730)))
end)
in (match (uu____21572) with
| (lift_wp, lift) -> begin
(

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect ({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift}); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in ((env), ((se)::[])))
end)))))
end
| FStar_Parser_AST.Splice (ids, t) -> begin
(

let t1 = (desugar_term env t)
in (

let se = (

let uu____21826 = (

let uu____21827 = (

let uu____21834 = (FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids)
in ((uu____21834), (t1)))
in FStar_Syntax_Syntax.Sig_splice (uu____21827))
in {FStar_Syntax_Syntax.sigel = uu____21826; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se)
in ((env1), ((se)::[])))))
end)))


let desugar_decls : env_t  ->  FStar_Parser_AST.decl Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env decls -> (

let uu____21862 = (FStar_List.fold_left (fun uu____21882 d -> (match (uu____21882) with
| (env1, sigelts) -> begin
(

let uu____21902 = (desugar_decl env1 d)
in (match (uu____21902) with
| (env2, se) -> begin
((env2), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls)
in (match (uu____21862) with
| (env1, sigelts) -> begin
(

let rec forward = (fun acc uu___111_21947 -> (match (uu___111_21947) with
| (se1)::(se2)::sigelts1 -> begin
(match (((se1.FStar_Syntax_Syntax.sigel), (se2.FStar_Syntax_Syntax.sigel))) with
| (FStar_Syntax_Syntax.Sig_declare_typ (uu____21961), FStar_Syntax_Syntax.Sig_let (uu____21962)) -> begin
(

let uu____21975 = (

let uu____21978 = (

let uu___141_21979 = se2
in (

let uu____21980 = (

let uu____21983 = (FStar_List.filter (fun uu___110_21997 -> (match (uu___110_21997) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____22001; FStar_Syntax_Syntax.vars = uu____22002}, uu____22003); FStar_Syntax_Syntax.pos = uu____22004; FStar_Syntax_Syntax.vars = uu____22005} when (

let uu____22028 = (

let uu____22029 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____22029))
in (Prims.op_Equality uu____22028 "FStar.Pervasives.Comment")) -> begin
true
end
| uu____22030 -> begin
false
end)) se1.FStar_Syntax_Syntax.sigattrs)
in (FStar_List.append uu____21983 se2.FStar_Syntax_Syntax.sigattrs))
in {FStar_Syntax_Syntax.sigel = uu___141_21979.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___141_21979.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___141_21979.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___141_21979.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu____21980}))
in (uu____21978)::(se1)::acc)
in (forward uu____21975 sigelts1))
end
| uu____22035 -> begin
(forward ((se1)::acc) ((se2)::sigelts1))
end)
end
| sigelts1 -> begin
(FStar_List.rev_append acc sigelts1)
end))
in (

let uu____22043 = (forward [] sigelts)
in ((env1), (uu____22043))))
end)))


let open_prims_all : (FStar_Parser_AST.decoration Prims.list  ->  FStar_Parser_AST.decl) Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Parser_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Parser_Const.all_lid)) FStar_Range.dummyRange))::[]


let generalize_annotated_univs : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun s -> (

let bs_univnames = (fun bs -> (

let uu____22085 = (

let uu____22092 = (FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name)
in (FStar_List.fold_left (fun uvs uu____22109 -> (match (uu____22109) with
| ({FStar_Syntax_Syntax.ppname = uu____22118; FStar_Syntax_Syntax.index = uu____22119; FStar_Syntax_Syntax.sort = t}, uu____22121) -> begin
(

let uu____22124 = (FStar_Syntax_Free.univnames t)
in (FStar_Util.set_union uvs uu____22124))
end)) uu____22092))
in (FStar_All.pipe_right bs uu____22085)))
in (

let empty_set = (FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name)
in (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____22132) -> begin
(failwith "Impossible: collect_annotated_universes: bare data/type constructor")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____22149) -> begin
(failwith "Impossible: collect_annotated_universes: bare data/type constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (sigs, lids) -> begin
(

let uvs = (

let uu____22177 = (FStar_All.pipe_right sigs (FStar_List.fold_left (fun uvs se -> (

let se_univs = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____22198, uu____22199, bs, t, uu____22202, uu____22203) -> begin
(

let uu____22212 = (bs_univnames bs)
in (

let uu____22215 = (FStar_Syntax_Free.univnames t)
in (FStar_Util.set_union uu____22212 uu____22215)))
end
| FStar_Syntax_Syntax.Sig_datacon (uu____22218, uu____22219, t, uu____22221, uu____22222, uu____22223) -> begin
(FStar_Syntax_Free.univnames t)
end
| uu____22228 -> begin
(failwith "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt")
end)
in (FStar_Util.set_union uvs se_univs))) empty_set))
in (FStar_All.pipe_right uu____22177 FStar_Util.set_elements))
in (

let usubst = (FStar_Syntax_Subst.univ_var_closing uvs)
in (

let uu___142_22238 = s
in (

let uu____22239 = (

let uu____22240 = (

let uu____22249 = (FStar_All.pipe_right sigs (FStar_List.map (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____22267, bs, t, lids1, lids2) -> begin
(

let uu___143_22280 = se
in (

let uu____22281 = (

let uu____22282 = (

let uu____22299 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let uu____22300 = (

let uu____22301 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst uu____22301 t))
in ((lid), (uvs), (uu____22299), (uu____22300), (lids1), (lids2))))
in FStar_Syntax_Syntax.Sig_inductive_typ (uu____22282))
in {FStar_Syntax_Syntax.sigel = uu____22281; FStar_Syntax_Syntax.sigrng = uu___143_22280.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___143_22280.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___143_22280.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___143_22280.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____22315, t, tlid, n1, lids1) -> begin
(

let uu___144_22324 = se
in (

let uu____22325 = (

let uu____22326 = (

let uu____22341 = (FStar_Syntax_Subst.subst usubst t)
in ((lid), (uvs), (uu____22341), (tlid), (n1), (lids1)))
in FStar_Syntax_Syntax.Sig_datacon (uu____22326))
in {FStar_Syntax_Syntax.sigel = uu____22325; FStar_Syntax_Syntax.sigrng = uu___144_22324.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___144_22324.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___144_22324.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___144_22324.FStar_Syntax_Syntax.sigattrs}))
end
| uu____22346 -> begin
(failwith "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt")
end))))
in ((uu____22249), (lids)))
in FStar_Syntax_Syntax.Sig_bundle (uu____22240))
in {FStar_Syntax_Syntax.sigel = uu____22239; FStar_Syntax_Syntax.sigrng = uu___142_22238.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___142_22238.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___142_22238.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___142_22238.FStar_Syntax_Syntax.sigattrs}))))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____22352, t) -> begin
(

let uvs = (

let uu____22357 = (FStar_Syntax_Free.univnames t)
in (FStar_All.pipe_right uu____22357 FStar_Util.set_elements))
in (

let uu___145_22364 = s
in (

let uu____22365 = (

let uu____22366 = (

let uu____22373 = (FStar_Syntax_Subst.close_univ_vars uvs t)
in ((lid), (uvs), (uu____22373)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____22366))
in {FStar_Syntax_Syntax.sigel = uu____22365; FStar_Syntax_Syntax.sigrng = uu___145_22364.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___145_22364.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___145_22364.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___145_22364.FStar_Syntax_Syntax.sigattrs})))
end
| FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) -> begin
(

let lb_univnames = (fun lb -> (

let uu____22403 = (FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____22406 = (match (lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, e, uu____22413) -> begin
(

let uvs1 = (bs_univnames bs)
in (

let uvs2 = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (uu____22442, (FStar_Util.Inl (t), uu____22444), uu____22445) -> begin
(FStar_Syntax_Free.univnames t)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____22492, (FStar_Util.Inr (c), uu____22494), uu____22495) -> begin
(FStar_Syntax_Free.univnames_comp c)
end
| uu____22542 -> begin
empty_set
end)
in (FStar_Util.set_union uvs1 uvs2)))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____22543, (FStar_Util.Inl (t), uu____22545), uu____22546) -> begin
(FStar_Syntax_Free.univnames t)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____22593, (FStar_Util.Inr (c), uu____22595), uu____22596) -> begin
(FStar_Syntax_Free.univnames_comp c)
end
| uu____22643 -> begin
empty_set
end)
in (FStar_Util.set_union uu____22403 uu____22406))))
in (

let all_lb_univs = (

let uu____22647 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun uvs lb -> (

let uu____22663 = (lb_univnames lb)
in (FStar_Util.set_union uvs uu____22663))) empty_set))
in (FStar_All.pipe_right uu____22647 FStar_Util.set_elements))
in (

let usubst = (FStar_Syntax_Subst.univ_var_closing all_lb_univs)
in (

let uu___146_22673 = s
in (

let uu____22674 = (

let uu____22675 = (

let uu____22682 = (

let uu____22689 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu___147_22701 = lb
in (

let uu____22702 = (FStar_Syntax_Subst.subst usubst lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____22705 = (FStar_Syntax_Subst.subst usubst lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___147_22701.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = all_lb_univs; FStar_Syntax_Syntax.lbtyp = uu____22702; FStar_Syntax_Syntax.lbeff = uu___147_22701.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____22705; FStar_Syntax_Syntax.lbattrs = uu___147_22701.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___147_22701.FStar_Syntax_Syntax.lbpos}))))))
in ((b), (uu____22689)))
in ((uu____22682), (lids)))
in FStar_Syntax_Syntax.Sig_let (uu____22675))
in {FStar_Syntax_Syntax.sigel = uu____22674; FStar_Syntax_Syntax.sigrng = uu___146_22673.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___146_22673.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___146_22673.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___146_22673.FStar_Syntax_Syntax.sigattrs})))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____22719, fml) -> begin
(

let uvs = (

let uu____22724 = (FStar_Syntax_Free.univnames fml)
in (FStar_All.pipe_right uu____22724 FStar_Util.set_elements))
in (

let uu___148_22731 = s
in (

let uu____22732 = (

let uu____22733 = (

let uu____22740 = (FStar_Syntax_Subst.close_univ_vars uvs fml)
in ((lid), (uvs), (uu____22740)))
in FStar_Syntax_Syntax.Sig_assume (uu____22733))
in {FStar_Syntax_Syntax.sigel = uu____22732; FStar_Syntax_Syntax.sigrng = uu___148_22731.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___148_22731.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___148_22731.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___148_22731.FStar_Syntax_Syntax.sigattrs})))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uu____22744, bs, c, flags1) -> begin
(

let uvs = (

let uu____22755 = (

let uu____22758 = (bs_univnames bs)
in (

let uu____22761 = (FStar_Syntax_Free.univnames_comp c)
in (FStar_Util.set_union uu____22758 uu____22761)))
in (FStar_All.pipe_right uu____22755 FStar_Util.set_elements))
in (

let usubst = (FStar_Syntax_Subst.univ_var_closing uvs)
in (

let uu___149_22771 = s
in (

let uu____22772 = (

let uu____22773 = (

let uu____22786 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let uu____22787 = (FStar_Syntax_Subst.subst_comp usubst c)
in ((lid), (uvs), (uu____22786), (uu____22787), (flags1))))
in FStar_Syntax_Syntax.Sig_effect_abbrev (uu____22773))
in {FStar_Syntax_Syntax.sigel = uu____22772; FStar_Syntax_Syntax.sigrng = uu___149_22771.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___149_22771.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___149_22771.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___149_22771.FStar_Syntax_Syntax.sigattrs}))))
end
| uu____22792 -> begin
s
end))))


let desugar_modul_common : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let env1 = (match (((curmod), (m))) with
| (FStar_Pervasives_Native.None, uu____22827) -> begin
env
end
| (FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.name = prev_lid; FStar_Syntax_Syntax.declarations = uu____22831; FStar_Syntax_Syntax.exports = uu____22832; FStar_Syntax_Syntax.is_interface = uu____22833}), FStar_Parser_AST.Module (current_lid, uu____22835)) when ((FStar_Ident.lid_equals prev_lid current_lid) && (FStar_Options.interactive ())) -> begin
env
end
| (FStar_Pervasives_Native.Some (prev_mod), uu____22843) -> begin
(

let uu____22846 = (FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod)
in (FStar_Pervasives_Native.fst uu____22846))
end)
in (

let uu____22851 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(

let uu____22887 = (FStar_Syntax_DsEnv.prepare_module_or_interface true admitted env1 mname FStar_Syntax_DsEnv.default_mii)
in ((uu____22887), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(

let uu____22904 = (FStar_Syntax_DsEnv.prepare_module_or_interface false false env1 mname FStar_Syntax_DsEnv.default_mii)
in ((uu____22904), (mname), (decls), (false)))
end)
in (match (uu____22851) with
| ((env2, pop_when_done), mname, decls, intf) -> begin
(

let uu____22934 = (desugar_decls env2 decls)
in (match (uu____22934) with
| (env3, sigelts) -> begin
(

let sigelts1 = (FStar_All.pipe_right sigelts (FStar_List.map generalize_annotated_univs))
in (

let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts1; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in ((env3), (modul), (pop_when_done))))
end))
end))))


let as_interface : FStar_Parser_AST.modul  ->  FStar_Parser_AST.modul = (fun m -> (match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface (((mname), (decls), (true)))
end
| i -> begin
i
end))


let desugar_partial_modul : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  env_t  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (

let m1 = (

let uu____23003 = ((FStar_Options.interactive ()) && (

let uu____23005 = (

let uu____23006 = (

let uu____23007 = (FStar_Options.file_list ())
in (FStar_List.hd uu____23007))
in (FStar_Util.get_file_extension uu____23006))
in (FStar_List.mem uu____23005 (("fsti")::("fsi")::[]))))
in (match (uu____23003) with
| true -> begin
(as_interface m)
end
| uu____23010 -> begin
m
end))
in (

let uu____23011 = (desugar_modul_common curmod env m1)
in (match (uu____23011) with
| (x, y, pop_when_done) -> begin
((match (pop_when_done) with
| true -> begin
(

let uu____23026 = (FStar_Syntax_DsEnv.pop ())
in ())
end
| uu____23027 -> begin
()
end);
((x), (y));
)
end))))


let desugar_modul : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (

let uu____23046 = (desugar_modul_common FStar_Pervasives_Native.None env m)
in (match (uu____23046) with
| (env1, modul, pop_when_done) -> begin
(

let uu____23060 = (FStar_Syntax_DsEnv.finish_module_or_interface env1 modul)
in (match (uu____23060) with
| (env2, modul1) -> begin
((

let uu____23072 = (FStar_Options.dump_module modul1.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____23072) with
| true -> begin
(

let uu____23073 = (FStar_Syntax_Print.modul_to_string modul1)
in (FStar_Util.print1 "Module after desugaring:\n%s\n" uu____23073))
end
| uu____23074 -> begin
()
end));
(

let uu____23075 = (match (pop_when_done) with
| true -> begin
(FStar_Syntax_DsEnv.export_interface modul1.FStar_Syntax_Syntax.name env2)
end
| uu____23076 -> begin
env2
end)
in ((uu____23075), (modul1)));
)
end))
end)))


let ast_modul_to_modul : FStar_Parser_AST.modul  ->  FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv = (fun modul env -> (

let uu____23093 = (desugar_modul env modul)
in (match (uu____23093) with
| (env1, modul1) -> begin
((modul1), (env1))
end)))


let decls_to_sigelts : FStar_Parser_AST.decl Prims.list  ->  FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv = (fun decls env -> (

let uu____23124 = (desugar_decls env decls)
in (match (uu____23124) with
| (env1, sigelts) -> begin
((sigelts), (env1))
end)))


let partial_ast_modul_to_modul : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Parser_AST.modul  ->  FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv = (fun modul a_modul env -> (

let uu____23168 = (desugar_partial_modul modul env a_modul)
in (match (uu____23168) with
| (env1, modul1) -> begin
((modul1), (env1))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Syntax_DsEnv.module_inclusion_info  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  unit FStar_Syntax_DsEnv.withenv = (fun m mii erase_univs en -> (

let erase_univs_ed = (fun ed -> (

let erase_binders = (fun bs -> (match (bs) with
| [] -> begin
[]
end
| uu____23254 -> begin
(

let t = (

let uu____23262 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (FStar_Syntax_Syntax.t_unit), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (erase_univs uu____23262))
in (

let uu____23271 = (

let uu____23272 = (FStar_Syntax_Subst.compress t)
in uu____23272.FStar_Syntax_Syntax.n)
in (match (uu____23271) with
| FStar_Syntax_Syntax.Tm_abs (bs1, uu____23282, uu____23283) -> begin
bs1
end
| uu____23304 -> begin
(failwith "Impossible")
end)))
end))
in (

let uu____23311 = (

let uu____23318 = (erase_binders ed.FStar_Syntax_Syntax.binders)
in (FStar_Syntax_Subst.open_term' uu____23318 FStar_Syntax_Syntax.t_unit))
in (match (uu____23311) with
| (binders, uu____23320, binders_opening) -> begin
(

let erase_term = (fun t -> (

let uu____23328 = (

let uu____23329 = (FStar_Syntax_Subst.subst binders_opening t)
in (erase_univs uu____23329))
in (FStar_Syntax_Subst.close binders uu____23328)))
in (

let erase_tscheme = (fun uu____23347 -> (match (uu____23347) with
| (us, t) -> begin
(

let t1 = (

let uu____23367 = (FStar_Syntax_Subst.shift_subst (FStar_List.length us) binders_opening)
in (FStar_Syntax_Subst.subst uu____23367 t))
in (

let uu____23370 = (

let uu____23371 = (erase_univs t1)
in (FStar_Syntax_Subst.close binders uu____23371))
in (([]), (uu____23370))))
end))
in (

let erase_action = (fun action -> (

let opening = (FStar_Syntax_Subst.shift_subst (FStar_List.length action.FStar_Syntax_Syntax.action_univs) binders_opening)
in (

let erased_action_params = (match (action.FStar_Syntax_Syntax.action_params) with
| [] -> begin
[]
end
| uu____23402 -> begin
(

let bs = (

let uu____23410 = (FStar_Syntax_Subst.subst_binders opening action.FStar_Syntax_Syntax.action_params)
in (FStar_All.pipe_left erase_binders uu____23410))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (FStar_Syntax_Syntax.t_unit), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____23440 = (

let uu____23441 = (

let uu____23444 = (FStar_Syntax_Subst.close binders t)
in (FStar_Syntax_Subst.compress uu____23444))
in uu____23441.FStar_Syntax_Syntax.n)
in (match (uu____23440) with
| FStar_Syntax_Syntax.Tm_abs (bs1, uu____23452, uu____23453) -> begin
bs1
end
| uu____23474 -> begin
(failwith "Impossible")
end))))
end)
in (

let erase_term1 = (fun t -> (

let uu____23487 = (

let uu____23488 = (FStar_Syntax_Subst.subst opening t)
in (erase_univs uu____23488))
in (FStar_Syntax_Subst.close binders uu____23487)))
in (

let uu___150_23489 = action
in (

let uu____23490 = (erase_term1 action.FStar_Syntax_Syntax.action_defn)
in (

let uu____23491 = (erase_term1 action.FStar_Syntax_Syntax.action_typ)
in {FStar_Syntax_Syntax.action_name = uu___150_23489.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___150_23489.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = erased_action_params; FStar_Syntax_Syntax.action_defn = uu____23490; FStar_Syntax_Syntax.action_typ = uu____23491})))))))
in (

let uu___151_23492 = ed
in (

let uu____23493 = (FStar_Syntax_Subst.close_binders binders)
in (

let uu____23494 = (erase_term ed.FStar_Syntax_Syntax.signature)
in (

let uu____23495 = (erase_tscheme ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____23496 = (erase_tscheme ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____23497 = (erase_tscheme ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____23498 = (erase_tscheme ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____23499 = (erase_tscheme ed.FStar_Syntax_Syntax.stronger)
in (

let uu____23500 = (erase_tscheme ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____23501 = (erase_tscheme ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____23502 = (erase_tscheme ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____23503 = (erase_tscheme ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____23504 = (erase_tscheme ed.FStar_Syntax_Syntax.trivial)
in (

let uu____23505 = (erase_term ed.FStar_Syntax_Syntax.repr)
in (

let uu____23506 = (erase_tscheme ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____23507 = (erase_tscheme ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____23508 = (FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = uu___151_23492.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___151_23492.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = uu____23493; FStar_Syntax_Syntax.signature = uu____23494; FStar_Syntax_Syntax.ret_wp = uu____23495; FStar_Syntax_Syntax.bind_wp = uu____23496; FStar_Syntax_Syntax.if_then_else = uu____23497; FStar_Syntax_Syntax.ite_wp = uu____23498; FStar_Syntax_Syntax.stronger = uu____23499; FStar_Syntax_Syntax.close_wp = uu____23500; FStar_Syntax_Syntax.assert_p = uu____23501; FStar_Syntax_Syntax.assume_p = uu____23502; FStar_Syntax_Syntax.null_wp = uu____23503; FStar_Syntax_Syntax.trivial = uu____23504; FStar_Syntax_Syntax.repr = uu____23505; FStar_Syntax_Syntax.return_repr = uu____23506; FStar_Syntax_Syntax.bind_repr = uu____23507; FStar_Syntax_Syntax.actions = uu____23508; FStar_Syntax_Syntax.eff_attrs = uu___151_23492.FStar_Syntax_Syntax.eff_attrs}))))))))))))))))))))
end))))
in (

let push_sigelt1 = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let se' = (

let uu___152_23524 = se
in (

let uu____23525 = (

let uu____23526 = (erase_univs_ed ed)
in FStar_Syntax_Syntax.Sig_new_effect (uu____23526))
in {FStar_Syntax_Syntax.sigel = uu____23525; FStar_Syntax_Syntax.sigrng = uu___152_23524.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___152_23524.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___152_23524.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___152_23524.FStar_Syntax_Syntax.sigattrs}))
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se')
in (push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng)))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed) -> begin
(

let se' = (

let uu___153_23530 = se
in (

let uu____23531 = (

let uu____23532 = (erase_univs_ed ed)
in FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____23532))
in {FStar_Syntax_Syntax.sigel = uu____23531; FStar_Syntax_Syntax.sigrng = uu___153_23530.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___153_23530.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___153_23530.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___153_23530.FStar_Syntax_Syntax.sigattrs}))
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se')
in (push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng)))
end
| uu____23534 -> begin
(FStar_Syntax_DsEnv.push_sigelt env se)
end))
in (

let uu____23535 = (FStar_Syntax_DsEnv.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name mii)
in (match (uu____23535) with
| (en1, pop_when_done) -> begin
(

let en2 = (

let uu____23547 = (FStar_Syntax_DsEnv.set_current_module en1 m.FStar_Syntax_Syntax.name)
in (FStar_List.fold_left push_sigelt1 uu____23547 m.FStar_Syntax_Syntax.exports))
in (

let env = (FStar_Syntax_DsEnv.finish en2 m)
in (

let uu____23549 = (match (pop_when_done) with
| true -> begin
(FStar_Syntax_DsEnv.export_interface m.FStar_Syntax_Syntax.name env)
end
| uu____23550 -> begin
env
end)
in ((()), (uu____23549)))))
end)))))




