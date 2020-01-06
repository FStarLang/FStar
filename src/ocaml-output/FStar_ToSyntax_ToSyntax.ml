
open Prims
open FStar_Pervasives

type annotated_pat =
(FStar_Syntax_Syntax.pat * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.typ) Prims.list)


let desugar_disjunctive_pattern : (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) Prims.list) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list = (fun annotated_pats when_opt branch1 -> (FStar_All.pipe_right annotated_pats (FStar_List.map (fun uu____103 -> (match (uu____103) with
| (pat, annots) -> begin
(

let branch2 = (FStar_List.fold_left (fun br uu____158 -> (match (uu____158) with
| (bv, ty) -> begin
(

let lb = (

let uu____176 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (bv)) [] ty FStar_Parser_Const.effect_Tot_lid uu____176 [] br.FStar_Syntax_Syntax.pos))
in (

let branch2 = (

let uu____182 = (

let uu____183 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____183)::[])
in (FStar_Syntax_Subst.close uu____182 branch1))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (branch2)))) FStar_Pervasives_Native.None br.FStar_Syntax_Syntax.pos)))
end)) branch1 annots)
in (FStar_Syntax_Util.branch ((pat), (when_opt), (branch2))))
end)))))


let trans_qual : FStar_Range.range  ->  FStar_Ident.lident FStar_Pervasives_Native.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun r maybe_effect_id uu___0_240 -> (match (uu___0_240) with
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
end))


let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun uu___1_260 -> (match (uu___1_260) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end
| FStar_Parser_AST.PushOptions (sopt) -> begin
FStar_Syntax_Syntax.PushOptions (sopt)
end
| FStar_Parser_AST.PopOptions -> begin
FStar_Syntax_Syntax.PopOptions
end
| FStar_Parser_AST.RestartSolver -> begin
FStar_Syntax_Syntax.RestartSolver
end
| FStar_Parser_AST.LightOff -> begin
FStar_Syntax_Syntax.LightOff
end))


let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option = (fun uu___2_278 -> (match (uu___2_278) with
| FStar_Parser_AST.Hash -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)
end
| uu____281 -> begin
FStar_Pervasives_Native.None
end))


let arg_withimp_e : 'Auu____289 . FStar_Parser_AST.imp  ->  'Auu____289  ->  ('Auu____289 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) = (fun imp t -> ((t), ((as_imp imp))))


let arg_withimp_t : 'Auu____315 . FStar_Parser_AST.imp  ->  'Auu____315  ->  ('Auu____315 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
((t), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end
| uu____334 -> begin
((t), (FStar_Pervasives_Native.None))
end))


let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (uu____355) -> begin
true
end
| uu____361 -> begin
false
end)))))


let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t1) -> begin
(unparen t1)
end
| uu____370 -> begin
t
end))


let tm_type_z : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (

let uu____377 = (

let uu____378 = (FStar_Ident.lid_of_path (("Type0")::[]) r)
in FStar_Parser_AST.Name (uu____378))
in (FStar_Parser_AST.mk_term uu____377 r FStar_Parser_AST.Kind)))


let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (

let uu____388 = (

let uu____389 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (uu____389))
in (FStar_Parser_AST.mk_term uu____388 r FStar_Parser_AST.Kind)))


let rec is_comp_type : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> (

let uu____405 = (

let uu____406 = (unparen t)
in uu____406.FStar_Parser_AST.tm)
in (match (uu____405) with
| FStar_Parser_AST.Name (l) -> begin
(

let uu____409 = (FStar_Syntax_DsEnv.try_lookup_effect_name env l)
in (FStar_All.pipe_right uu____409 FStar_Option.isSome))
end
| FStar_Parser_AST.Construct (l, uu____416) -> begin
(

let uu____429 = (FStar_Syntax_DsEnv.try_lookup_effect_name env l)
in (FStar_All.pipe_right uu____429 FStar_Option.isSome))
end
| FStar_Parser_AST.App (head1, uu____436, uu____437) -> begin
(is_comp_type env head1)
end
| FStar_Parser_AST.Paren (t1) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.Ascribed (t1, uu____442, uu____443) -> begin
(is_comp_type env t1)
end
| FStar_Parser_AST.LetOpen (uu____448, t1) -> begin
(is_comp_type env t1)
end
| uu____450 -> begin
false
end)))


let unit_ty : FStar_Parser_AST.term = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.unit_lid)) FStar_Range.dummyRange FStar_Parser_AST.Type_level)


type env_t =
FStar_Syntax_DsEnv.env


type lenv_t =
FStar_Syntax_Syntax.bv Prims.list


let desugar_name' : (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  env_t  ->  Prims.bool  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun setpos env resolve l -> (

let tm_attrs_opt = (match (resolve) with
| true -> begin
(FStar_Syntax_DsEnv.try_lookup_lid_with_attributes env l)
end
| uu____505 -> begin
(FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve env l)
end)
in (match (tm_attrs_opt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (tm, attrs) -> begin
(

let warn_if_deprecated = (fun attrs1 -> (FStar_List.iter (fun a -> (match (a.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____551; FStar_Syntax_Syntax.vars = uu____552}, args) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v FStar_Parser_Const.deprecated_attr) -> begin
(

let msg = (

let uu____580 = (FStar_Syntax_Print.term_to_string tm)
in (Prims.op_Hat uu____580 " is deprecated"))
in (

let msg1 = (match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____596 = (

let uu____597 = (

let uu____600 = (FStar_List.hd args)
in (FStar_Pervasives_Native.fst uu____600))
in uu____597.FStar_Syntax_Syntax.n)
in (match (uu____596) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____623)) when (not ((Prims.op_Equality (FStar_Util.trim_string s) ""))) -> begin
(Prims.op_Hat msg (Prims.op_Hat ", use " (Prims.op_Hat s " instead")))
end
| uu____630 -> begin
msg
end))
end
| uu____631 -> begin
msg
end)
in (

let uu____633 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.log_issue uu____633 ((FStar_Errors.Warning_DeprecatedDefinition), (msg1))))))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v FStar_Parser_Const.deprecated_attr) -> begin
(

let msg = (

let uu____638 = (FStar_Syntax_Print.term_to_string tm)
in (Prims.op_Hat uu____638 " is deprecated"))
in (

let uu____641 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.log_issue uu____641 ((FStar_Errors.Warning_DeprecatedDefinition), (msg)))))
end
| uu____643 -> begin
()
end)) attrs1))
in ((warn_if_deprecated attrs);
(

let tm1 = (setpos tm)
in FStar_Pervasives_Native.Some (tm1));
))
end)))


let desugar_name : 'Auu____659 . 'Auu____659  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  env_t  ->  Prims.bool  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun mk1 setpos env resolve l -> (FStar_Syntax_DsEnv.fail_or env (desugar_name' setpos env resolve) l))


let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n1 s r -> (

let uu____712 = (

let uu____715 = (

let uu____716 = (

let uu____722 = (FStar_Parser_AST.compile_op n1 s r)
in ((uu____722), (r)))
in (FStar_Ident.mk_ident uu____716))
in (uu____715)::[])
in (FStar_All.pipe_right uu____712 FStar_Ident.lid_of_ids)))


let op_as_term : 'Auu____738 . env_t  ->  Prims.int  ->  'Auu____738  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env arity rng op -> (

let r = (fun l dd -> (

let uu____776 = (

let uu____777 = (

let uu____778 = (FStar_Ident.set_lid_range l op.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____778 dd FStar_Pervasives_Native.None))
in (FStar_All.pipe_right uu____777 FStar_Syntax_Syntax.fv_to_tm))
in FStar_Pervasives_Native.Some (uu____776)))
in (

let fallback = (fun uu____786 -> (

let uu____787 = (FStar_Ident.text_of_id op)
in (match (uu____787) with
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

let uu____808 = (FStar_Options.ml_ish ())
in (match (uu____808) with
| true -> begin
(r FStar_Parser_Const.list_append_lid (FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "2"))))
end
| uu____814 -> begin
(r FStar_Parser_Const.list_tot_append_lid (FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "2"))))
end))
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
| uu____833 -> begin
FStar_Pervasives_Native.None
end)))
in (

let uu____835 = (

let uu____838 = (compile_op_lid arity op.FStar_Ident.idText op.FStar_Ident.idRange)
in (desugar_name' (fun t -> (

let uu___203_844 = t
in {FStar_Syntax_Syntax.n = uu___203_844.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = op.FStar_Ident.idRange; FStar_Syntax_Syntax.vars = uu___203_844.FStar_Syntax_Syntax.vars})) env true uu____838))
in (match (uu____835) with
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____849 -> begin
(fallback ())
end)))))


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (

let uu____864 = (FStar_Util.remove_dups (fun x y -> (Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) uu____864)))


let rec free_type_vars_b : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (uu____913) -> begin
((env), ([]))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____917 = (FStar_Syntax_DsEnv.push_bv env x)
in (match (uu____917) with
| (env1, uu____929) -> begin
((env1), ((x)::[]))
end))
end
| FStar_Parser_AST.Annotated (uu____932, term) -> begin
(

let uu____934 = (free_type_vars env term)
in ((env), (uu____934)))
end
| FStar_Parser_AST.TAnnotated (id1, uu____940) -> begin
(

let uu____941 = (FStar_Syntax_DsEnv.push_bv env id1)
in (match (uu____941) with
| (env1, uu____953) -> begin
((env1), ([]))
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____957 = (free_type_vars env t)
in ((env), (uu____957)))
end))
and free_type_vars : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (

let uu____964 = (

let uu____965 = (unparen t)
in uu____965.FStar_Parser_AST.tm)
in (match (uu____964) with
| FStar_Parser_AST.Labeled (uu____968) -> begin
(failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____981 = (FStar_Syntax_DsEnv.try_lookup_id env a)
in (match (uu____981) with
| FStar_Pervasives_Native.None -> begin
(a)::[]
end
| uu____986 -> begin
[]
end))
end
| FStar_Parser_AST.Wild -> begin
[]
end
| FStar_Parser_AST.Const (uu____989) -> begin
[]
end
| FStar_Parser_AST.Uvar (uu____990) -> begin
[]
end
| FStar_Parser_AST.Var (uu____991) -> begin
[]
end
| FStar_Parser_AST.Projector (uu____992) -> begin
[]
end
| FStar_Parser_AST.Discrim (uu____997) -> begin
[]
end
| FStar_Parser_AST.Name (uu____998) -> begin
[]
end
| FStar_Parser_AST.Requires (t1, uu____1000) -> begin
(free_type_vars env t1)
end
| FStar_Parser_AST.Ensures (t1, uu____1008) -> begin
(free_type_vars env t1)
end
| FStar_Parser_AST.NamedTyp (uu____1015, t1) -> begin
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
| FStar_Parser_AST.Construct (uu____1034, ts) -> begin
(FStar_List.collect (fun uu____1055 -> (match (uu____1055) with
| (t1, uu____1063) -> begin
(free_type_vars env t1)
end)) ts)
end
| FStar_Parser_AST.Op (uu____1064, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, uu____1072) -> begin
(

let uu____1073 = (free_type_vars env t1)
in (

let uu____1076 = (free_type_vars env t2)
in (FStar_List.append uu____1073 uu____1076)))
end
| FStar_Parser_AST.Refine (b, t1) -> begin
(

let uu____1081 = (free_type_vars_b env b)
in (match (uu____1081) with
| (env1, f) -> begin
(

let uu____1096 = (free_type_vars env1 t1)
in (FStar_List.append f uu____1096))
end))
end
| FStar_Parser_AST.Sum (binders, body) -> begin
(

let uu____1113 = (FStar_List.fold_left (fun uu____1137 bt -> (match (uu____1137) with
| (env1, free) -> begin
(

let uu____1161 = (match (bt) with
| FStar_Util.Inl (binder) -> begin
(free_type_vars_b env1 binder)
end
| FStar_Util.Inr (t1) -> begin
(

let uu____1176 = (free_type_vars env1 body)
in ((env1), (uu____1176)))
end)
in (match (uu____1161) with
| (env2, f) -> begin
((env2), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (uu____1113) with
| (env1, free) -> begin
(

let uu____1205 = (free_type_vars env1 body)
in (FStar_List.append free uu____1205))
end))
end
| FStar_Parser_AST.Product (binders, body) -> begin
(

let uu____1214 = (FStar_List.fold_left (fun uu____1234 binder -> (match (uu____1234) with
| (env1, free) -> begin
(

let uu____1254 = (free_type_vars_b env1 binder)
in (match (uu____1254) with
| (env2, f) -> begin
((env2), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (uu____1214) with
| (env1, free) -> begin
(

let uu____1285 = (free_type_vars env1 body)
in (FStar_List.append free uu____1285))
end))
end
| FStar_Parser_AST.Project (t1, uu____1289) -> begin
(free_type_vars env t1)
end
| FStar_Parser_AST.Attributes (cattributes) -> begin
(FStar_List.collect (free_type_vars env) cattributes)
end
| FStar_Parser_AST.CalcProof (rel, init1, steps) -> begin
(

let uu____1300 = (free_type_vars env rel)
in (

let uu____1303 = (

let uu____1306 = (free_type_vars env init1)
in (

let uu____1309 = (FStar_List.collect (fun uu____1318 -> (match (uu____1318) with
| FStar_Parser_AST.CalcStep (rel1, just, next) -> begin
(

let uu____1324 = (free_type_vars env rel1)
in (

let uu____1327 = (

let uu____1330 = (free_type_vars env just)
in (

let uu____1333 = (free_type_vars env next)
in (FStar_List.append uu____1330 uu____1333)))
in (FStar_List.append uu____1324 uu____1327)))
end)) steps)
in (FStar_List.append uu____1306 uu____1309)))
in (FStar_List.append uu____1300 uu____1303)))
end
| FStar_Parser_AST.Abs (uu____1336) -> begin
[]
end
| FStar_Parser_AST.Let (uu____1343) -> begin
[]
end
| FStar_Parser_AST.LetOpen (uu____1364) -> begin
[]
end
| FStar_Parser_AST.If (uu____1369) -> begin
[]
end
| FStar_Parser_AST.QForall (uu____1376) -> begin
[]
end
| FStar_Parser_AST.QExists (uu____1395) -> begin
[]
end
| FStar_Parser_AST.Record (uu____1414) -> begin
[]
end
| FStar_Parser_AST.Match (uu____1427) -> begin
[]
end
| FStar_Parser_AST.TryWith (uu____1442) -> begin
[]
end
| FStar_Parser_AST.Bind (uu____1457) -> begin
[]
end
| FStar_Parser_AST.Quote (uu____1464) -> begin
[]
end
| FStar_Parser_AST.VQuote (uu____1469) -> begin
[]
end
| FStar_Parser_AST.Antiquote (uu____1470) -> begin
[]
end
| FStar_Parser_AST.Seq (uu____1471) -> begin
[]
end)))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (

let rec aux = (fun args t1 -> (

let uu____1525 = (

let uu____1526 = (unparen t1)
in uu____1526.FStar_Parser_AST.tm)
in (match (uu____1525) with
| FStar_Parser_AST.App (t2, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t2)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t1.FStar_Parser_AST.range; FStar_Parser_AST.level = t1.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| uu____1568 -> begin
((t1), (args))
end)))
in (aux [] t)))


let close : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (

let uu____1593 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv uu____1593))
in (match ((Prims.op_Equality (FStar_List.length ftv) (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____1603 -> begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (

let uu____1615 = (

let uu____1616 = (

let uu____1621 = (tm_type x.FStar_Ident.idRange)
in ((x), (uu____1621)))
in FStar_Parser_AST.TAnnotated (uu____1616))
in (FStar_Parser_AST.mk_binder uu____1615 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end)))


let close_fun : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (

let uu____1639 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv uu____1639))
in (match ((Prims.op_Equality (FStar_List.length ftv) (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____1649 -> begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (

let uu____1661 = (

let uu____1662 = (

let uu____1667 = (tm_type x.FStar_Ident.idRange)
in ((x), (uu____1667)))
in FStar_Parser_AST.TAnnotated (uu____1662))
in (FStar_Parser_AST.mk_binder uu____1661 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))))))
in (

let t1 = (

let uu____1669 = (

let uu____1670 = (unparen t)
in uu____1670.FStar_Parser_AST.tm)
in (match (uu____1669) with
| FStar_Parser_AST.Product (uu____1671) -> begin
t
end
| uu____1678 -> begin
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
| uu____1715 -> begin
((bs), (t))
end))


let rec is_var_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatWild (uu____1726) -> begin
true
end
| FStar_Parser_AST.PatTvar (uu____1730, uu____1731) -> begin
true
end
| FStar_Parser_AST.PatVar (uu____1737, uu____1738) -> begin
true
end
| FStar_Parser_AST.PatAscribed (p1, uu____1745) -> begin
(is_var_pattern p1)
end
| uu____1758 -> begin
false
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p1, uu____1769) -> begin
(is_app_pattern p1)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____1782); FStar_Parser_AST.prange = uu____1783}, uu____1784) -> begin
true
end
| uu____1796 -> begin
false
end))


let replace_unit_pattern : FStar_Parser_AST.pattern  ->  FStar_Parser_AST.pattern = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatConst (FStar_Const.Const_unit) -> begin
(FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatAscribed ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatWild (FStar_Pervasives_Native.None)) p.FStar_Parser_AST.prange)), (((unit_ty), (FStar_Pervasives_Native.None)))))) p.FStar_Parser_AST.prange)
end
| uu____1812 -> begin
p
end))


let rec destruct_app_pattern : FStar_Syntax_DsEnv.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * (FStar_Parser_AST.term * FStar_Parser_AST.term FStar_Pervasives_Native.option) FStar_Pervasives_Native.option) = (fun env is_top_level1 p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p1, t) -> begin
(

let uu____1885 = (destruct_app_pattern env is_top_level1 p1)
in (match (uu____1885) with
| (name, args, uu____1928) -> begin
((name), (args), (FStar_Pervasives_Native.Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id1, uu____1978); FStar_Parser_AST.prange = uu____1979}, args) when is_top_level1 -> begin
(

let uu____1989 = (

let uu____1994 = (FStar_Syntax_DsEnv.qualify env id1)
in FStar_Util.Inr (uu____1994))
in ((uu____1989), (args), (FStar_Pervasives_Native.None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id1, uu____2016); FStar_Parser_AST.prange = uu____2017}, args) -> begin
((FStar_Util.Inl (id1)), (args), (FStar_Pervasives_Native.None))
end
| uu____2047 -> begin
(failwith "Not an app pattern")
end))


let rec gather_pattern_bound_vars_maybe_top : Prims.bool  ->  FStar_Ident.ident FStar_Util.set  ->  FStar_Parser_AST.pattern  ->  FStar_Ident.ident FStar_Util.set = (fun fail_on_patconst acc p -> (

let gather_pattern_bound_vars_from_list = (FStar_List.fold_left (gather_pattern_bound_vars_maybe_top fail_on_patconst) acc)
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatWild (uu____2106) -> begin
acc
end
| FStar_Parser_AST.PatName (uu____2109) -> begin
acc
end
| FStar_Parser_AST.PatOp (uu____2110) -> begin
acc
end
| FStar_Parser_AST.PatConst (uu____2111) -> begin
(match (fail_on_patconst) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Error_CannotRedefineConst), ("Constants cannot be redefined")) p.FStar_Parser_AST.prange)
end
| uu____2119 -> begin
acc
end)
end
| FStar_Parser_AST.PatApp (phead, pats) -> begin
(gather_pattern_bound_vars_from_list ((phead)::pats))
end
| FStar_Parser_AST.PatTvar (x, uu____2128) -> begin
(FStar_Util.set_add x acc)
end
| FStar_Parser_AST.PatVar (x, uu____2134) -> begin
(FStar_Util.set_add x acc)
end
| FStar_Parser_AST.PatList (pats) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatTuple (pats, uu____2143) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatOr (pats) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatRecord (guarded_pats) -> begin
(

let uu____2160 = (FStar_List.map FStar_Pervasives_Native.snd guarded_pats)
in (gather_pattern_bound_vars_from_list uu____2160))
end
| FStar_Parser_AST.PatAscribed (pat, uu____2168) -> begin
(gather_pattern_bound_vars_maybe_top fail_on_patconst acc pat)
end)))


let gather_pattern_bound_vars : Prims.bool  ->  FStar_Parser_AST.pattern  ->  FStar_Ident.ident FStar_Util.set = (fun fail_on_patconst p -> (

let acc = (FStar_Util.new_set (fun id1 id2 -> (match ((Prims.op_Equality id1.FStar_Ident.idText id2.FStar_Ident.idText)) with
| true -> begin
(Prims.parse_int "0")
end
| uu____2209 -> begin
(Prims.parse_int "1")
end)))
in (gather_pattern_bound_vars_maybe_top fail_on_patconst acc p)))

type bnd =
| LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option))


let uu___is_LocalBinder : bnd  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LocalBinder (_0) -> begin
true
end
| uu____2250 -> begin
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
| uu____2291 -> begin
false
end))


let __proj__LetBinder__item___0 : bnd  ->  (FStar_Ident.lident * (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)) = (fun projectee -> (match (projectee) with
| LetBinder (_0) -> begin
_0
end))


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun uu___3_2339 -> (match (uu___3_2339) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| uu____2346 -> begin
(failwith "Impossible")
end))


let mk_lb : (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list * (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)  ->  FStar_Syntax_Syntax.letbinding = (fun uu____2379 -> (match (uu____2379) with
| (attrs, n1, t, e, pos) -> begin
{FStar_Syntax_Syntax.lbname = n1; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = attrs; FStar_Syntax_Syntax.lbpos = pos}
end))


let no_annot_abs : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs t -> (FStar_Syntax_Util.abs bs t FStar_Pervasives_Native.None))


let mk_ref_read : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun tm -> (

let tm' = (

let uu____2461 = (

let uu____2478 = (

let uu____2481 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____2481))
in (

let uu____2482 = (

let uu____2493 = (

let uu____2502 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (uu____2502)))
in (uu____2493)::[])
in ((uu____2478), (uu____2482))))
in FStar_Syntax_Syntax.Tm_app (uu____2461))
in (FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_alloc : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun tm -> (

let tm' = (

let uu____2551 = (

let uu____2568 = (

let uu____2571 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____2571))
in (

let uu____2572 = (

let uu____2583 = (

let uu____2592 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (uu____2592)))
in (uu____2583)::[])
in ((uu____2568), (uu____2572))))
in FStar_Syntax_Syntax.Tm_app (uu____2551))
in (FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_assign : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t1 t2 pos -> (

let tm = (

let uu____2655 = (

let uu____2672 = (

let uu____2675 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____2675))
in (

let uu____2676 = (

let uu____2687 = (

let uu____2696 = (FStar_Syntax_Syntax.as_implicit false)
in ((t1), (uu____2696)))
in (

let uu____2704 = (

let uu____2715 = (

let uu____2724 = (FStar_Syntax_Syntax.as_implicit false)
in ((t2), (uu____2724)))
in (uu____2715)::[])
in (uu____2687)::uu____2704))
in ((uu____2672), (uu____2676))))
in FStar_Syntax_Syntax.Tm_app (uu____2655))
in (FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos)))


let generalize_annotated_univs : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun s -> (

let bs_univnames = (fun bs -> (

let uu____2784 = (

let uu____2799 = (FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name)
in (FStar_List.fold_left (fun uvs uu____2818 -> (match (uu____2818) with
| ({FStar_Syntax_Syntax.ppname = uu____2829; FStar_Syntax_Syntax.index = uu____2830; FStar_Syntax_Syntax.sort = t}, uu____2832) -> begin
(

let uu____2840 = (FStar_Syntax_Free.univnames t)
in (FStar_Util.set_union uvs uu____2840))
end)) uu____2799))
in (FStar_All.pipe_right bs uu____2784)))
in (

let empty_set = (FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name)
in (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____2856) -> begin
(failwith "Impossible: collect_annotated_universes: bare data/type constructor")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____2874) -> begin
(failwith "Impossible: collect_annotated_universes: bare data/type constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (sigs, lids) -> begin
(

let uvs = (

let uu____2902 = (FStar_All.pipe_right sigs (FStar_List.fold_left (fun uvs se -> (

let se_univs = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____2923, uu____2924, bs, t, uu____2927, uu____2928) -> begin
(

let uu____2937 = (bs_univnames bs)
in (

let uu____2940 = (FStar_Syntax_Free.univnames t)
in (FStar_Util.set_union uu____2937 uu____2940)))
end
| FStar_Syntax_Syntax.Sig_datacon (uu____2943, uu____2944, t, uu____2946, uu____2947, uu____2948) -> begin
(FStar_Syntax_Free.univnames t)
end
| uu____2955 -> begin
(failwith "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt")
end)
in (FStar_Util.set_union uvs se_univs))) empty_set))
in (FStar_All.pipe_right uu____2902 FStar_Util.set_elements))
in (

let usubst = (FStar_Syntax_Subst.univ_var_closing uvs)
in (

let uu___585_2964 = s
in (

let uu____2965 = (

let uu____2966 = (

let uu____2975 = (FStar_All.pipe_right sigs (FStar_List.map (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2993, bs, t, lids1, lids2) -> begin
(

let uu___596_3006 = se
in (

let uu____3007 = (

let uu____3008 = (

let uu____3025 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let uu____3026 = (

let uu____3027 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst uu____3027 t))
in ((lid), (uvs), (uu____3025), (uu____3026), (lids1), (lids2))))
in FStar_Syntax_Syntax.Sig_inductive_typ (uu____3008))
in {FStar_Syntax_Syntax.sigel = uu____3007; FStar_Syntax_Syntax.sigrng = uu___596_3006.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___596_3006.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___596_3006.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___596_3006.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___596_3006.FStar_Syntax_Syntax.sigopts}))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____3041, t, tlid, n1, lids1) -> begin
(

let uu___606_3052 = se
in (

let uu____3053 = (

let uu____3054 = (

let uu____3070 = (FStar_Syntax_Subst.subst usubst t)
in ((lid), (uvs), (uu____3070), (tlid), (n1), (lids1)))
in FStar_Syntax_Syntax.Sig_datacon (uu____3054))
in {FStar_Syntax_Syntax.sigel = uu____3053; FStar_Syntax_Syntax.sigrng = uu___606_3052.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___606_3052.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___606_3052.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___606_3052.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___606_3052.FStar_Syntax_Syntax.sigopts}))
end
| uu____3074 -> begin
(failwith "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt")
end))))
in ((uu____2975), (lids)))
in FStar_Syntax_Syntax.Sig_bundle (uu____2966))
in {FStar_Syntax_Syntax.sigel = uu____2965; FStar_Syntax_Syntax.sigrng = uu___585_2964.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___585_2964.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___585_2964.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___585_2964.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___585_2964.FStar_Syntax_Syntax.sigopts}))))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____3081, t) -> begin
(

let uvs = (

let uu____3084 = (FStar_Syntax_Free.univnames t)
in (FStar_All.pipe_right uu____3084 FStar_Util.set_elements))
in (

let uu___615_3089 = s
in (

let uu____3090 = (

let uu____3091 = (

let uu____3098 = (FStar_Syntax_Subst.close_univ_vars uvs t)
in ((lid), (uvs), (uu____3098)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____3091))
in {FStar_Syntax_Syntax.sigel = uu____3090; FStar_Syntax_Syntax.sigrng = uu___615_3089.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___615_3089.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___615_3089.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___615_3089.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___615_3089.FStar_Syntax_Syntax.sigopts})))
end
| FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) -> begin
(

let lb_univnames = (fun lb -> (

let uu____3122 = (FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____3125 = (match (lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, e, uu____3132) -> begin
(

let uvs1 = (bs_univnames bs)
in (

let uvs2 = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (uu____3165, (FStar_Util.Inl (t), uu____3167), uu____3168) -> begin
(FStar_Syntax_Free.univnames t)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3215, (FStar_Util.Inr (c), uu____3217), uu____3218) -> begin
(FStar_Syntax_Free.univnames_comp c)
end
| uu____3265 -> begin
empty_set
end)
in (FStar_Util.set_union uvs1 uvs2)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, uu____3267) -> begin
(bs_univnames bs)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3288, (FStar_Util.Inl (t), uu____3290), uu____3291) -> begin
(FStar_Syntax_Free.univnames t)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____3338, (FStar_Util.Inr (c), uu____3340), uu____3341) -> begin
(FStar_Syntax_Free.univnames_comp c)
end
| uu____3388 -> begin
empty_set
end)
in (FStar_Util.set_union uu____3122 uu____3125))))
in (

let all_lb_univs = (

let uu____3392 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun uvs lb -> (

let uu____3408 = (lb_univnames lb)
in (FStar_Util.set_union uvs uu____3408))) empty_set))
in (FStar_All.pipe_right uu____3392 FStar_Util.set_elements))
in (

let usubst = (FStar_Syntax_Subst.univ_var_closing all_lb_univs)
in (

let uu___674_3418 = s
in (

let uu____3419 = (

let uu____3420 = (

let uu____3427 = (

let uu____3428 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu___677_3440 = lb
in (

let uu____3441 = (FStar_Syntax_Subst.subst usubst lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____3444 = (FStar_Syntax_Subst.subst usubst lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___677_3440.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = all_lb_univs; FStar_Syntax_Syntax.lbtyp = uu____3441; FStar_Syntax_Syntax.lbeff = uu___677_3440.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____3444; FStar_Syntax_Syntax.lbattrs = uu___677_3440.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___677_3440.FStar_Syntax_Syntax.lbpos}))))))
in ((b), (uu____3428)))
in ((uu____3427), (lids)))
in FStar_Syntax_Syntax.Sig_let (uu____3420))
in {FStar_Syntax_Syntax.sigel = uu____3419; FStar_Syntax_Syntax.sigrng = uu___674_3418.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___674_3418.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___674_3418.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___674_3418.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___674_3418.FStar_Syntax_Syntax.sigopts})))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____3453, fml) -> begin
(

let uvs = (

let uu____3456 = (FStar_Syntax_Free.univnames fml)
in (FStar_All.pipe_right uu____3456 FStar_Util.set_elements))
in (

let uu___685_3461 = s
in (

let uu____3462 = (

let uu____3463 = (

let uu____3470 = (FStar_Syntax_Subst.close_univ_vars uvs fml)
in ((lid), (uvs), (uu____3470)))
in FStar_Syntax_Syntax.Sig_assume (uu____3463))
in {FStar_Syntax_Syntax.sigel = uu____3462; FStar_Syntax_Syntax.sigrng = uu___685_3461.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___685_3461.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___685_3461.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___685_3461.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___685_3461.FStar_Syntax_Syntax.sigopts})))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uu____3472, bs, c, flags) -> begin
(

let uvs = (

let uu____3481 = (

let uu____3484 = (bs_univnames bs)
in (

let uu____3487 = (FStar_Syntax_Free.univnames_comp c)
in (FStar_Util.set_union uu____3484 uu____3487)))
in (FStar_All.pipe_right uu____3481 FStar_Util.set_elements))
in (

let usubst = (FStar_Syntax_Subst.univ_var_closing uvs)
in (

let uu___696_3495 = s
in (

let uu____3496 = (

let uu____3497 = (

let uu____3510 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let uu____3511 = (FStar_Syntax_Subst.subst_comp usubst c)
in ((lid), (uvs), (uu____3510), (uu____3511), (flags))))
in FStar_Syntax_Syntax.Sig_effect_abbrev (uu____3497))
in {FStar_Syntax_Syntax.sigel = uu____3496; FStar_Syntax_Syntax.sigrng = uu___696_3495.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___696_3495.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___696_3495.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___696_3495.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___696_3495.FStar_Syntax_Syntax.sigopts}))))
end
| uu____3514 -> begin
s
end))))


let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun uu___4_3522 -> (match (uu___4_3522) with
| "lift1" -> begin
true
end
| "lift2" -> begin
true
end
| "pure" -> begin
true
end
| "app" -> begin
true
end
| "push" -> begin
true
end
| "wp_if_then_else" -> begin
true
end
| "wp_assert" -> begin
true
end
| "wp_assume" -> begin
true
end
| "wp_close" -> begin
true
end
| "stronger" -> begin
true
end
| "ite_wp" -> begin
true
end
| "wp_trivial" -> begin
true
end
| "ctx" -> begin
true
end
| "gctx" -> begin
true
end
| "lift_from_pure" -> begin
true
end
| "return_wp" -> begin
true
end
| "return_elab" -> begin
true
end
| "bind_wp" -> begin
true
end
| "bind_elab" -> begin
true
end
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
| uu____3571 -> begin
false
end))


let rec sum_to_universe : FStar_Syntax_Syntax.universe  ->  Prims.int  ->  FStar_Syntax_Syntax.universe = (fun u n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
u
end
| uu____3590 -> begin
(

let uu____3592 = (sum_to_universe u (n1 - (Prims.parse_int "1")))
in FStar_Syntax_Syntax.U_succ (uu____3592))
end))


let int_to_universe : Prims.int  ->  FStar_Syntax_Syntax.universe = (fun n1 -> (sum_to_universe FStar_Syntax_Syntax.U_zero n1))


let rec desugar_maybe_non_constant_universe : FStar_Parser_AST.term  ->  (Prims.int, FStar_Syntax_Syntax.universe) FStar_Util.either = (fun t -> (

let uu____3618 = (

let uu____3619 = (unparen t)
in uu____3619.FStar_Parser_AST.tm)
in (match (uu____3618) with
| FStar_Parser_AST.Wild -> begin
(

let uu____3625 = (

let uu____3626 = (FStar_Syntax_Unionfind.univ_fresh ())
in FStar_Syntax_Syntax.U_unif (uu____3626))
in FStar_Util.Inr (uu____3625))
end
| FStar_Parser_AST.Uvar (u) -> begin
FStar_Util.Inr (FStar_Syntax_Syntax.U_name (u))
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (repr, uu____3639)) -> begin
(

let n1 = (FStar_Util.int_of_string repr)
in ((match ((n1 < (Prims.parse_int "0"))) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_NegativeUniverseConstFatal_NotSupported), ((Prims.op_Hat "Negative universe constant  are not supported : " repr))) t.FStar_Parser_AST.range)
end
| uu____3661 -> begin
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

let uu____3730 = (sum_to_universe u n1)
in FStar_Util.Inr (uu____3730))
end
| (FStar_Util.Inr (u), FStar_Util.Inl (n1)) -> begin
(

let uu____3747 = (sum_to_universe u n1)
in FStar_Util.Inr (uu____3747))
end
| (FStar_Util.Inr (u11), FStar_Util.Inr (u21)) -> begin
(

let uu____3763 = (

let uu____3769 = (

let uu____3771 = (FStar_Parser_AST.term_to_string t)
in (Prims.op_Hat "This universe might contain a sum of two universe variables " uu____3771))
in ((FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars), (uu____3769)))
in (FStar_Errors.raise_error uu____3763 t.FStar_Parser_AST.range))
end)))
end
| FStar_Parser_AST.App (uu____3780) -> begin
(

let rec aux = (fun t1 univargs -> (

let uu____3817 = (

let uu____3818 = (unparen t1)
in uu____3818.FStar_Parser_AST.tm)
in (match (uu____3817) with
| FStar_Parser_AST.App (t2, targ, uu____3826) -> begin
(

let uarg = (desugar_maybe_non_constant_universe targ)
in (aux t2 ((uarg)::univargs)))
end
| FStar_Parser_AST.Var (max_lid1) -> begin
(match ((FStar_List.existsb (fun uu___5_3853 -> (match (uu___5_3853) with
| FStar_Util.Inr (uu____3860) -> begin
true
end
| uu____3863 -> begin
false
end)) univargs)) with
| true -> begin
(

let uu____3871 = (

let uu____3872 = (FStar_List.map (fun uu___6_3882 -> (match (uu___6_3882) with
| FStar_Util.Inl (n1) -> begin
(int_to_universe n1)
end
| FStar_Util.Inr (u) -> begin
u
end)) univargs)
in FStar_Syntax_Syntax.U_max (uu____3872))
in FStar_Util.Inr (uu____3871))
end
| uu____3894 -> begin
(

let nargs = (FStar_List.map (fun uu___7_3908 -> (match (uu___7_3908) with
| FStar_Util.Inl (n1) -> begin
n1
end
| FStar_Util.Inr (uu____3918) -> begin
(failwith "impossible")
end)) univargs)
in (

let uu____3922 = (FStar_List.fold_left (fun m n1 -> (match ((m > n1)) with
| true -> begin
m
end
| uu____3934 -> begin
n1
end)) (Prims.parse_int "0") nargs)
in FStar_Util.Inl (uu____3922)))
end)
end
| uu____3938 -> begin
(

let uu____3939 = (

let uu____3945 = (

let uu____3947 = (

let uu____3949 = (FStar_Parser_AST.term_to_string t1)
in (Prims.op_Hat uu____3949 " in universe context"))
in (Prims.op_Hat "Unexpected term " uu____3947))
in ((FStar_Errors.Fatal_UnexpectedTermInUniverse), (uu____3945)))
in (FStar_Errors.raise_error uu____3939 t1.FStar_Parser_AST.range))
end)))
in (aux t []))
end
| uu____3964 -> begin
(

let uu____3965 = (

let uu____3971 = (

let uu____3973 = (

let uu____3975 = (FStar_Parser_AST.term_to_string t)
in (Prims.op_Hat uu____3975 " in universe context"))
in (Prims.op_Hat "Unexpected term " uu____3973))
in ((FStar_Errors.Fatal_UnexpectedTermInUniverse), (uu____3971)))
in (FStar_Errors.raise_error uu____3965 t.FStar_Parser_AST.range))
end)))


let desugar_universe : FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.universe = (fun t -> (

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
| ((bv, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_quoted (e, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = uu____4016}); FStar_Syntax_Syntax.pos = uu____4017; FStar_Syntax_Syntax.vars = uu____4018}))::uu____4019 -> begin
(

let uu____4050 = (

let uu____4056 = (

let uu____4058 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____4058))
in ((FStar_Errors.Fatal_UnexpectedAntiquotation), (uu____4056)))
in (FStar_Errors.raise_error uu____4050 e.FStar_Syntax_Syntax.pos))
end
| ((bv, e))::uu____4064 -> begin
(

let uu____4083 = (

let uu____4089 = (

let uu____4091 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____4091))
in ((FStar_Errors.Fatal_UnexpectedAntiquotation), (uu____4089)))
in (FStar_Errors.raise_error uu____4083 e.FStar_Syntax_Syntax.pos))
end))


let check_fields : 'Auu____4104 . FStar_Syntax_DsEnv.env  ->  (FStar_Ident.lident * 'Auu____4104) Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_DsEnv.record_or_dc = (fun env fields rg -> (

let uu____4132 = (FStar_List.hd fields)
in (match (uu____4132) with
| (f, uu____4142) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f);
(

let record = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f)
in (

let check_field = (fun uu____4154 -> (match (uu____4154) with
| (f', uu____4160) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f');
(

let uu____4162 = (FStar_Syntax_DsEnv.belongs_to_record env f' record)
in (match (uu____4162) with
| true -> begin
()
end
| uu____4165 -> begin
(

let msg = (FStar_Util.format3 "Field %s belongs to record type %s, whereas field %s does not" f.FStar_Ident.str record.FStar_Syntax_DsEnv.typename.FStar_Ident.str f'.FStar_Ident.str)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_FieldsNotBelongToSameRecordType), (msg)) rg))
end));
)
end))
in ((

let uu____4172 = (FStar_List.tl fields)
in (FStar_List.iter check_field uu____4172));
(match (()) with
| () -> begin
record
end);
)));
)
end)))


let rec desugar_data_pat : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * annotated_pat Prims.list) = (fun env p -> (

let check_linear_pattern_variables = (fun pats r -> (

let rec pat_vars = (fun p1 -> (match (p1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____4498) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_wild (uu____4505) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_constant (uu____4506) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (uu____4508, pats1) -> begin
(

let aux = (fun out uu____4549 -> (match (uu____4549) with
| (p2, uu____4562) -> begin
(

let intersection = (

let uu____4572 = (pat_vars p2)
in (FStar_Util.set_intersect uu____4572 out))
in (

let uu____4575 = (FStar_Util.set_is_empty intersection)
in (match (uu____4575) with
| true -> begin
(

let uu____4580 = (pat_vars p2)
in (FStar_Util.set_union out uu____4580))
end
| uu____4583 -> begin
(

let duplicate_bv = (

let uu____4586 = (FStar_Util.set_elements intersection)
in (FStar_List.hd uu____4586))
in (

let uu____4589 = (

let uu____4595 = (FStar_Util.format1 "Non-linear patterns are not permitted: `%s` appears more than once in this pattern." duplicate_bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in ((FStar_Errors.Fatal_NonLinearPatternNotPermitted), (uu____4595)))
in (FStar_Errors.raise_error uu____4589 r)))
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

let uu____4619 = (pat_vars p1)
in (FStar_All.pipe_right uu____4619 (fun a1 -> ())))
end
| (p1)::ps -> begin
(

let pvars = (pat_vars p1)
in (

let aux = (fun p2 -> (

let uu____4647 = (

let uu____4649 = (pat_vars p2)
in (FStar_Util.set_eq pvars uu____4649))
in (match (uu____4647) with
| true -> begin
()
end
| uu____4653 -> begin
(

let nonlinear_vars = (

let uu____4658 = (pat_vars p2)
in (FStar_Util.set_symmetric_difference pvars uu____4658))
in (

let first_nonlinear_var = (

let uu____4662 = (FStar_Util.set_elements nonlinear_vars)
in (FStar_List.hd uu____4662))
in (

let uu____4665 = (

let uu____4671 = (FStar_Util.format1 "Patterns in this match are incoherent, variable %s is bound in some but not all patterns." first_nonlinear_var.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in ((FStar_Errors.Fatal_IncoherentPatterns), (uu____4671)))
in (FStar_Errors.raise_error uu____4665 r))))
end)))
in (FStar_List.iter aux ps)))
end)))
in (

let resolvex = (fun l e x -> (

let uu____4699 = (FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (Prims.op_Equality y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText x.FStar_Ident.idText))))
in (match (uu____4699) with
| FStar_Pervasives_Native.Some (y) -> begin
((l), (e), (y))
end
| uu____4716 -> begin
(

let uu____4719 = (FStar_Syntax_DsEnv.push_bv e x)
in (match (uu____4719) with
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
| FStar_Parser_AST.PatOr (uu____4870) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.PatOp (op) -> begin
(

let uu____4894 = (

let uu____4895 = (

let uu____4896 = (

let uu____4903 = (

let uu____4904 = (

let uu____4910 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") op.FStar_Ident.idText op.FStar_Ident.idRange)
in ((uu____4910), (op.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____4904))
in ((uu____4903), (FStar_Pervasives_Native.None)))
in FStar_Parser_AST.PatVar (uu____4896))
in {FStar_Parser_AST.pat = uu____4895; FStar_Parser_AST.prange = p1.FStar_Parser_AST.prange})
in (aux loc env1 uu____4894))
end
| FStar_Parser_AST.PatAscribed (p2, (t, tacopt)) -> begin
((match (tacopt) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (uu____4930) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly), ("Type ascriptions within patterns cannot be associated with a tactic")) orig.FStar_Parser_AST.prange)
end);
(

let uu____4933 = (aux loc env1 p2)
in (match (uu____4933) with
| (loc1, env', binder, p3, annots, imp) -> begin
(

let annot_pat_var = (fun p4 t1 -> (match (p4.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu___933_5022 = p4
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var ((

let uu___935_5027 = x
in {FStar_Syntax_Syntax.ppname = uu___935_5027.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___935_5027.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})); FStar_Syntax_Syntax.p = uu___933_5022.FStar_Syntax_Syntax.p})
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu___939_5029 = p4
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild ((

let uu___941_5034 = x
in {FStar_Syntax_Syntax.ppname = uu___941_5034.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___941_5034.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})); FStar_Syntax_Syntax.p = uu___939_5029.FStar_Syntax_Syntax.p})
end
| uu____5035 when top -> begin
p4
end
| uu____5036 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly), ("Type ascriptions within patterns are only allowed on variables")) orig.FStar_Parser_AST.prange)
end))
in (

let uu____5041 = (match (binder) with
| LetBinder (uu____5062) -> begin
(failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t1 = (

let uu____5087 = (close_fun env1 t)
in (desugar_term env1 uu____5087))
in (

let x1 = (

let uu___952_5089 = x
in {FStar_Syntax_Syntax.ppname = uu___952_5089.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___952_5089.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (((((x1), (t1)))::[]), (LocalBinder (((x1), (aq)))))))
end)
in (match (uu____5041) with
| (annots', binder1) -> begin
((loc1), (env'), (binder1), (p3), ((FStar_List.append annots' annots)), (imp))
end)))
end));
)
end
| FStar_Parser_AST.PatWild (aq) -> begin
(

let imp = (Prims.op_Equality aq (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))
in (

let aq1 = (trans_aqual env1 aq)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____5157 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env1), (LocalBinder (((x), (aq1)))), (uu____5157), ([]), (imp))))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____5171 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____5171), ([]), (false))))
end
| FStar_Parser_AST.PatTvar (x, aq) -> begin
(

let imp = (Prims.op_Equality aq (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))
in (

let aq1 = (trans_aqual env1 aq)
in (

let uu____5195 = (resolvex loc env1 x)
in (match (uu____5195) with
| (loc1, env2, xbv) -> begin
(

let uu____5224 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc1), (env2), (LocalBinder (((xbv), (aq1)))), (uu____5224), ([]), (imp)))
end))))
end
| FStar_Parser_AST.PatVar (x, aq) -> begin
(

let imp = (Prims.op_Equality aq (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))
in (

let aq1 = (trans_aqual env1 aq)
in (

let uu____5247 = (resolvex loc env1 x)
in (match (uu____5247) with
| (loc1, env2, xbv) -> begin
(

let uu____5276 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc1), (env2), (LocalBinder (((xbv), (aq1)))), (uu____5276), ([]), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l1 = (FStar_Syntax_DsEnv.fail_or env1 (FStar_Syntax_DsEnv.try_lookup_datacon env1) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____5291 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), ([])))))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____5291), ([]), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = uu____5321}, args) -> begin
(

let uu____5327 = (FStar_List.fold_right (fun arg uu____5388 -> (match (uu____5388) with
| (loc1, env2, annots, args1) -> begin
(

let uu____5469 = (aux loc1 env2 arg)
in (match (uu____5469) with
| (loc2, env3, uu____5516, arg1, ans, imp) -> begin
((loc2), (env3), ((FStar_List.append ans annots)), ((((arg1), (imp)))::args1))
end))
end)) args ((loc), (env1), ([]), ([])))
in (match (uu____5327) with
| (loc1, env2, annots, args1) -> begin
(

let l1 = (FStar_Syntax_DsEnv.fail_or env2 (FStar_Syntax_DsEnv.try_lookup_datacon env2) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____5648 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args1)))))
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____5648), (annots), (false)))))
end))
end
| FStar_Parser_AST.PatApp (uu____5666) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedPattern), ("Unexpected pattern")) p1.FStar_Parser_AST.prange)
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____5697 = (FStar_List.fold_right (fun pat uu____5748 -> (match (uu____5748) with
| (loc1, env2, annots, pats1) -> begin
(

let uu____5809 = (aux loc1 env2 pat)
in (match (uu____5809) with
| (loc2, env3, uu____5851, pat1, ans, uu____5854) -> begin
((loc2), (env3), ((FStar_List.append ans annots)), ((pat1)::pats1))
end))
end)) pats ((loc), (env1), ([]), ([])))
in (match (uu____5697) with
| (loc1, env2, annots, pats1) -> begin
(

let pat = (

let uu____5951 = (

let uu____5954 = (

let uu____5961 = (FStar_Range.end_range p1.FStar_Parser_AST.prange)
in (pos_r uu____5961))
in (

let uu____5962 = (

let uu____5963 = (

let uu____5977 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.nil_lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____5977), ([])))
in FStar_Syntax_Syntax.Pat_cons (uu____5963))
in (FStar_All.pipe_left uu____5954 uu____5962)))
in (FStar_List.fold_right (fun hd1 tl1 -> (

let r = (FStar_Range.union_ranges hd1.FStar_Syntax_Syntax.p tl1.FStar_Syntax_Syntax.p)
in (

let uu____6011 = (

let uu____6012 = (

let uu____6026 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.cons_lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____6026), ((((hd1), (false)))::(((tl1), (false)))::[])))
in FStar_Syntax_Syntax.Pat_cons (uu____6012))
in (FStar_All.pipe_left (pos_r r) uu____6011)))) pats1 uu____5951))
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (pat), (annots), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep1) -> begin
(

let uu____6084 = (FStar_List.fold_left (fun uu____6144 p2 -> (match (uu____6144) with
| (loc1, env2, annots, pats) -> begin
(

let uu____6226 = (aux loc1 env2 p2)
in (match (uu____6226) with
| (loc2, env3, uu____6273, pat, ans, uu____6276) -> begin
((loc2), (env3), ((FStar_List.append ans annots)), ((((pat), (false)))::pats))
end))
end)) ((loc), (env1), ([]), ([])) args)
in (match (uu____6084) with
| (loc1, env2, annots, args1) -> begin
(

let args2 = (FStar_List.rev args1)
in (

let l = (match (dep1) with
| true -> begin
(FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end
| uu____6430 -> begin
(FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end)
in (

let constr = (FStar_Syntax_DsEnv.fail_or env2 (FStar_Syntax_DsEnv.try_lookup_lid env2) l)
in (

let l1 = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____6442 -> begin
(failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____6445 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args2)))))
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____6445), (annots), (false))))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedPattern), ("Unexpected pattern")) p1.FStar_Parser_AST.prange)
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(

let record = (check_fields env1 fields p1.FStar_Parser_AST.prange)
in (

let fields1 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____6526 -> (match (uu____6526) with
| (f, p2) -> begin
((f.FStar_Ident.ident), (p2))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map (fun uu____6556 -> (match (uu____6556) with
| (f, uu____6562) -> begin
(

let uu____6563 = (FStar_All.pipe_right fields1 (FStar_List.tryFind (fun uu____6589 -> (match (uu____6589) with
| (g, uu____6596) -> begin
(Prims.op_Equality f.FStar_Ident.idText g.FStar_Ident.idText)
end))))
in (match (uu____6563) with
| FStar_Pervasives_Native.None -> begin
(FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatWild (FStar_Pervasives_Native.None)) p1.FStar_Parser_AST.prange)
end
| FStar_Pervasives_Native.Some (uu____6602, p2) -> begin
p2
end))
end))))
in (

let app = (

let uu____6609 = (

let uu____6610 = (

let uu____6617 = (

let uu____6618 = (

let uu____6619 = (FStar_Ident.lid_of_ids (FStar_List.append record.FStar_Syntax_DsEnv.typename.FStar_Ident.ns ((record.FStar_Syntax_DsEnv.constrname)::[])))
in FStar_Parser_AST.PatName (uu____6619))
in (FStar_Parser_AST.mk_pattern uu____6618 p1.FStar_Parser_AST.prange))
in ((uu____6617), (args)))
in FStar_Parser_AST.PatApp (uu____6610))
in (FStar_Parser_AST.mk_pattern uu____6609 p1.FStar_Parser_AST.prange))
in (

let uu____6622 = (aux loc env1 app)
in (match (uu____6622) with
| (env2, e, b, p2, annots, uu____6668) -> begin
(

let p3 = (match (p2.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args1) -> begin
(

let uu____6708 = (

let uu____6709 = (

let uu____6723 = (

let uu___1100_6724 = fv
in (

let uu____6725 = (

let uu____6728 = (

let uu____6729 = (

let uu____6736 = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map FStar_Pervasives_Native.fst))
in ((record.FStar_Syntax_DsEnv.typename), (uu____6736)))
in FStar_Syntax_Syntax.Record_ctor (uu____6729))
in FStar_Pervasives_Native.Some (uu____6728))
in {FStar_Syntax_Syntax.fv_name = uu___1100_6724.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = uu___1100_6724.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu____6725}))
in ((uu____6723), (args1)))
in FStar_Syntax_Syntax.Pat_cons (uu____6709))
in (FStar_All.pipe_left pos uu____6708))
end
| uu____6762 -> begin
p2
end)
in ((env2), (e), (b), (p3), (annots), (false)))
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

let uu____6848 = (aux' true loc env1 p2)
in (match (uu____6848) with
| (loc1, env2, var, p3, ans, uu____6892) -> begin
(

let uu____6907 = (FStar_List.fold_left (fun uu____6956 p4 -> (match (uu____6956) with
| (loc2, env3, ps1) -> begin
(

let uu____7021 = (aux' true loc2 env3 p4)
in (match (uu____7021) with
| (loc3, env4, uu____7062, p5, ans1, uu____7065) -> begin
((loc3), (env4), ((((p5), (ans1)))::ps1))
end))
end)) ((loc1), (env2), ([])) ps)
in (match (uu____6907) with
| (loc2, env3, ps1) -> begin
(

let pats = (((p3), (ans)))::(FStar_List.rev ps1)
in ((env3), (var), (pats)))
end))
end))
end
| uu____7226 -> begin
(

let uu____7227 = (aux' true loc env1 p1)
in (match (uu____7227) with
| (loc1, env2, vars, pat, ans, b) -> begin
((env2), (vars), ((((pat), (ans)))::[]))
end))
end)))
in (

let uu____7324 = (aux_maybe_or env p)
in (match (uu____7324) with
| (env1, b, pats) -> begin
((

let uu____7379 = (FStar_List.map FStar_Pervasives_Native.fst pats)
in (check_linear_pattern_variables uu____7379 p.FStar_Parser_AST.prange));
((env1), (b), (pats));
)
end)))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * annotated_pat Prims.list) = (fun top env p -> (

let mklet = (fun x ty tacopt -> (

let uu____7452 = (

let uu____7453 = (

let uu____7464 = (FStar_Syntax_DsEnv.qualify env x)
in ((uu____7464), (((ty), (tacopt)))))
in LetBinder (uu____7453))
in ((env), (uu____7452), ([]))))
in (

let op_to_ident = (fun x -> (

let uu____7481 = (

let uu____7487 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") x.FStar_Ident.idText x.FStar_Ident.idRange)
in ((uu____7487), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____7481)))
in (match (top) with
| true -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(

let uu____7509 = (op_to_ident x)
in (mklet uu____7509 FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None))
end
| FStar_Parser_AST.PatVar (x, uu____7511) -> begin
(mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatOp (x); FStar_Parser_AST.prange = uu____7517}, (t, tacopt)) -> begin
(

let tacopt1 = (FStar_Util.map_opt tacopt (desugar_term env))
in (

let uu____7533 = (op_to_ident x)
in (

let uu____7534 = (desugar_term env t)
in (mklet uu____7533 uu____7534 tacopt1))))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____7536); FStar_Parser_AST.prange = uu____7537}, (t, tacopt)) -> begin
(

let tacopt1 = (FStar_Util.map_opt tacopt (desugar_term env))
in (

let uu____7557 = (desugar_term env t)
in (mklet x uu____7557 tacopt1)))
end
| uu____7558 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedPattern), ("Unexpected pattern at the top-level")) p.FStar_Parser_AST.prange)
end)
end
| uu____7569 -> begin
(

let uu____7571 = (desugar_data_pat env p)
in (match (uu____7571) with
| (env1, binder, p1) -> begin
(

let p2 = (match (p1) with
| (({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (uu____7600); FStar_Syntax_Syntax.p = uu____7601}, uu____7602))::[] -> begin
[]
end
| (({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (uu____7615); FStar_Syntax_Syntax.p = uu____7616}, uu____7617))::[] -> begin
[]
end
| uu____7630 -> begin
p1
end)
in ((env1), (binder), (p2)))
end))
end))))
and desugar_binding_pat : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * annotated_pat Prims.list) = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * annotated_pat Prims.list) = (fun uu____7638 env pat -> (

let uu____7642 = (desugar_data_pat env pat)
in (match (uu____7642) with
| (env1, uu____7658, pat1) -> begin
((env1), (pat1))
end)))
and desugar_match_pat : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * annotated_pat Prims.list) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term_aq : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations) = (fun env e -> (

let env1 = (FStar_Syntax_DsEnv.set_expect_typ env false)
in (desugar_term_maybe_top false env1 e)))
and desugar_term : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let uu____7680 = (desugar_term_aq env e)
in (match (uu____7680) with
| (t, aq) -> begin
((check_no_aq aq);
t;
)
end)))
and desugar_typ_aq : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations) = (fun env e -> (

let env1 = (FStar_Syntax_DsEnv.set_expect_typ env true)
in (desugar_term_maybe_top false env1 e)))
and desugar_typ : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let uu____7699 = (desugar_typ_aq env e)
in (match (uu____7699) with
| (t, aq) -> begin
((check_no_aq aq);
t;
)
end)))
and desugar_machine_integer : FStar_Syntax_DsEnv.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun env repr uu____7709 range -> (match (uu____7709) with
| (signedness, width) -> begin
(

let tnm = (Prims.op_Hat "FStar." (Prims.op_Hat (match (signedness) with
| FStar_Const.Unsigned -> begin
"U"
end
| FStar_Const.Signed -> begin
""
end) (Prims.op_Hat "Int" (match (width) with
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

let uu____7731 = (

let uu____7733 = (FStar_Const.within_bounds repr signedness width)
in (not (uu____7733)))
in (match (uu____7731) with
| true -> begin
(

let uu____7736 = (

let uu____7742 = (FStar_Util.format2 "%s is not in the expected range for %s" repr tnm)
in ((FStar_Errors.Error_OutOfRange), (uu____7742)))
in (FStar_Errors.log_issue range uu____7736))
end
| uu____7746 -> begin
()
end));
(

let private_intro_nm = (Prims.op_Hat tnm (Prims.op_Hat ".__" (Prims.op_Hat (match (signedness) with
| FStar_Const.Unsigned -> begin
"u"
end
| FStar_Const.Signed -> begin
""
end) "int_to_t")))
in (

let intro_nm = (Prims.op_Hat tnm (Prims.op_Hat "." (Prims.op_Hat (match (signedness) with
| FStar_Const.Unsigned -> begin
"u"
end
| FStar_Const.Signed -> begin
""
end) "int_to_t")))
in (

let lid = (

let uu____7763 = (FStar_Ident.path_of_text intro_nm)
in (FStar_Ident.lid_of_path uu____7763 range))
in (

let lid1 = (

let uu____7767 = (FStar_Syntax_DsEnv.try_lookup_lid env lid)
in (match (uu____7767) with
| FStar_Pervasives_Native.Some (intro_term) -> begin
(match (intro_term.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let private_lid = (

let uu____7777 = (FStar_Ident.path_of_text private_intro_nm)
in (FStar_Ident.lid_of_path uu____7777 range))
in (

let private_fv = (

let uu____7779 = (FStar_Syntax_Util.incr_delta_depth fv.FStar_Syntax_Syntax.fv_delta)
in (FStar_Syntax_Syntax.lid_as_fv private_lid uu____7779 fv.FStar_Syntax_Syntax.fv_qual))
in (

let uu___1270_7780 = intro_term
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (private_fv); FStar_Syntax_Syntax.pos = uu___1270_7780.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___1270_7780.FStar_Syntax_Syntax.vars})))
end
| uu____7781 -> begin
(failwith (Prims.op_Hat "Unexpected non-fvar for " intro_nm))
end)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____7785 = (

let uu____7791 = (FStar_Util.format1 "Unexpected numeric literal.  Restart F* to load %s." tnm)
in ((FStar_Errors.Fatal_UnexpectedNumericLiteral), (uu____7791)))
in (FStar_Errors.raise_error uu____7785 range))
end))
in (

let repr1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (FStar_Pervasives_Native.None))))) FStar_Pervasives_Native.None range)
in (

let uu____7811 = (

let uu____7818 = (

let uu____7819 = (

let uu____7836 = (

let uu____7847 = (

let uu____7856 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr1), (uu____7856)))
in (uu____7847)::[])
in ((lid1), (uu____7836)))
in FStar_Syntax_Syntax.Tm_app (uu____7819))
in (FStar_Syntax_Syntax.mk uu____7818))
in (uu____7811 FStar_Pervasives_Native.None range)))))));
))
end))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations) = (fun top_level env top -> (

let mk1 = (fun e -> (FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
in (

let noaqs = []
in (

let join_aqs = (fun aqs -> (FStar_List.flatten aqs))
in (

let setpos = (fun e -> (

let uu___1286_7975 = e
in {FStar_Syntax_Syntax.n = uu___1286_7975.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___1286_7975.FStar_Syntax_Syntax.vars}))
in (

let uu____7978 = (

let uu____7979 = (unparen top)
in uu____7979.FStar_Parser_AST.tm)
in (match (uu____7978) with
| FStar_Parser_AST.Wild -> begin
(((setpos FStar_Syntax_Syntax.tun)), (noaqs))
end
| FStar_Parser_AST.Labeled (uu____7984) -> begin
(

let uu____7993 = (desugar_formula env top)
in ((uu____7993), (noaqs)))
end
| FStar_Parser_AST.Requires (t, lopt) -> begin
(

let uu____8002 = (desugar_formula env t)
in ((uu____8002), (noaqs)))
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(

let uu____8011 = (desugar_formula env t)
in ((uu____8011), (noaqs)))
end
| FStar_Parser_AST.Attributes (ts) -> begin
(failwith "Attributes should not be desugared by desugar_term_maybe_top")
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (i, FStar_Pervasives_Native.Some (size))) -> begin
(

let uu____8038 = (desugar_machine_integer env i size top.FStar_Parser_AST.range)
in ((uu____8038), (noaqs)))
end
| FStar_Parser_AST.Const (c) -> begin
(

let uu____8040 = (mk1 (FStar_Syntax_Syntax.Tm_constant (c)))
in ((uu____8040), (noaqs)))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "=!="; FStar_Ident.idRange = r}, args) -> begin
(

let e = (

let uu____8049 = (

let uu____8050 = (

let uu____8057 = (FStar_Ident.mk_ident (("=="), (r)))
in ((uu____8057), (args)))
in FStar_Parser_AST.Op (uu____8050))
in (FStar_Parser_AST.mk_term uu____8049 top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
in (

let uu____8062 = (

let uu____8063 = (

let uu____8064 = (

let uu____8071 = (FStar_Ident.mk_ident (("~"), (r)))
in ((uu____8071), ((e)::[])))
in FStar_Parser_AST.Op (uu____8064))
in (FStar_Parser_AST.mk_term uu____8063 top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
in (desugar_term_aq env uu____8062)))
end
| FStar_Parser_AST.Op (op_star, (lhs)::(rhs)::[]) when ((

let uu____8083 = (FStar_Ident.text_of_id op_star)
in (Prims.op_Equality uu____8083 "*")) && (

let uu____8088 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range op_star)
in (FStar_All.pipe_right uu____8088 FStar_Option.isNone))) -> begin
(

let rec flatten1 = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____8105}, (t1)::(t2)::[]) when (

let uu____8111 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range op_star)
in (FStar_All.pipe_right uu____8111 FStar_Option.isNone)) -> begin
(

let uu____8118 = (flatten1 t1)
in (FStar_List.append uu____8118 ((t2)::[])))
end
| uu____8121 -> begin
(t)::[]
end))
in (

let terms = (flatten1 lhs)
in (

let t = (

let uu___1334_8126 = top
in (

let uu____8127 = (

let uu____8128 = (

let uu____8139 = (FStar_List.map (fun _8150 -> FStar_Util.Inr (_8150)) terms)
in ((uu____8139), (rhs)))
in FStar_Parser_AST.Sum (uu____8128))
in {FStar_Parser_AST.tm = uu____8127; FStar_Parser_AST.range = uu___1334_8126.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___1334_8126.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env t))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____8158 = (

let uu____8159 = (FStar_Syntax_DsEnv.fail_or2 (FStar_Syntax_DsEnv.try_lookup_id env) a)
in (FStar_All.pipe_left setpos uu____8159))
in ((uu____8158), (noaqs)))
end
| FStar_Parser_AST.Uvar (u) -> begin
(

let uu____8165 = (

let uu____8171 = (

let uu____8173 = (

let uu____8175 = (FStar_Ident.text_of_id u)
in (Prims.op_Hat uu____8175 " in non-universe context"))
in (Prims.op_Hat "Unexpected universe variable " uu____8173))
in ((FStar_Errors.Fatal_UnexpectedUniverseVariable), (uu____8171)))
in (FStar_Errors.raise_error uu____8165 top.FStar_Parser_AST.range))
end
| FStar_Parser_AST.Op (s, args) -> begin
(

let uu____8190 = (op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)
in (match (uu____8190) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8197 = (

let uu____8203 = (

let uu____8205 = (FStar_Ident.text_of_id s)
in (Prims.op_Hat "Unexpected or unbound operator: " uu____8205))
in ((FStar_Errors.Fatal_UnepxectedOrUnboundOperator), (uu____8203)))
in (FStar_Errors.raise_error uu____8197 top.FStar_Parser_AST.range))
end
| FStar_Pervasives_Native.Some (op) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____8220 = (

let uu____8245 = (FStar_All.pipe_right args (FStar_List.map (fun t -> (

let uu____8307 = (desugar_term_aq env t)
in (match (uu____8307) with
| (t', s1) -> begin
((((t'), (FStar_Pervasives_Native.None))), (s1))
end)))))
in (FStar_All.pipe_right uu____8245 FStar_List.unzip))
in (match (uu____8220) with
| (args1, aqs) -> begin
(

let uu____8440 = (mk1 (FStar_Syntax_Syntax.Tm_app (((op), (args1)))))
in ((uu____8440), ((join_aqs aqs))))
end))
end
| uu____8453 -> begin
((op), (noaqs))
end)
end))
end
| FStar_Parser_AST.Construct (n1, ((a, uu____8457))::[]) when (Prims.op_Equality n1.FStar_Ident.str "SMTPat") -> begin
(

let uu____8474 = (

let uu___1363_8475 = top
in (

let uu____8476 = (

let uu____8477 = (

let uu____8484 = (

let uu___1365_8485 = top
in (

let uu____8486 = (

let uu____8487 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____8487))
in {FStar_Parser_AST.tm = uu____8486; FStar_Parser_AST.range = uu___1365_8485.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___1365_8485.FStar_Parser_AST.level}))
in ((uu____8484), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____8477))
in {FStar_Parser_AST.tm = uu____8476; FStar_Parser_AST.range = uu___1363_8475.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___1363_8475.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____8474))
end
| FStar_Parser_AST.Construct (n1, ((a, uu____8495))::[]) when (Prims.op_Equality n1.FStar_Ident.str "SMTPatT") -> begin
((FStar_Errors.log_issue top.FStar_Parser_AST.range ((FStar_Errors.Warning_SMTPatTDeprecated), ("SMTPatT is deprecated; please just use SMTPat")));
(

let uu____8515 = (

let uu___1375_8516 = top
in (

let uu____8517 = (

let uu____8518 = (

let uu____8525 = (

let uu___1377_8526 = top
in (

let uu____8527 = (

let uu____8528 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____8528))
in {FStar_Parser_AST.tm = uu____8527; FStar_Parser_AST.range = uu___1377_8526.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___1377_8526.FStar_Parser_AST.level}))
in ((uu____8525), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____8518))
in {FStar_Parser_AST.tm = uu____8517; FStar_Parser_AST.range = uu___1375_8516.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___1375_8516.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____8515));
)
end
| FStar_Parser_AST.Construct (n1, ((a, uu____8536))::[]) when (Prims.op_Equality n1.FStar_Ident.str "SMTPatOr") -> begin
(

let uu____8553 = (

let uu___1386_8554 = top
in (

let uu____8555 = (

let uu____8556 = (

let uu____8563 = (

let uu___1388_8564 = top
in (

let uu____8565 = (

let uu____8566 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat_or")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____8566))
in {FStar_Parser_AST.tm = uu____8565; FStar_Parser_AST.range = uu___1388_8564.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___1388_8564.FStar_Parser_AST.level}))
in ((uu____8563), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____8556))
in {FStar_Parser_AST.tm = uu____8555; FStar_Parser_AST.range = uu___1386_8554.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___1386_8554.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____8553))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____8572; FStar_Ident.ident = uu____8573; FStar_Ident.nsstr = uu____8574; FStar_Ident.str = "Type0"}) -> begin
(

let uu____8579 = (mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
in ((uu____8579), (noaqs)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____8580; FStar_Ident.ident = uu____8581; FStar_Ident.nsstr = uu____8582; FStar_Ident.str = "Type"}) -> begin
(

let uu____8587 = (mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
in ((uu____8587), (noaqs)))
end
| FStar_Parser_AST.Construct ({FStar_Ident.ns = uu____8588; FStar_Ident.ident = uu____8589; FStar_Ident.nsstr = uu____8590; FStar_Ident.str = "Type"}, ((t, FStar_Parser_AST.UnivApp))::[]) -> begin
(

let uu____8610 = (

let uu____8611 = (

let uu____8612 = (desugar_universe t)
in FStar_Syntax_Syntax.Tm_type (uu____8612))
in (mk1 uu____8611))
in ((uu____8610), (noaqs)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____8613; FStar_Ident.ident = uu____8614; FStar_Ident.nsstr = uu____8615; FStar_Ident.str = "Effect"}) -> begin
(

let uu____8620 = (mk1 (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
in ((uu____8620), (noaqs)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____8621; FStar_Ident.ident = uu____8622; FStar_Ident.nsstr = uu____8623; FStar_Ident.str = "True"}) -> begin
(

let uu____8628 = (

let uu____8629 = (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar uu____8629 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))
in ((uu____8628), (noaqs)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____8630; FStar_Ident.ident = uu____8631; FStar_Ident.nsstr = uu____8632; FStar_Ident.str = "False"}) -> begin
(

let uu____8637 = (

let uu____8638 = (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar uu____8638 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))
in ((uu____8637), (noaqs)))
end
| FStar_Parser_AST.Projector (eff_name, {FStar_Ident.idText = txt; FStar_Ident.idRange = uu____8641}) when ((is_special_effect_combinator txt) && (FStar_Syntax_DsEnv.is_effect_name env eff_name)) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name);
(

let uu____8644 = (FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name)
in (match (uu____8644) with
| FStar_Pervasives_Native.Some (ed) -> begin
(

let lid = (FStar_Syntax_Util.dm4f_lid ed txt)
in (

let uu____8653 = (FStar_Syntax_Syntax.fvar lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in ((uu____8653), (noaqs))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8655 = (

let uu____8657 = (FStar_Ident.text_of_lid eff_name)
in (FStar_Util.format2 "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)" uu____8657 txt))
in (failwith uu____8655))
end));
)
end
| FStar_Parser_AST.Var (l) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l);
(

let uu____8666 = (desugar_name mk1 setpos env true l)
in ((uu____8666), (noaqs)));
)
end
| FStar_Parser_AST.Name (l) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l);
(

let uu____8675 = (desugar_name mk1 setpos env true l)
in ((uu____8675), (noaqs)));
)
end
| FStar_Parser_AST.Projector (l, i) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l);
(

let name = (

let uu____8693 = (FStar_Syntax_DsEnv.try_lookup_datacon env l)
in (match (uu____8693) with
| FStar_Pervasives_Native.Some (uu____8703) -> begin
FStar_Pervasives_Native.Some (((true), (l)))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____8711 = (FStar_Syntax_DsEnv.try_lookup_root_effect_name env l)
in (match (uu____8711) with
| FStar_Pervasives_Native.Some (new_name) -> begin
FStar_Pervasives_Native.Some (((false), (new_name)))
end
| uu____8729 -> begin
FStar_Pervasives_Native.None
end))
end))
in (match (name) with
| FStar_Pervasives_Native.Some (resolve, new_name) -> begin
(

let uu____8750 = (

let uu____8751 = (FStar_Syntax_Util.mk_field_projector_name_from_ident new_name i)
in (desugar_name mk1 setpos env resolve uu____8751))
in ((uu____8750), (noaqs)))
end
| uu____8757 -> begin
(

let uu____8765 = (

let uu____8771 = (FStar_Util.format1 "Data constructor or effect %s not found" l.FStar_Ident.str)
in ((FStar_Errors.Fatal_EffectNotFound), (uu____8771)))
in (FStar_Errors.raise_error uu____8765 top.FStar_Parser_AST.range))
end));
)
end
| FStar_Parser_AST.Discrim (lid) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid);
(

let uu____8781 = (FStar_Syntax_DsEnv.try_lookup_datacon env lid)
in (match (uu____8781) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8788 = (

let uu____8794 = (FStar_Util.format1 "Data constructor %s not found" lid.FStar_Ident.str)
in ((FStar_Errors.Fatal_DataContructorNotFound), (uu____8794)))
in (FStar_Errors.raise_error uu____8788 top.FStar_Parser_AST.range))
end
| uu____8802 -> begin
(

let lid' = (FStar_Syntax_Util.mk_discriminator lid)
in (

let uu____8806 = (desugar_name mk1 setpos env true lid')
in ((uu____8806), (noaqs))))
end));
)
end
| FStar_Parser_AST.Construct (l, args) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l);
(

let uu____8828 = (FStar_Syntax_DsEnv.try_lookup_datacon env l)
in (match (uu____8828) with
| FStar_Pervasives_Native.Some (head1) -> begin
(

let head2 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (head1)))
in (match (args) with
| [] -> begin
((head2), (noaqs))
end
| uu____8847 -> begin
(

let uu____8854 = (FStar_Util.take (fun uu____8878 -> (match (uu____8878) with
| (uu____8884, imp) -> begin
(Prims.op_Equality imp FStar_Parser_AST.UnivApp)
end)) args)
in (match (uu____8854) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun x -> (desugar_universe (FStar_Pervasives_Native.fst x))) universes)
in (

let uu____8929 = (

let uu____8954 = (FStar_List.map (fun uu____8997 -> (match (uu____8997) with
| (t, imp) -> begin
(

let uu____9014 = (desugar_term_aq env t)
in (match (uu____9014) with
| (te, aq) -> begin
(((arg_withimp_e imp te)), (aq))
end))
end)) args1)
in (FStar_All.pipe_right uu____8954 FStar_List.unzip))
in (match (uu____8929) with
| (args2, aqs) -> begin
(

let head3 = (match ((Prims.op_Equality universes1 [])) with
| true -> begin
head2
end
| uu____9153 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_uinst (((head2), (universes1)))))
end)
in (

let uu____9157 = (mk1 (FStar_Syntax_Syntax.Tm_app (((head3), (args2)))))
in ((uu____9157), ((join_aqs aqs)))))
end)))
end))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let err = (

let uu____9176 = (FStar_Syntax_DsEnv.try_lookup_effect_name env l)
in (match (uu____9176) with
| FStar_Pervasives_Native.None -> begin
((FStar_Errors.Fatal_ConstructorNotFound), ((Prims.op_Hat "Constructor " (Prims.op_Hat l.FStar_Ident.str " not found"))))
end
| FStar_Pervasives_Native.Some (uu____9187) -> begin
((FStar_Errors.Fatal_UnexpectedEffect), ((Prims.op_Hat "Effect " (Prims.op_Hat l.FStar_Ident.str " used at an unexpected position"))))
end))
in (FStar_Errors.raise_error err top.FStar_Parser_AST.range))
end));
)
end
| FStar_Parser_AST.Sum (binders, t) when (FStar_Util.for_all (fun uu___8_9215 -> (match (uu___8_9215) with
| FStar_Util.Inr (uu____9221) -> begin
true
end
| uu____9223 -> begin
false
end)) binders) -> begin
(

let terms = (

let uu____9232 = (FStar_All.pipe_right binders (FStar_List.map (fun uu___9_9249 -> (match (uu___9_9249) with
| FStar_Util.Inr (x) -> begin
x
end
| FStar_Util.Inl (uu____9255) -> begin
(failwith "Impossible")
end))))
in (FStar_List.append uu____9232 ((t)::[])))
in (

let uu____9257 = (

let uu____9282 = (FStar_All.pipe_right terms (FStar_List.map (fun t1 -> (

let uu____9339 = (desugar_typ_aq env t1)
in (match (uu____9339) with
| (t', aq) -> begin
(

let uu____9350 = (FStar_Syntax_Syntax.as_arg t')
in ((uu____9350), (aq)))
end)))))
in (FStar_All.pipe_right uu____9282 FStar_List.unzip))
in (match (uu____9257) with
| (targs, aqs) -> begin
(

let tup = (

let uu____9460 = (FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_lid env) uu____9460))
in (

let uu____9469 = (mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
in ((uu____9469), ((join_aqs aqs)))))
end)))
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let uu____9496 = (

let uu____9513 = (

let uu____9520 = (

let uu____9527 = (FStar_All.pipe_left (fun _9536 -> FStar_Util.Inl (_9536)) (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type_level FStar_Pervasives_Native.None))
in (uu____9527)::[])
in (FStar_List.append binders uu____9520))
in (FStar_List.fold_left (fun uu____9581 b -> (match (uu____9581) with
| (env1, tparams, typs) -> begin
(

let uu____9642 = (match (b) with
| FStar_Util.Inl (b1) -> begin
(desugar_binder env1 b1)
end
| FStar_Util.Inr (t1) -> begin
(

let uu____9657 = (desugar_typ env1 t1)
in ((FStar_Pervasives_Native.None), (uu____9657)))
end)
in (match (uu____9642) with
| (xopt, t1) -> begin
(

let uu____9682 = (match (xopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____9691 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env1), (uu____9691)))
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_DsEnv.push_bv env1 x)
end)
in (match (uu____9682) with
| (env2, x) -> begin
(

let uu____9711 = (

let uu____9714 = (

let uu____9717 = (

let uu____9718 = (no_annot_abs tparams t1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____9718))
in (uu____9717)::[])
in (FStar_List.append typs uu____9714))
in ((env2), ((FStar_List.append tparams (((((

let uu___1547_9744 = x
in {FStar_Syntax_Syntax.ppname = uu___1547_9744.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___1547_9744.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})), (FStar_Pervasives_Native.None)))::[]))), (uu____9711)))
end))
end))
end)) ((env), ([]), ([])) uu____9513))
in (match (uu____9496) with
| (env1, uu____9772, targs) -> begin
(

let tup = (

let uu____9795 = (FStar_Parser_Const.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Syntax_DsEnv.fail_or env1 (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____9795))
in (

let uu____9796 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
in ((uu____9796), (noaqs))))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let uu____9815 = (uncurry binders t)
in (match (uu____9815) with
| (bs, t1) -> begin
(

let rec aux = (fun env1 bs1 uu___10_9859 -> (match (uu___10_9859) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range true env1 t1)
in (

let uu____9876 = (FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod)
in (FStar_All.pipe_left setpos uu____9876)))
end
| (hd1)::tl1 -> begin
(

let bb = (desugar_binder env1 hd1)
in (

let uu____9900 = (as_binder env1 hd1.FStar_Parser_AST.aqual bb)
in (match (uu____9900) with
| (b, env2) -> begin
(aux env2 ((b)::bs1) tl1)
end)))
end))
in (

let uu____9933 = (aux env [] bs)
in ((uu____9933), (noaqs))))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(

let uu____9942 = (desugar_binder env b)
in (match (uu____9942) with
| (FStar_Pervasives_Native.None, uu____9953) -> begin
(failwith "Missing binder in refinement")
end
| b1 -> begin
(

let uu____9968 = (as_binder env FStar_Pervasives_Native.None b1)
in (match (uu____9968) with
| ((x, uu____9984), env1) -> begin
(

let f1 = (desugar_formula env1 f)
in (

let uu____9997 = (

let uu____9998 = (FStar_Syntax_Util.refine x f1)
in (FStar_All.pipe_left setpos uu____9998))
in ((uu____9997), (noaqs))))
end))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let bvss = (FStar_List.map (gather_pattern_bound_vars false) binders)
in (

let check_disjoint = (fun sets -> (

let rec aux = (fun acc sets1 -> (match (sets1) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (set1)::sets2 -> begin
(

let i = (FStar_Util.set_intersect acc set1)
in (

let uu____10077 = (FStar_Util.set_is_empty i)
in (match (uu____10077) with
| true -> begin
(

let uu____10082 = (FStar_Util.set_union acc set1)
in (aux uu____10082 sets2))
end
| uu____10085 -> begin
(

let uu____10087 = (

let uu____10088 = (FStar_Util.set_elements i)
in (FStar_List.hd uu____10088))
in FStar_Pervasives_Native.Some (uu____10087))
end)))
end))
in (

let uu____10091 = (FStar_Syntax_Syntax.new_id_set ())
in (aux uu____10091 sets))))
in ((

let uu____10095 = (check_disjoint bvss)
in (match (uu____10095) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (id1) -> begin
(

let uu____10099 = (

let uu____10105 = (FStar_Util.format1 "Non-linear patterns are not permitted: `%s` appears more than once in this function definition." id1.FStar_Ident.idText)
in ((FStar_Errors.Fatal_NonLinearPatternNotPermitted), (uu____10105)))
in (

let uu____10109 = (FStar_Ident.range_of_id id1)
in (FStar_Errors.raise_error uu____10099 uu____10109)))
end));
(

let binders1 = (FStar_All.pipe_right binders (FStar_List.map replace_unit_pattern))
in (

let uu____10117 = (FStar_List.fold_left (fun uu____10137 pat -> (match (uu____10137) with
| (env1, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (uu____10163, (t, FStar_Pervasives_Native.None)) -> begin
(

let uu____10173 = (

let uu____10176 = (free_type_vars env1 t)
in (FStar_List.append uu____10176 ftvs))
in ((env1), (uu____10173)))
end
| FStar_Parser_AST.PatAscribed (uu____10181, (t, FStar_Pervasives_Native.Some (tac))) -> begin
(

let uu____10192 = (

let uu____10195 = (free_type_vars env1 t)
in (

let uu____10198 = (

let uu____10201 = (free_type_vars env1 tac)
in (FStar_List.append uu____10201 ftvs))
in (FStar_List.append uu____10195 uu____10198)))
in ((env1), (uu____10192)))
end
| uu____10206 -> begin
((env1), (ftvs))
end)
end)) ((env), ([])) binders1)
in (match (uu____10117) with
| (uu____10215, ftv) -> begin
(

let ftv1 = (sort_ftv ftv)
in (

let binders2 = (

let uu____10227 = (FStar_All.pipe_right ftv1 (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append uu____10227 binders1))
in (

let rec aux = (fun env1 bs sc_pat_opt uu___11_10284 -> (match (uu___11_10284) with
| [] -> begin
(

let uu____10311 = (desugar_term_aq env1 body)
in (match (uu____10311) with
| (body1, aq) -> begin
(

let body2 = (match (sc_pat_opt) with
| FStar_Pervasives_Native.Some (sc, pat) -> begin
(

let body2 = (

let uu____10348 = (

let uu____10349 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right uu____10349 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close uu____10348 body1))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (FStar_Pervasives_Native.None), (body2)))::[])))) FStar_Pervasives_Native.None body2.FStar_Syntax_Syntax.pos))
end
| FStar_Pervasives_Native.None -> begin
body1
end)
in (

let uu____10418 = (

let uu____10421 = (no_annot_abs (FStar_List.rev bs) body2)
in (setpos uu____10421))
in ((uu____10418), (aq))))
end))
end
| (p)::rest -> begin
(

let uu____10436 = (desugar_binding_pat env1 p)
in (match (uu____10436) with
| (env2, b, pat) -> begin
(

let pat1 = (match (pat) with
| [] -> begin
FStar_Pervasives_Native.None
end
| ((p1, uu____10470))::[] -> begin
FStar_Pervasives_Native.Some (p1)
end
| uu____10485 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnsupportedDisjuctivePatterns), ("Disjunctive patterns are not supported in abstractions")) p.FStar_Parser_AST.prange)
end)
in (

let uu____10494 = (match (b) with
| LetBinder (uu____10535) -> begin
(failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt1 = (match (((pat1), (sc_pat_opt))) with
| (FStar_Pervasives_Native.None, uu____10604) -> begin
sc_pat_opt
end
| (FStar_Pervasives_Native.Some (p1), FStar_Pervasives_Native.None) -> begin
(

let uu____10658 = (

let uu____10667 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____10667), (p1)))
in FStar_Pervasives_Native.Some (uu____10658))
end
| (FStar_Pervasives_Native.Some (p1), FStar_Pervasives_Native.Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (uu____10729), uu____10730) -> begin
(

let tup2 = (

let uu____10732 = (FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____10732 FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____10737 = (

let uu____10744 = (

let uu____10745 = (

let uu____10762 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (

let uu____10765 = (

let uu____10776 = (FStar_Syntax_Syntax.as_arg sc)
in (

let uu____10785 = (

let uu____10796 = (

let uu____10805 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____10805))
in (uu____10796)::[])
in (uu____10776)::uu____10785))
in ((uu____10762), (uu____10765))))
in FStar_Syntax_Syntax.Tm_app (uu____10745))
in (FStar_Syntax_Syntax.mk uu____10744))
in (uu____10737 FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
in (

let p2 = (

let uu____10853 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p1), (false)))::[])))) uu____10853))
in FStar_Pervasives_Native.Some (((sc1), (p2))))))
end
| (FStar_Syntax_Syntax.Tm_app (uu____10904, args), FStar_Syntax_Syntax.Pat_cons (uu____10906, pats)) -> begin
(

let tupn = (

let uu____10951 = (FStar_Parser_Const.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____10951 FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____10964 = (

let uu____10965 = (

let uu____10982 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (

let uu____10985 = (

let uu____10996 = (

let uu____11007 = (

let uu____11016 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____11016))
in (uu____11007)::[])
in (FStar_List.append args uu____10996))
in ((uu____10982), (uu____10985))))
in FStar_Syntax_Syntax.Tm_app (uu____10965))
in (mk1 uu____10964))
in (

let p2 = (

let uu____11064 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p1), (false)))::[])))))) uu____11064))
in FStar_Pervasives_Native.Some (((sc1), (p2))))))
end
| uu____11111 -> begin
(failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt1)))
end)
in (match (uu____10494) with
| (b1, sc_pat_opt1) -> begin
(aux env2 ((b1)::bs) sc_pat_opt1 rest)
end)))
end))
end))
in (aux env [] FStar_Pervasives_Native.None binders2))))
end)));
)))
end
| FStar_Parser_AST.App (uu____11205, uu____11206, FStar_Parser_AST.UnivApp) -> begin
(

let rec aux = (fun universes e -> (

let uu____11228 = (

let uu____11229 = (unparen e)
in uu____11229.FStar_Parser_AST.tm)
in (match (uu____11228) with
| FStar_Parser_AST.App (e1, t, FStar_Parser_AST.UnivApp) -> begin
(

let univ_arg = (desugar_universe t)
in (aux ((univ_arg)::universes) e1))
end
| uu____11239 -> begin
(

let uu____11240 = (desugar_term_aq env e)
in (match (uu____11240) with
| (head1, aq) -> begin
(

let uu____11253 = (mk1 (FStar_Syntax_Syntax.Tm_uinst (((head1), (universes)))))
in ((uu____11253), (aq)))
end))
end)))
in (aux [] top))
end
| FStar_Parser_AST.App (uu____11260) -> begin
(

let rec aux = (fun args aqs e -> (

let uu____11337 = (

let uu____11338 = (unparen e)
in uu____11338.FStar_Parser_AST.tm)
in (match (uu____11337) with
| FStar_Parser_AST.App (e1, t, imp) when (Prims.op_disEquality imp FStar_Parser_AST.UnivApp) -> begin
(

let uu____11356 = (desugar_term_aq env t)
in (match (uu____11356) with
| (t1, aq) -> begin
(

let arg = (arg_withimp_e imp t1)
in (aux ((arg)::args) ((aq)::aqs) e1))
end))
end
| uu____11404 -> begin
(

let uu____11405 = (desugar_term_aq env e)
in (match (uu____11405) with
| (head1, aq) -> begin
(

let uu____11426 = (mk1 (FStar_Syntax_Syntax.Tm_app (((head1), (args)))))
in ((uu____11426), ((join_aqs ((aq)::aqs)))))
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

let uu____11489 = (FStar_Parser_AST.mkExplicitApp bind1 ((t1)::(k)::[]) top.FStar_Parser_AST.range)
in (desugar_term_aq env uu____11489))))))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(

let t = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), ((((FStar_Pervasives_Native.None), ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatWild (FStar_Pervasives_Native.None)) t1.FStar_Parser_AST.range)), (t1)))))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
in (

let uu____11541 = (desugar_term_aq env t)
in (match (uu____11541) with
| (tm, s) -> begin
(

let uu____11552 = (mk1 (FStar_Syntax_Syntax.Tm_meta (((tm), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))))
in ((uu____11552), (s)))
end)))
end
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(

let env1 = (FStar_Syntax_DsEnv.push_namespace env lid)
in (

let uu____11558 = (

let uu____11571 = (FStar_Syntax_DsEnv.expect_typ env1)
in (match (uu____11571) with
| true -> begin
desugar_typ_aq
end
| uu____11584 -> begin
desugar_term_aq
end))
in (uu____11558 env1 e)))
end
| FStar_Parser_AST.Let (qual, lbs, body) -> begin
(

let is_rec = (Prims.op_Equality qual FStar_Parser_AST.Rec)
in (

let ds_let_rec_or_app = (fun uu____11638 -> (

let bindings = lbs
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun uu____11781 -> (match (uu____11781) with
| (attr_opt, (p, def)) -> begin
(

let uu____11839 = (is_app_pattern p)
in (match (uu____11839) with
| true -> begin
(

let uu____11872 = (destruct_app_pattern env top_level p)
in ((attr_opt), (uu____11872), (def)))
end
| uu____11917 -> begin
(match ((FStar_Parser_AST.un_function p def)) with
| FStar_Pervasives_Native.Some (p1, def1) -> begin
(

let uu____11955 = (destruct_app_pattern env top_level p1)
in ((attr_opt), (uu____11955), (def1)))
end
| uu____12000 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id1, uu____12038); FStar_Parser_AST.prange = uu____12039}, t) -> begin
(match (top_level) with
| true -> begin
(

let uu____12088 = (

let uu____12109 = (

let uu____12114 = (FStar_Syntax_DsEnv.qualify env id1)
in FStar_Util.Inr (uu____12114))
in ((uu____12109), ([]), (FStar_Pervasives_Native.Some (t))))
in ((attr_opt), (uu____12088), (def)))
end
| uu____12159 -> begin
((attr_opt), (((FStar_Util.Inl (id1)), ([]), (FStar_Pervasives_Native.Some (t)))), (def))
end)
end
| FStar_Parser_AST.PatVar (id1, uu____12206) -> begin
(match (top_level) with
| true -> begin
(

let uu____12242 = (

let uu____12263 = (

let uu____12268 = (FStar_Syntax_DsEnv.qualify env id1)
in FStar_Util.Inr (uu____12268))
in ((uu____12263), ([]), (FStar_Pervasives_Native.None)))
in ((attr_opt), (uu____12242), (def)))
end
| uu____12313 -> begin
((attr_opt), (((FStar_Util.Inl (id1)), ([]), (FStar_Pervasives_Native.None))), (def))
end)
end
| uu____12359 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedLetBinding), ("Unexpected let binding")) p.FStar_Parser_AST.prange)
end)
end)
end))
end))))
in (

let uu____12392 = (FStar_List.fold_left (fun uu____12481 uu____12482 -> (match (((uu____12481), (uu____12482))) with
| ((env1, fnames, rec_bindings, used_markers), (_attr_opt, (f, uu____12612, uu____12613), uu____12614)) -> begin
(

let uu____12748 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let uu____12788 = (FStar_Syntax_DsEnv.push_bv' env1 x)
in (match (uu____12788) with
| (env2, xx, used_marker) -> begin
(

let dummy_ref = (FStar_Util.mk_ref true)
in (

let uu____12823 = (

let uu____12826 = (FStar_Syntax_Syntax.mk_binder xx)
in (uu____12826)::rec_bindings)
in ((env2), (FStar_Util.Inl (xx)), (uu____12823), ((used_marker)::used_markers))))
end))
end
| FStar_Util.Inr (l) -> begin
(

let uu____12842 = (FStar_Syntax_DsEnv.push_top_level_rec_binding env1 l.FStar_Ident.ident FStar_Syntax_Syntax.delta_equational)
in (match (uu____12842) with
| (env2, used_marker) -> begin
((env2), (FStar_Util.Inr (l)), (rec_bindings), ((used_marker)::used_markers))
end))
end)
in (match (uu____12748) with
| (env2, lbname, rec_bindings1, used_markers1) -> begin
((env2), ((lbname)::fnames), (rec_bindings1), (used_markers1))
end))
end)) ((env), ([]), ([]), ([])) funs)
in (match (uu____12392) with
| (env', fnames, rec_bindings, used_markers) -> begin
(

let fnames1 = (FStar_List.rev fnames)
in (

let rec_bindings1 = (FStar_List.rev rec_bindings)
in (

let used_markers1 = (FStar_List.rev used_markers)
in (

let desugar_one_def = (fun env1 lbname uu____13095 -> (match (uu____13095) with
| (attrs_opt, (uu____13135, args, result_t), def) -> begin
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

let uu____13227 = (is_comp_type env1 t)
in (match (uu____13227) with
| true -> begin
((

let uu____13231 = (FStar_All.pipe_right args1 (FStar_List.tryFind (fun x -> (

let uu____13241 = (is_var_pattern x)
in (not (uu____13241))))))
in (match (uu____13231) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (p) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ComputationTypeNotAllowed), ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")) p.FStar_Parser_AST.prange)
end));
t;
)
end
| uu____13246 -> begin
(

let uu____13248 = (((FStar_Options.ml_ish ()) && (

let uu____13251 = (FStar_Syntax_DsEnv.try_lookup_effect_name env1 FStar_Parser_Const.effect_ML_lid)
in (FStar_Option.isSome uu____13251))) && ((not (is_rec)) || (Prims.op_disEquality (FStar_List.length args1) (Prims.parse_int "0"))))
in (match (uu____13248) with
| true -> begin
(FStar_Parser_AST.ml_comp t)
end
| uu____13257 -> begin
(FStar_Parser_AST.tot_comp t)
end))
end))
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t1), (tacopt)))) def.FStar_Parser_AST.range FStar_Parser_AST.Expr))
end)
in (

let def2 = (match (args1) with
| [] -> begin
def1
end
| uu____13262 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.un_curry_abs args1 def1) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
end)
in (

let uu____13265 = (desugar_term_aq env1 def2)
in (match (uu____13265) with
| (body1, aq) -> begin
(

let lbname1 = (match (lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl (x)
end
| FStar_Util.Inr (l) -> begin
(

let uu____13287 = (

let uu____13288 = (FStar_Syntax_Util.incr_delta_qualifier body1)
in (FStar_Syntax_Syntax.lid_as_fv l uu____13288 FStar_Pervasives_Native.None))
in FStar_Util.Inr (uu____13287))
end)
in (

let body2 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.close rec_bindings1 body1)
end
| uu____13295 -> begin
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
in (((mk_lb ((attrs), (lbname1), (FStar_Syntax_Syntax.tun), (body2), (pos)))), (aq)))))
end))))))
end))
in (

let uu____13329 = (

let uu____13346 = (FStar_List.map2 (desugar_one_def (match (is_rec) with
| true -> begin
env'
end
| uu____13408 -> begin
env
end)) fnames1 funs)
in (FStar_All.pipe_right uu____13346 FStar_List.unzip))
in (match (uu____13329) with
| (lbs1, aqss) -> begin
(

let uu____13488 = (desugar_term_aq env' body)
in (match (uu____13488) with
| (body1, aq) -> begin
((match (is_rec) with
| true -> begin
(FStar_List.iter2 (fun uu____13594 used_marker -> (match (uu____13594) with
| (_attr_opt, (f, uu____13668, uu____13669), uu____13670) -> begin
(

let uu____13727 = (

let uu____13729 = (FStar_ST.op_Bang used_marker)
in (not (uu____13729)))
in (match (uu____13727) with
| true -> begin
(

let uu____13753 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let uu____13771 = (FStar_Ident.string_of_ident x)
in (

let uu____13773 = (FStar_Ident.range_of_id x)
in ((uu____13771), ("Local"), (uu____13773))))
end
| FStar_Util.Inr (l) -> begin
(

let uu____13778 = (FStar_Ident.string_of_lid l)
in (

let uu____13780 = (FStar_Ident.range_of_lid l)
in ((uu____13778), ("Global"), (uu____13780))))
end)
in (match (uu____13753) with
| (nm, gl, rng) -> begin
(

let uu____13791 = (

let uu____13797 = (FStar_Util.format2 "%s binding %s is recursive but not used in its body" gl nm)
in ((FStar_Errors.Warning_UnusedLetRec), (uu____13797)))
in (FStar_Errors.log_issue rng uu____13791))
end))
end
| uu____13801 -> begin
()
end))
end)) funs used_markers1)
end
| uu____13803 -> begin
()
end);
(

let uu____13805 = (

let uu____13808 = (

let uu____13809 = (

let uu____13823 = (FStar_Syntax_Subst.close rec_bindings1 body1)
in ((((is_rec), (lbs1))), (uu____13823)))
in FStar_Syntax_Syntax.Tm_let (uu____13809))
in (FStar_All.pipe_left mk1 uu____13808))
in ((uu____13805), ((FStar_List.append aq (FStar_List.flatten aqss)))));
)
end))
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

let uu____13925 = (desugar_term_aq env t1)
in (match (uu____13925) with
| (t11, aq0) -> begin
(

let uu____13946 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (uu____13946) with
| (env1, binder, pat1) -> begin
(

let uu____13976 = (match (binder) with
| LetBinder (l, (t, _tacopt)) -> begin
(

let uu____14018 = (desugar_term_aq env1 t2)
in (match (uu____14018) with
| (body1, aq) -> begin
(

let fv = (

let uu____14040 = (FStar_Syntax_Util.incr_delta_qualifier t11)
in (FStar_Syntax_Syntax.lid_as_fv l uu____14040 FStar_Pervasives_Native.None))
in (

let uu____14041 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_let (((((false), (((mk_lb ((attrs), (FStar_Util.Inr (fv)), (t), (t11), (t11.FStar_Syntax_Syntax.pos))))::[]))), (body1)))))
in ((uu____14041), (aq))))
end))
end
| LocalBinder (x, uu____14082) -> begin
(

let uu____14083 = (desugar_term_aq env1 t2)
in (match (uu____14083) with
| (body1, aq) -> begin
(

let body2 = (match (pat1) with
| [] -> begin
body1
end
| (({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (uu____14105); FStar_Syntax_Syntax.p = uu____14106}, uu____14107))::[] -> begin
body1
end
| uu____14120 -> begin
(

let uu____14123 = (

let uu____14130 = (

let uu____14131 = (

let uu____14154 = (FStar_Syntax_Syntax.bv_to_name x)
in (

let uu____14157 = (desugar_disjunctive_pattern pat1 FStar_Pervasives_Native.None body1)
in ((uu____14154), (uu____14157))))
in FStar_Syntax_Syntax.Tm_match (uu____14131))
in (FStar_Syntax_Syntax.mk uu____14130))
in (uu____14123 FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
end)
in (

let uu____14194 = (

let uu____14197 = (

let uu____14198 = (

let uu____14212 = (

let uu____14215 = (

let uu____14216 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____14216)::[])
in (FStar_Syntax_Subst.close uu____14215 body2))
in ((((false), (((mk_lb ((attrs), (FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t11), (t11.FStar_Syntax_Syntax.pos))))::[]))), (uu____14212)))
in FStar_Syntax_Syntax.Tm_let (uu____14198))
in (FStar_All.pipe_left mk1 uu____14197))
in ((uu____14194), (aq))))
end))
end)
in (match (uu____13976) with
| (tm, aq1) -> begin
((tm), ((FStar_List.append aq0 aq1)))
end))
end))
end))))
in (

let uu____14324 = (FStar_List.hd lbs)
in (match (uu____14324) with
| (attrs, (head_pat, defn)) -> begin
(

let uu____14368 = (is_rec || (is_app_pattern head_pat))
in (match (uu____14368) with
| true -> begin
(ds_let_rec_or_app ())
end
| uu____14375 -> begin
(ds_non_rec attrs head_pat defn body)
end))
end)))))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (

let t_bool1 = (

let uu____14384 = (

let uu____14385 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in FStar_Syntax_Syntax.Tm_fvar (uu____14385))
in (mk1 uu____14384))
in (

let uu____14386 = (desugar_term_aq env t1)
in (match (uu____14386) with
| (t1', aq1) -> begin
(

let uu____14397 = (desugar_term_aq env t2)
in (match (uu____14397) with
| (t2', aq2) -> begin
(

let uu____14408 = (desugar_term_aq env t3)
in (match (uu____14408) with
| (t3', aq3) -> begin
(

let uu____14419 = (

let uu____14420 = (

let uu____14421 = (

let uu____14444 = (

let uu____14461 = (

let uu____14476 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) t1.FStar_Parser_AST.range)
in ((uu____14476), (FStar_Pervasives_Native.None), (t2')))
in (

let uu____14490 = (

let uu____14507 = (

let uu____14522 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) t1.FStar_Parser_AST.range)
in ((uu____14522), (FStar_Pervasives_Native.None), (t3')))
in (uu____14507)::[])
in (uu____14461)::uu____14490))
in ((t1'), (uu____14444)))
in FStar_Syntax_Syntax.Tm_match (uu____14421))
in (mk1 uu____14420))
in ((uu____14419), ((join_aqs ((aq1)::(aq2)::(aq3)::[])))))
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

let try_with_lid1 = (FStar_Ident.lid_of_path (("try_with")::[]) r)
in (

let try_with1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (try_with_lid1)) r FStar_Parser_AST.Expr)
in (

let a1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((try_with1), (body), (FStar_Parser_AST.Nothing)))) r top.FStar_Parser_AST.level)
in (

let a2 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((a1), (handler), (FStar_Parser_AST.Nothing)))) r top.FStar_Parser_AST.level)
in (desugar_term_aq env a2))))))))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(

let desugar_branch = (fun uu____14718 -> (match (uu____14718) with
| (pat, wopt, b) -> begin
(

let uu____14740 = (desugar_match_pat env pat)
in (match (uu____14740) with
| (env1, pat1) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (e1) -> begin
(

let uu____14771 = (desugar_term env1 e1)
in FStar_Pervasives_Native.Some (uu____14771))
end)
in (

let uu____14776 = (desugar_term_aq env1 b)
in (match (uu____14776) with
| (b1, aq) -> begin
(

let uu____14789 = (desugar_disjunctive_pattern pat1 wopt1 b1)
in ((uu____14789), (aq)))
end)))
end))
end))
in (

let uu____14794 = (desugar_term_aq env e)
in (match (uu____14794) with
| (e1, aq) -> begin
(

let uu____14805 = (

let uu____14836 = (

let uu____14869 = (FStar_List.map desugar_branch branches)
in (FStar_All.pipe_right uu____14869 FStar_List.unzip))
in (FStar_All.pipe_right uu____14836 (fun uu____15087 -> (match (uu____15087) with
| (x, y) -> begin
(((FStar_List.flatten x)), (y))
end))))
in (match (uu____14805) with
| (brs, aqs) -> begin
(

let uu____15306 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_match (((e1), (brs)))))
in ((uu____15306), ((join_aqs ((aq)::aqs)))))
end))
end)))
end
| FStar_Parser_AST.Ascribed (e, t, tac_opt) -> begin
(

let uu____15340 = (

let uu____15361 = (is_comp_type env t)
in (match (uu____15361) with
| true -> begin
(

let comp = (desugar_comp t.FStar_Parser_AST.range true env t)
in ((FStar_Util.Inr (comp)), ([])))
end
| uu____15414 -> begin
(

let uu____15416 = (desugar_term_aq env t)
in (match (uu____15416) with
| (tm, aq) -> begin
((FStar_Util.Inl (tm)), (aq))
end))
end))
in (match (uu____15340) with
| (annot, aq0) -> begin
(

let tac_opt1 = (FStar_Util.map_opt tac_opt (desugar_term env))
in (

let uu____15508 = (desugar_term_aq env e)
in (match (uu____15508) with
| (e1, aq) -> begin
(

let uu____15519 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_ascribed (((e1), (((annot), (tac_opt1))), (FStar_Pervasives_Native.None)))))
in ((uu____15519), ((FStar_List.append aq0 aq))))
end)))
end))
end
| FStar_Parser_AST.Record (uu____15558, []) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedEmptyRecord), ("Unexpected empty record")) top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let record = (check_fields env fields top.FStar_Parser_AST.range)
in (

let user_ns = (

let uu____15601 = (FStar_List.hd fields)
in (match (uu____15601) with
| (f, uu____15613) -> begin
f.FStar_Ident.ns
end))
in (

let get_field = (fun xopt f -> (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun uu____15659 -> (match (uu____15659) with
| (g, uu____15666) -> begin
(Prims.op_Equality f.FStar_Ident.idText g.FStar_Ident.ident.FStar_Ident.idText)
end))))
in (

let fn = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((f)::[])))
in (match (found) with
| FStar_Pervasives_Native.Some (uu____15673, e) -> begin
((fn), (e))
end
| FStar_Pervasives_Native.None -> begin
(match (xopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____15687 = (

let uu____15693 = (FStar_Util.format2 "Field %s of record type %s is missing" f.FStar_Ident.idText record.FStar_Syntax_DsEnv.typename.FStar_Ident.str)
in ((FStar_Errors.Fatal_MissingFieldInRecord), (uu____15693)))
in (FStar_Errors.raise_error uu____15687 top.FStar_Parser_AST.range))
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

let uu____15704 = (

let uu____15715 = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map (fun uu____15746 -> (match (uu____15746) with
| (f, uu____15756) -> begin
(

let uu____15757 = (

let uu____15758 = (get_field FStar_Pervasives_Native.None f)
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____15758))
in ((uu____15757), (FStar_Parser_AST.Nothing)))
end))))
in ((user_constrname), (uu____15715)))
in FStar_Parser_AST.Construct (uu____15704))
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (

let uu____15776 = (

let uu____15777 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____15777))
in (FStar_Parser_AST.mk_term uu____15776 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record1 = (

let uu____15779 = (

let uu____15792 = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map (fun uu____15822 -> (match (uu____15822) with
| (f, uu____15832) -> begin
(get_field (FStar_Pervasives_Native.Some (xterm)) f)
end))))
in ((FStar_Pervasives_Native.None), (uu____15792)))
in FStar_Parser_AST.Record (uu____15779))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), ((((FStar_Pervasives_Native.None), ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (FStar_Pervasives_Native.None)))) x.FStar_Ident.idRange)), (e)))))::[]), ((FStar_Parser_AST.mk_term record1 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm1 = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let uu____15892 = (desugar_term_aq env recterm1)
in (match (uu____15892) with
| (e, s) -> begin
(match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____15908; FStar_Syntax_Syntax.vars = uu____15909}, args) -> begin
(

let uu____15935 = (

let uu____15936 = (

let uu____15937 = (

let uu____15954 = (

let uu____15957 = (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos)
in (

let uu____15958 = (

let uu____15961 = (

let uu____15962 = (

let uu____15969 = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map FStar_Pervasives_Native.fst))
in ((record.FStar_Syntax_DsEnv.typename), (uu____15969)))
in FStar_Syntax_Syntax.Record_ctor (uu____15962))
in FStar_Pervasives_Native.Some (uu____15961))
in (FStar_Syntax_Syntax.fvar uu____15957 FStar_Syntax_Syntax.delta_constant uu____15958)))
in ((uu____15954), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____15937))
in (FStar_All.pipe_left mk1 uu____15936))
in ((uu____15935), (s)))
end
| uu____15998 -> begin
((e), (s))
end)
end))))))))
end
| FStar_Parser_AST.Project (e, f) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f);
(

let uu____16002 = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f)
in (match (uu____16002) with
| (constrname, is_rec) -> begin
(

let uu____16021 = (desugar_term_aq env e)
in (match (uu____16021) with
| (e1, s) -> begin
(

let projname = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname f.FStar_Ident.ident)
in (

let qual = (match (is_rec) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (((constrname), (f.FStar_Ident.ident))))
end
| uu____16039 -> begin
FStar_Pervasives_Native.None
end)
in (

let uu____16041 = (

let uu____16042 = (

let uu____16043 = (

let uu____16060 = (

let uu____16063 = (

let uu____16064 = (FStar_Ident.range_of_lid f)
in (FStar_Ident.set_lid_range projname uu____16064))
in (FStar_Syntax_Syntax.fvar uu____16063 (FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "1"))) qual))
in (

let uu____16066 = (

let uu____16077 = (FStar_Syntax_Syntax.as_arg e1)
in (uu____16077)::[])
in ((uu____16060), (uu____16066))))
in FStar_Syntax_Syntax.Tm_app (uu____16043))
in (FStar_All.pipe_left mk1 uu____16042))
in ((uu____16041), (s)))))
end))
end));
)
end
| FStar_Parser_AST.NamedTyp (uu____16114, e) -> begin
(desugar_term_aq env e)
end
| FStar_Parser_AST.Paren (e) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.VQuote (e) -> begin
(

let tm = (desugar_term env e)
in (

let uu____16124 = (

let uu____16125 = (FStar_Syntax_Subst.compress tm)
in uu____16125.FStar_Syntax_Syntax.n)
in (match (uu____16124) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____16133 = (

let uu___2115_16134 = (

let uu____16135 = (

let uu____16137 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____16137))
in (FStar_Syntax_Util.exp_string uu____16135))
in {FStar_Syntax_Syntax.n = uu___2115_16134.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = e.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___2115_16134.FStar_Syntax_Syntax.vars})
in ((uu____16133), (noaqs)))
end
| uu____16138 -> begin
(

let uu____16139 = (

let uu____16145 = (

let uu____16147 = (FStar_Syntax_Print.term_to_string tm)
in (Prims.op_Hat "VQuote, expected an fvar, got: " uu____16147))
in ((FStar_Errors.Fatal_UnexpectedTermVQuote), (uu____16145)))
in (FStar_Errors.raise_error uu____16139 top.FStar_Parser_AST.range))
end)))
end
| FStar_Parser_AST.Quote (e, FStar_Parser_AST.Static) -> begin
(

let uu____16156 = (desugar_term_aq env e)
in (match (uu____16156) with
| (tm, vts) -> begin
(

let qi = {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = vts}
in (

let uu____16168 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_quoted (((tm), (qi)))))
in ((uu____16168), (noaqs))))
end))
end
| FStar_Parser_AST.Antiquote (e) -> begin
(

let bv = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (

let uu____16173 = (FStar_Syntax_Syntax.bv_to_name bv)
in (

let uu____16174 = (

let uu____16175 = (

let uu____16182 = (desugar_term env e)
in ((bv), (uu____16182)))
in (uu____16175)::[])
in ((uu____16173), (uu____16174)))))
end
| FStar_Parser_AST.Quote (e, FStar_Parser_AST.Dynamic) -> begin
(

let qi = {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = []}
in (

let uu____16207 = (

let uu____16208 = (

let uu____16209 = (

let uu____16216 = (desugar_term env e)
in ((uu____16216), (qi)))
in FStar_Syntax_Syntax.Tm_quoted (uu____16209))
in (FStar_All.pipe_left mk1 uu____16208))
in ((uu____16207), (noaqs))))
end
| FStar_Parser_AST.CalcProof (rel, init_expr, steps) -> begin
(

let eta_and_annot = (fun rel1 -> (

let x = (FStar_Ident.gen rel1.FStar_Parser_AST.range)
in (

let y = (FStar_Ident.gen rel1.FStar_Parser_AST.range)
in (

let xt = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar (x)) rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr)
in (

let yt = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar (y)) rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr)
in (

let pats = ((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (FStar_Pervasives_Native.None)))) rel1.FStar_Parser_AST.range))::((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((y), (FStar_Pervasives_Native.None)))) rel1.FStar_Parser_AST.range))::[]
in (

let uu____16245 = (

let uu____16246 = (

let uu____16253 = (

let uu____16254 = (

let uu____16255 = (

let uu____16264 = (FStar_Parser_AST.mkApp rel1 ((((xt), (FStar_Parser_AST.Nothing)))::(((yt), (FStar_Parser_AST.Nothing)))::[]) rel1.FStar_Parser_AST.range)
in (

let uu____16277 = (

let uu____16278 = (

let uu____16279 = (FStar_Ident.lid_of_str "Type0")
in FStar_Parser_AST.Name (uu____16279))
in (FStar_Parser_AST.mk_term uu____16278 rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((uu____16264), (uu____16277), (FStar_Pervasives_Native.None))))
in FStar_Parser_AST.Ascribed (uu____16255))
in (FStar_Parser_AST.mk_term uu____16254 rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((pats), (uu____16253)))
in FStar_Parser_AST.Abs (uu____16246))
in (FStar_Parser_AST.mk_term uu____16245 rel1.FStar_Parser_AST.range FStar_Parser_AST.Expr))))))))
in (

let rel1 = (eta_and_annot rel)
in (

let wild = (fun r -> (FStar_Parser_AST.mk_term FStar_Parser_AST.Wild r FStar_Parser_AST.Expr))
in (

let init1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (FStar_Parser_Const.calc_init_lid)) FStar_Range.dummyRange FStar_Parser_AST.Expr)
in (

let last_expr = (

let uu____16294 = (FStar_List.last steps)
in (match (uu____16294) with
| FStar_Pervasives_Native.Some (FStar_Parser_AST.CalcStep (uu____16297, uu____16298, last_expr)) -> begin
last_expr
end
| uu____16300 -> begin
(failwith "impossible: no last_expr on calc")
end))
in (

let step = (fun r -> (FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (FStar_Parser_Const.calc_step_lid)) r FStar_Parser_AST.Expr))
in (

let finish1 = (FStar_Parser_AST.mkApp (FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (FStar_Parser_Const.calc_finish_lid)) top.FStar_Parser_AST.range FStar_Parser_AST.Expr) ((((rel1), (FStar_Parser_AST.Nothing)))::[]) top.FStar_Parser_AST.range)
in (

let e = (FStar_Parser_AST.mkApp init1 ((((init_expr), (FStar_Parser_AST.Nothing)))::[]) FStar_Range.dummyRange)
in (

let uu____16328 = (FStar_List.fold_left (fun uu____16345 uu____16346 -> (match (((uu____16345), (uu____16346))) with
| ((e1, prev), FStar_Parser_AST.CalcStep (rel2, just, next_expr)) -> begin
(

let pf = (

let uu____16369 = (

let uu____16376 = (

let uu____16383 = (

let uu____16390 = (

let uu____16397 = (

let uu____16402 = (eta_and_annot rel2)
in ((uu____16402), (FStar_Parser_AST.Nothing)))
in (

let uu____16403 = (

let uu____16410 = (

let uu____16417 = (

let uu____16422 = (FStar_Parser_AST.thunk e1)
in ((uu____16422), (FStar_Parser_AST.Nothing)))
in (

let uu____16423 = (

let uu____16430 = (

let uu____16435 = (FStar_Parser_AST.thunk just)
in ((uu____16435), (FStar_Parser_AST.Nothing)))
in (uu____16430)::[])
in (uu____16417)::uu____16423))
in (((next_expr), (FStar_Parser_AST.Nothing)))::uu____16410)
in (uu____16397)::uu____16403))
in (((prev), (FStar_Parser_AST.Hash)))::uu____16390)
in (((init_expr), (FStar_Parser_AST.Hash)))::uu____16383)
in ((((wild rel2.FStar_Parser_AST.range)), (FStar_Parser_AST.Hash)))::uu____16376)
in (FStar_Parser_AST.mkApp (step rel2.FStar_Parser_AST.range) uu____16369 FStar_Range.dummyRange))
in ((pf), (next_expr)))
end)) ((e), (init_expr)) steps)
in (match (uu____16328) with
| (e1, uu____16473) -> begin
(

let e2 = (

let uu____16475 = (

let uu____16482 = (

let uu____16489 = (

let uu____16496 = (

let uu____16501 = (FStar_Parser_AST.thunk e1)
in ((uu____16501), (FStar_Parser_AST.Nothing)))
in (uu____16496)::[])
in (((last_expr), (FStar_Parser_AST.Hash)))::uu____16489)
in (((init_expr), (FStar_Parser_AST.Hash)))::uu____16482)
in (FStar_Parser_AST.mkApp finish1 uu____16475 FStar_Range.dummyRange))
in (desugar_term_maybe_top top_level env e2))
end))))))))))
end
| uu____16518 when (Prims.op_Equality top.FStar_Parser_AST.level FStar_Parser_AST.Formula) -> begin
(

let uu____16519 = (desugar_formula env top)
in ((uu____16519), (noaqs)))
end
| uu____16520 -> begin
(

let uu____16521 = (

let uu____16527 = (

let uu____16529 = (FStar_Parser_AST.term_to_string top)
in (Prims.op_Hat "Unexpected term: " uu____16529))
in ((FStar_Errors.Fatal_UnexpectedTerm), (uu____16527)))
in (FStar_Errors.raise_error uu____16521 top.FStar_Parser_AST.range))
end)))))))
and desugar_args : FStar_Syntax_DsEnv.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____16573 -> (match (uu____16573) with
| (a, imp) -> begin
(

let uu____16586 = (desugar_term env a)
in (arg_withimp_e imp uu____16586))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun r allow_type_promotion env t -> (

let fail1 = (fun err -> (FStar_Errors.raise_error err r))
in (

let is_requires = (fun uu____16623 -> (match (uu____16623) with
| (t1, uu____16630) -> begin
(

let uu____16631 = (

let uu____16632 = (unparen t1)
in uu____16632.FStar_Parser_AST.tm)
in (match (uu____16631) with
| FStar_Parser_AST.Requires (uu____16634) -> begin
true
end
| uu____16643 -> begin
false
end))
end))
in (

let is_ensures = (fun uu____16655 -> (match (uu____16655) with
| (t1, uu____16662) -> begin
(

let uu____16663 = (

let uu____16664 = (unparen t1)
in uu____16664.FStar_Parser_AST.tm)
in (match (uu____16663) with
| FStar_Parser_AST.Ensures (uu____16666) -> begin
true
end
| uu____16675 -> begin
false
end))
end))
in (

let is_app = (fun head1 uu____16693 -> (match (uu____16693) with
| (t1, uu____16701) -> begin
(

let uu____16702 = (

let uu____16703 = (unparen t1)
in uu____16703.FStar_Parser_AST.tm)
in (match (uu____16702) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = uu____16706; FStar_Parser_AST.level = uu____16707}, uu____16708, uu____16709) -> begin
(Prims.op_Equality d.FStar_Ident.ident.FStar_Ident.idText head1)
end
| uu____16711 -> begin
false
end))
end))
in (

let is_smt_pat = (fun uu____16723 -> (match (uu____16723) with
| (t1, uu____16730) -> begin
(

let uu____16731 = (

let uu____16732 = (unparen t1)
in uu____16732.FStar_Parser_AST.tm)
in (match (uu____16731) with
| FStar_Parser_AST.Construct (cons1, (({FStar_Parser_AST.tm = FStar_Parser_AST.Construct (smtpat, uu____16736); FStar_Parser_AST.range = uu____16737; FStar_Parser_AST.level = uu____16738}, uu____16739))::(uu____16740)::[]) -> begin
((FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid) && (FStar_Util.for_some (fun s -> (Prims.op_Equality smtpat.FStar_Ident.str s)) (("SMTPat")::("SMTPatT")::("SMTPatOr")::[])))
end
| FStar_Parser_AST.Construct (cons1, (({FStar_Parser_AST.tm = FStar_Parser_AST.Var (smtpat); FStar_Parser_AST.range = uu____16789; FStar_Parser_AST.level = uu____16790}, uu____16791))::(uu____16792)::[]) -> begin
((FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid) && (FStar_Util.for_some (fun s -> (Prims.op_Equality smtpat.FStar_Ident.str s)) (("smt_pat")::("smt_pat_or")::[])))
end
| uu____16825 -> begin
false
end))
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t1 -> (

let uu____16860 = (head_and_args t1)
in (match (uu____16860) with
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

let thunk_ens = (fun uu____16953 -> (match (uu____16953) with
| (e, i) -> begin
(

let uu____16964 = (FStar_Parser_AST.thunk e)
in ((uu____16964), (i)))
end))
in (

let fail_lemma = (fun uu____16976 -> (

let expected_one_of = ("Lemma post")::("Lemma (ensures post)")::("Lemma (requires pre) (ensures post)")::("Lemma post [SMTPat ...]")::("Lemma (ensures post) [SMTPat ...]")::("Lemma (ensures post) (decreases d)")::("Lemma (ensures post) (decreases d) [SMTPat ...]")::("Lemma (requires pre) (ensures post) (decreases d)")::("Lemma (requires pre) (ensures post) [SMTPat ...]")::("Lemma (requires pre) (ensures post) (decreases d) [SMTPat ...]")::[]
in (

let msg = (FStar_String.concat "\n\t" expected_one_of)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_InvalidLemmaArgument), ((Prims.op_Hat "Invalid arguments to \'Lemma\'; expected one of the following:\n\t" msg))) t1.FStar_Parser_AST.range))))
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

let uu____17082 = (

let uu____17089 = (

let uu____17096 = (thunk_ens ens)
in (uu____17096)::(nil_pat)::[])
in (req_true)::uu____17089)
in (unit_tm)::uu____17082)
end
| (req)::(ens)::[] when ((is_requires req) && (is_ensures ens)) -> begin
(

let uu____17143 = (

let uu____17150 = (

let uu____17157 = (thunk_ens ens)
in (uu____17157)::(nil_pat)::[])
in (req)::uu____17150)
in (unit_tm)::uu____17143)
end
| (ens)::(smtpat)::[] when ((((

let uu____17206 = (is_requires ens)
in (not (uu____17206))) && (

let uu____17209 = (is_smt_pat ens)
in (not (uu____17209)))) && (

let uu____17212 = (is_decreases ens)
in (not (uu____17212)))) && (is_smt_pat smtpat)) -> begin
(

let uu____17214 = (

let uu____17221 = (

let uu____17228 = (thunk_ens ens)
in (uu____17228)::(smtpat)::[])
in (req_true)::uu____17221)
in (unit_tm)::uu____17214)
end
| (ens)::(dec)::[] when ((is_ensures ens) && (is_decreases dec)) -> begin
(

let uu____17275 = (

let uu____17282 = (

let uu____17289 = (thunk_ens ens)
in (uu____17289)::(nil_pat)::(dec)::[])
in (req_true)::uu____17282)
in (unit_tm)::uu____17275)
end
| (ens)::(dec)::(smtpat)::[] when (((is_ensures ens) && (is_decreases dec)) && (is_smt_pat smtpat)) -> begin
(

let uu____17349 = (

let uu____17356 = (

let uu____17363 = (thunk_ens ens)
in (uu____17363)::(smtpat)::(dec)::[])
in (req_true)::uu____17356)
in (unit_tm)::uu____17349)
end
| (req)::(ens)::(dec)::[] when (((is_requires req) && (is_ensures ens)) && (is_decreases dec)) -> begin
(

let uu____17423 = (

let uu____17430 = (

let uu____17437 = (thunk_ens ens)
in (uu____17437)::(nil_pat)::(dec)::[])
in (req)::uu____17430)
in (unit_tm)::uu____17423)
end
| (req)::(ens)::(smtpat)::[] when (((is_requires req) && (is_ensures ens)) && (is_smt_pat smtpat)) -> begin
(

let uu____17497 = (

let uu____17504 = (

let uu____17511 = (thunk_ens ens)
in (uu____17511)::(smtpat)::[])
in (req)::uu____17504)
in (unit_tm)::uu____17497)
end
| (req)::(ens)::(dec)::(smtpat)::[] when ((((is_requires req) && (is_ensures ens)) && (is_smt_pat smtpat)) && (is_decreases dec)) -> begin
(

let uu____17576 = (

let uu____17583 = (

let uu____17590 = (thunk_ens ens)
in (uu____17590)::(dec)::(smtpat)::[])
in (req)::uu____17583)
in (unit_tm)::uu____17576)
end
| _other -> begin
(fail_lemma ())
end)
in (

let head_and_attributes = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes env) lemma)
in ((head_and_attributes), (args1)))))))))
end
| FStar_Parser_AST.Name (l) when (FStar_Syntax_DsEnv.is_effect_name env l) -> begin
(

let uu____17652 = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes env) l)
in ((uu____17652), (args)))
end
| FStar_Parser_AST.Name (l) when ((

let uu____17680 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Ident.lid_equals uu____17680 FStar_Parser_Const.prims_lid)) && (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Tot")) -> begin
(

let uu____17683 = (

let uu____17690 = (FStar_Ident.set_lid_range FStar_Parser_Const.effect_Tot_lid head1.FStar_Parser_AST.range)
in ((uu____17690), ([])))
in ((uu____17683), (args)))
end
| FStar_Parser_AST.Name (l) when ((

let uu____17708 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Ident.lid_equals uu____17708 FStar_Parser_Const.prims_lid)) && (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "GTot")) -> begin
(

let uu____17711 = (

let uu____17718 = (FStar_Ident.set_lid_range FStar_Parser_Const.effect_GTot_lid head1.FStar_Parser_AST.range)
in ((uu____17718), ([])))
in ((uu____17711), (args)))
end
| FStar_Parser_AST.Name (l) when (((Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Type") || (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Type0")) || (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Effect")) -> begin
(

let uu____17740 = (

let uu____17747 = (FStar_Ident.set_lid_range FStar_Parser_Const.effect_Tot_lid head1.FStar_Parser_AST.range)
in ((uu____17747), ([])))
in ((uu____17740), ((((t1), (FStar_Parser_AST.Nothing)))::[])))
end
| uu____17770 when allow_type_promotion -> begin
(

let default_effect = (

let uu____17772 = (FStar_Options.ml_ish ())
in (match (uu____17772) with
| true -> begin
FStar_Parser_Const.effect_ML_lid
end
| uu____17775 -> begin
((

let uu____17778 = (FStar_Options.warn_default_effects ())
in (match (uu____17778) with
| true -> begin
(FStar_Errors.log_issue head1.FStar_Parser_AST.range ((FStar_Errors.Warning_UseDefaultEffect), ("Using default effect Tot")))
end
| uu____17783 -> begin
()
end));
FStar_Parser_Const.effect_Tot_lid;
)
end))
in (

let uu____17785 = (

let uu____17792 = (FStar_Ident.set_lid_range default_effect head1.FStar_Parser_AST.range)
in ((uu____17792), ([])))
in ((uu____17785), ((((t1), (FStar_Parser_AST.Nothing)))::[]))))
end
| uu____17815 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_EffectNotFound), ("Expected an effect constructor")) t1.FStar_Parser_AST.range)
end)
end)))
in (

let uu____17834 = (pre_process_comp_typ t)
in (match (uu____17834) with
| ((eff, cattributes), args) -> begin
((match ((Prims.op_Equality (FStar_List.length args) (Prims.parse_int "0"))) with
| true -> begin
(

let uu____17886 = (

let uu____17892 = (

let uu____17894 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" uu____17894))
in ((FStar_Errors.Fatal_NotEnoughArgsToEffect), (uu____17892)))
in (fail1 uu____17886))
end
| uu____17898 -> begin
()
end);
(

let is_universe = (fun uu____17910 -> (match (uu____17910) with
| (uu____17916, imp) -> begin
(Prims.op_Equality imp FStar_Parser_AST.UnivApp)
end))
in (

let uu____17918 = (FStar_Util.take is_universe args)
in (match (uu____17918) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun uu____17977 -> (match (uu____17977) with
| (u, imp) -> begin
(desugar_universe u)
end)) universes)
in (

let uu____17984 = (

let uu____17999 = (FStar_List.hd args1)
in (

let uu____18008 = (FStar_List.tl args1)
in ((uu____17999), (uu____18008))))
in (match (uu____17984) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (FStar_Pervasives_Native.fst result_arg))
in (

let rest1 = (desugar_args env rest)
in (

let uu____18063 = (

let is_decrease = (fun uu____18102 -> (match (uu____18102) with
| (t1, uu____18113) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____18124; FStar_Syntax_Syntax.vars = uu____18125}, (uu____18126)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.decreases_lid)
end
| uu____18165 -> begin
false
end)
end))
in (FStar_All.pipe_right rest1 (FStar_List.partition is_decrease)))
in (match (uu____18063) with
| (dec, rest2) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun uu____18282 -> (match (uu____18282) with
| (t1, uu____18292) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____18301, ((arg, uu____18303))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| uu____18342 -> begin
(failwith "impos")
end)
end))))
in (

let no_additional_args = (

let is_empty = (fun l -> (match (l) with
| [] -> begin
true
end
| uu____18363 -> begin
false
end))
in ((((is_empty decreases_clause) && (is_empty rest2)) && (is_empty cattributes)) && (is_empty universes1)))
in (

let uu____18375 = (no_additional_args && (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid))
in (match (uu____18375) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end
| uu____18380 -> begin
(

let uu____18382 = (no_additional_args && (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid))
in (match (uu____18382) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end
| uu____18387 -> begin
(

let flags = (

let uu____18392 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Lemma_lid)
in (match (uu____18392) with
| true -> begin
(FStar_Syntax_Syntax.LEMMA)::[]
end
| uu____18397 -> begin
(

let uu____18399 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid)
in (match (uu____18399) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____18404 -> begin
(

let uu____18406 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_ML_lid)
in (match (uu____18406) with
| true -> begin
(FStar_Syntax_Syntax.MLEFFECT)::[]
end
| uu____18411 -> begin
(

let uu____18413 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid)
in (match (uu____18413) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____18418 -> begin
[]
end))
end))
end))
end))
in (

let flags1 = (FStar_List.append flags cattributes)
in (

let rest3 = (

let uu____18434 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Lemma_lid)
in (match (uu____18434) with
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

let uu____18525 = (FStar_Ident.set_lid_range FStar_Parser_Const.pattern_lid pat.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar uu____18525 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.mk_Tm_app nil ((((pattern), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::[]) FStar_Pervasives_Native.None pat.FStar_Syntax_Syntax.pos)))
end
| uu____18546 -> begin
pat
end)
in (

let uu____18547 = (

let uu____18558 = (

let uu____18569 = (

let uu____18578 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat1), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) FStar_Pervasives_Native.None pat1.FStar_Syntax_Syntax.pos)
in ((uu____18578), (aq)))
in (uu____18569)::[])
in (ens)::uu____18558)
in (req)::uu____18547))
end
| uu____18619 -> begin
rest2
end)
end
| uu____18630 -> begin
rest2
end))
in (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = universes1; FStar_Syntax_Syntax.effect_name = eff; FStar_Syntax_Syntax.result_typ = result_typ; FStar_Syntax_Syntax.effect_args = rest3; FStar_Syntax_Syntax.flags = (FStar_List.append flags1 decreases_clause)}))))
end))
end))))
end))))
end)))
end)));
)
end))))))))))
and desugar_formula : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env f -> (

let mk1 = (fun t -> (FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let uu___2410_18654 = t
in {FStar_Syntax_Syntax.n = uu___2410_18654.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___2410_18654.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let uu___2417_18708 = b
in {FStar_Parser_AST.b = uu___2417_18708.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___2417_18708.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___2417_18708.FStar_Parser_AST.aqual}))
in (

let with_pats = (fun env1 uu____18737 body1 -> (match (uu____18737) with
| (names1, pats1) -> begin
(match (((names1), (pats1))) with
| ([], []) -> begin
body1
end
| ([], (uu____18783)::uu____18784) -> begin
(failwith "Impossible: Annotated pattern without binders in scope")
end
| uu____18802 -> begin
(

let names2 = (FStar_All.pipe_right names1 (FStar_List.map (fun i -> (

let uu___2436_18829 = (FStar_Syntax_DsEnv.fail_or2 (FStar_Syntax_DsEnv.try_lookup_id env1) i)
in {FStar_Syntax_Syntax.n = uu___2436_18829.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = i.FStar_Ident.idRange; FStar_Syntax_Syntax.vars = uu___2436_18829.FStar_Syntax_Syntax.vars}))))
in (

let pats2 = (FStar_All.pipe_right pats1 (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (

let uu____18892 = (desugar_term env1 e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) uu____18892))))))))
in (mk1 (FStar_Syntax_Syntax.Tm_meta (((body1), (FStar_Syntax_Syntax.Meta_pattern (((names2), (pats2))))))))))
end)
end))
in (match (tk) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____18923 = (FStar_Syntax_DsEnv.push_bv env a)
in (match (uu____18923) with
| (env1, a1) -> begin
(

let a2 = (

let uu___2449_18933 = a1
in {FStar_Syntax_Syntax.ppname = uu___2449_18933.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___2449_18933.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let body1 = (desugar_formula env1 body)
in (

let body2 = (with_pats env1 pats body1)
in (

let body3 = (

let uu____18939 = (

let uu____18942 = (

let uu____18943 = (FStar_Syntax_Syntax.mk_binder a2)
in (uu____18943)::[])
in (no_annot_abs uu____18942 body2))
in (FStar_All.pipe_left setpos uu____18939))
in (

let uu____18964 = (

let uu____18965 = (

let uu____18982 = (

let uu____18985 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Syntax_Syntax.fvar uu____18985 (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None))
in (

let uu____18987 = (

let uu____18998 = (FStar_Syntax_Syntax.as_arg body3)
in (uu____18998)::[])
in ((uu____18982), (uu____18987))))
in FStar_Syntax_Syntax.Tm_app (uu____18965))
in (FStar_All.pipe_left mk1 uu____18964))))))
end))
end
| uu____19037 -> begin
(failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body1 = (

let uu____19102 = (q ((rest), (pats), (body)))
in (

let uu____19105 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term uu____19102 uu____19105 FStar_Parser_AST.Formula)))
in (

let uu____19106 = (q (((b)::[]), ((([]), ([]))), (body1)))
in (FStar_Parser_AST.mk_term uu____19106 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| uu____19117 -> begin
(failwith "impossible")
end))
in (

let uu____19121 = (

let uu____19122 = (unparen f)
in uu____19122.FStar_Parser_AST.tm)
in (match (uu____19121) with
| FStar_Parser_AST.Labeled (f1, l, p) -> begin
(

let f2 = (desugar_formula env f1)
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((f2), (FStar_Syntax_Syntax.Meta_labeled (((l), (f2.FStar_Syntax_Syntax.pos), (p)))))))))
end
| FStar_Parser_AST.QForall ([], uu____19135, uu____19136) -> begin
(failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QExists ([], uu____19160, uu____19161) -> begin
(failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____19217 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env uu____19217)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____19261 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env uu____19261)))
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
| uu____19325 -> begin
(desugar_term env f)
end)))))))
and desugar_binder : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.TAnnotated (x, t) -> begin
(

let uu____19336 = (desugar_typ env t)
in ((FStar_Pervasives_Native.Some (x)), (uu____19336)))
end
| FStar_Parser_AST.Annotated (x, t) -> begin
(

let uu____19341 = (desugar_typ env t)
in ((FStar_Pervasives_Native.Some (x)), (uu____19341)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____19345 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) FStar_Pervasives_Native.None x.FStar_Ident.idRange)
in ((FStar_Pervasives_Native.Some (x)), (uu____19345)))
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____19349 = (desugar_typ env t)
in ((FStar_Pervasives_Native.None), (uu____19349)))
end
| FStar_Parser_AST.Variable (x) -> begin
((FStar_Pervasives_Native.Some (x)), (FStar_Syntax_Syntax.tun))
end))
and as_binder : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  (FStar_Ident.ident FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) * FStar_Syntax_DsEnv.env) = (fun env imp uu___12_19357 -> (match (uu___12_19357) with
| (FStar_Pervasives_Native.None, k) -> begin
(

let uu____19379 = (FStar_Syntax_Syntax.null_binder k)
in ((uu____19379), (env)))
end
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____19396 = (FStar_Syntax_DsEnv.push_bv env a)
in (match (uu____19396) with
| (env1, a1) -> begin
(

let uu____19413 = (

let uu____19420 = (trans_aqual env1 imp)
in (((

let uu___2549_19426 = a1
in {FStar_Syntax_Syntax.ppname = uu___2549_19426.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___2549_19426.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), (uu____19420)))
in ((uu____19413), (env1)))
end))
end))
and trans_aqual : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.aqual = (fun env uu___13_19434 -> (match (uu___13_19434) with
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)
end
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality)
end
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta (t)) -> begin
(

let uu____19438 = (

let uu____19439 = (desugar_term env t)
in FStar_Syntax_Syntax.Meta (uu____19439))
in FStar_Pervasives_Native.Some (uu____19438))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))


let typars_of_binders : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list) = (fun env bs -> (

let uu____19467 = (FStar_List.fold_left (fun uu____19500 b -> (match (uu____19500) with
| (env1, out) -> begin
(

let tk = (desugar_binder env1 (

let uu___2567_19544 = b
in {FStar_Parser_AST.b = uu___2567_19544.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___2567_19544.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___2567_19544.FStar_Parser_AST.aqual}))
in (match (tk) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____19559 = (FStar_Syntax_DsEnv.push_bv env1 a)
in (match (uu____19559) with
| (env2, a1) -> begin
(

let a2 = (

let uu___2577_19577 = a1
in {FStar_Syntax_Syntax.ppname = uu___2577_19577.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___2577_19577.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let uu____19578 = (

let uu____19585 = (

let uu____19590 = (trans_aqual env2 b.FStar_Parser_AST.aqual)
in ((a2), (uu____19590)))
in (uu____19585)::out)
in ((env2), (uu____19578))))
end))
end
| uu____19601 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedBinder), ("Unexpected binder")) b.FStar_Parser_AST.brange)
end))
end)) ((env), ([])) bs)
in (match (uu____19467) with
| (env1, tpars) -> begin
((env1), ((FStar_List.rev tpars)))
end)))


let desugar_attributes : env_t  ->  FStar_Parser_AST.term Prims.list  ->  FStar_Syntax_Syntax.cflag Prims.list = (fun env cattributes -> (

let desugar_attribute = (fun t -> (

let uu____19689 = (

let uu____19690 = (unparen t)
in uu____19690.FStar_Parser_AST.tm)
in (match (uu____19689) with
| FStar_Parser_AST.Var ({FStar_Ident.ns = uu____19691; FStar_Ident.ident = uu____19692; FStar_Ident.nsstr = uu____19693; FStar_Ident.str = "cps"}) -> begin
FStar_Syntax_Syntax.CPS
end
| uu____19698 -> begin
(

let uu____19699 = (

let uu____19705 = (

let uu____19707 = (FStar_Parser_AST.term_to_string t)
in (Prims.op_Hat "Unknown attribute " uu____19707))
in ((FStar_Errors.Fatal_UnknownAttribute), (uu____19705)))
in (FStar_Errors.raise_error uu____19699 t.FStar_Parser_AST.range))
end)))
in (FStar_List.map desugar_attribute cattributes)))


let binder_ident : FStar_Parser_AST.binder  ->  FStar_Ident.ident FStar_Pervasives_Native.option = (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.TAnnotated (x, uu____19724) -> begin
FStar_Pervasives_Native.Some (x)
end
| FStar_Parser_AST.Annotated (x, uu____19726) -> begin
FStar_Pervasives_Native.Some (x)
end
| FStar_Parser_AST.TVariable (x) -> begin
FStar_Pervasives_Native.Some (x)
end
| FStar_Parser_AST.Variable (x) -> begin
FStar_Pervasives_Native.Some (x)
end
| FStar_Parser_AST.NoName (uu____19729) -> begin
FStar_Pervasives_Native.None
end))


let binder_idents : FStar_Parser_AST.binder Prims.list  ->  FStar_Ident.ident Prims.list = (fun bs -> (FStar_List.collect (fun b -> (

let uu____19747 = (binder_ident b)
in (FStar_Common.list_of_option uu____19747))) bs))


let mk_data_discriminators : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_DsEnv.env  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun quals env datas -> (

let quals1 = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___14_19784 -> (match (uu___14_19784) with
| FStar_Syntax_Syntax.NoExtract -> begin
true
end
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____19789 -> begin
false
end))))
in (

let quals2 = (fun q -> (

let uu____19803 = ((

let uu____19807 = (FStar_Syntax_DsEnv.iface env)
in (not (uu____19807))) || (FStar_Syntax_DsEnv.admitted_iface env))
in (match (uu____19803) with
| true -> begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals1)
end
| uu____19812 -> begin
(FStar_List.append q quals1)
end)))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (

let uu____19824 = (FStar_Ident.range_of_lid disc_name)
in (

let uu____19825 = (quals2 ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((disc_name), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = uu____19824; FStar_Syntax_Syntax.sigquals = uu____19825; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []; FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None})))))))))


let mk_indexed_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  FStar_Syntax_DsEnv.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq env lid fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let uu____19865 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____19903 -> (match (uu____19903) with
| (x, uu____19914) -> begin
(

let uu____19919 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____19919) with
| (field_name, uu____19927) -> begin
(

let only_decl = (((

let uu____19932 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____19932)) || (Prims.op_disEquality fvq FStar_Syntax_Syntax.Data_ctor)) || (

let uu____19934 = (

let uu____19936 = (FStar_Syntax_DsEnv.current_module env)
in uu____19936.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____19934)))
in (

let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____19954 = (FStar_List.filter (fun uu___15_19958 -> (match (uu___15_19958) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____19961 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____19954)
end
| uu____19963 -> begin
q
end))
in (

let quals1 = (

let iquals1 = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___16_19976 -> (match (uu___16_19976) with
| FStar_Syntax_Syntax.NoExtract -> begin
true
end
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____19981 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals1)))
in (

let decl = (

let uu____19984 = (FStar_Ident.range_of_lid field_name)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = uu____19984; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []; FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None})
in (match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____19988 -> begin
(

let dd = (

let uu____19991 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____19991) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "1")))
end
| uu____19998 -> begin
FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "1"))
end))
in (

let lb = (

let uu____20002 = (

let uu____20007 = (FStar_Syntax_Syntax.lid_as_fv field_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____20007))
in {FStar_Syntax_Syntax.lbname = uu____20002; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbattrs = []; FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange})
in (

let impl = (

let uu____20011 = (

let uu____20012 = (

let uu____20019 = (

let uu____20022 = (

let uu____20023 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____20023 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____20022)::[])
in ((((false), ((lb)::[]))), (uu____20019)))
in FStar_Syntax_Syntax.Sig_let (uu____20012))
in {FStar_Syntax_Syntax.sigel = uu____20011; FStar_Syntax_Syntax.sigrng = p; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []; FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None})
in (match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____20039 -> begin
(decl)::(impl)::[]
end))))
end))))))
end))
end))))
in (FStar_All.pipe_right uu____19865 FStar_List.flatten))))


let mk_data_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____20072, t, uu____20074, n1, uu____20076) when (

let uu____20083 = (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
in (not (uu____20083))) -> begin
(

let uu____20085 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____20085) with
| (formals, uu____20103) -> begin
(match (formals) with
| [] -> begin
[]
end
| uu____20132 -> begin
(

let filter_records = (fun uu___17_20148 -> (match (uu___17_20148) with
| FStar_Syntax_Syntax.RecordConstructor (uu____20151, fns) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| uu____20163 -> begin
FStar_Pervasives_Native.None
end))
in (

let fv_qual = (

let uu____20165 = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals filter_records)
in (match (uu____20165) with
| FStar_Pervasives_Native.None -> begin
FStar_Syntax_Syntax.Data_ctor
end
| FStar_Pervasives_Native.Some (q) -> begin
q
end))
in (

let iquals1 = (match (((FStar_List.contains FStar_Syntax_Syntax.Abstract iquals) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private iquals))))) with
| true -> begin
(FStar_Syntax_Syntax.Private)::iquals
end
| uu____20175 -> begin
iquals
end)
in (

let uu____20177 = (FStar_Util.first_N n1 formals)
in (match (uu____20177) with
| (uu____20206, rest) -> begin
(mk_indexed_projector_names iquals1 fv_qual env lid rest)
end)))))
end)
end))
end
| uu____20240 -> begin
[]
end))


let mk_typ_abbrev : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.decl  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun env d lid uvs typars kopt t lids quals rng -> (

let attrs = (FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs)
in (

let val_attrs = (

let uu____20334 = (FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs env lid)
in (FStar_All.pipe_right uu____20334 FStar_Pervasives_Native.snd))
in (

let dd = (

let uu____20358 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____20358) with
| true -> begin
(

let uu____20364 = (FStar_Syntax_Util.incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (uu____20364))
end
| uu____20365 -> begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end))
in (

let lb = (

let uu____20368 = (

let uu____20373 = (FStar_Syntax_Syntax.lid_as_fv lid dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____20373))
in (

let uu____20374 = (match ((FStar_Util.is_some kopt)) with
| true -> begin
(

let uu____20380 = (

let uu____20383 = (FStar_All.pipe_right kopt FStar_Util.must)
in (FStar_Syntax_Syntax.mk_Total uu____20383))
in (FStar_Syntax_Util.arrow typars uu____20380))
end
| uu____20386 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let uu____20388 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = uu____20368; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____20374; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____20388; FStar_Syntax_Syntax.lbattrs = []; FStar_Syntax_Syntax.lbpos = rng})))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (lids))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = (FStar_List.append val_attrs attrs); FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None})))))


let rec desugar_tycon : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.decl  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d quals tcs -> (

let rng = d.FStar_Parser_AST.drange
in (

let tycon_id = (fun uu___18_20442 -> (match (uu___18_20442) with
| FStar_Parser_AST.TyconAbstract (id1, uu____20444, uu____20445) -> begin
id1
end
| FStar_Parser_AST.TyconAbbrev (id1, uu____20455, uu____20456, uu____20457) -> begin
id1
end
| FStar_Parser_AST.TyconRecord (id1, uu____20467, uu____20468, uu____20469) -> begin
id1
end
| FStar_Parser_AST.TyconVariant (id1, uu____20499, uu____20500, uu____20501) -> begin
id1
end))
in (

let binder_to_term1 = (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (x, uu____20547) -> begin
(

let uu____20548 = (

let uu____20549 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____20549))
in (FStar_Parser_AST.mk_term uu____20548 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| FStar_Parser_AST.Variable (x) -> begin
(

let uu____20551 = (

let uu____20552 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____20552))
in (FStar_Parser_AST.mk_term uu____20551 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| FStar_Parser_AST.TAnnotated (a, uu____20554) -> begin
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
| uu____20585 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (

let uu____20593 = (

let uu____20594 = (

let uu____20601 = (binder_to_term1 b)
in ((out), (uu____20601), ((imp_of_aqual b))))
in FStar_Parser_AST.App (uu____20594))
in (FStar_Parser_AST.mk_term uu____20593 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun uu___19_20613 -> (match (uu___19_20613) with
| FStar_Parser_AST.TyconRecord (id1, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.op_Hat "Mk" id1.FStar_Ident.idText)), (id1.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun uu____20670 -> (match (uu____20670) with
| (x, t, uu____20681) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated (((x), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr FStar_Pervasives_Native.None)
end)) fields)
in (

let result = (

let uu____20687 = (

let uu____20688 = (

let uu____20689 = (FStar_Ident.lid_of_ids ((id1)::[]))
in FStar_Parser_AST.Var (uu____20689))
in (FStar_Parser_AST.mk_term uu____20688 id1.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____20687 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id1.FStar_Ident.idRange FStar_Parser_AST.Type_level)
in (

let names1 = (

let uu____20696 = (binder_idents parms)
in (id1)::uu____20696)
in ((FStar_List.iter (fun uu____20714 -> (match (uu____20714) with
| (f, uu____20724, uu____20725) -> begin
(

let uu____20730 = (FStar_Util.for_some (fun i -> (FStar_Ident.ident_equals f i)) names1)
in (match (uu____20730) with
| true -> begin
(

let uu____20735 = (

let uu____20741 = (

let uu____20743 = (FStar_Ident.string_of_ident f)
in (FStar_Util.format1 "Field %s shadows the record\'s name or a parameter of it, please rename it" uu____20743))
in ((FStar_Errors.Error_FieldShadow), (uu____20741)))
in (FStar_Errors.raise_error uu____20735 f.FStar_Ident.idRange))
end
| uu____20747 -> begin
()
end))
end)) fields);
(

let uu____20749 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____20776 -> (match (uu____20776) with
| (x, uu____20786, uu____20787) -> begin
x
end))))
in ((FStar_Parser_AST.TyconVariant (((id1), (parms), (kopt), ((((constrName), (FStar_Pervasives_Native.Some (constrTyp)), (FStar_Pervasives_Native.None), (false)))::[])))), (uu____20749)));
))))))
end
| uu____20845 -> begin
(failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals1 _env mutuals uu___20_20885 -> (match (uu___20_20885) with
| FStar_Parser_AST.TyconAbstract (id1, binders, kopt) -> begin
(

let uu____20909 = (typars_of_binders _env binders)
in (match (uu____20909) with
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

let uu____20945 = (

let uu____20946 = (

let uu____20947 = (FStar_Ident.lid_of_ids ((id1)::[]))
in FStar_Parser_AST.Var (uu____20947))
in (FStar_Parser_AST.mk_term uu____20946 id1.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____20945 binders))
in (

let qlid = (FStar_Syntax_DsEnv.qualify _env id1)
in (

let typars1 = (FStar_Syntax_Subst.close_binders typars)
in (

let k1 = (FStar_Syntax_Subst.close typars1 k)
in (

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((qlid), ([]), (typars1), (k1), (mutuals), ([]))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []; FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None}
in (

let uu____20956 = (FStar_Syntax_DsEnv.push_top_level_rec_binding _env id1 FStar_Syntax_Syntax.delta_constant)
in (match (uu____20956) with
| (_env1, uu____20973) -> begin
(

let uu____20980 = (FStar_Syntax_DsEnv.push_top_level_rec_binding _env' id1 FStar_Syntax_Syntax.delta_constant)
in (match (uu____20980) with
| (_env2, uu____20997) -> begin
((_env1), (_env2), (se), (tconstr))
end))
end))))))))
end))
end
| uu____21004 -> begin
(failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env1 bs -> (

let uu____21047 = (FStar_List.fold_left (fun uu____21081 uu____21082 -> (match (((uu____21081), (uu____21082))) with
| ((env2, tps), (x, imp)) -> begin
(

let uu____21151 = (FStar_Syntax_DsEnv.push_bv env2 x.FStar_Syntax_Syntax.ppname)
in (match (uu____21151) with
| (env3, y) -> begin
((env3), ((((y), (imp)))::tps))
end))
end)) ((env1), ([])) bs)
in (match (uu____21047) with
| (env2, bs1) -> begin
((env2), ((FStar_List.rev bs1)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id1, bs, kopt))::[] -> begin
(

let kopt1 = (match (kopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____21242 = (tm_type_z id1.FStar_Ident.idRange)
in FStar_Pervasives_Native.Some (uu____21242))
end
| uu____21243 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id1), (bs), (kopt1)))
in (

let uu____21251 = (desugar_abstract_tc quals env [] tc)
in (match (uu____21251) with
| (uu____21264, uu____21265, se, uu____21267) -> begin
(

let se1 = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, uu____21270, typars, k, [], []) -> begin
(

let quals1 = se.FStar_Syntax_Syntax.sigquals
in (

let quals2 = (match ((FStar_List.contains FStar_Syntax_Syntax.Assumption quals1)) with
| true -> begin
quals1
end
| uu____21286 -> begin
((

let uu____21289 = (

let uu____21291 = (FStar_Options.ml_ish ())
in (not (uu____21291)))
in (match (uu____21289) with
| true -> begin
(

let uu____21294 = (

let uu____21300 = (

let uu____21302 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Adding an implicit \'assume new\' qualifier on %s" uu____21302))
in ((FStar_Errors.Warning_AddImplicitAssumeNewQualifier), (uu____21300)))
in (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng uu____21294))
end
| uu____21306 -> begin
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
| uu____21315 -> begin
(

let uu____21316 = (

let uu____21323 = (

let uu____21324 = (

let uu____21339 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (uu____21339)))
in FStar_Syntax_Syntax.Tm_arrow (uu____21324))
in (FStar_Syntax_Syntax.mk uu____21323))
in (uu____21316 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
end)
in (

let uu___2866_21352 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t))); FStar_Syntax_Syntax.sigrng = uu___2866_21352.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = uu___2866_21352.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___2866_21352.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___2866_21352.FStar_Syntax_Syntax.sigopts}))))
end
| uu____21353 -> begin
(failwith "Impossible")
end)
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se1)
in (

let env2 = (

let uu____21357 = (FStar_Syntax_DsEnv.qualify env1 id1)
in (FStar_Syntax_DsEnv.push_doc env1 uu____21357 d.FStar_Parser_AST.doc))
in ((env2), ((se1)::[])))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id1, binders, kopt, t))::[] -> begin
(

let uu____21370 = (typars_of_binders env binders)
in (match (uu____21370) with
| (env', typars) -> begin
(

let kopt1 = (match (kopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____21404 = (FStar_Util.for_some (fun uu___21_21407 -> (match (uu___21_21407) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| uu____21410 -> begin
false
end)) quals)
in (match (uu____21404) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.teff)
end
| uu____21415 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Pervasives_Native.Some (k) -> begin
(

let uu____21418 = (desugar_term env' k)
in FStar_Pervasives_Native.Some (uu____21418))
end)
in (

let t0 = t
in (

let quals1 = (

let uu____21423 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___22_21429 -> (match (uu___22_21429) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| uu____21432 -> begin
false
end))))
in (match (uu____21423) with
| true -> begin
quals
end
| uu____21437 -> begin
(match ((Prims.op_Equality t0.FStar_Parser_AST.level FStar_Parser_AST.Formula)) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals
end
| uu____21442 -> begin
quals
end)
end))
in (

let qlid = (FStar_Syntax_DsEnv.qualify env id1)
in (

let se = (

let uu____21446 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Effect))
in (match (uu____21446) with
| true -> begin
(

let uu____21452 = (

let uu____21459 = (

let uu____21460 = (unparen t)
in uu____21460.FStar_Parser_AST.tm)
in (match (uu____21459) with
| FStar_Parser_AST.Construct (head1, args) -> begin
(

let uu____21481 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____21511))::args_rev -> begin
(

let uu____21523 = (

let uu____21524 = (unparen last_arg)
in uu____21524.FStar_Parser_AST.tm)
in (match (uu____21523) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____21552 -> begin
(([]), (args))
end))
end
| uu____21561 -> begin
(([]), (args))
end)
in (match (uu____21481) with
| (cattributes, args1) -> begin
(

let uu____21600 = (desugar_attributes env cattributes)
in (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((head1), (args1)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (uu____21600)))
end))
end
| uu____21611 -> begin
((t), ([]))
end))
in (match (uu____21452) with
| (t1, cattributes) -> begin
(

let c = (desugar_comp t1.FStar_Parser_AST.range false env' t1)
in (

let typars1 = (FStar_Syntax_Subst.close_binders typars)
in (

let c1 = (FStar_Syntax_Subst.close_comp typars1 c)
in (

let quals2 = (FStar_All.pipe_right quals1 (FStar_List.filter (fun uu___23_21634 -> (match (uu___23_21634) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| uu____21637 -> begin
true
end))))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((qlid), ([]), (typars1), (c1), ((FStar_List.append cattributes (FStar_Syntax_Util.comp_flags c1))))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []; FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None}))))
end))
end
| uu____21641 -> begin
(

let t1 = (desugar_typ env' t)
in (mk_typ_abbrev env d qlid [] typars kopt1 t1 ((qlid)::[]) quals1 rng))
end))
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se)
in (

let env2 = (FStar_Syntax_DsEnv.push_doc env1 qlid d.FStar_Parser_AST.doc)
in ((env2), ((se)::[])))))))))
end))
end
| (FStar_Parser_AST.TyconRecord (uu____21646))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let uu____21670 = (tycon_record_as_variant trec)
in (match (uu____21670) with
| (t, fs) -> begin
(

let uu____21687 = (

let uu____21690 = (

let uu____21691 = (

let uu____21700 = (

let uu____21703 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Ident.ids_of_lid uu____21703))
in ((uu____21700), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____21691))
in (uu____21690)::quals)
in (desugar_tycon env d uu____21687 ((t)::[])))
end)))
end
| (uu____21708)::uu____21709 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals1 et tc -> (

let uu____21879 = et
in (match (uu____21879) with
| (env1, tcs1) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (uu____22109) -> begin
(

let trec = tc
in (

let uu____22133 = (tycon_record_as_variant trec)
in (match (uu____22133) with
| (t, fs) -> begin
(

let uu____22193 = (

let uu____22196 = (

let uu____22197 = (

let uu____22206 = (

let uu____22209 = (FStar_Syntax_DsEnv.current_module env1)
in (FStar_Ident.ids_of_lid uu____22209))
in ((uu____22206), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____22197))
in (uu____22196)::quals1)
in (collect_tcs uu____22193 ((env1), (tcs1)) t))
end)))
end
| FStar_Parser_AST.TyconVariant (id1, binders, kopt, constructors) -> begin
(

let uu____22299 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id1), (binders), (kopt)))))
in (match (uu____22299) with
| (env2, uu____22360, se, tconstr) -> begin
((env2), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals1))))::tcs1))
end))
end
| FStar_Parser_AST.TyconAbbrev (id1, binders, kopt, t) -> begin
(

let uu____22513 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id1), (binders), (kopt)))))
in (match (uu____22513) with
| (env2, uu____22574, se, tconstr) -> begin
((env2), ((FStar_Util.Inr (((se), (binders), (t), (quals1))))::tcs1))
end))
end
| uu____22702 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType), ("Mutually defined type contains a non-inductive element")) rng)
end)
end)))
in (

let uu____22752 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (uu____22752) with
| (env1, tcs1) -> begin
(

let tcs2 = (FStar_List.rev tcs1)
in (

let docs_tps_sigelts = (FStar_All.pipe_right tcs2 (FStar_List.collect (fun uu___25_23268 -> (match (uu___25_23268) with
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (id1, uvs, tpars, k, uu____23334, uu____23335); FStar_Syntax_Syntax.sigrng = uu____23336; FStar_Syntax_Syntax.sigquals = uu____23337; FStar_Syntax_Syntax.sigmeta = uu____23338; FStar_Syntax_Syntax.sigattrs = uu____23339; FStar_Syntax_Syntax.sigopts = uu____23340}, binders, t, quals1) -> begin
(

let t1 = (

let uu____23406 = (typars_of_binders env1 binders)
in (match (uu____23406) with
| (env2, tpars1) -> begin
(

let uu____23433 = (push_tparams env2 tpars1)
in (match (uu____23433) with
| (env_tps, tpars2) -> begin
(

let t1 = (desugar_typ env_tps t)
in (

let tpars3 = (FStar_Syntax_Subst.close_binders tpars2)
in (FStar_Syntax_Subst.close tpars3 t1)))
end))
end))
in (

let uu____23462 = (

let uu____23481 = (mk_typ_abbrev env1 d id1 uvs tpars (FStar_Pervasives_Native.Some (k)) t1 ((id1)::[]) quals1 rng)
in ((((id1), (d.FStar_Parser_AST.doc))), ([]), (uu____23481)))
in (uu____23462)::[]))
end
| FStar_Util.Inl ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs1, tpars, k, mutuals1, uu____23541); FStar_Syntax_Syntax.sigrng = uu____23542; FStar_Syntax_Syntax.sigquals = tname_quals; FStar_Syntax_Syntax.sigmeta = uu____23544; FStar_Syntax_Syntax.sigattrs = uu____23545; FStar_Syntax_Syntax.sigopts = uu____23546}, constrs, tconstr, quals1) -> begin
(

let mk_tot = (fun t -> (

let tot1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((tot1), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)))
in (

let tycon = ((tname), (tpars), (k))
in (

let uu____23649 = (push_tparams env1 tpars)
in (match (uu____23649) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun uu____23716 -> (match (uu____23716) with
| (x, uu____23728) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let tot_tconstr = (mk_tot tconstr)
in (

let attrs = (FStar_List.map (desugar_term env1) d.FStar_Parser_AST.attrs)
in (

let val_attrs = (

let uu____23739 = (FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs env1 tname)
in (FStar_All.pipe_right uu____23739 FStar_Pervasives_Native.snd))
in (

let uu____23762 = (

let uu____23789 = (FStar_All.pipe_right constrs (FStar_List.map (fun uu____23899 -> (match (uu____23899) with
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
| uu____23954 -> begin
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

let uu____23959 = (close env_tps t)
in (desugar_term env_tps uu____23959))
in (

let name = (FStar_Syntax_DsEnv.qualify env1 id1)
in (

let quals2 = (FStar_All.pipe_right tname_quals (FStar_List.collect (fun uu___24_23970 -> (match (uu___24_23970) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| uu____23982 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (

let uu____23990 = (

let uu____24009 = (

let uu____24010 = (

let uu____24011 = (

let uu____24027 = (

let uu____24028 = (

let uu____24031 = (FStar_All.pipe_right t1 FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total uu____24031))
in (FStar_Syntax_Util.arrow data_tpars uu____24028))
in ((name), (univs1), (uu____24027), (tname), (ntps), (mutuals1)))
in FStar_Syntax_Syntax.Sig_datacon (uu____24011))
in {FStar_Syntax_Syntax.sigel = uu____24010; FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = (FStar_List.append val_attrs attrs); FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None})
in ((((name), (doc1))), (tps), (uu____24009)))
in ((name), (uu____23990))))))))
end))))
in (FStar_All.pipe_left FStar_List.split uu____23789))
in (match (uu____23762) with
| (constrNames, constrs1) -> begin
(((((tname), (d.FStar_Parser_AST.doc))), ([]), ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs1), (tpars), (k), (mutuals1), (constrNames))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = tname_quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = (FStar_List.append val_attrs attrs); FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None})))::constrs1
end))))))
end))))
end
| uu____24243 -> begin
(failwith "impossible")
end))))
in (

let name_docs = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.map (fun uu____24371 -> (match (uu____24371) with
| (name_doc, uu____24397, uu____24398) -> begin
name_doc
end))))
in (

let sigelts = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.map (fun uu____24470 -> (match (uu____24470) with
| (uu____24489, uu____24490, se) -> begin
se
end))))
in (

let uu____24516 = (

let uu____24523 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle sigelts quals uu____24523 rng))
in (match (uu____24516) with
| (bundle, abbrevs) -> begin
(

let env2 = (FStar_Syntax_DsEnv.push_sigelt env0 bundle)
in (

let env3 = (FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env2 abbrevs)
in (

let data_ops = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.collect (fun uu____24585 -> (match (uu____24585) with
| (uu____24606, tps, se) -> begin
(mk_data_projector_names quals env3 se)
end))))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, uu____24654, tps, k, uu____24657, constrs) -> begin
(

let quals1 = se.FStar_Syntax_Syntax.sigquals
in (

let quals2 = (match (((FStar_List.contains FStar_Syntax_Syntax.Abstract quals1) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals1))))) with
| true -> begin
(FStar_Syntax_Syntax.Private)::quals1
end
| uu____24676 -> begin
quals1
end)
in (

let uu____24678 = (FStar_All.pipe_right constrs (FStar_List.filter (fun data_lid -> (

let data_quals = (

let data_se = (

let uu____24693 = (FStar_All.pipe_right sigelts (FStar_List.find (fun se1 -> (match (se1.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (name, uu____24710, uu____24711, uu____24712, uu____24713, uu____24714) -> begin
(FStar_Ident.lid_equals name data_lid)
end
| uu____24721 -> begin
false
end))))
in (FStar_All.pipe_right uu____24693 FStar_Util.must))
in data_se.FStar_Syntax_Syntax.sigquals)
in (

let uu____24725 = (FStar_All.pipe_right data_quals (FStar_List.existsb (fun uu___26_24732 -> (match (uu___26_24732) with
| FStar_Syntax_Syntax.RecordConstructor (uu____24734) -> begin
true
end
| uu____24744 -> begin
false
end))))
in (not (uu____24725)))))))
in (mk_data_discriminators quals2 env3 uu____24678))))
end
| uu____24746 -> begin
[]
end))))
in (

let ops = (FStar_List.append discs data_ops)
in (

let env4 = (FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env3 ops)
in (

let env5 = (FStar_List.fold_left (fun acc uu____24763 -> (match (uu____24763) with
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


let desugar_binders : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list) = (fun env binders -> (

let uu____24808 = (FStar_List.fold_left (fun uu____24843 b -> (match (uu____24843) with
| (env1, binders1) -> begin
(

let uu____24887 = (desugar_binder env1 b)
in (match (uu____24887) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____24910 = (as_binder env1 b.FStar_Parser_AST.aqual ((FStar_Pervasives_Native.Some (a)), (k)))
in (match (uu____24910) with
| (binder, env2) -> begin
((env2), ((binder)::binders1))
end))
end
| uu____24963 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_MissingNameInBinder), ("Missing name in binder")) b.FStar_Parser_AST.brange)
end))
end)) ((env), ([])) binders)
in (match (uu____24808) with
| (env1, binders1) -> begin
((env1), ((FStar_List.rev binders1)))
end)))


let push_reflect_effect : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lid  ->  FStar_Range.range  ->  FStar_Syntax_DsEnv.env = (fun env quals effect_name range -> (

let uu____25067 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___27_25074 -> (match (uu___27_25074) with
| FStar_Syntax_Syntax.Reflectable (uu____25076) -> begin
true
end
| uu____25078 -> begin
false
end))))
in (match (uu____25067) with
| true -> begin
(

let monad_env = (FStar_Syntax_DsEnv.enter_monad_scope env effect_name.FStar_Ident.ident)
in (

let reflect_lid = (

let uu____25083 = (FStar_Ident.id_of_text "reflect")
in (FStar_All.pipe_right uu____25083 (FStar_Syntax_DsEnv.qualify monad_env)))
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (effect_name))::[]
in (

let refl_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = range; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []; FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None}
in (FStar_Syntax_DsEnv.push_sigelt env refl_decl)))))
end
| uu____25089 -> begin
env
end)))


let parse_attr_with_list : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident  ->  (Prims.int Prims.list FStar_Pervasives_Native.option * Prims.bool) = (fun warn at1 head1 -> (

let warn1 = (fun uu____25134 -> (match (warn) with
| true -> begin
(

let uu____25136 = (

let uu____25142 = (

let uu____25144 = (FStar_Ident.string_of_lid head1)
in (FStar_Util.format1 "Found ill-applied \'%s\', argument should be a non-empty list of integer literals" uu____25144))
in ((FStar_Errors.Warning_UnappliedFail), (uu____25142)))
in (FStar_Errors.log_issue at1.FStar_Syntax_Syntax.pos uu____25136))
end
| uu____25148 -> begin
()
end))
in (

let uu____25150 = (FStar_Syntax_Util.head_and_args at1)
in (match (uu____25150) with
| (hd1, args) -> begin
(

let uu____25203 = (

let uu____25204 = (FStar_Syntax_Subst.compress hd1)
in uu____25204.FStar_Syntax_Syntax.n)
in (match (uu____25203) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv head1) -> begin
(match (args) with
| [] -> begin
((FStar_Pervasives_Native.Some ([])), (true))
end
| ((a1, uu____25248))::[] -> begin
(

let uu____25273 = (

let uu____25278 = (

let uu____25287 = (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_int)
in (FStar_Syntax_Embeddings.unembed uu____25287 a1))
in (uu____25278 true FStar_Syntax_Embeddings.id_norm_cb))
in (match (uu____25273) with
| FStar_Pervasives_Native.Some (es) -> begin
(

let uu____25310 = (

let uu____25316 = (FStar_List.map FStar_BigInt.to_int_fs es)
in FStar_Pervasives_Native.Some (uu____25316))
in ((uu____25310), (true)))
end
| uu____25331 -> begin
((warn1 ());
((FStar_Pervasives_Native.None), (true));
)
end))
end
| uu____25347 -> begin
((warn1 ());
((FStar_Pervasives_Native.None), (true));
)
end)
end
| uu____25369 -> begin
((FStar_Pervasives_Native.None), (false))
end))
end))))


let get_fail_attr : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  (Prims.int Prims.list * Prims.bool) FStar_Pervasives_Native.option = (fun warn at1 -> (

let rebind = (fun res b -> (match (res) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (l) -> begin
FStar_Pervasives_Native.Some (((l), (b)))
end))
in (

let uu____25486 = (parse_attr_with_list warn at1 FStar_Parser_Const.fail_attr)
in (match (uu____25486) with
| (res, matched) -> begin
(match (matched) with
| true -> begin
(rebind res false)
end
| uu____25533 -> begin
(

let uu____25535 = (parse_attr_with_list warn at1 FStar_Parser_Const.fail_lax_attr)
in (match (uu____25535) with
| (res1, uu____25557) -> begin
(rebind res1 true)
end))
end)
end))))


let rec desugar_effect : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  Prims.bool  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.term Prims.list  ->  (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals is_layered1 eff_name eff_binders eff_typ eff_decls attrs -> (

let env0 = env
in (

let monad_env = (FStar_Syntax_DsEnv.enter_monad_scope env eff_name)
in (

let uu____25729 = (desugar_binders monad_env eff_binders)
in (match (uu____25729) with
| (env1, binders) -> begin
(

let eff_t = (desugar_term env1 eff_typ)
in (

let num_indices = (

let uu____25768 = (

let uu____25777 = (FStar_Syntax_Util.arrow_formals eff_t)
in (FStar_Pervasives_Native.fst uu____25777))
in (FStar_List.length uu____25768))
in ((match ((is_layered1 && (num_indices <= (Prims.parse_int "1")))) with
| true -> begin
(

let uu____25811 = (

let uu____25817 = (

let uu____25819 = (

let uu____25821 = (FStar_Ident.text_of_id eff_name)
in (Prims.op_Hat uu____25821 "is defined as a layered effect but has no indices"))
in (Prims.op_Hat "Effect " uu____25819))
in ((FStar_Errors.Fatal_NotEnoughArgumentsForEffect), (uu____25817)))
in (FStar_Errors.raise_error uu____25811 d.FStar_Parser_AST.drange))
end
| uu____25826 -> begin
()
end);
(

let for_free = (Prims.op_Equality num_indices (Prims.parse_int "1"))
in (

let mandatory_members = (

let rr_members = ("repr")::("return")::("bind")::[]
in (match (for_free) with
| true -> begin
rr_members
end
| uu____25851 -> begin
(match (is_layered1) with
| true -> begin
(FStar_List.append rr_members (("subcomp")::("if_then_else")::[]))
end
| uu____25863 -> begin
(FStar_List.append rr_members (("return_wp")::("bind_wp")::("if_then_else")::("ite_wp")::("stronger")::("close_wp")::("trivial")::[]))
end)
end))
in (

let name_of_eff_decl = (fun decl -> (match (decl.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____25889, uu____25890, ((FStar_Parser_AST.TyconAbbrev (name, uu____25892, uu____25893, uu____25894), uu____25895))::[]) -> begin
(FStar_Ident.text_of_id name)
end
| uu____25932 -> begin
(failwith "Malformed effect member declaration.")
end))
in (

let uu____25935 = (FStar_List.partition (fun decl -> (

let uu____25947 = (name_of_eff_decl decl)
in (FStar_List.mem uu____25947 mandatory_members))) eff_decls)
in (match (uu____25935) with
| (mandatory_members_decls, actions) -> begin
(

let uu____25966 = (FStar_All.pipe_right mandatory_members_decls (FStar_List.fold_left (fun uu____25995 decl -> (match (uu____25995) with
| (env2, out) -> begin
(

let uu____26015 = (desugar_decl env2 decl)
in (match (uu____26015) with
| (env3, ses) -> begin
(

let uu____26028 = (

let uu____26031 = (FStar_List.hd ses)
in (uu____26031)::out)
in ((env3), (uu____26028)))
end))
end)) ((env1), ([]))))
in (match (uu____25966) with
| (env2, decls) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (

let actions_docs = (FStar_All.pipe_right actions (FStar_List.map (fun d1 -> (match (d1.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____26100, uu____26101, ((FStar_Parser_AST.TyconAbbrev (name, action_params, uu____26104, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (uu____26105, ((def, uu____26107))::((cps_type, uu____26109))::[]); FStar_Parser_AST.range = uu____26110; FStar_Parser_AST.level = uu____26111}), doc1))::[]) when (not (for_free)) -> begin
(

let uu____26167 = (desugar_binders env2 action_params)
in (match (uu____26167) with
| (env3, action_params1) -> begin
(

let action_params2 = (FStar_Syntax_Subst.close_binders action_params1)
in (

let uu____26205 = (

let uu____26206 = (FStar_Syntax_DsEnv.qualify env3 name)
in (

let uu____26207 = (

let uu____26208 = (desugar_term env3 def)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____26208))
in (

let uu____26215 = (

let uu____26216 = (desugar_typ env3 cps_type)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____26216))
in {FStar_Syntax_Syntax.action_name = uu____26206; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = action_params2; FStar_Syntax_Syntax.action_defn = uu____26207; FStar_Syntax_Syntax.action_typ = uu____26215})))
in ((uu____26205), (doc1))))
end))
end
| FStar_Parser_AST.Tycon (uu____26225, uu____26226, ((FStar_Parser_AST.TyconAbbrev (name, action_params, uu____26229, defn), doc1))::[]) when (for_free || is_layered1) -> begin
(

let uu____26268 = (desugar_binders env2 action_params)
in (match (uu____26268) with
| (env3, action_params1) -> begin
(

let action_params2 = (FStar_Syntax_Subst.close_binders action_params1)
in (

let uu____26306 = (

let uu____26307 = (FStar_Syntax_DsEnv.qualify env3 name)
in (

let uu____26308 = (

let uu____26309 = (desugar_term env3 defn)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____26309))
in {FStar_Syntax_Syntax.action_name = uu____26307; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = action_params2; FStar_Syntax_Syntax.action_defn = uu____26308; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
in ((uu____26306), (doc1))))
end))
end
| uu____26318 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_MalformedActionDeclaration), ("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).")) d1.FStar_Parser_AST.drange)
end))))
in (

let actions1 = (FStar_List.map FStar_Pervasives_Native.fst actions_docs)
in (

let eff_t1 = (FStar_Syntax_Subst.close binders1 eff_t)
in (

let lookup1 = (fun s -> (

let l = (

let uu____26354 = (FStar_Ident.mk_ident ((s), (d.FStar_Parser_AST.drange)))
in (FStar_Syntax_DsEnv.qualify env2 uu____26354))
in (

let uu____26356 = (

let uu____26357 = (FStar_Syntax_DsEnv.fail_or env2 (FStar_Syntax_DsEnv.try_lookup_definition env2) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders1) uu____26357))
in (([]), (uu____26356)))))
in (

let mname = (FStar_Syntax_DsEnv.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange (FStar_Pervasives_Native.Some (mname))) quals)
in (

let dummy_tscheme = (([]), (FStar_Syntax_Syntax.tun))
in (

let combinators = (match (for_free) with
| true -> begin
(

let uu____26379 = (

let uu____26380 = (

let uu____26383 = (lookup1 "repr")
in FStar_Pervasives_Native.Some (uu____26383))
in (

let uu____26385 = (

let uu____26388 = (lookup1 "return")
in FStar_Pervasives_Native.Some (uu____26388))
in (

let uu____26390 = (

let uu____26393 = (lookup1 "bind")
in FStar_Pervasives_Native.Some (uu____26393))
in {FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = uu____26380; FStar_Syntax_Syntax.return_repr = uu____26385; FStar_Syntax_Syntax.bind_repr = uu____26390})))
in FStar_Syntax_Syntax.DM4F_eff (uu____26379))
end
| uu____26395 -> begin
(match (is_layered1) with
| true -> begin
(

let to_comb = (fun uu____26431 -> (match (uu____26431) with
| (us, t) -> begin
((((us), (t))), (dummy_tscheme))
end))
in (

let uu____26490 = (

let uu____26491 = (FStar_Ident.lid_of_str "")
in (

let uu____26493 = (

let uu____26498 = (lookup1 "repr")
in (FStar_All.pipe_right uu____26498 to_comb))
in (

let uu____26520 = (

let uu____26525 = (lookup1 "return")
in (FStar_All.pipe_right uu____26525 to_comb))
in (

let uu____26547 = (

let uu____26552 = (lookup1 "bind")
in (FStar_All.pipe_right uu____26552 to_comb))
in (

let uu____26574 = (

let uu____26579 = (lookup1 "subcomp")
in (FStar_All.pipe_right uu____26579 to_comb))
in (

let uu____26601 = (

let uu____26606 = (lookup1 "if_then_else")
in (FStar_All.pipe_right uu____26606 to_comb))
in {FStar_Syntax_Syntax.l_base_effect = uu____26491; FStar_Syntax_Syntax.l_repr = uu____26493; FStar_Syntax_Syntax.l_return = uu____26520; FStar_Syntax_Syntax.l_bind = uu____26547; FStar_Syntax_Syntax.l_subcomp = uu____26574; FStar_Syntax_Syntax.l_if_then_else = uu____26601}))))))
in FStar_Syntax_Syntax.Layered_eff (uu____26490)))
end
| uu____26628 -> begin
(

let rr = (FStar_Util.for_some (fun uu___28_26633 -> (match (uu___28_26633) with
| FStar_Syntax_Syntax.Reifiable -> begin
true
end
| FStar_Syntax_Syntax.Reflectable (uu____26636) -> begin
true
end
| uu____26638 -> begin
false
end)) qualifiers)
in (

let uu____26640 = (

let uu____26641 = (lookup1 "return_wp")
in (

let uu____26643 = (lookup1 "bind_wp")
in (

let uu____26645 = (lookup1 "stronger")
in (

let uu____26647 = (lookup1 "if_then_else")
in (

let uu____26649 = (lookup1 "ite_wp")
in (

let uu____26651 = (lookup1 "close_wp")
in (

let uu____26653 = (lookup1 "trivial")
in (

let uu____26655 = (match (rr) with
| true -> begin
(

let uu____26661 = (lookup1 "repr")
in FStar_Pervasives_Native.Some (uu____26661))
end
| uu____26663 -> begin
FStar_Pervasives_Native.None
end)
in (

let uu____26665 = (match (rr) with
| true -> begin
(

let uu____26671 = (lookup1 "return")
in FStar_Pervasives_Native.Some (uu____26671))
end
| uu____26673 -> begin
FStar_Pervasives_Native.None
end)
in (

let uu____26675 = (match (rr) with
| true -> begin
(

let uu____26681 = (lookup1 "bind")
in FStar_Pervasives_Native.Some (uu____26681))
end
| uu____26683 -> begin
FStar_Pervasives_Native.None
end)
in {FStar_Syntax_Syntax.ret_wp = uu____26641; FStar_Syntax_Syntax.bind_wp = uu____26643; FStar_Syntax_Syntax.stronger = uu____26645; FStar_Syntax_Syntax.if_then_else = uu____26647; FStar_Syntax_Syntax.ite_wp = uu____26649; FStar_Syntax_Syntax.close_wp = uu____26651; FStar_Syntax_Syntax.trivial = uu____26653; FStar_Syntax_Syntax.repr = uu____26655; FStar_Syntax_Syntax.return_repr = uu____26665; FStar_Syntax_Syntax.bind_repr = uu____26675}))))))))))
in FStar_Syntax_Syntax.Primitive_eff (uu____26640)))
end)
end)
in (

let sigel = (

let uu____26686 = (

let uu____26687 = (FStar_List.map (desugar_term env2) attrs)
in {FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = (([]), (eff_t1)); FStar_Syntax_Syntax.combinators = combinators; FStar_Syntax_Syntax.actions = actions1; FStar_Syntax_Syntax.eff_attrs = uu____26687})
in FStar_Syntax_Syntax.Sig_new_effect (uu____26686))
in (

let se = {FStar_Syntax_Syntax.sigel = sigel; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qualifiers; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []; FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None}
in (

let env3 = (FStar_Syntax_DsEnv.push_sigelt env0 se)
in (

let env4 = (FStar_Syntax_DsEnv.push_doc env3 mname d.FStar_Parser_AST.doc)
in (

let env5 = (FStar_All.pipe_right actions_docs (FStar_List.fold_left (fun env5 uu____26718 -> (match (uu____26718) with
| (a, doc1) -> begin
(

let env6 = (

let uu____26732 = (FStar_Syntax_Util.action_as_lb mname a a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_DsEnv.push_sigelt env5 uu____26732))
in (FStar_Syntax_DsEnv.push_doc env6 a.FStar_Syntax_Syntax.action_name doc1))
end)) env4))
in (

let env6 = (push_reflect_effect env5 qualifiers mname d.FStar_Parser_AST.drange)
in (

let env7 = (FStar_Syntax_DsEnv.push_doc env6 mname d.FStar_Parser_AST.doc)
in ((env7), ((se)::[]))))))))))))))))))
end))
end)))));
)))
end)))))
and desugar_redefine_effect : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.decl  ->  (FStar_Ident.lident FStar_Pervasives_Native.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier)  ->  FStar_Parser_AST.qualifier Prims.list  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d trans_qual1 quals eff_name eff_binders defn -> (

let env0 = env
in (

let env1 = (FStar_Syntax_DsEnv.enter_monad_scope env eff_name)
in (

let uu____26756 = (desugar_binders env1 eff_binders)
in (match (uu____26756) with
| (env2, binders) -> begin
(

let uu____26793 = (

let uu____26804 = (head_and_args defn)
in (match (uu____26804) with
| (head1, args) -> begin
(

let lid = (match (head1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
l
end
| uu____26841 -> begin
(

let uu____26842 = (

let uu____26848 = (

let uu____26850 = (

let uu____26852 = (FStar_Parser_AST.term_to_string head1)
in (Prims.op_Hat uu____26852 " not found"))
in (Prims.op_Hat "Effect " uu____26850))
in ((FStar_Errors.Fatal_EffectNotFound), (uu____26848)))
in (FStar_Errors.raise_error uu____26842 d.FStar_Parser_AST.drange))
end)
in (

let ed = (FStar_Syntax_DsEnv.fail_or env2 (FStar_Syntax_DsEnv.try_lookup_effect_defn env2) lid)
in (

let uu____26858 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____26888))::args_rev -> begin
(

let uu____26900 = (

let uu____26901 = (unparen last_arg)
in uu____26901.FStar_Parser_AST.tm)
in (match (uu____26900) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____26929 -> begin
(([]), (args))
end))
end
| uu____26938 -> begin
(([]), (args))
end)
in (match (uu____26858) with
| (cattributes, args1) -> begin
(

let uu____26981 = (desugar_args env2 args1)
in (

let uu____26982 = (desugar_attributes env2 cattributes)
in ((lid), (ed), (uu____26981), (uu____26982))))
end))))
end))
in (match (uu____26793) with
| (ed_lid, ed, args, cattributes) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in ((match ((Prims.op_disEquality (FStar_List.length args) (FStar_List.length ed.FStar_Syntax_Syntax.binders))) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ArgumentLengthMismatch), ("Unexpected number of arguments to effect constructor")) defn.FStar_Parser_AST.range)
end
| uu____27020 -> begin
()
end);
(

let uu____27022 = (FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit)
in (match (uu____27022) with
| (ed_binders, uu____27036, ed_binders_opening) -> begin
(

let sub' = (fun shift_n uu____27055 -> (match (uu____27055) with
| (us, x) -> begin
(

let x1 = (

let uu____27070 = (FStar_Syntax_Subst.shift_subst (shift_n + (FStar_List.length us)) ed_binders_opening)
in (FStar_Syntax_Subst.subst uu____27070 x))
in (

let s = (FStar_Syntax_Util.subst_of_list ed_binders args)
in (

let uu____27074 = (

let uu____27075 = (FStar_Syntax_Subst.subst s x1)
in ((us), (uu____27075)))
in (FStar_Syntax_Subst.close_tscheme binders1 uu____27074))))
end))
in (

let sub1 = (sub' (Prims.parse_int "0"))
in (

let mname = (FStar_Syntax_DsEnv.qualify env0 eff_name)
in (

let ed1 = (

let uu____27096 = (sub1 ed.FStar_Syntax_Syntax.signature)
in (

let uu____27097 = (FStar_Syntax_Util.apply_eff_combinators sub1 ed.FStar_Syntax_Syntax.combinators)
in (

let uu____27098 = (FStar_List.map (fun action -> (

let nparam = (FStar_List.length action.FStar_Syntax_Syntax.action_params)
in (

let uu____27114 = (FStar_Syntax_DsEnv.qualify env2 action.FStar_Syntax_Syntax.action_unqualified_name)
in (

let uu____27115 = (

let uu____27116 = (sub' nparam (([]), (action.FStar_Syntax_Syntax.action_defn)))
in (FStar_Pervasives_Native.snd uu____27116))
in (

let uu____27131 = (

let uu____27132 = (sub' nparam (([]), (action.FStar_Syntax_Syntax.action_typ)))
in (FStar_Pervasives_Native.snd uu____27132))
in {FStar_Syntax_Syntax.action_name = uu____27114; FStar_Syntax_Syntax.action_unqualified_name = action.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = action.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = uu____27115; FStar_Syntax_Syntax.action_typ = uu____27131}))))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.cattributes = cattributes; FStar_Syntax_Syntax.univs = ed.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = uu____27096; FStar_Syntax_Syntax.combinators = uu____27097; FStar_Syntax_Syntax.actions = uu____27098; FStar_Syntax_Syntax.eff_attrs = ed.FStar_Syntax_Syntax.eff_attrs})))
in (

let se = (

let uu____27148 = (

let uu____27151 = (trans_qual1 (FStar_Pervasives_Native.Some (mname)))
in (FStar_List.map uu____27151 quals))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (ed1); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = uu____27148; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []; FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None})
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

let uu____27172 = (FStar_Syntax_Util.action_as_lb mname a a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_DsEnv.push_sigelt env5 uu____27172))
in (FStar_Syntax_DsEnv.push_doc env6 a.FStar_Syntax_Syntax.action_name doc1)))) env4))
in (

let env6 = (

let uu____27174 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____27174) with
| true -> begin
(

let reflect_lid = (

let uu____27181 = (FStar_Ident.id_of_text "reflect")
in (FStar_All.pipe_right uu____27181 (FStar_Syntax_DsEnv.qualify monad_env)))
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]
in (

let refl_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []; FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None}
in (FStar_Syntax_DsEnv.push_sigelt env5 refl_decl))))
end
| uu____27187 -> begin
env5
end))
in (

let env7 = (FStar_Syntax_DsEnv.push_doc env6 mname d.FStar_Parser_AST.doc)
in ((env7), ((se)::[])))))))))))))
end));
))
end))
end)))))
and mk_comment_attr : FStar_Parser_AST.decl  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list = (fun d -> (

let uu____27193 = (match (d.FStar_Parser_AST.doc) with
| FStar_Pervasives_Native.None -> begin
((""), ([]))
end
| FStar_Pervasives_Native.Some (fsdoc) -> begin
fsdoc
end)
in (match (uu____27193) with
| (text, kv) -> begin
(

let summary = (match ((FStar_List.assoc "summary" kv)) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (s) -> begin
(Prims.op_Hat "  " (Prims.op_Hat s "\n"))
end)
in (

let pp = (match ((FStar_List.assoc "type" kv)) with
| FStar_Pervasives_Native.Some (uu____27280) -> begin
(

let uu____27283 = (

let uu____27285 = (FStar_Parser_ToDocument.signature_to_document d)
in (FStar_Pprint.pretty_string 0.950000 (Prims.parse_int "80") uu____27285))
in (Prims.op_Hat "\n  " uu____27283))
end
| uu____27288 -> begin
""
end)
in (

let other = (FStar_List.filter_map (fun uu____27307 -> (match (uu____27307) with
| (k, v1) -> begin
(match (((Prims.op_disEquality k "summary") && (Prims.op_disEquality k "type"))) with
| true -> begin
FStar_Pervasives_Native.Some ((Prims.op_Hat k (Prims.op_Hat ": " v1)))
end
| uu____27333 -> begin
FStar_Pervasives_Native.None
end)
end)) kv)
in (

let other1 = (match ((Prims.op_disEquality other [])) with
| true -> begin
(Prims.op_Hat (FStar_String.concat "\n" other) "\n")
end
| uu____27346 -> begin
""
end)
in (

let str = (Prims.op_Hat summary (Prims.op_Hat pp (Prims.op_Hat other1 text)))
in (

let fv = (

let uu____27352 = (FStar_Ident.lid_of_str "FStar.Pervasives.Comment")
in (FStar_Syntax_Syntax.fvar uu____27352 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))
in (match ((Prims.op_Equality str "")) with
| true -> begin
[]
end
| uu____27363 -> begin
(

let arg = (FStar_Syntax_Util.exp_string str)
in (

let uu____27366 = (

let uu____27369 = (

let uu____27380 = (FStar_Syntax_Syntax.as_arg arg)
in (uu____27380)::[])
in (FStar_Syntax_Util.mk_app fv uu____27369))
in (uu____27366)::[]))
end)))))))
end)))
and desugar_decl_aux : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (

let env0 = (

let uu____27416 = (FStar_Syntax_DsEnv.snapshot env)
in (FStar_All.pipe_right uu____27416 FStar_Pervasives_Native.snd))
in (

let uu____27428 = (desugar_decl_noattrs env d)
in (match (uu____27428) with
| (env1, sigelts) -> begin
(

let attrs = (FStar_List.map (desugar_term env1) d.FStar_Parser_AST.attrs)
in (

let val_attrs = (match (sigelts) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (uu____27455); FStar_Syntax_Syntax.sigrng = uu____27456; FStar_Syntax_Syntax.sigquals = uu____27457; FStar_Syntax_Syntax.sigmeta = uu____27458; FStar_Syntax_Syntax.sigattrs = uu____27459; FStar_Syntax_Syntax.sigopts = uu____27460})::[] -> begin
(

let uu____27473 = (

let uu____27476 = (

let uu____27479 = (FStar_List.hd sigelts)
in (FStar_Syntax_Util.lids_of_sigelt uu____27479))
in (FStar_All.pipe_right uu____27476 (FStar_List.collect (fun nm -> (

let uu____27487 = (FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs env0 nm)
in (FStar_Pervasives_Native.snd uu____27487))))))
in (FStar_All.pipe_right uu____27473 (FStar_List.filter (fun t -> (

let uu____27509 = (get_fail_attr false t)
in (FStar_Option.isNone uu____27509))))))
end
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____27529); FStar_Syntax_Syntax.sigrng = uu____27530; FStar_Syntax_Syntax.sigquals = uu____27531; FStar_Syntax_Syntax.sigmeta = uu____27532; FStar_Syntax_Syntax.sigattrs = uu____27533; FStar_Syntax_Syntax.sigopts = uu____27534})::uu____27535 -> begin
(

let uu____27560 = (

let uu____27563 = (

let uu____27566 = (FStar_List.hd sigelts)
in (FStar_Syntax_Util.lids_of_sigelt uu____27566))
in (FStar_All.pipe_right uu____27563 (FStar_List.collect (fun nm -> (

let uu____27574 = (FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs env0 nm)
in (FStar_Pervasives_Native.snd uu____27574))))))
in (FStar_All.pipe_right uu____27560 (FStar_List.filter (fun t -> (

let uu____27596 = (get_fail_attr false t)
in (FStar_Option.isNone uu____27596))))))
end
| uu____27616 -> begin
[]
end)
in (

let attrs1 = (

let uu____27624 = (mk_comment_attr d)
in (FStar_List.append uu____27624 (FStar_List.append attrs val_attrs)))
in (

let uu____27633 = (FStar_List.mapi (fun i sigelt -> (match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
(

let uu___3468_27643 = sigelt
in {FStar_Syntax_Syntax.sigel = uu___3468_27643.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___3468_27643.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___3468_27643.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___3468_27643.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = attrs1; FStar_Syntax_Syntax.sigopts = uu___3468_27643.FStar_Syntax_Syntax.sigopts})
end
| uu____27644 -> begin
(

let uu___3470_27646 = sigelt
in (

let uu____27647 = (FStar_List.filter (fun at1 -> (

let uu____27653 = (get_fail_attr false at1)
in (FStar_Option.isNone uu____27653))) attrs1)
in {FStar_Syntax_Syntax.sigel = uu___3470_27646.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___3470_27646.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___3470_27646.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___3470_27646.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu____27647; FStar_Syntax_Syntax.sigopts = uu___3470_27646.FStar_Syntax_Syntax.sigopts}))
end)) sigelts)
in ((env1), (uu____27633))))))
end))))
and desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (

let uu____27679 = (desugar_decl_aux env d)
in (match (uu____27679) with
| (env1, ses) -> begin
(

let uu____27690 = (FStar_All.pipe_right ses (FStar_List.map generalize_annotated_univs))
in ((env1), (uu____27690)))
end)))
and desugar_decl_noattrs : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (

let trans_qual1 = (trans_qual d.FStar_Parser_AST.drange)
in (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(

let p1 = (trans_pragma p)
in ((FStar_Syntax_Util.process_pragma p1 d.FStar_Parser_AST.drange);
(

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_pragma (p1); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []; FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None}
in ((env), ((se)::[])));
))
end
| FStar_Parser_AST.Fsdoc (uu____27718) -> begin
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
| FStar_Parser_AST.Friend (lid) -> begin
(

let uu____27723 = (FStar_Syntax_DsEnv.iface env)
in (match (uu____27723) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_FriendInterface), ("\'friend\' declarations are not allowed in interfaces")) d.FStar_Parser_AST.drange)
end
| uu____27736 -> begin
(

let uu____27738 = (

let uu____27740 = (

let uu____27742 = (FStar_Syntax_DsEnv.dep_graph env)
in (

let uu____27743 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Parser_Dep.module_has_interface uu____27742 uu____27743)))
in (not (uu____27740)))
in (match (uu____27738) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_FriendInterface), ("\'friend\' declarations are not allowed in modules that lack interfaces")) d.FStar_Parser_AST.drange)
end
| uu____27755 -> begin
(

let uu____27757 = (

let uu____27759 = (

let uu____27761 = (FStar_Syntax_DsEnv.dep_graph env)
in (FStar_Parser_Dep.module_has_interface uu____27761 lid))
in (not (uu____27759)))
in (match (uu____27757) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_FriendInterface), ("\'friend\' declarations cannot refer to modules that lack interfaces")) d.FStar_Parser_AST.drange)
end
| uu____27773 -> begin
(

let uu____27775 = (

let uu____27777 = (

let uu____27779 = (FStar_Syntax_DsEnv.dep_graph env)
in (FStar_Parser_Dep.deps_has_implementation uu____27779 lid))
in (not (uu____27777)))
in (match (uu____27775) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_FriendInterface), ("\'friend\' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")) d.FStar_Parser_AST.drange)
end
| uu____27791 -> begin
((env), ([]))
end))
end))
end))
end))
end
| FStar_Parser_AST.Include (lid) -> begin
(

let env1 = (FStar_Syntax_DsEnv.push_include env lid)
in ((env1), ([])))
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(

let uu____27797 = (FStar_Syntax_DsEnv.push_module_abbrev env x l)
in ((uu____27797), ([])))
end
| FStar_Parser_AST.Tycon (is_effect, typeclass, tcs) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let quals1 = (match (is_effect) with
| true -> begin
(FStar_Parser_AST.Effect_qual)::quals
end
| uu____27828 -> begin
quals
end)
in (

let quals2 = (match (typeclass) with
| true -> begin
(match (tcs) with
| ((FStar_Parser_AST.TyconRecord (uu____27838), uu____27839))::[] -> begin
(FStar_Parser_AST.Noeq)::quals1
end
| uu____27878 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Error_BadClassDecl), ("Ill-formed `class` declaration: definition must be a record type")) d.FStar_Parser_AST.drange)
end)
end
| uu____27891 -> begin
quals1
end)
in (

let tcs1 = (FStar_List.map (fun uu____27905 -> (match (uu____27905) with
| (x, uu____27913) -> begin
x
end)) tcs)
in (

let uu____27918 = (

let uu____27923 = (FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals2)
in (desugar_tycon env d uu____27923 tcs1))
in (match (uu____27918) with
| (env1, ses) -> begin
(

let mkclass = (fun lid -> (

let uu____27940 = (

let uu____27941 = (

let uu____27948 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (FStar_Syntax_Syntax.mk_binder uu____27948))
in (uu____27941)::[])
in (

let uu____27961 = (

let uu____27964 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.mk_class_lid)
in (

let uu____27967 = (

let uu____27978 = (

let uu____27987 = (

let uu____27988 = (FStar_Ident.string_of_lid lid)
in (FStar_Syntax_Util.exp_string uu____27988))
in (FStar_Syntax_Syntax.as_arg uu____27987))
in (uu____27978)::[])
in (FStar_Syntax_Util.mk_app uu____27964 uu____27967)))
in (FStar_Syntax_Util.abs uu____27940 uu____27961 FStar_Pervasives_Native.None))))
in (

let get_meths = (fun se -> (

let rec get_fname = (fun quals3 -> (match (quals3) with
| (FStar_Syntax_Syntax.Projector (uu____28028, id1))::uu____28030 -> begin
FStar_Pervasives_Native.Some (id1)
end
| (uu____28033)::quals4 -> begin
(get_fname quals4)
end
| [] -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____28037 = (get_fname se.FStar_Syntax_Syntax.sigquals)
in (match (uu____28037) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (id1) -> begin
(

let uu____28043 = (FStar_Syntax_DsEnv.qualify env1 id1)
in (uu____28043)::[])
end))))
in (

let rec splice_decl = (fun meths se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses1, uu____28064) -> begin
(FStar_List.concatMap (splice_decl meths) ses1)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____28074, uu____28075, uu____28076, uu____28077, uu____28078) -> begin
(

let uu____28087 = (

let uu____28088 = (

let uu____28089 = (

let uu____28096 = (mkclass lid)
in ((meths), (uu____28096)))
in FStar_Syntax_Syntax.Sig_splice (uu____28089))
in {FStar_Syntax_Syntax.sigel = uu____28088; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []; FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None})
in (uu____28087)::[])
end
| uu____28099 -> begin
[]
end))
in (

let extra = (match (typeclass) with
| true -> begin
(

let meths = (FStar_List.concatMap get_meths ses)
in (FStar_List.concatMap (splice_decl meths) ses))
end
| uu____28109 -> begin
[]
end)
in (

let env2 = (FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env1 extra)
in ((env2), ((FStar_List.append ses extra))))))))
end))))))
end
| FStar_Parser_AST.TopLevelLet (isrec, lets) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let expand_toplevel_pattern = ((Prims.op_Equality isrec FStar_Parser_AST.NoLetQualifier) && (match (lets) with
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatOp (uu____28133); FStar_Parser_AST.prange = uu____28134}, uu____28135))::[] -> begin
false
end
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____28145); FStar_Parser_AST.prange = uu____28146}, uu____28147))::[] -> begin
false
end
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatOp (uu____28163); FStar_Parser_AST.prange = uu____28164}, uu____28165); FStar_Parser_AST.prange = uu____28166}, uu____28167))::[] -> begin
false
end
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____28189); FStar_Parser_AST.prange = uu____28190}, uu____28191); FStar_Parser_AST.prange = uu____28192}, uu____28193))::[] -> begin
false
end
| ((p, uu____28222))::[] -> begin
(

let uu____28231 = (is_app_pattern p)
in (not (uu____28231)))
end
| uu____28233 -> begin
false
end))
in (match ((not (expand_toplevel_pattern))) with
| true -> begin
(

let lets1 = (FStar_List.map (fun x -> ((FStar_Pervasives_Native.None), (x))) lets)
in (

let as_inner_let = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets1), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)
in (

let uu____28308 = (desugar_term_maybe_top true env as_inner_let)
in (match (uu____28308) with
| (ds_lets, aq) -> begin
((check_no_aq aq);
(

let uu____28321 = (

let uu____28322 = (FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets)
in uu____28322.FStar_Syntax_Syntax.n)
in (match (uu____28321) with
| FStar_Syntax_Syntax.Tm_let (lbs, uu____28332) -> begin
(

let fvs = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let uu____28363 = (FStar_List.fold_right (fun fv uu____28388 -> (match (uu____28388) with
| (qs, ats) -> begin
(

let uu____28415 = (FStar_Syntax_DsEnv.lookup_letbinding_quals_and_attrs env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (match (uu____28415) with
| (qs', ats') -> begin
(((FStar_List.append qs' qs)), ((FStar_List.append ats' ats)))
end))
end)) fvs (([]), ([])))
in (match (uu____28363) with
| (val_quals, val_attrs) -> begin
(

let quals1 = (match (quals) with
| (uu____28469)::uu____28470 -> begin
(FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals)
end
| uu____28473 -> begin
val_quals
end)
in (

let quals2 = (

let uu____28477 = (FStar_All.pipe_right lets1 (FStar_Util.for_some (fun uu____28510 -> (match (uu____28510) with
| (uu____28524, (uu____28525, t)) -> begin
(Prims.op_Equality t.FStar_Parser_AST.level FStar_Parser_AST.Formula)
end))))
in (match (uu____28477) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals1
end
| uu____28542 -> begin
quals1
end))
in (

let lbs1 = (

let uu____28545 = (FStar_All.pipe_right quals2 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____28545) with
| true -> begin
(

let uu____28551 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu___3656_28566 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let uu___3658_28568 = fv
in {FStar_Syntax_Syntax.fv_name = uu___3658_28568.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = uu___3658_28568.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = uu___3656_28566.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___3656_28566.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___3656_28566.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___3656_28566.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___3656_28566.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___3656_28566.FStar_Syntax_Syntax.lbpos})))))
in (((FStar_Pervasives_Native.fst lbs)), (uu____28551)))
end
| uu____28575 -> begin
lbs
end))
in (

let names1 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (

let attrs = (FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs)
in (

let s = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((lbs1), (names1))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = (FStar_List.append val_attrs attrs); FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None}
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env s)
in (

let env2 = (FStar_List.fold_left (fun env2 id1 -> (FStar_Syntax_DsEnv.push_doc env2 id1 d.FStar_Parser_AST.doc)) env1 names1)
in ((env2), ((s)::[]))))))))))
end)))
end
| uu____28598 -> begin
(failwith "Desugaring a let did not produce a let")
end));
)
end))))
end
| uu____28604 -> begin
(

let uu____28606 = (match (lets) with
| ((pat, body))::[] -> begin
((pat), (body))
end
| uu____28625 -> begin
(failwith "expand_toplevel_pattern should only allow single definition lets")
end)
in (match (uu____28606) with
| (pat, body) -> begin
(

let fresh_toplevel_name = (FStar_Ident.gen FStar_Range.dummyRange)
in (

let fresh_pat = (

let var_pat = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((fresh_toplevel_name), (FStar_Pervasives_Native.None)))) FStar_Range.dummyRange)
in (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat1, ty) -> begin
(

let uu___3684_28662 = pat1
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed (((var_pat), (ty))); FStar_Parser_AST.prange = uu___3684_28662.FStar_Parser_AST.prange})
end
| uu____28669 -> begin
var_pat
end))
in (

let main_let = (desugar_decl env (

let uu___3688_28676 = d
in {FStar_Parser_AST.d = FStar_Parser_AST.TopLevelLet (((isrec), ((((fresh_pat), (body)))::[]))); FStar_Parser_AST.drange = uu___3688_28676.FStar_Parser_AST.drange; FStar_Parser_AST.doc = uu___3688_28676.FStar_Parser_AST.doc; FStar_Parser_AST.quals = (FStar_Parser_AST.Private)::d.FStar_Parser_AST.quals; FStar_Parser_AST.attrs = uu___3688_28676.FStar_Parser_AST.attrs}))
in (

let build_projection = (fun uu____28712 id1 -> (match (uu____28712) with
| (env1, ses) -> begin
(

let main = (

let uu____28733 = (

let uu____28734 = (FStar_Ident.lid_of_ids ((fresh_toplevel_name)::[]))
in FStar_Parser_AST.Var (uu____28734))
in (FStar_Parser_AST.mk_term uu____28733 FStar_Range.dummyRange FStar_Parser_AST.Expr))
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

let uu____28784 = (desugar_decl env1 id_decl)
in (match (uu____28784) with
| (env2, ses') -> begin
((env2), ((FStar_List.append ses ses')))
end))))))))
end))
in (

let bvs = (

let uu____28802 = (gather_pattern_bound_vars true pat)
in (FStar_All.pipe_right uu____28802 FStar_Util.set_elements))
in (FStar_List.fold_left build_projection main_let bvs))))))
end))
end)))
end
| FStar_Parser_AST.Main (t) -> begin
(

let e = (desugar_term env t)
in (

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_main (e); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []; FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None}
in ((env), ((se)::[]))))
end
| FStar_Parser_AST.Assume (id1, t) -> begin
(

let f = (desugar_formula env t)
in (

let lid = (FStar_Syntax_DsEnv.qualify env id1)
in (

let env1 = (FStar_Syntax_DsEnv.push_doc env lid d.FStar_Parser_AST.doc)
in ((env1), (({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_assume (((lid), ([]), (f))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []; FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None})::[])))))
end
| FStar_Parser_AST.Val (id1, t) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let t1 = (

let uu____28826 = (close_fun env t)
in (desugar_term env uu____28826))
in (

let quals1 = (

let uu____28830 = ((FStar_Syntax_DsEnv.iface env) && (FStar_Syntax_DsEnv.admitted_iface env))
in (match (uu____28830) with
| true -> begin
(FStar_Parser_AST.Assumption)::quals
end
| uu____28835 -> begin
quals
end))
in (

let lid = (FStar_Syntax_DsEnv.qualify env id1)
in (

let attrs = (FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs)
in (

let se = (

let uu____28842 = (FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals1)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), ([]), (t1))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = uu____28842; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = attrs; FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None})
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se)
in (

let env2 = (FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc)
in ((env2), ((se)::[]))))))))))
end
| FStar_Parser_AST.Exception (id1, t_opt) -> begin
(

let t = (match (t_opt) with
| FStar_Pervasives_Native.None -> begin
(FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_lid env) FStar_Parser_Const.exn_lid)
end
| FStar_Pervasives_Native.Some (term) -> begin
(

let t = (desugar_term env term)
in (

let uu____28856 = (

let uu____28865 = (FStar_Syntax_Syntax.null_binder t)
in (uu____28865)::[])
in (

let uu____28884 = (

let uu____28887 = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_lid env) FStar_Parser_Const.exn_lid)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____28887))
in (FStar_Syntax_Util.arrow uu____28856 uu____28884))))
end)
in (

let l = (FStar_Syntax_DsEnv.qualify env id1)
in (

let qual = (FStar_Syntax_Syntax.ExceptionConstructor)::[]
in (

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((l), ([]), (t), (FStar_Parser_Const.exn_lid), ((Prims.parse_int "0")), ((FStar_Parser_Const.exn_lid)::[]))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qual; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []; FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None}
in (

let se' = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((se)::[]), ((l)::[]))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qual; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []; FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None}
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
in (

let attrs = d.FStar_Parser_AST.attrs
in (desugar_effect env d quals false eff_name eff_binders eff_typ eff_decls attrs)))
end
| FStar_Parser_AST.LayeredEffect (FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_typ, eff_decls)) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let attrs = d.FStar_Parser_AST.attrs
in (desugar_effect env d quals true eff_name eff_binders eff_typ eff_decls attrs)))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(

let lookup1 = (fun l1 -> (

let uu____28958 = (FStar_Syntax_DsEnv.try_lookup_effect_defn env l1)
in (match (uu____28958) with
| FStar_Pervasives_Native.None -> begin
(

let uu____28961 = (

let uu____28967 = (

let uu____28969 = (

let uu____28971 = (FStar_Syntax_Print.lid_to_string l1)
in (Prims.op_Hat uu____28971 " not found"))
in (Prims.op_Hat "Effect name " uu____28969))
in ((FStar_Errors.Fatal_EffectNotFound), (uu____28967)))
in (FStar_Errors.raise_error uu____28961 d.FStar_Parser_AST.drange))
end
| FStar_Pervasives_Native.Some (l2) -> begin
l2
end)))
in (

let src_ed = (lookup1 l.FStar_Parser_AST.msource)
in (

let dst_ed = (lookup1 l.FStar_Parser_AST.mdest)
in (

let uu____28979 = (

let uu____28981 = ((FStar_Syntax_Util.is_layered src_ed) || (FStar_Syntax_Util.is_layered dst_ed))
in (not (uu____28981)))
in (match (uu____28979) with
| true -> begin
(

let uu____28988 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(

let uu____29006 = (

let uu____29009 = (

let uu____29010 = (desugar_term env t)
in (([]), (uu____29010)))
in FStar_Pervasives_Native.Some (uu____29009))
in ((uu____29006), (FStar_Pervasives_Native.None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(

let uu____29023 = (

let uu____29026 = (

let uu____29027 = (desugar_term env wp)
in (([]), (uu____29027)))
in FStar_Pervasives_Native.Some (uu____29026))
in (

let uu____29034 = (

let uu____29037 = (

let uu____29038 = (desugar_term env t)
in (([]), (uu____29038)))
in FStar_Pervasives_Native.Some (uu____29037))
in ((uu____29023), (uu____29034))))
end
| FStar_Parser_AST.LiftForFree (t) -> begin
(

let uu____29050 = (

let uu____29053 = (

let uu____29054 = (desugar_term env t)
in (([]), (uu____29054)))
in FStar_Pervasives_Native.Some (uu____29053))
in ((FStar_Pervasives_Native.None), (uu____29050)))
end)
in (match (uu____28988) with
| (lift_wp, lift) -> begin
(

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect ({FStar_Syntax_Syntax.source = src_ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.target = dst_ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift}); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []; FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None}
in ((env), ((se)::[])))
end))
end
| uu____29080 -> begin
(match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(

let sub_eff = (

let uu____29088 = (

let uu____29091 = (

let uu____29092 = (desugar_term env t)
in (([]), (uu____29092)))
in FStar_Pervasives_Native.Some (uu____29091))
in {FStar_Syntax_Syntax.source = src_ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.target = dst_ed.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.lift_wp = FStar_Pervasives_Native.None; FStar_Syntax_Syntax.lift = uu____29088})
in ((env), (({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect (sub_eff); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []; FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None})::[])))
end
| uu____29099 -> begin
(failwith "Impossible! unexpected lift_op for lift to a layered effect")
end)
end)))))
end
| FStar_Parser_AST.Splice (ids, t) -> begin
(

let t1 = (desugar_term env t)
in (

let se = (

let uu____29113 = (

let uu____29114 = (

let uu____29121 = (FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids)
in ((uu____29121), (t1)))
in FStar_Syntax_Syntax.Sig_splice (uu____29114))
in {FStar_Syntax_Syntax.sigel = uu____29113; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []; FStar_Syntax_Syntax.sigopts = FStar_Pervasives_Native.None})
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se)
in ((env1), ((se)::[])))))
end)))


let desugar_decls : env_t  ->  FStar_Parser_AST.decl Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env decls -> (

let uu____29148 = (FStar_List.fold_left (fun uu____29168 d -> (match (uu____29168) with
| (env1, sigelts) -> begin
(

let uu____29188 = (desugar_decl env1 d)
in (match (uu____29188) with
| (env2, se) -> begin
((env2), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls)
in (match (uu____29148) with
| (env1, sigelts) -> begin
((env1), (sigelts))
end)))


let open_prims_all : (FStar_Parser_AST.decoration Prims.list  ->  FStar_Parser_AST.decl) Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Parser_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Parser_Const.all_lid)) FStar_Range.dummyRange))::[]


let desugar_modul_common : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let env1 = (match (((curmod), (m))) with
| (FStar_Pervasives_Native.None, uu____29279) -> begin
env
end
| (FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.name = prev_lid; FStar_Syntax_Syntax.declarations = uu____29283; FStar_Syntax_Syntax.exports = uu____29284; FStar_Syntax_Syntax.is_interface = uu____29285}), FStar_Parser_AST.Module (current_lid, uu____29287)) when ((FStar_Ident.lid_equals prev_lid current_lid) && (FStar_Options.interactive ())) -> begin
env
end
| (FStar_Pervasives_Native.Some (prev_mod), uu____29296) -> begin
(

let uu____29299 = (FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod)
in (FStar_Pervasives_Native.fst uu____29299))
end)
in (

let uu____29304 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(

let uu____29346 = (FStar_Syntax_DsEnv.prepare_module_or_interface true admitted env1 mname FStar_Syntax_DsEnv.default_mii)
in ((uu____29346), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(

let uu____29368 = (FStar_Syntax_DsEnv.prepare_module_or_interface false false env1 mname FStar_Syntax_DsEnv.default_mii)
in ((uu____29368), (mname), (decls), (false)))
end)
in (match (uu____29304) with
| ((env2, pop_when_done), mname, decls, intf) -> begin
(

let uu____29410 = (desugar_decls env2 decls)
in (match (uu____29410) with
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


let desugar_partial_modul : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  env_t  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (

let m1 = (

let uu____29478 = ((FStar_Options.interactive ()) && (

let uu____29481 = (

let uu____29483 = (

let uu____29485 = (FStar_Options.file_list ())
in (FStar_List.hd uu____29485))
in (FStar_Util.get_file_extension uu____29483))
in (FStar_List.mem uu____29481 (("fsti")::("fsi")::[]))))
in (match (uu____29478) with
| true -> begin
(as_interface m)
end
| uu____29497 -> begin
m
end))
in (

let uu____29499 = (desugar_modul_common curmod env m1)
in (match (uu____29499) with
| (env1, modul, pop_when_done) -> begin
(match (pop_when_done) with
| true -> begin
(

let uu____29521 = (FStar_Syntax_DsEnv.pop ())
in ((uu____29521), (modul)))
end
| uu____29522 -> begin
((env1), (modul))
end)
end))))


let desugar_modul : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (

let uu____29543 = (desugar_modul_common FStar_Pervasives_Native.None env m)
in (match (uu____29543) with
| (env1, modul, pop_when_done) -> begin
(

let uu____29560 = (FStar_Syntax_DsEnv.finish_module_or_interface env1 modul)
in (match (uu____29560) with
| (env2, modul1) -> begin
((

let uu____29572 = (FStar_Options.dump_module modul1.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____29572) with
| true -> begin
(

let uu____29575 = (FStar_Syntax_Print.modul_to_string modul1)
in (FStar_Util.print1 "Module after desugaring:\n%s\n" uu____29575))
end
| uu____29578 -> begin
()
end));
(

let uu____29580 = (match (pop_when_done) with
| true -> begin
(FStar_Syntax_DsEnv.export_interface modul1.FStar_Syntax_Syntax.name env2)
end
| uu____29582 -> begin
env2
end)
in ((uu____29580), (modul1)));
)
end))
end)))


let with_options : 'a . (unit  ->  'a)  ->  'a = (fun f -> ((FStar_Options.push ());
(

let res = (f ())
in (

let light = (FStar_Options.ml_ish ())
in ((FStar_Options.pop ());
(match (light) with
| true -> begin
(FStar_Options.set_ml_ish ())
end
| uu____29607 -> begin
()
end);
res;
)));
))


let ast_modul_to_modul : FStar_Parser_AST.modul  ->  FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv = (fun modul env -> (with_options (fun uu____29630 -> (

let uu____29631 = (desugar_modul env modul)
in (match (uu____29631) with
| (e, m) -> begin
((m), (e))
end)))))


let decls_to_sigelts : FStar_Parser_AST.decl Prims.list  ->  FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv = (fun decls env -> (with_options (fun uu____29669 -> (

let uu____29670 = (desugar_decls env decls)
in (match (uu____29670) with
| (env1, sigelts) -> begin
((sigelts), (env1))
end)))))


let partial_ast_modul_to_modul : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Parser_AST.modul  ->  FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv = (fun modul a_modul env -> (with_options (fun uu____29721 -> (

let uu____29722 = (desugar_partial_modul modul env a_modul)
in (match (uu____29722) with
| (env1, modul1) -> begin
((modul1), (env1))
end)))))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Syntax_DsEnv.module_inclusion_info  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  unit FStar_Syntax_DsEnv.withenv = (fun m mii erase_univs en -> (

let erase_univs_ed = (fun ed -> (

let erase_binders = (fun bs -> (match (bs) with
| [] -> begin
[]
end
| uu____29817 -> begin
(

let t = (

let uu____29827 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (FStar_Syntax_Syntax.t_unit), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (erase_univs uu____29827))
in (

let uu____29840 = (

let uu____29841 = (FStar_Syntax_Subst.compress t)
in uu____29841.FStar_Syntax_Syntax.n)
in (match (uu____29840) with
| FStar_Syntax_Syntax.Tm_abs (bs1, uu____29853, uu____29854) -> begin
bs1
end
| uu____29879 -> begin
(failwith "Impossible")
end)))
end))
in (

let uu____29889 = (

let uu____29896 = (erase_binders ed.FStar_Syntax_Syntax.binders)
in (FStar_Syntax_Subst.open_term' uu____29896 FStar_Syntax_Syntax.t_unit))
in (match (uu____29889) with
| (binders, uu____29898, binders_opening) -> begin
(

let erase_term = (fun t -> (

let uu____29906 = (

let uu____29907 = (FStar_Syntax_Subst.subst binders_opening t)
in (erase_univs uu____29907))
in (FStar_Syntax_Subst.close binders uu____29906)))
in (

let erase_tscheme = (fun uu____29925 -> (match (uu____29925) with
| (us, t) -> begin
(

let t1 = (

let uu____29945 = (FStar_Syntax_Subst.shift_subst (FStar_List.length us) binders_opening)
in (FStar_Syntax_Subst.subst uu____29945 t))
in (

let uu____29948 = (

let uu____29949 = (erase_univs t1)
in (FStar_Syntax_Subst.close binders uu____29949))
in (([]), (uu____29948))))
end))
in (

let erase_action = (fun action -> (

let opening = (FStar_Syntax_Subst.shift_subst (FStar_List.length action.FStar_Syntax_Syntax.action_univs) binders_opening)
in (

let erased_action_params = (match (action.FStar_Syntax_Syntax.action_params) with
| [] -> begin
[]
end
| uu____29972 -> begin
(

let bs = (

let uu____29982 = (FStar_Syntax_Subst.subst_binders opening action.FStar_Syntax_Syntax.action_params)
in (FStar_All.pipe_left erase_binders uu____29982))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (FStar_Syntax_Syntax.t_unit), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____30022 = (

let uu____30023 = (

let uu____30026 = (FStar_Syntax_Subst.close binders t)
in (FStar_Syntax_Subst.compress uu____30026))
in uu____30023.FStar_Syntax_Syntax.n)
in (match (uu____30022) with
| FStar_Syntax_Syntax.Tm_abs (bs1, uu____30028, uu____30029) -> begin
bs1
end
| uu____30054 -> begin
(failwith "Impossible")
end))))
end)
in (

let erase_term1 = (fun t -> (

let uu____30062 = (

let uu____30063 = (FStar_Syntax_Subst.subst opening t)
in (erase_univs uu____30063))
in (FStar_Syntax_Subst.close binders uu____30062)))
in (

let uu___3960_30064 = action
in (

let uu____30065 = (erase_term1 action.FStar_Syntax_Syntax.action_defn)
in (

let uu____30066 = (erase_term1 action.FStar_Syntax_Syntax.action_typ)
in {FStar_Syntax_Syntax.action_name = uu___3960_30064.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___3960_30064.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = erased_action_params; FStar_Syntax_Syntax.action_defn = uu____30065; FStar_Syntax_Syntax.action_typ = uu____30066})))))))
in (

let uu___3962_30067 = ed
in (

let uu____30068 = (FStar_Syntax_Subst.close_binders binders)
in (

let uu____30069 = (erase_tscheme ed.FStar_Syntax_Syntax.signature)
in (

let uu____30070 = (FStar_Syntax_Util.apply_eff_combinators erase_tscheme ed.FStar_Syntax_Syntax.combinators)
in (

let uu____30071 = (FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.mname = uu___3962_30067.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.cattributes = uu___3962_30067.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = uu____30068; FStar_Syntax_Syntax.signature = uu____30069; FStar_Syntax_Syntax.combinators = uu____30070; FStar_Syntax_Syntax.actions = uu____30071; FStar_Syntax_Syntax.eff_attrs = uu___3962_30067.FStar_Syntax_Syntax.eff_attrs}))))))))
end))))
in (

let push_sigelt1 = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let se' = (

let uu___3969_30087 = se
in (

let uu____30088 = (

let uu____30089 = (erase_univs_ed ed)
in FStar_Syntax_Syntax.Sig_new_effect (uu____30089))
in {FStar_Syntax_Syntax.sigel = uu____30088; FStar_Syntax_Syntax.sigrng = uu___3969_30087.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___3969_30087.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___3969_30087.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___3969_30087.FStar_Syntax_Syntax.sigattrs; FStar_Syntax_Syntax.sigopts = uu___3969_30087.FStar_Syntax_Syntax.sigopts}))
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se')
in (push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng)))
end
| uu____30091 -> begin
(FStar_Syntax_DsEnv.push_sigelt env se)
end))
in (

let uu____30092 = (FStar_Syntax_DsEnv.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name mii)
in (match (uu____30092) with
| (en1, pop_when_done) -> begin
(

let en2 = (

let uu____30109 = (FStar_Syntax_DsEnv.set_current_module en1 m.FStar_Syntax_Syntax.name)
in (FStar_List.fold_left push_sigelt1 uu____30109 m.FStar_Syntax_Syntax.exports))
in (

let env = (FStar_Syntax_DsEnv.finish en2 m)
in (

let uu____30111 = (match (pop_when_done) with
| true -> begin
(FStar_Syntax_DsEnv.export_interface m.FStar_Syntax_Syntax.name env)
end
| uu____30113 -> begin
env
end)
in ((()), (uu____30111)))))
end)))))




