
open Prims
open FStar_Pervasives

let desugar_disjunctive_pattern : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.branch Prims.list = (fun pats when_opt branch1 -> (FStar_All.pipe_right pats (FStar_List.map (fun pat -> (FStar_Syntax_Util.branch ((pat), (when_opt), (branch1)))))))


let trans_aqual : FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option = (fun uu___85_58 -> (match (uu___85_58) with
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)
end
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality)
end
| uu____63 -> begin
FStar_Pervasives_Native.None
end))


let trans_qual : FStar_Range.range  ->  FStar_Ident.lident FStar_Pervasives_Native.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun r maybe_effect_id uu___86_76 -> (match (uu___86_76) with
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


let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun uu___87_83 -> (match (uu___87_83) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end
| FStar_Parser_AST.LightOff -> begin
FStar_Syntax_Syntax.LightOff
end))


let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option = (fun uu___88_92 -> (match (uu___88_92) with
| FStar_Parser_AST.Hash -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)
end
| uu____95 -> begin
FStar_Pervasives_Native.None
end))


let arg_withimp_e : 'Auu____99 . FStar_Parser_AST.imp  ->  'Auu____99  ->  ('Auu____99 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) = (fun imp t -> ((t), ((as_imp imp))))


let arg_withimp_t : 'Auu____119 . FStar_Parser_AST.imp  ->  'Auu____119  ->  ('Auu____119 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
((t), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end
| uu____136 -> begin
((t), (FStar_Pervasives_Native.None))
end))


let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (uu____151) -> begin
true
end
| uu____156 -> begin
false
end)))))


let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t1) -> begin
(unparen t1)
end
| uu____161 -> begin
t
end))


let tm_type_z : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (

let uu____165 = (

let uu____166 = (FStar_Ident.lid_of_path (("Type0")::[]) r)
in FStar_Parser_AST.Name (uu____166))
in (FStar_Parser_AST.mk_term uu____165 r FStar_Parser_AST.Kind)))


let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (

let uu____170 = (

let uu____171 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (uu____171))
in (FStar_Parser_AST.mk_term uu____170 r FStar_Parser_AST.Kind)))


let rec is_comp_type : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> (

let uu____178 = (

let uu____179 = (unparen t)
in uu____179.FStar_Parser_AST.tm)
in (match (uu____178) with
| FStar_Parser_AST.Name (l) -> begin
(

let uu____181 = (FStar_Syntax_DsEnv.try_lookup_effect_name env l)
in (FStar_All.pipe_right uu____181 FStar_Option.isSome))
end
| FStar_Parser_AST.Construct (l, uu____187) -> begin
(

let uu____200 = (FStar_Syntax_DsEnv.try_lookup_effect_name env l)
in (FStar_All.pipe_right uu____200 FStar_Option.isSome))
end
| FStar_Parser_AST.App (head1, uu____206, uu____207) -> begin
(is_comp_type env head1)
end
| FStar_Parser_AST.Paren (t1) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.Ascribed (t1, uu____210, uu____211) -> begin
(is_comp_type env t1)
end
| FStar_Parser_AST.LetOpen (uu____216, t1) -> begin
(is_comp_type env t1)
end
| uu____218 -> begin
false
end)))


let unit_ty : FStar_Parser_AST.term = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.unit_lid)) FStar_Range.dummyRange FStar_Parser_AST.Type_level)


let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n1 s r -> (

let uu____228 = (

let uu____231 = (

let uu____232 = (

let uu____237 = (FStar_Parser_AST.compile_op n1 s r)
in ((uu____237), (r)))
in (FStar_Ident.mk_ident uu____232))
in (uu____231)::[])
in (FStar_All.pipe_right uu____228 FStar_Ident.lid_of_ids)))


let op_as_term : 'Auu____245 . FStar_Syntax_DsEnv.env  ->  Prims.int  ->  'Auu____245  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env arity rng op -> (

let r = (fun l dd -> (

let uu____273 = (

let uu____274 = (FStar_Syntax_Syntax.lid_as_fv (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd FStar_Pervasives_Native.None)
in (FStar_All.pipe_right uu____274 FStar_Syntax_Syntax.fv_to_tm))
in FStar_Pervasives_Native.Some (uu____273)))
in (

let fallback = (fun uu____280 -> (match ((FStar_Ident.text_of_id op)) with
| "=" -> begin
(r FStar_Parser_Const.op_Eq FStar_Syntax_Syntax.Delta_equational)
end
| ":=" -> begin
(r FStar_Parser_Const.write_lid FStar_Syntax_Syntax.Delta_equational)
end
| "<" -> begin
(r FStar_Parser_Const.op_LT FStar_Syntax_Syntax.Delta_equational)
end
| "<=" -> begin
(r FStar_Parser_Const.op_LTE FStar_Syntax_Syntax.Delta_equational)
end
| ">" -> begin
(r FStar_Parser_Const.op_GT FStar_Syntax_Syntax.Delta_equational)
end
| ">=" -> begin
(r FStar_Parser_Const.op_GTE FStar_Syntax_Syntax.Delta_equational)
end
| "&&" -> begin
(r FStar_Parser_Const.op_And FStar_Syntax_Syntax.Delta_equational)
end
| "||" -> begin
(r FStar_Parser_Const.op_Or FStar_Syntax_Syntax.Delta_equational)
end
| "+" -> begin
(r FStar_Parser_Const.op_Addition FStar_Syntax_Syntax.Delta_equational)
end
| "-" when (Prims.op_Equality arity (Prims.parse_int "1")) -> begin
(r FStar_Parser_Const.op_Minus FStar_Syntax_Syntax.Delta_equational)
end
| "-" -> begin
(r FStar_Parser_Const.op_Subtraction FStar_Syntax_Syntax.Delta_equational)
end
| "/" -> begin
(r FStar_Parser_Const.op_Division FStar_Syntax_Syntax.Delta_equational)
end
| "%" -> begin
(r FStar_Parser_Const.op_Modulus FStar_Syntax_Syntax.Delta_equational)
end
| "!" -> begin
(r FStar_Parser_Const.read_lid FStar_Syntax_Syntax.Delta_equational)
end
| "@" -> begin
(

let uu____283 = (FStar_Options.ml_ish ())
in (match (uu____283) with
| true -> begin
(r FStar_Parser_Const.list_append_lid FStar_Syntax_Syntax.Delta_equational)
end
| uu____286 -> begin
(r FStar_Parser_Const.list_tot_append_lid FStar_Syntax_Syntax.Delta_equational)
end))
end
| "^" -> begin
(r FStar_Parser_Const.strcat_lid FStar_Syntax_Syntax.Delta_equational)
end
| "|>" -> begin
(r FStar_Parser_Const.pipe_right_lid FStar_Syntax_Syntax.Delta_equational)
end
| "<|" -> begin
(r FStar_Parser_Const.pipe_left_lid FStar_Syntax_Syntax.Delta_equational)
end
| "<>" -> begin
(r FStar_Parser_Const.op_notEq FStar_Syntax_Syntax.Delta_equational)
end
| "~" -> begin
(r FStar_Parser_Const.not_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "2"))))
end
| "==" -> begin
(r FStar_Parser_Const.eq2_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "2"))))
end
| "<<" -> begin
(r FStar_Parser_Const.precedes_lid FStar_Syntax_Syntax.Delta_constant)
end
| "/\\" -> begin
(r FStar_Parser_Const.and_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))))
end
| "\\/" -> begin
(r FStar_Parser_Const.or_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))))
end
| "==>" -> begin
(r FStar_Parser_Const.imp_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))))
end
| "<==>" -> begin
(r FStar_Parser_Const.iff_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "2"))))
end
| uu____287 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____288 = (

let uu____295 = (compile_op_lid arity op.FStar_Ident.idText op.FStar_Ident.idRange)
in (FStar_Syntax_DsEnv.try_lookup_lid env uu____295))
in (match (uu____288) with
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some ((FStar_Pervasives_Native.fst t))
end
| uu____307 -> begin
(fallback ())
end)))))


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (

let uu____323 = (FStar_Util.remove_dups (fun x y -> (Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) uu____323)))


let rec free_type_vars_b : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (uu____362) -> begin
((env), ([]))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____366 = (FStar_Syntax_DsEnv.push_bv env x)
in (match (uu____366) with
| (env1, uu____378) -> begin
((env1), ((x)::[]))
end))
end
| FStar_Parser_AST.Annotated (uu____381, term) -> begin
(

let uu____383 = (free_type_vars env term)
in ((env), (uu____383)))
end
| FStar_Parser_AST.TAnnotated (id1, uu____389) -> begin
(

let uu____390 = (FStar_Syntax_DsEnv.push_bv env id1)
in (match (uu____390) with
| (env1, uu____402) -> begin
((env1), ([]))
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____406 = (free_type_vars env t)
in ((env), (uu____406)))
end))
and free_type_vars : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (

let uu____413 = (

let uu____414 = (unparen t)
in uu____414.FStar_Parser_AST.tm)
in (match (uu____413) with
| FStar_Parser_AST.Labeled (uu____417) -> begin
(failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____427 = (FStar_Syntax_DsEnv.try_lookup_id env a)
in (match (uu____427) with
| FStar_Pervasives_Native.None -> begin
(a)::[]
end
| uu____440 -> begin
[]
end))
end
| FStar_Parser_AST.Wild -> begin
[]
end
| FStar_Parser_AST.Const (uu____447) -> begin
[]
end
| FStar_Parser_AST.Uvar (uu____448) -> begin
[]
end
| FStar_Parser_AST.Var (uu____449) -> begin
[]
end
| FStar_Parser_AST.Projector (uu____450) -> begin
[]
end
| FStar_Parser_AST.Discrim (uu____455) -> begin
[]
end
| FStar_Parser_AST.Name (uu____456) -> begin
[]
end
| FStar_Parser_AST.Requires (t1, uu____458) -> begin
(free_type_vars env t1)
end
| FStar_Parser_AST.Ensures (t1, uu____464) -> begin
(free_type_vars env t1)
end
| FStar_Parser_AST.NamedTyp (uu____469, t1) -> begin
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
| FStar_Parser_AST.Construct (uu____487, ts) -> begin
(FStar_List.collect (fun uu____508 -> (match (uu____508) with
| (t1, uu____516) -> begin
(free_type_vars env t1)
end)) ts)
end
| FStar_Parser_AST.Op (uu____517, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, uu____525) -> begin
(

let uu____526 = (free_type_vars env t1)
in (

let uu____529 = (free_type_vars env t2)
in (FStar_List.append uu____526 uu____529)))
end
| FStar_Parser_AST.Refine (b, t1) -> begin
(

let uu____534 = (free_type_vars_b env b)
in (match (uu____534) with
| (env1, f) -> begin
(

let uu____549 = (free_type_vars env1 t1)
in (FStar_List.append f uu____549))
end))
end
| FStar_Parser_AST.Product (binders, body) -> begin
(

let uu____558 = (FStar_List.fold_left (fun uu____578 binder -> (match (uu____578) with
| (env1, free) -> begin
(

let uu____598 = (free_type_vars_b env1 binder)
in (match (uu____598) with
| (env2, f) -> begin
((env2), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (uu____558) with
| (env1, free) -> begin
(

let uu____629 = (free_type_vars env1 body)
in (FStar_List.append free uu____629))
end))
end
| FStar_Parser_AST.Sum (binders, body) -> begin
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
| FStar_Parser_AST.Project (t1, uu____713) -> begin
(free_type_vars env t1)
end
| FStar_Parser_AST.Attributes (cattributes) -> begin
(FStar_List.collect (free_type_vars env) cattributes)
end
| FStar_Parser_AST.Abs (uu____717) -> begin
[]
end
| FStar_Parser_AST.Let (uu____724) -> begin
[]
end
| FStar_Parser_AST.LetOpen (uu____745) -> begin
[]
end
| FStar_Parser_AST.If (uu____750) -> begin
[]
end
| FStar_Parser_AST.QForall (uu____757) -> begin
[]
end
| FStar_Parser_AST.QExists (uu____770) -> begin
[]
end
| FStar_Parser_AST.Record (uu____783) -> begin
[]
end
| FStar_Parser_AST.Match (uu____796) -> begin
[]
end
| FStar_Parser_AST.TryWith (uu____811) -> begin
[]
end
| FStar_Parser_AST.Bind (uu____826) -> begin
[]
end
| FStar_Parser_AST.Quote (uu____833) -> begin
[]
end
| FStar_Parser_AST.VQuote (uu____838) -> begin
[]
end
| FStar_Parser_AST.Seq (uu____839) -> begin
[]
end)))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (

let rec aux = (fun args t1 -> (

let uu____886 = (

let uu____887 = (unparen t1)
in uu____887.FStar_Parser_AST.tm)
in (match (uu____886) with
| FStar_Parser_AST.App (t2, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t2)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t1.FStar_Parser_AST.range; FStar_Parser_AST.level = t1.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| uu____929 -> begin
((t1), (args))
end)))
in (aux [] t)))


let close : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (

let uu____949 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv uu____949))
in (match ((Prims.op_Equality (FStar_List.length ftv) (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____956 -> begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (

let uu____967 = (

let uu____968 = (

let uu____973 = (tm_type x.FStar_Ident.idRange)
in ((x), (uu____973)))
in FStar_Parser_AST.TAnnotated (uu____968))
in (FStar_Parser_AST.mk_binder uu____967 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end)))


let close_fun : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (

let uu____986 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv uu____986))
in (match ((Prims.op_Equality (FStar_List.length ftv) (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____993 -> begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (

let uu____1004 = (

let uu____1005 = (

let uu____1010 = (tm_type x.FStar_Ident.idRange)
in ((x), (uu____1010)))
in FStar_Parser_AST.TAnnotated (uu____1005))
in (FStar_Parser_AST.mk_binder uu____1004 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))))))
in (

let t1 = (

let uu____1012 = (

let uu____1013 = (unparen t)
in uu____1013.FStar_Parser_AST.tm)
in (match (uu____1012) with
| FStar_Parser_AST.Product (uu____1014) -> begin
t
end
| uu____1021 -> begin
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
| uu____1053 -> begin
((bs), (t))
end))


let rec is_var_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatWild -> begin
true
end
| FStar_Parser_AST.PatTvar (uu____1059, uu____1060) -> begin
true
end
| FStar_Parser_AST.PatVar (uu____1065, uu____1066) -> begin
true
end
| FStar_Parser_AST.PatAscribed (p1, uu____1072) -> begin
(is_var_pattern p1)
end
| uu____1085 -> begin
false
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p1, uu____1090) -> begin
(is_app_pattern p1)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____1103); FStar_Parser_AST.prange = uu____1104}, uu____1105) -> begin
true
end
| uu____1116 -> begin
false
end))


let replace_unit_pattern : FStar_Parser_AST.pattern  ->  FStar_Parser_AST.pattern = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatConst (FStar_Const.Const_unit) -> begin
(FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatAscribed ((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)), (((unit_ty), (FStar_Pervasives_Native.None)))))) p.FStar_Parser_AST.prange)
end
| uu____1128 -> begin
p
end))


let rec destruct_app_pattern : FStar_Syntax_DsEnv.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * (FStar_Parser_AST.term * FStar_Parser_AST.term FStar_Pervasives_Native.option) FStar_Pervasives_Native.option) = (fun env is_top_level1 p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p1, t) -> begin
(

let uu____1192 = (destruct_app_pattern env is_top_level1 p1)
in (match (uu____1192) with
| (name, args, uu____1235) -> begin
((name), (args), (FStar_Pervasives_Native.Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id1, uu____1285); FStar_Parser_AST.prange = uu____1286}, args) when is_top_level1 -> begin
(

let uu____1296 = (

let uu____1301 = (FStar_Syntax_DsEnv.qualify env id1)
in FStar_Util.Inr (uu____1301))
in ((uu____1296), (args), (FStar_Pervasives_Native.None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id1, uu____1323); FStar_Parser_AST.prange = uu____1324}, args) -> begin
((FStar_Util.Inl (id1)), (args), (FStar_Pervasives_Native.None))
end
| uu____1354 -> begin
(failwith "Not an app pattern")
end))


let rec gather_pattern_bound_vars_maybe_top : FStar_Ident.ident FStar_Util.set  ->  FStar_Parser_AST.pattern  ->  FStar_Ident.ident FStar_Util.set = (fun acc p -> (

let gather_pattern_bound_vars_from_list = (FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc)
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatWild -> begin
acc
end
| FStar_Parser_AST.PatConst (uu____1398) -> begin
acc
end
| FStar_Parser_AST.PatVar (uu____1399, FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)) -> begin
acc
end
| FStar_Parser_AST.PatName (uu____1402) -> begin
acc
end
| FStar_Parser_AST.PatTvar (uu____1403) -> begin
acc
end
| FStar_Parser_AST.PatOp (uu____1410) -> begin
acc
end
| FStar_Parser_AST.PatApp (phead, pats) -> begin
(gather_pattern_bound_vars_from_list ((phead)::pats))
end
| FStar_Parser_AST.PatVar (x, uu____1418) -> begin
(FStar_Util.set_add x acc)
end
| FStar_Parser_AST.PatList (pats) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatTuple (pats, uu____1427) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatOr (pats) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatRecord (guarded_pats) -> begin
(

let uu____1442 = (FStar_List.map FStar_Pervasives_Native.snd guarded_pats)
in (gather_pattern_bound_vars_from_list uu____1442))
end
| FStar_Parser_AST.PatAscribed (pat, uu____1450) -> begin
(gather_pattern_bound_vars_maybe_top acc pat)
end)))


let gather_pattern_bound_vars : FStar_Parser_AST.pattern  ->  FStar_Ident.ident FStar_Util.set = (

let acc = (FStar_Util.new_set (fun id1 id2 -> (match ((Prims.op_Equality id1.FStar_Ident.idText id2.FStar_Ident.idText)) with
| true -> begin
(Prims.parse_int "0")
end
| uu____1474 -> begin
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
| uu____1506 -> begin
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
| uu____1540 -> begin
false
end))


let __proj__LetBinder__item___0 : bnd  ->  (FStar_Ident.lident * (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)) = (fun projectee -> (match (projectee) with
| LetBinder (_0) -> begin
_0
end))


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun uu___89_1584 -> (match (uu___89_1584) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| uu____1591 -> begin
(failwith "Impossible")
end))


let as_binder : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  (FStar_Ident.ident FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_DsEnv.env) = (fun env imp uu___90_1616 -> (match (uu___90_1616) with
| (FStar_Pervasives_Native.None, k) -> begin
(

let uu____1632 = (FStar_Syntax_Syntax.null_binder k)
in ((uu____1632), (env)))
end
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____1637 = (FStar_Syntax_DsEnv.push_bv env a)
in (match (uu____1637) with
| (env1, a1) -> begin
(((((

let uu___114_1657 = a1
in {FStar_Syntax_Syntax.ppname = uu___114_1657.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___114_1657.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), ((trans_aqual imp)))), (env1))
end))
end))


type env_t =
FStar_Syntax_DsEnv.env


type lenv_t =
FStar_Syntax_Syntax.bv Prims.list


let mk_lb : (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list * (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)  ->  FStar_Syntax_Syntax.letbinding = (fun uu____1684 -> (match (uu____1684) with
| (attrs, n1, t, e, pos) -> begin
{FStar_Syntax_Syntax.lbname = n1; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = attrs; FStar_Syntax_Syntax.lbpos = pos}
end))


let no_annot_abs : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t FStar_Pervasives_Native.None))


let mk_ref_read : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun tm -> (

let tm' = (

let uu____1752 = (

let uu____1767 = (

let uu____1768 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____1768))
in (

let uu____1769 = (

let uu____1778 = (

let uu____1785 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (uu____1785)))
in (uu____1778)::[])
in ((uu____1767), (uu____1769))))
in FStar_Syntax_Syntax.Tm_app (uu____1752))
in (FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_alloc : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun tm -> (

let tm' = (

let uu____1818 = (

let uu____1833 = (

let uu____1834 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____1834))
in (

let uu____1835 = (

let uu____1844 = (

let uu____1851 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (uu____1851)))
in (uu____1844)::[])
in ((uu____1833), (uu____1835))))
in FStar_Syntax_Syntax.Tm_app (uu____1818))
in (FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_assign : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t1 t2 pos -> (

let tm = (

let uu____1894 = (

let uu____1909 = (

let uu____1910 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____1910))
in (

let uu____1911 = (

let uu____1920 = (

let uu____1927 = (FStar_Syntax_Syntax.as_implicit false)
in ((t1), (uu____1927)))
in (

let uu____1930 = (

let uu____1939 = (

let uu____1946 = (FStar_Syntax_Syntax.as_implicit false)
in ((t2), (uu____1946)))
in (uu____1939)::[])
in (uu____1920)::uu____1930))
in ((uu____1909), (uu____1911))))
in FStar_Syntax_Syntax.Tm_app (uu____1894))
in (FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos)))


let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun uu___91_1977 -> (match (uu___91_1977) with
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
| uu____1978 -> begin
false
end))


let rec sum_to_universe : FStar_Syntax_Syntax.universe  ->  Prims.int  ->  FStar_Syntax_Syntax.universe = (fun u n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
u
end
| uu____1985 -> begin
(

let uu____1986 = (sum_to_universe u (n1 - (Prims.parse_int "1")))
in FStar_Syntax_Syntax.U_succ (uu____1986))
end))


let int_to_universe : Prims.int  ->  FStar_Syntax_Syntax.universe = (fun n1 -> (sum_to_universe FStar_Syntax_Syntax.U_zero n1))


let rec desugar_maybe_non_constant_universe : FStar_Parser_AST.term  ->  (Prims.int, FStar_Syntax_Syntax.universe) FStar_Util.either = (fun t -> (

let uu____2001 = (

let uu____2002 = (unparen t)
in uu____2002.FStar_Parser_AST.tm)
in (match (uu____2001) with
| FStar_Parser_AST.Wild -> begin
(

let uu____2007 = (

let uu____2008 = (FStar_Syntax_Unionfind.univ_fresh ())
in FStar_Syntax_Syntax.U_unif (uu____2008))
in FStar_Util.Inr (uu____2007))
end
| FStar_Parser_AST.Uvar (u) -> begin
FStar_Util.Inr (FStar_Syntax_Syntax.U_name (u))
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (repr, uu____2019)) -> begin
(

let n1 = (FStar_Util.int_of_string repr)
in ((match ((n1 < (Prims.parse_int "0"))) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_NegativeUniverseConstFatal_NotSupported), ((Prims.strcat "Negative universe constant  are not supported : " repr))) t.FStar_Parser_AST.range)
end
| uu____2034 -> begin
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

let uu____2091 = (sum_to_universe u n1)
in FStar_Util.Inr (uu____2091))
end
| (FStar_Util.Inr (u), FStar_Util.Inl (n1)) -> begin
(

let uu____2102 = (sum_to_universe u n1)
in FStar_Util.Inr (uu____2102))
end
| (FStar_Util.Inr (u11), FStar_Util.Inr (u21)) -> begin
(

let uu____2113 = (

let uu____2118 = (

let uu____2119 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "This universe might contain a sum of two universe variables " uu____2119))
in ((FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars), (uu____2118)))
in (FStar_Errors.raise_error uu____2113 t.FStar_Parser_AST.range))
end)))
end
| FStar_Parser_AST.App (uu____2124) -> begin
(

let rec aux = (fun t1 univargs -> (

let uu____2154 = (

let uu____2155 = (unparen t1)
in uu____2155.FStar_Parser_AST.tm)
in (match (uu____2154) with
| FStar_Parser_AST.App (t2, targ, uu____2162) -> begin
(

let uarg = (desugar_maybe_non_constant_universe targ)
in (aux t2 ((uarg)::univargs)))
end
| FStar_Parser_AST.Var (max_lid1) -> begin
(match ((FStar_List.existsb (fun uu___92_2192 -> (match (uu___92_2192) with
| FStar_Util.Inr (uu____2197) -> begin
true
end
| uu____2198 -> begin
false
end)) univargs)) with
| true -> begin
(

let uu____2203 = (

let uu____2204 = (FStar_List.map (fun uu___93_2213 -> (match (uu___93_2213) with
| FStar_Util.Inl (n1) -> begin
(int_to_universe n1)
end
| FStar_Util.Inr (u) -> begin
u
end)) univargs)
in FStar_Syntax_Syntax.U_max (uu____2204))
in FStar_Util.Inr (uu____2203))
end
| uu____2220 -> begin
(

let nargs = (FStar_List.map (fun uu___94_2230 -> (match (uu___94_2230) with
| FStar_Util.Inl (n1) -> begin
n1
end
| FStar_Util.Inr (uu____2236) -> begin
(failwith "impossible")
end)) univargs)
in (

let uu____2237 = (FStar_List.fold_left (fun m n1 -> (match ((m > n1)) with
| true -> begin
m
end
| uu____2242 -> begin
n1
end)) (Prims.parse_int "0") nargs)
in FStar_Util.Inl (uu____2237)))
end)
end
| uu____2243 -> begin
(

let uu____2244 = (

let uu____2249 = (

let uu____2250 = (

let uu____2251 = (FStar_Parser_AST.term_to_string t1)
in (Prims.strcat uu____2251 " in universe context"))
in (Prims.strcat "Unexpected term " uu____2250))
in ((FStar_Errors.Fatal_UnexpectedTermInUniverse), (uu____2249)))
in (FStar_Errors.raise_error uu____2244 t1.FStar_Parser_AST.range))
end)))
in (aux t []))
end
| uu____2260 -> begin
(

let uu____2261 = (

let uu____2266 = (

let uu____2267 = (

let uu____2268 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat uu____2268 " in universe context"))
in (Prims.strcat "Unexpected term " uu____2267))
in ((FStar_Errors.Fatal_UnexpectedTermInUniverse), (uu____2266)))
in (FStar_Errors.raise_error uu____2261 t.FStar_Parser_AST.range))
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


let check_no_aq : FStar_Syntax_Syntax.antiquotations  ->  Prims.unit = (fun aq -> (match (aq) with
| [] -> begin
()
end
| ((bv, b, e))::uu____2297 -> begin
(

let uu____2320 = (

let uu____2325 = (

let uu____2326 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected antiquotation: %s(%s)" (match (b) with
| true -> begin
"`@"
end
| uu____2327 -> begin
"`#"
end) uu____2326))
in ((FStar_Errors.Fatal_UnexpectedAntiquotation), (uu____2325)))
in (FStar_Errors.raise_error uu____2320 e.FStar_Syntax_Syntax.pos))
end))


let check_fields : 'Auu____2332 . FStar_Syntax_DsEnv.env  ->  (FStar_Ident.lident * 'Auu____2332) Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_DsEnv.record_or_dc = (fun env fields rg -> (

let uu____2357 = (FStar_List.hd fields)
in (match (uu____2357) with
| (f, uu____2367) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f);
(

let record = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f)
in (

let check_field = (fun uu____2377 -> (match (uu____2377) with
| (f', uu____2383) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f');
(

let uu____2385 = (FStar_Syntax_DsEnv.belongs_to_record env f' record)
in (match (uu____2385) with
| true -> begin
()
end
| uu____2386 -> begin
(

let msg = (FStar_Util.format3 "Field %s belongs to record type %s, whereas field %s does not" f.FStar_Ident.str record.FStar_Syntax_DsEnv.typename.FStar_Ident.str f'.FStar_Ident.str)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_FieldsNotBelongToSameRecordType), (msg)) rg))
end));
)
end))
in ((

let uu____2389 = (FStar_List.tl fields)
in (FStar_List.iter check_field uu____2389));
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
| FStar_Syntax_Syntax.Pat_dot_term (uu____2638) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_wild (uu____2645) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_constant (uu____2646) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (uu____2648, pats1) -> begin
(

let aux = (fun out uu____2682 -> (match (uu____2682) with
| (p2, uu____2694) -> begin
(

let intersection = (

let uu____2702 = (pat_vars p2)
in (FStar_Util.set_intersect uu____2702 out))
in (

let uu____2705 = (FStar_Util.set_is_empty intersection)
in (match (uu____2705) with
| true -> begin
(

let uu____2708 = (pat_vars p2)
in (FStar_Util.set_union out uu____2708))
end
| uu____2711 -> begin
(

let duplicate_bv = (

let uu____2713 = (FStar_Util.set_elements intersection)
in (FStar_List.hd uu____2713))
in (

let uu____2716 = (

let uu____2721 = (FStar_Util.format1 "Non-linear patterns are not permitted. %s appears more than once in this pattern." duplicate_bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in ((FStar_Errors.Fatal_NonLinearPatternNotPermitted), (uu____2721)))
in (FStar_Errors.raise_error uu____2716 r)))
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

let uu____2741 = (pat_vars p1)
in (FStar_All.pipe_right uu____2741 FStar_Pervasives.ignore))
end
| (p1)::ps -> begin
(

let pvars = (pat_vars p1)
in (

let aux = (fun p2 -> (

let uu____2761 = (

let uu____2762 = (pat_vars p2)
in (FStar_Util.set_eq pvars uu____2762))
in (match (uu____2761) with
| true -> begin
()
end
| uu____2765 -> begin
(

let nonlinear_vars = (

let uu____2769 = (pat_vars p2)
in (FStar_Util.set_symmetric_difference pvars uu____2769))
in (

let first_nonlinear_var = (

let uu____2773 = (FStar_Util.set_elements nonlinear_vars)
in (FStar_List.hd uu____2773))
in (

let uu____2776 = (

let uu____2781 = (FStar_Util.format1 "Patterns in this match are incoherent, variable %s is bound in some but not all patterns." first_nonlinear_var.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in ((FStar_Errors.Fatal_IncoherentPatterns), (uu____2781)))
in (FStar_Errors.raise_error uu____2776 r))))
end)))
in (FStar_List.iter aux ps)))
end)))
in ((match (((is_mut), (p.FStar_Parser_AST.pat))) with
| (false, uu____2785) -> begin
()
end
| (true, FStar_Parser_AST.PatVar (uu____2786)) -> begin
()
end
| (true, uu____2793) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_LetMutableForVariablesOnly), ("let-mutable is for variables only")) p.FStar_Parser_AST.prange)
end);
(

let push_bv_maybe_mut = (match (is_mut) with
| true -> begin
FStar_Syntax_DsEnv.push_bv_mutable
end
| uu____2811 -> begin
FStar_Syntax_DsEnv.push_bv
end)
in (

let resolvex = (fun l e x -> (

let uu____2828 = (FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (Prims.op_Equality y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText x.FStar_Ident.idText))))
in (match (uu____2828) with
| FStar_Pervasives_Native.Some (y) -> begin
((l), (e), (y))
end
| uu____2842 -> begin
(

let uu____2845 = (push_bv_maybe_mut e x)
in (match (uu____2845) with
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
| FStar_Parser_AST.PatOr (uu____2932) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.PatOp (op) -> begin
(

let uu____2948 = (

let uu____2949 = (

let uu____2950 = (

let uu____2957 = (

let uu____2958 = (

let uu____2963 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") op.FStar_Ident.idText op.FStar_Ident.idRange)
in ((uu____2963), (op.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____2958))
in ((uu____2957), (FStar_Pervasives_Native.None)))
in FStar_Parser_AST.PatVar (uu____2950))
in {FStar_Parser_AST.pat = uu____2949; FStar_Parser_AST.prange = p1.FStar_Parser_AST.prange})
in (aux loc env1 uu____2948))
end
| FStar_Parser_AST.PatAscribed (p2, (t, tacopt)) -> begin
((match (tacopt) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (uu____2980) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly), ("Type ascriptions within patterns are cannot be associated with a tactic")) orig.FStar_Parser_AST.prange)
end);
(

let uu____2981 = (aux loc env1 p2)
in (match (uu____2981) with
| (loc1, env', binder, p3, imp) -> begin
(

let annot_pat_var = (fun p4 t1 -> (match (p4.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu___115_3035 = p4
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var ((

let uu___116_3040 = x
in {FStar_Syntax_Syntax.ppname = uu___116_3040.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___116_3040.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})); FStar_Syntax_Syntax.p = uu___115_3035.FStar_Syntax_Syntax.p})
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu___117_3042 = p4
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild ((

let uu___118_3047 = x
in {FStar_Syntax_Syntax.ppname = uu___118_3047.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___118_3047.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})); FStar_Syntax_Syntax.p = uu___117_3042.FStar_Syntax_Syntax.p})
end
| uu____3048 when top -> begin
p4
end
| uu____3049 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly), ("Type ascriptions within patterns are only allowed on variables")) orig.FStar_Parser_AST.prange)
end))
in (

let uu____3052 = (match (binder) with
| LetBinder (uu____3065) -> begin
(failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t1 = (

let uu____3085 = (close_fun env1 t)
in (desugar_term env1 uu____3085))
in ((match ((match (x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
false
end
| uu____3087 -> begin
true
end)) with
| true -> begin
(

let uu____3088 = (

let uu____3093 = (

let uu____3094 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____3095 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____3096 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n" uu____3094 uu____3095 uu____3096))))
in ((FStar_Errors.Warning_MultipleAscriptions), (uu____3093)))
in (FStar_Errors.log_issue orig.FStar_Parser_AST.prange uu____3088))
end
| uu____3097 -> begin
()
end);
(

let uu____3098 = (annot_pat_var p3 t1)
in ((uu____3098), (LocalBinder ((((

let uu___119_3104 = x
in {FStar_Syntax_Syntax.ppname = uu___119_3104.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___119_3104.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})), (aq))))));
))
end)
in (match (uu____3052) with
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

let uu____3126 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3126), (false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____3137 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3137), (false))))
end
| FStar_Parser_AST.PatTvar (x, aq) -> begin
(

let imp = (Prims.op_Equality aq (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))
in (

let aq1 = (trans_aqual aq)
in (

let uu____3158 = (resolvex loc env1 x)
in (match (uu____3158) with
| (loc1, env2, xbv) -> begin
(

let uu____3180 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc1), (env2), (LocalBinder (((xbv), (aq1)))), (uu____3180), (imp)))
end))))
end
| FStar_Parser_AST.PatVar (x, aq) -> begin
(

let imp = (Prims.op_Equality aq (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))
in (

let aq1 = (trans_aqual aq)
in (

let uu____3201 = (resolvex loc env1 x)
in (match (uu____3201) with
| (loc1, env2, xbv) -> begin
(

let uu____3223 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc1), (env2), (LocalBinder (((xbv), (aq1)))), (uu____3223), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l1 = (FStar_Syntax_DsEnv.fail_or env1 (FStar_Syntax_DsEnv.try_lookup_datacon env1) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____3235 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), ([])))))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3235), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = uu____3259}, args) -> begin
(

let uu____3265 = (FStar_List.fold_right (fun arg uu____3306 -> (match (uu____3306) with
| (loc1, env2, args1) -> begin
(

let uu____3354 = (aux loc1 env2 arg)
in (match (uu____3354) with
| (loc2, env3, uu____3383, arg1, imp) -> begin
((loc2), (env3), ((((arg1), (imp)))::args1))
end))
end)) args ((loc), (env1), ([])))
in (match (uu____3265) with
| (loc1, env2, args1) -> begin
(

let l1 = (FStar_Syntax_DsEnv.fail_or env2 (FStar_Syntax_DsEnv.try_lookup_datacon env2) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____3453 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args1)))))
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3453), (false)))))
end))
end
| FStar_Parser_AST.PatApp (uu____3470) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedPattern), ("Unexpected pattern")) p1.FStar_Parser_AST.prange)
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____3492 = (FStar_List.fold_right (fun pat uu____3525 -> (match (uu____3525) with
| (loc1, env2, pats1) -> begin
(

let uu____3557 = (aux loc1 env2 pat)
in (match (uu____3557) with
| (loc2, env3, uu____3582, pat1, uu____3584) -> begin
((loc2), (env3), ((pat1)::pats1))
end))
end)) pats ((loc), (env1), ([])))
in (match (uu____3492) with
| (loc1, env2, pats1) -> begin
(

let pat = (

let uu____3627 = (

let uu____3630 = (

let uu____3635 = (FStar_Range.end_range p1.FStar_Parser_AST.prange)
in (pos_r uu____3635))
in (

let uu____3636 = (

let uu____3637 = (

let uu____3650 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____3650), ([])))
in FStar_Syntax_Syntax.Pat_cons (uu____3637))
in (FStar_All.pipe_left uu____3630 uu____3636)))
in (FStar_List.fold_right (fun hd1 tl1 -> (

let r = (FStar_Range.union_ranges hd1.FStar_Syntax_Syntax.p tl1.FStar_Syntax_Syntax.p)
in (

let uu____3682 = (

let uu____3683 = (

let uu____3696 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____3696), ((((hd1), (false)))::(((tl1), (false)))::[])))
in FStar_Syntax_Syntax.Pat_cons (uu____3683))
in (FStar_All.pipe_left (pos_r r) uu____3682)))) pats1 uu____3627))
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep1) -> begin
(

let uu____3740 = (FStar_List.fold_left (fun uu____3780 p2 -> (match (uu____3780) with
| (loc1, env2, pats) -> begin
(

let uu____3829 = (aux loc1 env2 p2)
in (match (uu____3829) with
| (loc2, env3, uu____3858, pat, uu____3860) -> begin
((loc2), (env3), ((((pat), (false)))::pats))
end))
end)) ((loc), (env1), ([])) args)
in (match (uu____3740) with
| (loc1, env2, args1) -> begin
(

let args2 = (FStar_List.rev args1)
in (

let l = (match (dep1) with
| true -> begin
(FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end
| uu____3948 -> begin
(FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end)
in (

let uu____3955 = (FStar_Syntax_DsEnv.fail_or env2 (FStar_Syntax_DsEnv.try_lookup_lid env2) l)
in (match (uu____3955) with
| (constr, uu____3977) -> begin
(

let l1 = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____3980 -> begin
(failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____3982 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args2)))))
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3982), (false)))))
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

let fields1 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____4053 -> (match (uu____4053) with
| (f, p2) -> begin
((f.FStar_Ident.ident), (p2))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map (fun uu____4083 -> (match (uu____4083) with
| (f, uu____4089) -> begin
(

let uu____4090 = (FStar_All.pipe_right fields1 (FStar_List.tryFind (fun uu____4116 -> (match (uu____4116) with
| (g, uu____4122) -> begin
(Prims.op_Equality f.FStar_Ident.idText g.FStar_Ident.idText)
end))))
in (match (uu____4090) with
| FStar_Pervasives_Native.None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p1.FStar_Parser_AST.prange)
end
| FStar_Pervasives_Native.Some (uu____4127, p2) -> begin
p2
end))
end))))
in (

let app = (

let uu____4134 = (

let uu____4135 = (

let uu____4142 = (

let uu____4143 = (

let uu____4144 = (FStar_Ident.lid_of_ids (FStar_List.append record.FStar_Syntax_DsEnv.typename.FStar_Ident.ns ((record.FStar_Syntax_DsEnv.constrname)::[])))
in FStar_Parser_AST.PatName (uu____4144))
in (FStar_Parser_AST.mk_pattern uu____4143 p1.FStar_Parser_AST.prange))
in ((uu____4142), (args)))
in FStar_Parser_AST.PatApp (uu____4135))
in (FStar_Parser_AST.mk_pattern uu____4134 p1.FStar_Parser_AST.prange))
in (

let uu____4147 = (aux loc env1 app)
in (match (uu____4147) with
| (env2, e, b, p2, uu____4176) -> begin
(

let p3 = (match (p2.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args1) -> begin
(

let uu____4204 = (

let uu____4205 = (

let uu____4218 = (

let uu___120_4219 = fv
in (

let uu____4220 = (

let uu____4223 = (

let uu____4224 = (

let uu____4231 = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map FStar_Pervasives_Native.fst))
in ((record.FStar_Syntax_DsEnv.typename), (uu____4231)))
in FStar_Syntax_Syntax.Record_ctor (uu____4224))
in FStar_Pervasives_Native.Some (uu____4223))
in {FStar_Syntax_Syntax.fv_name = uu___120_4219.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = uu___120_4219.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu____4220}))
in ((uu____4218), (args1)))
in FStar_Syntax_Syntax.Pat_cons (uu____4205))
in (FStar_All.pipe_left pos uu____4204))
end
| uu____4258 -> begin
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

let uu____4308 = (aux' true loc env1 p2)
in (match (uu____4308) with
| (loc1, env2, var, p3, uu____4335) -> begin
(

let uu____4340 = (FStar_List.fold_left (fun uu____4372 p4 -> (match (uu____4372) with
| (loc2, env3, ps1) -> begin
(

let uu____4405 = (aux' true loc2 env3 p4)
in (match (uu____4405) with
| (loc3, env4, uu____4430, p5, uu____4432) -> begin
((loc3), (env4), ((p5)::ps1))
end))
end)) ((loc1), (env2), ([])) ps)
in (match (uu____4340) with
| (loc2, env3, ps1) -> begin
(

let pats = (p3)::(FStar_List.rev ps1)
in ((env3), (var), (pats)))
end))
end))
end
| uu____4483 -> begin
(

let uu____4484 = (aux' true loc env1 p1)
in (match (uu____4484) with
| (loc1, env2, vars, pat, b) -> begin
((env2), (vars), ((pat)::[]))
end))
end)))
in (

let uu____4524 = (aux_maybe_or env p)
in (match (uu____4524) with
| (env1, b, pats) -> begin
((check_linear_pattern_variables pats p.FStar_Parser_AST.prange);
((env1), (b), (pats));
)
end))))));
)))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.list) = (fun top env p is_mut -> (

let mklet = (fun x -> (

let uu____4583 = (

let uu____4584 = (

let uu____4595 = (FStar_Syntax_DsEnv.qualify env x)
in ((uu____4595), (((FStar_Syntax_Syntax.tun), (FStar_Pervasives_Native.None)))))
in LetBinder (uu____4584))
in ((env), (uu____4583), ([]))))
in (match (top) with
| true -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(

let uu____4623 = (

let uu____4624 = (

let uu____4629 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") x.FStar_Ident.idText x.FStar_Ident.idRange)
in ((uu____4629), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____4624))
in (mklet uu____4623))
end
| FStar_Parser_AST.PatVar (x, uu____4631) -> begin
(mklet x)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____4637); FStar_Parser_AST.prange = uu____4638}, (t, tacopt)) -> begin
(

let tacopt1 = (FStar_Util.map_opt tacopt (desugar_term env))
in (

let uu____4658 = (

let uu____4659 = (

let uu____4670 = (FStar_Syntax_DsEnv.qualify env x)
in (

let uu____4671 = (

let uu____4678 = (desugar_term env t)
in ((uu____4678), (tacopt1)))
in ((uu____4670), (uu____4671))))
in LetBinder (uu____4659))
in ((env), (uu____4658), ([]))))
end
| uu____4689 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedPattern), ("Unexpected pattern at the top-level")) p.FStar_Parser_AST.prange)
end)
end
| uu____4698 -> begin
(

let uu____4699 = (desugar_data_pat env p is_mut)
in (match (uu____4699) with
| (env1, binder, p1) -> begin
(

let p2 = (match (p1) with
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (uu____4728); FStar_Syntax_Syntax.p = uu____4729})::[] -> begin
[]
end
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (uu____4734); FStar_Syntax_Syntax.p = uu____4735})::[] -> begin
[]
end
| uu____4740 -> begin
p1
end)
in ((env1), (binder), (p2)))
end))
end)))
and desugar_binding_pat : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.list) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat Prims.list) = (fun uu____4747 env pat -> (

let uu____4750 = (desugar_data_pat env pat false)
in (match (uu____4750) with
| (env1, uu____4766, pat1) -> begin
((env1), (pat1))
end)))
and desugar_match_pat : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat Prims.list) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term_aq : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations) = (fun env e -> (

let env1 = (FStar_Syntax_DsEnv.set_expect_typ env false)
in (desugar_term_maybe_top false env1 e)))
and desugar_term : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let uu____4785 = (desugar_term_aq env e)
in (match (uu____4785) with
| (t, aq) -> begin
((check_no_aq aq);
t;
)
end)))
and desugar_typ_aq : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations) = (fun env e -> (

let env1 = (FStar_Syntax_DsEnv.set_expect_typ env true)
in (desugar_term_maybe_top false env1 e)))
and desugar_typ : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let uu____4802 = (desugar_typ_aq env e)
in (match (uu____4802) with
| (t, aq) -> begin
((check_no_aq aq);
t;
)
end)))
and desugar_machine_integer : FStar_Syntax_DsEnv.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun env repr uu____4812 range -> (match (uu____4812) with
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

let uu____4822 = (

let uu____4823 = (FStar_Const.within_bounds repr signedness width)
in (not (uu____4823)))
in (match (uu____4822) with
| true -> begin
(

let uu____4824 = (

let uu____4829 = (FStar_Util.format2 "%s is not in the expected range for %s" repr tnm)
in ((FStar_Errors.Error_OutOfRange), (uu____4829)))
in (FStar_Errors.log_issue range uu____4824))
end
| uu____4830 -> begin
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

let lid = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text intro_nm) range)
in (

let lid1 = (

let uu____4837 = (FStar_Syntax_DsEnv.try_lookup_lid env lid)
in (match (uu____4837) with
| FStar_Pervasives_Native.Some (intro_term, uu____4847) -> begin
(match (intro_term.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let private_lid = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text private_intro_nm) range)
in (

let private_fv = (

let uu____4857 = (FStar_Syntax_Util.incr_delta_depth fv.FStar_Syntax_Syntax.fv_delta)
in (FStar_Syntax_Syntax.lid_as_fv private_lid uu____4857 fv.FStar_Syntax_Syntax.fv_qual))
in (

let uu___121_4858 = intro_term
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (private_fv); FStar_Syntax_Syntax.pos = uu___121_4858.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___121_4858.FStar_Syntax_Syntax.vars})))
end
| uu____4859 -> begin
(failwith (Prims.strcat "Unexpected non-fvar for " intro_nm))
end)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4866 = (

let uu____4871 = (FStar_Util.format1 "Unexpected numeric literal.  Restart F* to load %s." tnm)
in ((FStar_Errors.Fatal_UnexpectedNumericLiteral), (uu____4871)))
in (FStar_Errors.raise_error uu____4866 range))
end))
in (

let repr1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (FStar_Pervasives_Native.None))))) FStar_Pervasives_Native.None range)
in (

let uu____4887 = (

let uu____4890 = (

let uu____4891 = (

let uu____4906 = (

let uu____4915 = (

let uu____4922 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr1), (uu____4922)))
in (uu____4915)::[])
in ((lid1), (uu____4906)))
in FStar_Syntax_Syntax.Tm_app (uu____4891))
in (FStar_Syntax_Syntax.mk uu____4890))
in (uu____4887 FStar_Pervasives_Native.None range)))))));
))
end))
and desugar_name : (FStar_Syntax_Syntax.term'  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  env_t  ->  Prims.bool  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.term = (fun mk1 setpos env resolve l -> (

let uu____4961 = (FStar_Syntax_DsEnv.fail_or env ((match (resolve) with
| true -> begin
FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
end
| uu____4978 -> begin
FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve
end) env) l)
in (match (uu____4961) with
| (tm, mut, attrs) -> begin
(

let warn_if_deprecated = (fun attrs1 -> (FStar_List.iter (fun a -> (match (a.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____5007; FStar_Syntax_Syntax.vars = uu____5008}, args) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v FStar_Parser_Const.deprecated_attr) -> begin
(

let msg = (

let uu____5031 = (FStar_Syntax_Print.term_to_string tm)
in (Prims.strcat uu____5031 " is deprecated"))
in (

let msg1 = (match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5039 = (

let uu____5040 = (

let uu____5043 = (FStar_List.hd args)
in (FStar_Pervasives_Native.fst uu____5043))
in uu____5040.FStar_Syntax_Syntax.n)
in (match (uu____5039) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____5059)) when (not ((Prims.op_Equality (FStar_Util.trim_string s) ""))) -> begin
(Prims.strcat msg (Prims.strcat ", use " (Prims.strcat s " instead")))
end
| uu____5060 -> begin
msg
end))
end
| uu____5061 -> begin
msg
end)
in (FStar_Errors.log_issue (FStar_Ident.range_of_lid l) ((FStar_Errors.Warning_DeprecatedDefinition), (msg1)))))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v FStar_Parser_Const.deprecated_attr) -> begin
(

let msg = (

let uu____5064 = (FStar_Syntax_Print.term_to_string tm)
in (Prims.strcat uu____5064 " is deprecated"))
in (FStar_Errors.log_issue (FStar_Ident.range_of_lid l) ((FStar_Errors.Warning_DeprecatedDefinition), (msg))))
end
| uu____5065 -> begin
()
end)) attrs1))
in ((warn_if_deprecated attrs);
(

let tm1 = (setpos tm)
in (match (mut) with
| true -> begin
(

let uu____5070 = (

let uu____5071 = (

let uu____5078 = (mk_ref_read tm1)
in ((uu____5078), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval))))
in FStar_Syntax_Syntax.Tm_meta (uu____5071))
in (FStar_All.pipe_left mk1 uu____5070))
end
| uu____5083 -> begin
tm1
end));
))
end)))
and desugar_attributes : env_t  ->  FStar_Parser_AST.term Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun env cattributes -> (

let desugar_attribute = (fun t -> (

let uu____5094 = (

let uu____5095 = (unparen t)
in uu____5095.FStar_Parser_AST.tm)
in (match (uu____5094) with
| FStar_Parser_AST.Var ({FStar_Ident.ns = uu____5096; FStar_Ident.ident = uu____5097; FStar_Ident.nsstr = uu____5098; FStar_Ident.str = "cps"}) -> begin
FStar_Syntax_Syntax.CPS
end
| uu____5101 -> begin
(

let uu____5102 = (

let uu____5107 = (

let uu____5108 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "Unknown attribute " uu____5108))
in ((FStar_Errors.Fatal_UnknownAttribute), (uu____5107)))
in (FStar_Errors.raise_error uu____5102 t.FStar_Parser_AST.range))
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

let uu___122_5197 = e
in {FStar_Syntax_Syntax.n = uu___122_5197.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___122_5197.FStar_Syntax_Syntax.vars}))
in (

let uu____5200 = (

let uu____5201 = (unparen top)
in uu____5201.FStar_Parser_AST.tm)
in (match (uu____5200) with
| FStar_Parser_AST.Wild -> begin
(((setpos FStar_Syntax_Syntax.tun)), (noaqs))
end
| FStar_Parser_AST.Labeled (uu____5218) -> begin
(

let uu____5225 = (desugar_formula env top)
in ((uu____5225), (noaqs)))
end
| FStar_Parser_AST.Requires (t, lopt) -> begin
(

let uu____5242 = (desugar_formula env t)
in ((uu____5242), (noaqs)))
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(

let uu____5259 = (desugar_formula env t)
in ((uu____5259), (noaqs)))
end
| FStar_Parser_AST.Attributes (ts) -> begin
(failwith "Attributes should not be desugared by desugar_term_maybe_top")
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (i, FStar_Pervasives_Native.Some (size))) -> begin
(

let uu____5293 = (desugar_machine_integer env i size top.FStar_Parser_AST.range)
in ((uu____5293), (noaqs)))
end
| FStar_Parser_AST.Const (c) -> begin
(

let uu____5305 = (mk1 (FStar_Syntax_Syntax.Tm_constant (c)))
in ((uu____5305), (noaqs)))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "=!="; FStar_Ident.idRange = r}, args) -> begin
(

let e = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Op ((((FStar_Ident.mk_ident (("=="), (r)))), (args)))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (desugar_term_aq env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Op ((((FStar_Ident.mk_ident (("~"), (r)))), ((e)::[])))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))
end
| FStar_Parser_AST.Op (op_star, (uu____5332)::(uu____5333)::[]) when ((Prims.op_Equality (FStar_Ident.text_of_id op_star) "*") && (

let uu____5337 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range op_star)
in (FStar_All.pipe_right uu____5337 FStar_Option.isNone))) -> begin
(

let rec flatten1 = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____5350}, (t1)::(t2)::[]) -> begin
(

let uu____5355 = (flatten1 t1)
in (FStar_List.append uu____5355 ((t2)::[])))
end
| uu____5358 -> begin
(t)::[]
end))
in (

let uu____5359 = (

let uu____5368 = (

let uu____5375 = (

let uu____5378 = (unparen top)
in (flatten1 uu____5378))
in (FStar_All.pipe_right uu____5375 (FStar_List.map (fun t -> (

let uu____5397 = (desugar_typ_aq env t)
in (match (uu____5397) with
| (t', aq) -> begin
(

let uu____5408 = (FStar_Syntax_Syntax.as_arg t')
in ((uu____5408), (aq)))
end))))))
in (FStar_All.pipe_right uu____5368 FStar_List.unzip))
in (match (uu____5359) with
| (targs, aqs) -> begin
(

let uu____5437 = (

let uu____5442 = (FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_lid env) uu____5442))
in (match (uu____5437) with
| (tup, uu____5452) -> begin
(

let uu____5453 = (mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
in ((uu____5453), ((join_aqs aqs))))
end))
end)))
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____5471 = (

let uu____5474 = (

let uu____5477 = (FStar_Syntax_DsEnv.fail_or2 (FStar_Syntax_DsEnv.try_lookup_id env) a)
in (FStar_Pervasives_Native.fst uu____5477))
in (FStar_All.pipe_left setpos uu____5474))
in ((uu____5471), (noaqs)))
end
| FStar_Parser_AST.Uvar (u) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedUniverseVariable), ((Prims.strcat "Unexpected universe variable " (Prims.strcat (FStar_Ident.text_of_id u) " in non-universe context")))) top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Op (s, args) -> begin
(

let uu____5513 = (op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)
in (match (uu____5513) with
| FStar_Pervasives_Native.None -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnepxectedOrUnboundOperator), ((Prims.strcat "Unexpected or unbound operator: " (FStar_Ident.text_of_id s)))) top.FStar_Parser_AST.range)
end
| FStar_Pervasives_Native.Some (op) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5529 = (

let uu____5544 = (FStar_All.pipe_right args (FStar_List.map (fun t -> (

let uu____5586 = (desugar_term_aq env t)
in (match (uu____5586) with
| (t', s1) -> begin
((((t'), (FStar_Pervasives_Native.None))), (s1))
end)))))
in (FStar_All.pipe_right uu____5544 FStar_List.unzip))
in (match (uu____5529) with
| (args1, aqs) -> begin
(

let uu____5669 = (mk1 (FStar_Syntax_Syntax.Tm_app (((op), (args1)))))
in ((uu____5669), ((join_aqs aqs))))
end))
end
| uu____5692 -> begin
((op), (noaqs))
end)
end))
end
| FStar_Parser_AST.Construct (n1, ((a, uu____5705))::[]) when (Prims.op_Equality n1.FStar_Ident.str "SMTPat") -> begin
(

let uu____5720 = (

let uu___123_5721 = top
in (

let uu____5722 = (

let uu____5723 = (

let uu____5730 = (

let uu___124_5731 = top
in (

let uu____5732 = (

let uu____5733 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____5733))
in {FStar_Parser_AST.tm = uu____5732; FStar_Parser_AST.range = uu___124_5731.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___124_5731.FStar_Parser_AST.level}))
in ((uu____5730), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____5723))
in {FStar_Parser_AST.tm = uu____5722; FStar_Parser_AST.range = uu___123_5721.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___123_5721.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____5720))
end
| FStar_Parser_AST.Construct (n1, ((a, uu____5736))::[]) when (Prims.op_Equality n1.FStar_Ident.str "SMTPatT") -> begin
((FStar_Errors.log_issue top.FStar_Parser_AST.range ((FStar_Errors.Warning_SMTPatTDeprecated), ("SMTPatT is deprecated; please just use SMTPat")));
(

let uu____5752 = (

let uu___125_5753 = top
in (

let uu____5754 = (

let uu____5755 = (

let uu____5762 = (

let uu___126_5763 = top
in (

let uu____5764 = (

let uu____5765 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____5765))
in {FStar_Parser_AST.tm = uu____5764; FStar_Parser_AST.range = uu___126_5763.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___126_5763.FStar_Parser_AST.level}))
in ((uu____5762), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____5755))
in {FStar_Parser_AST.tm = uu____5754; FStar_Parser_AST.range = uu___125_5753.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___125_5753.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____5752));
)
end
| FStar_Parser_AST.Construct (n1, ((a, uu____5768))::[]) when (Prims.op_Equality n1.FStar_Ident.str "SMTPatOr") -> begin
(

let uu____5783 = (

let uu___127_5784 = top
in (

let uu____5785 = (

let uu____5786 = (

let uu____5793 = (

let uu___128_5794 = top
in (

let uu____5795 = (

let uu____5796 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat_or")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____5796))
in {FStar_Parser_AST.tm = uu____5795; FStar_Parser_AST.range = uu___128_5794.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___128_5794.FStar_Parser_AST.level}))
in ((uu____5793), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____5786))
in {FStar_Parser_AST.tm = uu____5785; FStar_Parser_AST.range = uu___127_5784.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___127_5784.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____5783))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____5797; FStar_Ident.ident = uu____5798; FStar_Ident.nsstr = uu____5799; FStar_Ident.str = "Type0"}) -> begin
(

let uu____5802 = (mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
in ((uu____5802), (noaqs)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____5817; FStar_Ident.ident = uu____5818; FStar_Ident.nsstr = uu____5819; FStar_Ident.str = "Type"}) -> begin
(

let uu____5822 = (mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
in ((uu____5822), (noaqs)))
end
| FStar_Parser_AST.Construct ({FStar_Ident.ns = uu____5837; FStar_Ident.ident = uu____5838; FStar_Ident.nsstr = uu____5839; FStar_Ident.str = "Type"}, ((t, FStar_Parser_AST.UnivApp))::[]) -> begin
(

let uu____5857 = (

let uu____5860 = (

let uu____5861 = (desugar_universe t)
in FStar_Syntax_Syntax.Tm_type (uu____5861))
in (mk1 uu____5860))
in ((uu____5857), (noaqs)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____5874; FStar_Ident.ident = uu____5875; FStar_Ident.nsstr = uu____5876; FStar_Ident.str = "Effect"}) -> begin
(

let uu____5879 = (mk1 (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
in ((uu____5879), (noaqs)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____5894; FStar_Ident.ident = uu____5895; FStar_Ident.nsstr = uu____5896; FStar_Ident.str = "True"}) -> begin
(

let uu____5899 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in ((uu____5899), (noaqs)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____5910; FStar_Ident.ident = uu____5911; FStar_Ident.nsstr = uu____5912; FStar_Ident.str = "False"}) -> begin
(

let uu____5915 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in ((uu____5915), (noaqs)))
end
| FStar_Parser_AST.Projector (eff_name, {FStar_Ident.idText = txt; FStar_Ident.idRange = uu____5928}) when ((is_special_effect_combinator txt) && (FStar_Syntax_DsEnv.is_effect_name env eff_name)) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name);
(

let uu____5930 = (FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name)
in (match (uu____5930) with
| FStar_Pervasives_Native.Some (ed) -> begin
(

let lid = (FStar_Syntax_Util.dm4f_lid ed txt)
in (

let uu____5939 = (FStar_Syntax_Syntax.fvar lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in ((uu____5939), (noaqs))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5950 = (FStar_Util.format2 "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)" (FStar_Ident.text_of_lid eff_name) txt)
in (failwith uu____5950))
end));
)
end
| FStar_Parser_AST.Var (l) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l);
(

let uu____5957 = (desugar_name mk1 setpos env true l)
in ((uu____5957), (noaqs)));
)
end
| FStar_Parser_AST.Name (l) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l);
(

let uu____5970 = (desugar_name mk1 setpos env true l)
in ((uu____5970), (noaqs)));
)
end
| FStar_Parser_AST.Projector (l, i) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l);
(

let name = (

let uu____5991 = (FStar_Syntax_DsEnv.try_lookup_datacon env l)
in (match (uu____5991) with
| FStar_Pervasives_Native.Some (uu____6000) -> begin
FStar_Pervasives_Native.Some (((true), (l)))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____6005 = (FStar_Syntax_DsEnv.try_lookup_root_effect_name env l)
in (match (uu____6005) with
| FStar_Pervasives_Native.Some (new_name) -> begin
FStar_Pervasives_Native.Some (((false), (new_name)))
end
| uu____6019 -> begin
FStar_Pervasives_Native.None
end))
end))
in (match (name) with
| FStar_Pervasives_Native.Some (resolve, new_name) -> begin
(

let uu____6036 = (

let uu____6037 = (FStar_Syntax_Util.mk_field_projector_name_from_ident new_name i)
in (desugar_name mk1 setpos env resolve uu____6037))
in ((uu____6036), (noaqs)))
end
| uu____6048 -> begin
(

let uu____6055 = (

let uu____6060 = (FStar_Util.format1 "Data constructor or effect %s not found" l.FStar_Ident.str)
in ((FStar_Errors.Fatal_EffectNotFound), (uu____6060)))
in (FStar_Errors.raise_error uu____6055 top.FStar_Parser_AST.range))
end));
)
end
| FStar_Parser_AST.Discrim (lid) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid);
(

let uu____6067 = (FStar_Syntax_DsEnv.try_lookup_datacon env lid)
in (match (uu____6067) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6074 = (

let uu____6079 = (FStar_Util.format1 "Data constructor %s not found" lid.FStar_Ident.str)
in ((FStar_Errors.Fatal_DataContructorNotFound), (uu____6079)))
in (FStar_Errors.raise_error uu____6074 top.FStar_Parser_AST.range))
end
| uu____6084 -> begin
(

let lid' = (FStar_Syntax_Util.mk_discriminator lid)
in (

let uu____6088 = (desugar_name mk1 setpos env true lid')
in ((uu____6088), (noaqs))))
end));
)
end
| FStar_Parser_AST.Construct (l, args) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l);
(

let uu____6114 = (FStar_Syntax_DsEnv.try_lookup_datacon env l)
in (match (uu____6114) with
| FStar_Pervasives_Native.Some (head1) -> begin
(

let head2 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (head1)))
in (match (args) with
| [] -> begin
((head2), (noaqs))
end
| uu____6145 -> begin
(

let uu____6152 = (FStar_Util.take (fun uu____6176 -> (match (uu____6176) with
| (uu____6181, imp) -> begin
(Prims.op_Equality imp FStar_Parser_AST.UnivApp)
end)) args)
in (match (uu____6152) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun x -> (desugar_universe (FStar_Pervasives_Native.fst x))) universes)
in (

let uu____6226 = (

let uu____6241 = (FStar_List.map (fun uu____6274 -> (match (uu____6274) with
| (t, imp) -> begin
(

let uu____6291 = (desugar_term_aq env t)
in (match (uu____6291) with
| (te, aq) -> begin
(((arg_withimp_e imp te)), (aq))
end))
end)) args1)
in (FStar_All.pipe_right uu____6241 FStar_List.unzip))
in (match (uu____6226) with
| (args2, aqs) -> begin
(

let head3 = (match ((Prims.op_Equality universes1 [])) with
| true -> begin
head2
end
| uu____6379 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_uinst (((head2), (universes1)))))
end)
in (

let uu____6384 = (mk1 (FStar_Syntax_Syntax.Tm_app (((head3), (args2)))))
in ((uu____6384), ((join_aqs aqs)))))
end)))
end))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let err = (

let uu____6414 = (FStar_Syntax_DsEnv.try_lookup_effect_name env l)
in (match (uu____6414) with
| FStar_Pervasives_Native.None -> begin
((FStar_Errors.Fatal_ConstructorNotFound), ((Prims.strcat "Constructor " (Prims.strcat l.FStar_Ident.str " not found"))))
end
| FStar_Pervasives_Native.Some (uu____6421) -> begin
((FStar_Errors.Fatal_UnexpectedEffect), ((Prims.strcat "Effect " (Prims.strcat l.FStar_Ident.str " used at an unexpected position"))))
end))
in (FStar_Errors.raise_error err top.FStar_Parser_AST.range))
end));
)
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let uu____6432 = (FStar_List.fold_left (fun uu____6477 b -> (match (uu____6477) with
| (env1, tparams, typs) -> begin
(

let uu____6534 = (desugar_binder env1 b)
in (match (uu____6534) with
| (xopt, t1) -> begin
(

let uu____6563 = (match (xopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6572 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env1), (uu____6572)))
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_DsEnv.push_bv env1 x)
end)
in (match (uu____6563) with
| (env2, x) -> begin
(

let uu____6592 = (

let uu____6595 = (

let uu____6598 = (

let uu____6599 = (no_annot_abs tparams t1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____6599))
in (uu____6598)::[])
in (FStar_List.append typs uu____6595))
in ((env2), ((FStar_List.append tparams (((((

let uu___129_6625 = x
in {FStar_Syntax_Syntax.ppname = uu___129_6625.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___129_6625.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})), (FStar_Pervasives_Native.None)))::[]))), (uu____6592)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type_level FStar_Pervasives_Native.None))::[])))
in (match (uu____6432) with
| (env1, uu____6653, targs) -> begin
(

let uu____6675 = (

let uu____6680 = (FStar_Parser_Const.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Syntax_DsEnv.fail_or env1 (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____6680))
in (match (uu____6675) with
| (tup, uu____6690) -> begin
(

let uu____6691 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
in ((uu____6691), (noaqs)))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let uu____6716 = (uncurry binders t)
in (match (uu____6716) with
| (bs, t1) -> begin
(

let rec aux = (fun env1 bs1 uu___95_6752 -> (match (uu___95_6752) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range env1 t1)
in (

let uu____6766 = (FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod)
in (FStar_All.pipe_left setpos uu____6766)))
end
| (hd1)::tl1 -> begin
(

let bb = (desugar_binder env1 hd1)
in (

let uu____6788 = (as_binder env1 hd1.FStar_Parser_AST.aqual bb)
in (match (uu____6788) with
| (b, env2) -> begin
(aux env2 ((b)::bs1) tl1)
end)))
end))
in (

let uu____6797 = (aux env [] bs)
in ((uu____6797), (noaqs))))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(

let uu____6818 = (desugar_binder env b)
in (match (uu____6818) with
| (FStar_Pervasives_Native.None, uu____6829) -> begin
(failwith "Missing binder in refinement")
end
| b1 -> begin
(

let uu____6843 = (as_binder env FStar_Pervasives_Native.None b1)
in (match (uu____6843) with
| ((x, uu____6853), env1) -> begin
(

let f1 = (desugar_formula env1 f)
in (

let uu____6860 = (

let uu____6863 = (FStar_Syntax_Util.refine x f1)
in (FStar_All.pipe_left setpos uu____6863))
in ((uu____6860), (noaqs))))
end))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let binders1 = (FStar_All.pipe_right binders (FStar_List.map replace_unit_pattern))
in (

let uu____6895 = (FStar_List.fold_left (fun uu____6915 pat -> (match (uu____6915) with
| (env1, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (uu____6941, (t, FStar_Pervasives_Native.None)) -> begin
(

let uu____6951 = (

let uu____6954 = (free_type_vars env1 t)
in (FStar_List.append uu____6954 ftvs))
in ((env1), (uu____6951)))
end
| FStar_Parser_AST.PatAscribed (uu____6959, (t, FStar_Pervasives_Native.Some (tac))) -> begin
(

let uu____6970 = (

let uu____6973 = (free_type_vars env1 t)
in (

let uu____6976 = (

let uu____6979 = (free_type_vars env1 tac)
in (FStar_List.append uu____6979 ftvs))
in (FStar_List.append uu____6973 uu____6976)))
in ((env1), (uu____6970)))
end
| uu____6984 -> begin
((env1), (ftvs))
end)
end)) ((env), ([])) binders1)
in (match (uu____6895) with
| (uu____6993, ftv) -> begin
(

let ftv1 = (sort_ftv ftv)
in (

let binders2 = (

let uu____7005 = (FStar_All.pipe_right ftv1 (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append uu____7005 binders1))
in (

let rec aux = (fun env1 bs sc_pat_opt uu___96_7050 -> (match (uu___96_7050) with
| [] -> begin
(

let uu____7073 = (desugar_term_aq env1 body)
in (match (uu____7073) with
| (body1, aq) -> begin
(

let body2 = (match (sc_pat_opt) with
| FStar_Pervasives_Native.Some (sc, pat) -> begin
(

let body2 = (

let uu____7104 = (

let uu____7105 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right uu____7105 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close uu____7104 body1))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (FStar_Pervasives_Native.None), (body2)))::[])))) FStar_Pervasives_Native.None body2.FStar_Syntax_Syntax.pos))
end
| FStar_Pervasives_Native.None -> begin
body1
end)
in (

let uu____7158 = (

let uu____7161 = (no_annot_abs (FStar_List.rev bs) body2)
in (setpos uu____7161))
in ((uu____7158), (aq))))
end))
end
| (p)::rest -> begin
(

let uu____7174 = (desugar_binding_pat env1 p)
in (match (uu____7174) with
| (env2, b, pat) -> begin
(

let pat1 = (match (pat) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (p1)::[] -> begin
FStar_Pervasives_Native.Some (p1)
end
| uu____7202 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnsupportedDisjuctivePatterns), ("Disjunctive patterns are not supported in abstractions")) p.FStar_Parser_AST.prange)
end)
in (

let uu____7207 = (match (b) with
| LetBinder (uu____7240) -> begin
(failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt1 = (match (((pat1), (sc_pat_opt))) with
| (FStar_Pervasives_Native.None, uu____7296) -> begin
sc_pat_opt
end
| (FStar_Pervasives_Native.Some (p1), FStar_Pervasives_Native.None) -> begin
(

let uu____7332 = (

let uu____7337 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____7337), (p1)))
in FStar_Pervasives_Native.Some (uu____7332))
end
| (FStar_Pervasives_Native.Some (p1), FStar_Pervasives_Native.Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (uu____7373), uu____7374) -> begin
(

let tup2 = (

let uu____7376 = (FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____7376 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____7380 = (

let uu____7383 = (

let uu____7384 = (

let uu____7399 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (

let uu____7402 = (

let uu____7405 = (FStar_Syntax_Syntax.as_arg sc)
in (

let uu____7406 = (

let uu____7409 = (

let uu____7410 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____7410))
in (uu____7409)::[])
in (uu____7405)::uu____7406))
in ((uu____7399), (uu____7402))))
in FStar_Syntax_Syntax.Tm_app (uu____7384))
in (FStar_Syntax_Syntax.mk uu____7383))
in (uu____7380 FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
in (

let p2 = (

let uu____7421 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p1), (false)))::[])))) uu____7421))
in FStar_Pervasives_Native.Some (((sc1), (p2))))))
end
| (FStar_Syntax_Syntax.Tm_app (uu____7452, args), FStar_Syntax_Syntax.Pat_cons (uu____7454, pats)) -> begin
(

let tupn = (

let uu____7493 = (FStar_Parser_Const.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____7493 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____7503 = (

let uu____7504 = (

let uu____7519 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (

let uu____7522 = (

let uu____7531 = (

let uu____7540 = (

let uu____7541 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____7541))
in (uu____7540)::[])
in (FStar_List.append args uu____7531))
in ((uu____7519), (uu____7522))))
in FStar_Syntax_Syntax.Tm_app (uu____7504))
in (mk1 uu____7503))
in (

let p2 = (

let uu____7561 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p1), (false)))::[])))))) uu____7561))
in FStar_Pervasives_Native.Some (((sc1), (p2))))))
end
| uu____7596 -> begin
(failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt1)))
end)
in (match (uu____7207) with
| (b1, sc_pat_opt1) -> begin
(aux env2 ((b1)::bs) sc_pat_opt1 rest)
end)))
end))
end))
in (aux env [] FStar_Pervasives_Native.None binders2))))
end)))
end
| FStar_Parser_AST.App (uu____7667, uu____7668, FStar_Parser_AST.UnivApp) -> begin
(

let rec aux = (fun universes e -> (

let uu____7686 = (

let uu____7687 = (unparen e)
in uu____7687.FStar_Parser_AST.tm)
in (match (uu____7686) with
| FStar_Parser_AST.App (e1, t, FStar_Parser_AST.UnivApp) -> begin
(

let univ_arg = (desugar_universe t)
in (aux ((univ_arg)::universes) e1))
end
| uu____7697 -> begin
(

let uu____7698 = (desugar_term_aq env e)
in (match (uu____7698) with
| (head1, aq) -> begin
(

let uu____7711 = (mk1 (FStar_Syntax_Syntax.Tm_uinst (((head1), (universes)))))
in ((uu____7711), (aq)))
end))
end)))
in (aux [] top))
end
| FStar_Parser_AST.App (uu____7718) -> begin
(

let rec aux = (fun args aqs e -> (

let uu____7771 = (

let uu____7772 = (unparen e)
in uu____7772.FStar_Parser_AST.tm)
in (match (uu____7771) with
| FStar_Parser_AST.App (e1, t, imp) when (Prims.op_disEquality imp FStar_Parser_AST.UnivApp) -> begin
(

let uu____7792 = (desugar_term_aq env t)
in (match (uu____7792) with
| (t1, aq) -> begin
(

let arg = (arg_withimp_e imp t1)
in (aux ((arg)::args) ((aq)::aqs) e1))
end))
end
| uu____7828 -> begin
(

let uu____7829 = (desugar_term_aq env e)
in (match (uu____7829) with
| (head1, aq) -> begin
(

let uu____7852 = (mk1 (FStar_Syntax_Syntax.Tm_app (((head1), (args)))))
in ((uu____7852), ((join_aqs ((aq)::aqs)))))
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

let uu____7892 = (FStar_Parser_AST.mkExplicitApp bind1 ((t1)::(k)::[]) top.FStar_Parser_AST.range)
in (desugar_term_aq env uu____7892))))))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(

let t = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), ((((FStar_Pervasives_Native.None), ((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
in (

let uu____7944 = (desugar_term_aq env t)
in (match (uu____7944) with
| (tm, s) -> begin
(

let uu____7955 = (mk1 (FStar_Syntax_Syntax.Tm_meta (((tm), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))))
in ((uu____7955), (s)))
end)))
end
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(

let env1 = (FStar_Syntax_DsEnv.push_namespace env lid)
in (

let uu____7963 = (

let uu____7972 = (FStar_Syntax_DsEnv.expect_typ env1)
in (match (uu____7972) with
| true -> begin
desugar_typ_aq
end
| uu____7981 -> begin
desugar_term_aq
end))
in (uu____7963 env1 e)))
end
| FStar_Parser_AST.Let (qual, lbs, body) -> begin
(

let is_rec = (Prims.op_Equality qual FStar_Parser_AST.Rec)
in (

let ds_let_rec_or_app = (fun uu____8023 -> (

let bindings = lbs
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun uu____8166 -> (match (uu____8166) with
| (attr_opt, (p, def)) -> begin
(

let uu____8224 = (is_app_pattern p)
in (match (uu____8224) with
| true -> begin
(

let uu____8255 = (destruct_app_pattern env top_level p)
in ((attr_opt), (uu____8255), (def)))
end
| uu____8300 -> begin
(match ((FStar_Parser_AST.un_function p def)) with
| FStar_Pervasives_Native.Some (p1, def1) -> begin
(

let uu____8337 = (destruct_app_pattern env top_level p1)
in ((attr_opt), (uu____8337), (def1)))
end
| uu____8382 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id1, uu____8420); FStar_Parser_AST.prange = uu____8421}, t) -> begin
(match (top_level) with
| true -> begin
(

let uu____8469 = (

let uu____8490 = (

let uu____8495 = (FStar_Syntax_DsEnv.qualify env id1)
in FStar_Util.Inr (uu____8495))
in ((uu____8490), ([]), (FStar_Pervasives_Native.Some (t))))
in ((attr_opt), (uu____8469), (def)))
end
| uu____8540 -> begin
((attr_opt), (((FStar_Util.Inl (id1)), ([]), (FStar_Pervasives_Native.Some (t)))), (def))
end)
end
| FStar_Parser_AST.PatVar (id1, uu____8586) -> begin
(match (top_level) with
| true -> begin
(

let uu____8621 = (

let uu____8642 = (

let uu____8647 = (FStar_Syntax_DsEnv.qualify env id1)
in FStar_Util.Inr (uu____8647))
in ((uu____8642), ([]), (FStar_Pervasives_Native.None)))
in ((attr_opt), (uu____8621), (def)))
end
| uu____8692 -> begin
((attr_opt), (((FStar_Util.Inl (id1)), ([]), (FStar_Pervasives_Native.None))), (def))
end)
end
| uu____8737 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedLetBinding), ("Unexpected let binding")) p.FStar_Parser_AST.prange)
end)
end)
end))
end))))
in (

let uu____8768 = (FStar_List.fold_left (fun uu____8841 uu____8842 -> (match (((uu____8841), (uu____8842))) with
| ((env1, fnames, rec_bindings), (_attr_opt, (f, uu____8950, uu____8951), uu____8952)) -> begin
(

let uu____9069 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let uu____9095 = (FStar_Syntax_DsEnv.push_bv env1 x)
in (match (uu____9095) with
| (env2, xx) -> begin
(

let uu____9114 = (

let uu____9117 = (FStar_Syntax_Syntax.mk_binder xx)
in (uu____9117)::rec_bindings)
in ((env2), (FStar_Util.Inl (xx)), (uu____9114)))
end))
end
| FStar_Util.Inr (l) -> begin
(

let uu____9125 = (FStar_Syntax_DsEnv.push_top_level_rec_binding env1 l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in ((uu____9125), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (uu____9069) with
| (env2, lbname, rec_bindings1) -> begin
((env2), ((lbname)::fnames), (rec_bindings1))
end))
end)) ((env), ([]), ([])) funs)
in (match (uu____8768) with
| (env', fnames, rec_bindings) -> begin
(

let fnames1 = (FStar_List.rev fnames)
in (

let rec_bindings1 = (FStar_List.rev rec_bindings)
in (

let desugar_one_def = (fun env1 lbname uu____9267 -> (match (uu____9267) with
| (attrs_opt, (uu____9303, args, result_t), def) -> begin
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

let uu____9391 = (is_comp_type env1 t)
in (match (uu____9391) with
| true -> begin
((

let uu____9393 = (FStar_All.pipe_right args1 (FStar_List.tryFind (fun x -> (

let uu____9403 = (is_var_pattern x)
in (not (uu____9403))))))
in (match (uu____9393) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (p) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ComputationTypeNotAllowed), ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")) p.FStar_Parser_AST.prange)
end));
t;
)
end
| uu____9405 -> begin
(

let uu____9406 = (((FStar_Options.ml_ish ()) && (

let uu____9408 = (FStar_Syntax_DsEnv.try_lookup_effect_name env1 FStar_Parser_Const.effect_ML_lid)
in (FStar_Option.isSome uu____9408))) && ((not (is_rec)) || (Prims.op_disEquality (FStar_List.length args1) (Prims.parse_int "0"))))
in (match (uu____9406) with
| true -> begin
(FStar_Parser_AST.ml_comp t)
end
| uu____9411 -> begin
(FStar_Parser_AST.tot_comp t)
end))
end))
in (

let uu____9412 = (FStar_Range.union_ranges t1.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t1), (tacopt)))) uu____9412 FStar_Parser_AST.Expr)))
end)
in (

let def2 = (match (args1) with
| [] -> begin
def1
end
| uu____9416 -> begin
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

let uu____9431 = (

let uu____9432 = (FStar_Syntax_Util.incr_delta_qualifier body1)
in (FStar_Syntax_Syntax.lid_as_fv l uu____9432 FStar_Pervasives_Native.None))
in FStar_Util.Inr (uu____9431))
end)
in (

let body2 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.close rec_bindings1 body1)
end
| uu____9434 -> begin
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
| uu____9490 -> begin
env
end)) fnames1 funs)
in (

let uu____9491 = (desugar_term_aq env' body)
in (match (uu____9491) with
| (body1, aq) -> begin
(

let uu____9504 = (

let uu____9507 = (

let uu____9508 = (

let uu____9521 = (FStar_Syntax_Subst.close rec_bindings1 body1)
in ((((is_rec), (lbs1))), (uu____9521)))
in FStar_Syntax_Syntax.Tm_let (uu____9508))
in (FStar_All.pipe_left mk1 uu____9507))
in ((uu____9504), (aq)))
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
| uu____9580 -> begin
t11
end)
in (

let uu____9581 = (desugar_binding_pat_maybe_top top_level env pat is_mutable)
in (match (uu____9581) with
| (env1, binder, pat1) -> begin
(

let uu____9603 = (match (binder) with
| LetBinder (l, (t, _tacopt)) -> begin
(

let uu____9629 = (desugar_term_aq env1 t2)
in (match (uu____9629) with
| (body1, aq) -> begin
(

let fv = (

let uu____9643 = (FStar_Syntax_Util.incr_delta_qualifier t12)
in (FStar_Syntax_Syntax.lid_as_fv l uu____9643 FStar_Pervasives_Native.None))
in (

let uu____9644 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_let (((((false), (((mk_lb ((attrs), (FStar_Util.Inr (fv)), (t), (t12), (t12.FStar_Syntax_Syntax.pos))))::[]))), (body1)))))
in ((uu____9644), (aq))))
end))
end
| LocalBinder (x, uu____9668) -> begin
(

let uu____9669 = (desugar_term_aq env1 t2)
in (match (uu____9669) with
| (body1, aq) -> begin
(

let body2 = (match (pat1) with
| [] -> begin
body1
end
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (uu____9683); FStar_Syntax_Syntax.p = uu____9684})::[] -> begin
body1
end
| uu____9689 -> begin
(

let uu____9692 = (

let uu____9695 = (

let uu____9696 = (

let uu____9719 = (FStar_Syntax_Syntax.bv_to_name x)
in (

let uu____9720 = (desugar_disjunctive_pattern pat1 FStar_Pervasives_Native.None body1)
in ((uu____9719), (uu____9720))))
in FStar_Syntax_Syntax.Tm_match (uu____9696))
in (FStar_Syntax_Syntax.mk uu____9695))
in (uu____9692 FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
end)
in (

let uu____9730 = (

let uu____9733 = (

let uu____9734 = (

let uu____9747 = (

let uu____9748 = (

let uu____9749 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____9749)::[])
in (FStar_Syntax_Subst.close uu____9748 body2))
in ((((false), (((mk_lb ((attrs), (FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t12), (t12.FStar_Syntax_Syntax.pos))))::[]))), (uu____9747)))
in FStar_Syntax_Syntax.Tm_let (uu____9734))
in (FStar_All.pipe_left mk1 uu____9733))
in ((uu____9730), (aq))))
end))
end)
in (match (uu____9603) with
| (tm, aq) -> begin
(match (is_mutable) with
| true -> begin
(

let uu____9790 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((tm), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc))))))
in ((uu____9790), (aq)))
end
| uu____9799 -> begin
((tm), (aq))
end)
end))
end)))))))
in (

let uu____9802 = (FStar_List.hd lbs)
in (match (uu____9802) with
| (attrs, (head_pat, defn)) -> begin
(

let uu____9846 = (is_rec || (is_app_pattern head_pat))
in (match (uu____9846) with
| true -> begin
(ds_let_rec_or_app ())
end
| uu____9851 -> begin
(ds_non_rec attrs head_pat defn body)
end))
end)))))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (

let t_bool1 = (

let uu____9859 = (

let uu____9860 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Syntax_Syntax.Tm_fvar (uu____9860))
in (mk1 uu____9859))
in (

let uu____9861 = (desugar_term_aq env t1)
in (match (uu____9861) with
| (t1', aq1) -> begin
(

let uu____9872 = (desugar_term_aq env t2)
in (match (uu____9872) with
| (t2', aq2) -> begin
(

let uu____9883 = (desugar_term_aq env t3)
in (match (uu____9883) with
| (t3', aq3) -> begin
(

let uu____9894 = (

let uu____9897 = (

let uu____9898 = (

let uu____9921 = (FStar_Syntax_Util.ascribe t1' ((FStar_Util.Inl (t_bool1)), (FStar_Pervasives_Native.None)))
in (

let uu____9942 = (

let uu____9957 = (

let uu____9970 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) t2.FStar_Parser_AST.range)
in ((uu____9970), (FStar_Pervasives_Native.None), (t2')))
in (

let uu____9981 = (

let uu____9996 = (

let uu____10009 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) t3.FStar_Parser_AST.range)
in ((uu____10009), (FStar_Pervasives_Native.None), (t3')))
in (uu____9996)::[])
in (uu____9957)::uu____9981))
in ((uu____9921), (uu____9942))))
in FStar_Syntax_Syntax.Tm_match (uu____9898))
in (mk1 uu____9897))
in ((uu____9894), ((join_aqs ((aq1)::(aq2)::(aq3)::[])))))
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

let desugar_branch = (fun uu____10168 -> (match (uu____10168) with
| (pat, wopt, b) -> begin
(

let uu____10190 = (desugar_match_pat env pat)
in (match (uu____10190) with
| (env1, pat1) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (e1) -> begin
(

let uu____10215 = (desugar_term env1 e1)
in FStar_Pervasives_Native.Some (uu____10215))
end)
in (

let uu____10216 = (desugar_term_aq env1 b)
in (match (uu____10216) with
| (b1, aq) -> begin
(

let uu____10229 = (desugar_disjunctive_pattern pat1 wopt1 b1)
in ((uu____10229), (aq)))
end)))
end))
end))
in (

let uu____10234 = (desugar_term_aq env e)
in (match (uu____10234) with
| (e1, aq) -> begin
(

let uu____10245 = (

let uu____10254 = (

let uu____10265 = (FStar_List.map desugar_branch branches)
in (FStar_All.pipe_right uu____10265 FStar_List.unzip))
in (FStar_All.pipe_right uu____10254 (fun uu____10329 -> (match (uu____10329) with
| (x, y) -> begin
(((FStar_List.flatten x)), (y))
end))))
in (match (uu____10245) with
| (brs, aqs) -> begin
(

let uu____10380 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_match (((e1), (brs)))))
in ((uu____10380), ((join_aqs ((aq)::aqs)))))
end))
end)))
end
| FStar_Parser_AST.Ascribed (e, t, tac_opt) -> begin
(

let annot = (

let uu____10413 = (is_comp_type env t)
in (match (uu____10413) with
| true -> begin
(

let uu____10420 = (desugar_comp t.FStar_Parser_AST.range env t)
in FStar_Util.Inr (uu____10420))
end
| uu____10425 -> begin
(

let uu____10426 = (desugar_term env t)
in FStar_Util.Inl (uu____10426))
end))
in (

let tac_opt1 = (FStar_Util.map_opt tac_opt (desugar_term env))
in (

let uu____10432 = (desugar_term_aq env e)
in (match (uu____10432) with
| (e1, aq) -> begin
(

let uu____10443 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_ascribed (((e1), (((annot), (tac_opt1))), (FStar_Pervasives_Native.None)))))
in ((uu____10443), (aq)))
end))))
end
| FStar_Parser_AST.Record (uu____10472, []) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedEmptyRecord), ("Unexpected empty record")) top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let record = (check_fields env fields top.FStar_Parser_AST.range)
in (

let user_ns = (

let uu____10513 = (FStar_List.hd fields)
in (match (uu____10513) with
| (f, uu____10525) -> begin
f.FStar_Ident.ns
end))
in (

let get_field = (fun xopt f -> (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun uu____10567 -> (match (uu____10567) with
| (g, uu____10573) -> begin
(Prims.op_Equality f.FStar_Ident.idText g.FStar_Ident.ident.FStar_Ident.idText)
end))))
in (

let fn = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((f)::[])))
in (match (found) with
| FStar_Pervasives_Native.Some (uu____10579, e) -> begin
((fn), (e))
end
| FStar_Pervasives_Native.None -> begin
(match (xopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____10593 = (

let uu____10598 = (FStar_Util.format2 "Field %s of record type %s is missing" f.FStar_Ident.idText record.FStar_Syntax_DsEnv.typename.FStar_Ident.str)
in ((FStar_Errors.Fatal_MissingFieldInRecord), (uu____10598)))
in (FStar_Errors.raise_error uu____10593 top.FStar_Parser_AST.range))
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

let uu____10606 = (

let uu____10617 = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map (fun uu____10648 -> (match (uu____10648) with
| (f, uu____10658) -> begin
(

let uu____10659 = (

let uu____10660 = (get_field FStar_Pervasives_Native.None f)
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____10660))
in ((uu____10659), (FStar_Parser_AST.Nothing)))
end))))
in ((user_constrname), (uu____10617)))
in FStar_Parser_AST.Construct (uu____10606))
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (

let uu____10678 = (

let uu____10679 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____10679))
in (FStar_Parser_AST.mk_term uu____10678 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record1 = (

let uu____10681 = (

let uu____10694 = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map (fun uu____10724 -> (match (uu____10724) with
| (f, uu____10734) -> begin
(get_field (FStar_Pervasives_Native.Some (xterm)) f)
end))))
in ((FStar_Pervasives_Native.None), (uu____10694)))
in FStar_Parser_AST.Record (uu____10681))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), ((((FStar_Pervasives_Native.None), ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (FStar_Pervasives_Native.None)))) x.FStar_Ident.idRange)), (e)))))::[]), ((FStar_Parser_AST.mk_term record1 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm1 = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let uu____10794 = (desugar_term_aq env recterm1)
in (match (uu____10794) with
| (e, s) -> begin
(match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____10810; FStar_Syntax_Syntax.vars = uu____10811}, args) -> begin
(

let uu____10833 = (

let uu____10836 = (

let uu____10837 = (

let uu____10852 = (

let uu____10853 = (

let uu____10856 = (

let uu____10857 = (

let uu____10864 = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map FStar_Pervasives_Native.fst))
in ((record.FStar_Syntax_DsEnv.typename), (uu____10864)))
in FStar_Syntax_Syntax.Record_ctor (uu____10857))
in FStar_Pervasives_Native.Some (uu____10856))
in (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant uu____10853))
in ((uu____10852), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____10837))
in (FStar_All.pipe_left mk1 uu____10836))
in ((uu____10833), (s)))
end
| uu____10893 -> begin
((e), (s))
end)
end))))))))
end
| FStar_Parser_AST.Project (e, f) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f);
(

let uu____10897 = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f)
in (match (uu____10897) with
| (constrname, is_rec) -> begin
(

let uu____10912 = (desugar_term_aq env e)
in (match (uu____10912) with
| (e1, s) -> begin
(

let projname = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname f.FStar_Ident.ident)
in (

let qual = (match (is_rec) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (((constrname), (f.FStar_Ident.ident))))
end
| uu____10929 -> begin
FStar_Pervasives_Native.None
end)
in (

let uu____10930 = (

let uu____10933 = (

let uu____10934 = (

let uu____10949 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projname (FStar_Ident.range_of_lid f)) FStar_Syntax_Syntax.Delta_equational qual)
in (

let uu____10950 = (

let uu____10953 = (FStar_Syntax_Syntax.as_arg e1)
in (uu____10953)::[])
in ((uu____10949), (uu____10950))))
in FStar_Syntax_Syntax.Tm_app (uu____10934))
in (FStar_All.pipe_left mk1 uu____10933))
in ((uu____10930), (s)))))
end))
end));
)
end
| FStar_Parser_AST.NamedTyp (uu____10960, e) -> begin
(desugar_term_aq env e)
end
| FStar_Parser_AST.Paren (e) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.VQuote (e) -> begin
(

let tm = (desugar_term env e)
in (

let uu____10969 = (

let uu____10970 = (FStar_Syntax_Subst.compress tm)
in uu____10970.FStar_Syntax_Syntax.n)
in (match (uu____10969) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____10978 = (

let uu___130_10981 = (

let uu____10982 = (

let uu____10983 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____10983))
in (FStar_Syntax_Util.exp_string uu____10982))
in {FStar_Syntax_Syntax.n = uu___130_10981.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = e.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___130_10981.FStar_Syntax_Syntax.vars})
in ((uu____10978), (noaqs)))
end
| uu____10996 -> begin
(

let uu____10997 = (

let uu____11002 = (

let uu____11003 = (FStar_Syntax_Print.term_to_string tm)
in (Prims.strcat "VQuote, expected an fvar, got: " uu____11003))
in ((FStar_Errors.Fatal_UnexpectedTermVQuote), (uu____11002)))
in (FStar_Errors.raise_error uu____10997 top.FStar_Parser_AST.range))
end)))
end
| FStar_Parser_AST.Quote (e, FStar_Parser_AST.Static) -> begin
(

let uu____11009 = (desugar_term_aq env e)
in (match (uu____11009) with
| (tm, vts) -> begin
(

let qi = {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = vts}
in (

let uu____11021 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_quoted (((tm), (qi)))))
in ((uu____11021), (noaqs))))
end))
end
| FStar_Parser_AST.Antiquote (b, e) -> begin
(

let bv = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (

let uu____11041 = (FStar_Syntax_Syntax.bv_to_name bv)
in (

let uu____11042 = (

let uu____11051 = (

let uu____11058 = (desugar_term env e)
in ((bv), (b), (uu____11058)))
in (uu____11051)::[])
in ((uu____11041), (uu____11042)))))
end
| FStar_Parser_AST.Quote (e, FStar_Parser_AST.Dynamic) -> begin
(

let qi = {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = []}
in (

let uu____11089 = (

let uu____11092 = (

let uu____11093 = (

let uu____11100 = (desugar_term env e)
in ((uu____11100), (qi)))
in FStar_Syntax_Syntax.Tm_quoted (uu____11093))
in (FStar_All.pipe_left mk1 uu____11092))
in ((uu____11089), (noaqs))))
end
| uu____11115 when (Prims.op_Equality top.FStar_Parser_AST.level FStar_Parser_AST.Formula) -> begin
(

let uu____11116 = (desugar_formula env top)
in ((uu____11116), (noaqs)))
end
| uu____11127 -> begin
(

let uu____11128 = (

let uu____11133 = (

let uu____11134 = (FStar_Parser_AST.term_to_string top)
in (Prims.strcat "Unexpected term: " uu____11134))
in ((FStar_Errors.Fatal_UnexpectedTerm), (uu____11133)))
in (FStar_Errors.raise_error uu____11128 top.FStar_Parser_AST.range))
end)))))))
and not_ascribed : FStar_Parser_AST.term  ->  Prims.bool = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Ascribed (uu____11140) -> begin
false
end
| uu____11149 -> begin
true
end))
and is_synth_by_tactic : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun e t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (l, r, FStar_Parser_AST.Hash) -> begin
(is_synth_by_tactic e l)
end
| FStar_Parser_AST.Var (lid) -> begin
(

let uu____11155 = (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name e lid)
in (match (uu____11155) with
| FStar_Pervasives_Native.Some (lid1) -> begin
(FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid)
end
| FStar_Pervasives_Native.None -> begin
false
end))
end
| uu____11159 -> begin
false
end))
and desugar_args : FStar_Syntax_DsEnv.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____11196 -> (match (uu____11196) with
| (a, imp) -> begin
(

let uu____11209 = (desugar_term env a)
in (arg_withimp_e imp uu____11209))
end)))))
and desugar_comp : FStar_Range.range  ->  FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun r env t -> (

let fail1 = (fun a err -> (FStar_Errors.raise_error err r))
in (

let is_requires = (fun uu____11235 -> (match (uu____11235) with
| (t1, uu____11241) -> begin
(

let uu____11242 = (

let uu____11243 = (unparen t1)
in uu____11243.FStar_Parser_AST.tm)
in (match (uu____11242) with
| FStar_Parser_AST.Requires (uu____11244) -> begin
true
end
| uu____11251 -> begin
false
end))
end))
in (

let is_ensures = (fun uu____11259 -> (match (uu____11259) with
| (t1, uu____11265) -> begin
(

let uu____11266 = (

let uu____11267 = (unparen t1)
in uu____11267.FStar_Parser_AST.tm)
in (match (uu____11266) with
| FStar_Parser_AST.Ensures (uu____11268) -> begin
true
end
| uu____11275 -> begin
false
end))
end))
in (

let is_app = (fun head1 uu____11286 -> (match (uu____11286) with
| (t1, uu____11292) -> begin
(

let uu____11293 = (

let uu____11294 = (unparen t1)
in uu____11294.FStar_Parser_AST.tm)
in (match (uu____11293) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = uu____11296; FStar_Parser_AST.level = uu____11297}, uu____11298, uu____11299) -> begin
(Prims.op_Equality d.FStar_Ident.ident.FStar_Ident.idText head1)
end
| uu____11300 -> begin
false
end))
end))
in (

let is_smt_pat = (fun uu____11308 -> (match (uu____11308) with
| (t1, uu____11314) -> begin
(

let uu____11315 = (

let uu____11316 = (unparen t1)
in uu____11316.FStar_Parser_AST.tm)
in (match (uu____11315) with
| FStar_Parser_AST.Construct (cons1, (({FStar_Parser_AST.tm = FStar_Parser_AST.Construct (smtpat, uu____11319); FStar_Parser_AST.range = uu____11320; FStar_Parser_AST.level = uu____11321}, uu____11322))::(uu____11323)::[]) -> begin
((FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid) && (FStar_Util.for_some (fun s -> (Prims.op_Equality smtpat.FStar_Ident.str s)) (("SMTPat")::("SMTPatT")::("SMTPatOr")::[])))
end
| FStar_Parser_AST.Construct (cons1, (({FStar_Parser_AST.tm = FStar_Parser_AST.Var (smtpat); FStar_Parser_AST.range = uu____11362; FStar_Parser_AST.level = uu____11363}, uu____11364))::(uu____11365)::[]) -> begin
((FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid) && (FStar_Util.for_some (fun s -> (Prims.op_Equality smtpat.FStar_Ident.str s)) (("smt_pat")::("smt_pat_or")::[])))
end
| uu____11390 -> begin
false
end))
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t1 -> (

let uu____11418 = (head_and_args t1)
in (match (uu____11418) with
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

let thunk_ens = (fun uu____11512 -> (match (uu____11512) with
| (e, i) -> begin
(

let uu____11523 = (thunk_ens_ e)
in ((uu____11523), (i)))
end))
in (

let fail_lemma = (fun uu____11533 -> (

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

let uu____11613 = (

let uu____11620 = (

let uu____11627 = (thunk_ens ens)
in (uu____11627)::(nil_pat)::[])
in (req_true)::uu____11620)
in (unit_tm)::uu____11613)
end
| (req)::(ens)::[] when ((is_requires req) && (is_ensures ens)) -> begin
(

let uu____11674 = (

let uu____11681 = (

let uu____11688 = (thunk_ens ens)
in (uu____11688)::(nil_pat)::[])
in (req)::uu____11681)
in (unit_tm)::uu____11674)
end
| (ens)::(smtpat)::[] when ((((

let uu____11737 = (is_requires ens)
in (not (uu____11737))) && (

let uu____11739 = (is_smt_pat ens)
in (not (uu____11739)))) && (

let uu____11741 = (is_decreases ens)
in (not (uu____11741)))) && (is_smt_pat smtpat)) -> begin
(

let uu____11742 = (

let uu____11749 = (

let uu____11756 = (thunk_ens ens)
in (uu____11756)::(smtpat)::[])
in (req_true)::uu____11749)
in (unit_tm)::uu____11742)
end
| (ens)::(dec)::[] when ((is_ensures ens) && (is_decreases dec)) -> begin
(

let uu____11803 = (

let uu____11810 = (

let uu____11817 = (thunk_ens ens)
in (uu____11817)::(nil_pat)::(dec)::[])
in (req_true)::uu____11810)
in (unit_tm)::uu____11803)
end
| (ens)::(dec)::(smtpat)::[] when (((is_ensures ens) && (is_decreases dec)) && (is_smt_pat smtpat)) -> begin
(

let uu____11877 = (

let uu____11884 = (

let uu____11891 = (thunk_ens ens)
in (uu____11891)::(smtpat)::(dec)::[])
in (req_true)::uu____11884)
in (unit_tm)::uu____11877)
end
| (req)::(ens)::(dec)::[] when (((is_requires req) && (is_ensures ens)) && (is_decreases dec)) -> begin
(

let uu____11951 = (

let uu____11958 = (

let uu____11965 = (thunk_ens ens)
in (uu____11965)::(nil_pat)::(dec)::[])
in (req)::uu____11958)
in (unit_tm)::uu____11951)
end
| (req)::(ens)::(smtpat)::[] when (((is_requires req) && (is_ensures ens)) && (is_smt_pat smtpat)) -> begin
(

let uu____12025 = (

let uu____12032 = (

let uu____12039 = (thunk_ens ens)
in (uu____12039)::(smtpat)::[])
in (req)::uu____12032)
in (unit_tm)::uu____12025)
end
| (req)::(ens)::(dec)::(smtpat)::[] when ((((is_requires req) && (is_ensures ens)) && (is_smt_pat smtpat)) && (is_decreases dec)) -> begin
(

let uu____12104 = (

let uu____12111 = (

let uu____12118 = (thunk_ens ens)
in (uu____12118)::(dec)::(smtpat)::[])
in (req)::uu____12111)
in (unit_tm)::uu____12104)
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

let uu____12180 = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes env) l)
in ((uu____12180), (args)))
end
| FStar_Parser_AST.Name (l) when ((

let uu____12208 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Ident.lid_equals uu____12208 FStar_Parser_Const.prims_lid)) && (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Tot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Parser_Const.effect_Tot_lid head1.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when ((

let uu____12226 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Ident.lid_equals uu____12226 FStar_Parser_Const.prims_lid)) && (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "GTot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Parser_Const.effect_GTot_lid head1.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when (((Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Type") || (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Type0")) || (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Effect")) -> begin
(((((FStar_Ident.set_lid_range FStar_Parser_Const.effect_Tot_lid head1.FStar_Parser_AST.range)), ([]))), ((((t1), (FStar_Parser_AST.Nothing)))::[]))
end
| uu____12264 -> begin
(

let default_effect = (

let uu____12266 = (FStar_Options.ml_ish ())
in (match (uu____12266) with
| true -> begin
FStar_Parser_Const.effect_ML_lid
end
| uu____12267 -> begin
((

let uu____12269 = (FStar_Options.warn_default_effects ())
in (match (uu____12269) with
| true -> begin
(FStar_Errors.log_issue head1.FStar_Parser_AST.range ((FStar_Errors.Warning_UseDefaultEffect), ("Using default effect Tot")))
end
| uu____12270 -> begin
()
end));
FStar_Parser_Const.effect_Tot_lid;
)
end))
in (((((FStar_Ident.set_lid_range default_effect head1.FStar_Parser_AST.range)), ([]))), ((((t1), (FStar_Parser_AST.Nothing)))::[])))
end)
end)))
in (

let uu____12293 = (pre_process_comp_typ t)
in (match (uu____12293) with
| ((eff, cattributes), args) -> begin
((Obj.magic ((match ((Prims.op_Equality (FStar_List.length args) (Prims.parse_int "0"))) with
| true -> begin
(Obj.repr (

let uu____12342 = (

let uu____12347 = (

let uu____12348 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" uu____12348))
in ((FStar_Errors.Fatal_NotEnoughArgsToEffect), (uu____12347)))
in (fail1 () uu____12342)))
end
| uu____12349 -> begin
(Obj.repr ())
end)));
(

let is_universe = (fun uu____12357 -> (match (uu____12357) with
| (uu____12362, imp) -> begin
(Prims.op_Equality imp FStar_Parser_AST.UnivApp)
end))
in (

let uu____12364 = (FStar_Util.take is_universe args)
in (match (uu____12364) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun uu____12423 -> (match (uu____12423) with
| (u, imp) -> begin
(desugar_universe u)
end)) universes)
in (

let uu____12430 = (

let uu____12445 = (FStar_List.hd args1)
in (

let uu____12454 = (FStar_List.tl args1)
in ((uu____12445), (uu____12454))))
in (match (uu____12430) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (FStar_Pervasives_Native.fst result_arg))
in (

let rest1 = (desugar_args env rest)
in (

let uu____12509 = (

let is_decrease = (fun uu____12545 -> (match (uu____12545) with
| (t1, uu____12555) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____12565; FStar_Syntax_Syntax.vars = uu____12566}, (uu____12567)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.decreases_lid)
end
| uu____12598 -> begin
false
end)
end))
in (FStar_All.pipe_right rest1 (FStar_List.partition is_decrease)))
in (match (uu____12509) with
| (dec, rest2) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun uu____12712 -> (match (uu____12712) with
| (t1, uu____12722) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____12731, ((arg, uu____12733))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| uu____12762 -> begin
(failwith "impos")
end)
end))))
in (

let no_additional_args = (

let is_empty = (fun a l -> (match (l) with
| [] -> begin
true
end
| uu____12775 -> begin
false
end))
in ((((is_empty () (Obj.magic (decreases_clause))) && (is_empty () (Obj.magic (rest2)))) && (is_empty () (Obj.magic (cattributes)))) && (is_empty () (Obj.magic (universes1)))))
in (match ((no_additional_args && (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid))) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end
| uu____12780 -> begin
(match ((no_additional_args && (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid))) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end
| uu____12783 -> begin
(

let flags1 = (match ((FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Lemma_lid)) with
| true -> begin
(FStar_Syntax_Syntax.LEMMA)::[]
end
| uu____12789 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____12792 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Parser_Const.effect_ML_lid)) with
| true -> begin
(FStar_Syntax_Syntax.MLEFFECT)::[]
end
| uu____12795 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____12798 -> begin
[]
end)
end)
end)
end)
in (

let flags2 = (FStar_List.append flags1 cattributes)
in (

let rest3 = (match ((FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Lemma_lid)) with
| true -> begin
(match (rest2) with
| (req)::(ens)::((pat, aq))::[] -> begin
(

let pat1 = (match (pat.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid) -> begin
(

let nil = (FStar_Syntax_Syntax.mk_Tm_uinst pat ((FStar_Syntax_Syntax.U_zero)::[]))
in (

let pattern = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.pattern_lid pat.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.mk_Tm_app nil ((((pattern), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::[]) FStar_Pervasives_Native.None pat.FStar_Syntax_Syntax.pos)))
end
| uu____12915 -> begin
pat
end)
in (

let uu____12916 = (

let uu____12927 = (

let uu____12938 = (

let uu____12947 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat1), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) FStar_Pervasives_Native.None pat1.FStar_Syntax_Syntax.pos)
in ((uu____12947), (aq)))
in (uu____12938)::[])
in (ens)::uu____12927)
in (req)::uu____12916))
end
| uu____12988 -> begin
rest2
end)
end
| uu____12999 -> begin
rest2
end)
in (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = universes1; FStar_Syntax_Syntax.effect_name = eff; FStar_Syntax_Syntax.result_typ = result_typ; FStar_Syntax_Syntax.effect_args = rest3; FStar_Syntax_Syntax.flags = (FStar_List.append flags2 decreases_clause)}))))
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
| uu____13010 -> begin
FStar_Pervasives_Native.None
end))
in (

let mk1 = (fun t -> (FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let uu___131_13027 = t
in {FStar_Syntax_Syntax.n = uu___131_13027.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___131_13027.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let uu___132_13061 = b
in {FStar_Parser_AST.b = uu___132_13061.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___132_13061.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___132_13061.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env1 pats1 -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (

let uu____13120 = (desugar_term env1 e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) uu____13120)))))) pats1))
in (match (tk) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____13133 = (FStar_Syntax_DsEnv.push_bv env a)
in (match (uu____13133) with
| (env1, a1) -> begin
(

let a2 = (

let uu___133_13143 = a1
in {FStar_Syntax_Syntax.ppname = uu___133_13143.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___133_13143.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats1 = (desugar_pats env1 pats)
in (

let body1 = (desugar_formula env1 body)
in (

let body2 = (match (pats1) with
| [] -> begin
body1
end
| uu____13165 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_meta (((body1), (FStar_Syntax_Syntax.Meta_pattern (pats1))))))
end)
in (

let body3 = (

let uu____13179 = (

let uu____13182 = (

let uu____13183 = (FStar_Syntax_Syntax.mk_binder a2)
in (uu____13183)::[])
in (no_annot_abs uu____13182 body2))
in (FStar_All.pipe_left setpos uu____13179))
in (

let uu____13188 = (

let uu____13189 = (

let uu____13204 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let uu____13205 = (

let uu____13208 = (FStar_Syntax_Syntax.as_arg body3)
in (uu____13208)::[])
in ((uu____13204), (uu____13205))))
in FStar_Syntax_Syntax.Tm_app (uu____13189))
in (FStar_All.pipe_left mk1 uu____13188)))))))
end))
end
| uu____13213 -> begin
(failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body1 = (

let uu____13285 = (q ((rest), (pats), (body)))
in (

let uu____13292 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term uu____13285 uu____13292 FStar_Parser_AST.Formula)))
in (

let uu____13293 = (q (((b)::[]), ([]), (body1)))
in (FStar_Parser_AST.mk_term uu____13293 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| uu____13302 -> begin
(failwith "impossible")
end))
in (

let uu____13305 = (

let uu____13306 = (unparen f)
in uu____13306.FStar_Parser_AST.tm)
in (match (uu____13305) with
| FStar_Parser_AST.Labeled (f1, l, p) -> begin
(

let f2 = (desugar_formula env f1)
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((f2), (FStar_Syntax_Syntax.Meta_labeled (((l), (f2.FStar_Syntax_Syntax.pos), (p)))))))))
end
| FStar_Parser_AST.QForall ([], uu____13313, uu____13314) -> begin
(failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QExists ([], uu____13325, uu____13326) -> begin
(failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____13357 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env uu____13357)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____13393 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env uu____13393)))
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
| uu____13436 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list) = (fun env bs -> (

let uu____13441 = (FStar_List.fold_left (fun uu____13477 b -> (match (uu____13477) with
| (env1, out) -> begin
(

let tk = (desugar_binder env1 (

let uu___134_13529 = b
in {FStar_Parser_AST.b = uu___134_13529.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___134_13529.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___134_13529.FStar_Parser_AST.aqual}))
in (match (tk) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____13546 = (FStar_Syntax_DsEnv.push_bv env1 a)
in (match (uu____13546) with
| (env2, a1) -> begin
(

let a2 = (

let uu___135_13566 = a1
in {FStar_Syntax_Syntax.ppname = uu___135_13566.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___135_13566.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in ((env2), ((((a2), ((trans_aqual b.FStar_Parser_AST.aqual))))::out)))
end))
end
| uu____13583 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedBinder), ("Unexpected binder")) b.FStar_Parser_AST.brange)
end))
end)) ((env), ([])) bs)
in (match (uu____13441) with
| (env1, tpars) -> begin
((env1), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.TAnnotated (x, t) -> begin
(

let uu____13670 = (desugar_typ env t)
in ((FStar_Pervasives_Native.Some (x)), (uu____13670)))
end
| FStar_Parser_AST.Annotated (x, t) -> begin
(

let uu____13675 = (desugar_typ env t)
in ((FStar_Pervasives_Native.Some (x)), (uu____13675)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____13679 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) FStar_Pervasives_Native.None x.FStar_Ident.idRange)
in ((FStar_Pervasives_Native.Some (x)), (uu____13679)))
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____13687 = (desugar_typ env t)
in ((FStar_Pervasives_Native.None), (uu____13687)))
end
| FStar_Parser_AST.Variable (x) -> begin
((FStar_Pervasives_Native.Some (x)), (FStar_Syntax_Syntax.tun))
end))


let mk_data_discriminators : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_DsEnv.env  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun quals env datas -> (

let quals1 = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___97_13720 -> (match (uu___97_13720) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____13721 -> begin
false
end))))
in (

let quals2 = (fun q -> (

let uu____13732 = ((

let uu____13735 = (FStar_Syntax_DsEnv.iface env)
in (not (uu____13735))) || (FStar_Syntax_DsEnv.admitted_iface env))
in (match (uu____13732) with
| true -> begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals1)
end
| uu____13738 -> begin
(FStar_List.append q quals1)
end)))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (

let uu____13748 = (quals2 ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((disc_name), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid disc_name); FStar_Syntax_Syntax.sigquals = uu____13748; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))))))))


let mk_indexed_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  FStar_Syntax_DsEnv.env  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq env lid fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let uu____13779 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____13809 -> (match (uu____13809) with
| (x, uu____13817) -> begin
(

let uu____13818 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____13818) with
| (field_name, uu____13826) -> begin
(

let only_decl = (((

let uu____13830 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____13830)) || (Prims.op_disEquality fvq FStar_Syntax_Syntax.Data_ctor)) || (

let uu____13832 = (

let uu____13833 = (FStar_Syntax_DsEnv.current_module env)
in uu____13833.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____13832)))
in (

let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____13847 = (FStar_List.filter (fun uu___98_13851 -> (match (uu___98_13851) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____13852 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____13847)
end
| uu____13853 -> begin
q
end))
in (

let quals1 = (

let iquals1 = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___99_13865 -> (match (uu___99_13865) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____13866 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals1)))
in (

let decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid field_name); FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____13872 -> begin
(

let dd = (

let uu____13874 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____13874) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____13877 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lb = (

let uu____13879 = (

let uu____13884 = (FStar_Syntax_Syntax.lid_as_fv field_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____13884))
in {FStar_Syntax_Syntax.lbname = uu____13879; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbattrs = []; FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange})
in (

let impl = (

let uu____13888 = (

let uu____13889 = (

let uu____13896 = (

let uu____13899 = (

let uu____13900 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____13900 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____13899)::[])
in ((((false), ((lb)::[]))), (uu____13896)))
in FStar_Syntax_Syntax.Sig_let (uu____13889))
in {FStar_Syntax_Syntax.sigel = uu____13888; FStar_Syntax_Syntax.sigrng = p; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____13919 -> begin
(decl)::(impl)::[]
end))))
end))))))
end))
end))))
in (FStar_All.pipe_right uu____13779 FStar_List.flatten))))


let mk_data_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____13944, t, uu____13946, n1, uu____13948) when (not ((FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid))) -> begin
(

let uu____13953 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____13953) with
| (formals, uu____13969) -> begin
(match (formals) with
| [] -> begin
[]
end
| uu____13992 -> begin
(

let filter_records = (fun uu___100_14004 -> (match (uu___100_14004) with
| FStar_Syntax_Syntax.RecordConstructor (uu____14007, fns) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| uu____14019 -> begin
FStar_Pervasives_Native.None
end))
in (

let fv_qual = (

let uu____14021 = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals filter_records)
in (match (uu____14021) with
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
| uu____14030 -> begin
iquals
end)
in (

let uu____14031 = (FStar_Util.first_N n1 formals)
in (match (uu____14031) with
| (uu____14054, rest) -> begin
(mk_indexed_projector_names iquals1 fv_qual env lid rest)
end)))))
end)
end))
end
| uu____14080 -> begin
[]
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (

let dd = (

let uu____14130 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____14130) with
| true -> begin
(

let uu____14133 = (FStar_Syntax_Util.incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (uu____14133))
end
| uu____14134 -> begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end))
in (

let lb = (

let uu____14136 = (

let uu____14141 = (FStar_Syntax_Syntax.lid_as_fv lid dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____14141))
in (

let uu____14142 = (

let uu____14145 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars uu____14145))
in (

let uu____14148 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = uu____14136; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____14142; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____14148; FStar_Syntax_Syntax.lbattrs = []; FStar_Syntax_Syntax.lbpos = rng})))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (lids))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))


let rec desugar_tycon : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.decl  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d quals tcs -> (

let rng = d.FStar_Parser_AST.drange
in (

let tycon_id = (fun uu___101_14195 -> (match (uu___101_14195) with
| FStar_Parser_AST.TyconAbstract (id1, uu____14197, uu____14198) -> begin
id1
end
| FStar_Parser_AST.TyconAbbrev (id1, uu____14208, uu____14209, uu____14210) -> begin
id1
end
| FStar_Parser_AST.TyconRecord (id1, uu____14220, uu____14221, uu____14222) -> begin
id1
end
| FStar_Parser_AST.TyconVariant (id1, uu____14252, uu____14253, uu____14254) -> begin
id1
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (x, uu____14296) -> begin
(

let uu____14297 = (

let uu____14298 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____14298))
in (FStar_Parser_AST.mk_term uu____14297 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| FStar_Parser_AST.Variable (x) -> begin
(

let uu____14300 = (

let uu____14301 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____14301))
in (FStar_Parser_AST.mk_term uu____14300 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| FStar_Parser_AST.TAnnotated (a, uu____14303) -> begin
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
| uu____14326 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (

let uu____14332 = (

let uu____14333 = (

let uu____14340 = (binder_to_term b)
in ((out), (uu____14340), ((imp_of_aqual b))))
in FStar_Parser_AST.App (uu____14333))
in (FStar_Parser_AST.mk_term uu____14332 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun uu___102_14350 -> (match (uu___102_14350) with
| FStar_Parser_AST.TyconRecord (id1, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id1.FStar_Ident.idText)), (id1.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun uu____14405 -> (match (uu____14405) with
| (x, t, uu____14416) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Syntax_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr FStar_Pervasives_Native.None)
end)) fields)
in (

let result = (

let uu____14422 = (

let uu____14423 = (

let uu____14424 = (FStar_Ident.lid_of_ids ((id1)::[]))
in FStar_Parser_AST.Var (uu____14424))
in (FStar_Parser_AST.mk_term uu____14423 id1.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____14422 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id1.FStar_Ident.idRange FStar_Parser_AST.Type_level)
in (

let uu____14428 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____14455 -> (match (uu____14455) with
| (x, uu____14465, uu____14466) -> begin
(FStar_Syntax_Util.unmangle_field_name x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id1), (parms), (kopt), ((((constrName), (FStar_Pervasives_Native.Some (constrTyp)), (FStar_Pervasives_Native.None), (false)))::[])))), (uu____14428)))))))
end
| uu____14519 -> begin
(failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals1 _env mutuals uu___103_14550 -> (match (uu___103_14550) with
| FStar_Parser_AST.TyconAbstract (id1, binders, kopt) -> begin
(

let uu____14574 = (typars_of_binders _env binders)
in (match (uu____14574) with
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

let uu____14620 = (

let uu____14621 = (

let uu____14622 = (FStar_Ident.lid_of_ids ((id1)::[]))
in FStar_Parser_AST.Var (uu____14622))
in (FStar_Parser_AST.mk_term uu____14621 id1.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____14620 binders))
in (

let qlid = (FStar_Syntax_DsEnv.qualify _env id1)
in (

let typars1 = (FStar_Syntax_Subst.close_binders typars)
in (

let k1 = (FStar_Syntax_Subst.close typars1 k)
in (

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((qlid), ([]), (typars1), (k1), (mutuals), ([]))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (

let _env1 = (FStar_Syntax_DsEnv.push_top_level_rec_binding _env id1 FStar_Syntax_Syntax.Delta_constant)
in (

let _env2 = (FStar_Syntax_DsEnv.push_top_level_rec_binding _env' id1 FStar_Syntax_Syntax.Delta_constant)
in ((_env1), (_env2), (se), (tconstr))))))))))
end))
end
| uu____14635 -> begin
(failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env1 bs -> (

let uu____14679 = (FStar_List.fold_left (fun uu____14719 uu____14720 -> (match (((uu____14719), (uu____14720))) with
| ((env2, tps), (x, imp)) -> begin
(

let uu____14811 = (FStar_Syntax_DsEnv.push_bv env2 x.FStar_Syntax_Syntax.ppname)
in (match (uu____14811) with
| (env3, y) -> begin
((env3), ((((y), (imp)))::tps))
end))
end)) ((env1), ([])) bs)
in (match (uu____14679) with
| (env2, bs1) -> begin
((env2), ((FStar_List.rev bs1)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id1, bs, kopt))::[] -> begin
(

let kopt1 = (match (kopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____14924 = (tm_type_z id1.FStar_Ident.idRange)
in FStar_Pervasives_Native.Some (uu____14924))
end
| uu____14925 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id1), (bs), (kopt1)))
in (

let uu____14933 = (desugar_abstract_tc quals env [] tc)
in (match (uu____14933) with
| (uu____14946, uu____14947, se, uu____14949) -> begin
(

let se1 = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, uu____14952, typars, k, [], []) -> begin
(

let quals1 = se.FStar_Syntax_Syntax.sigquals
in (

let quals2 = (match ((FStar_List.contains FStar_Syntax_Syntax.Assumption quals1)) with
| true -> begin
quals1
end
| uu____14967 -> begin
((

let uu____14969 = (

let uu____14970 = (FStar_Options.ml_ish ())
in (not (uu____14970)))
in (match (uu____14969) with
| true -> begin
(

let uu____14971 = (

let uu____14976 = (

let uu____14977 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Adding an implicit \'assume new\' qualifier on %s" uu____14977))
in ((FStar_Errors.Warning_AddImplicitAssumeNewQualifier), (uu____14976)))
in (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng uu____14971))
end
| uu____14978 -> begin
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
| uu____14984 -> begin
(

let uu____14985 = (

let uu____14988 = (

let uu____14989 = (

let uu____15002 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (uu____15002)))
in FStar_Syntax_Syntax.Tm_arrow (uu____14989))
in (FStar_Syntax_Syntax.mk uu____14988))
in (uu____14985 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
end)
in (

let uu___136_15006 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t))); FStar_Syntax_Syntax.sigrng = uu___136_15006.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = uu___136_15006.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___136_15006.FStar_Syntax_Syntax.sigattrs}))))
end
| uu____15009 -> begin
(failwith "Impossible")
end)
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se1)
in (

let env2 = (

let uu____15012 = (FStar_Syntax_DsEnv.qualify env1 id1)
in (FStar_Syntax_DsEnv.push_doc env1 uu____15012 d.FStar_Parser_AST.doc))
in ((env2), ((se1)::[])))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id1, binders, kopt, t))::[] -> begin
(

let uu____15027 = (typars_of_binders env binders)
in (match (uu____15027) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____15063 = (FStar_Util.for_some (fun uu___104_15065 -> (match (uu___104_15065) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| uu____15066 -> begin
false
end)) quals)
in (match (uu____15063) with
| true -> begin
FStar_Syntax_Syntax.teff
end
| uu____15067 -> begin
FStar_Syntax_Util.ktype
end))
end
| FStar_Pervasives_Native.Some (k) -> begin
(desugar_term env' k)
end)
in (

let t0 = t
in (

let quals1 = (

let uu____15073 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___105_15077 -> (match (uu___105_15077) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| uu____15078 -> begin
false
end))))
in (match (uu____15073) with
| true -> begin
quals
end
| uu____15081 -> begin
(match ((Prims.op_Equality t0.FStar_Parser_AST.level FStar_Parser_AST.Formula)) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals
end
| uu____15084 -> begin
quals
end)
end))
in (

let qlid = (FStar_Syntax_DsEnv.qualify env id1)
in (

let se = (

let uu____15087 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Effect))
in (match (uu____15087) with
| true -> begin
(

let uu____15090 = (

let uu____15097 = (

let uu____15098 = (unparen t)
in uu____15098.FStar_Parser_AST.tm)
in (match (uu____15097) with
| FStar_Parser_AST.Construct (head1, args) -> begin
(

let uu____15119 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____15149))::args_rev -> begin
(

let uu____15161 = (

let uu____15162 = (unparen last_arg)
in uu____15162.FStar_Parser_AST.tm)
in (match (uu____15161) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____15190 -> begin
(([]), (args))
end))
end
| uu____15199 -> begin
(([]), (args))
end)
in (match (uu____15119) with
| (cattributes, args1) -> begin
(

let uu____15238 = (desugar_attributes env cattributes)
in (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((head1), (args1)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (uu____15238)))
end))
end
| uu____15249 -> begin
((t), ([]))
end))
in (match (uu____15090) with
| (t1, cattributes) -> begin
(

let c = (desugar_comp t1.FStar_Parser_AST.range env' t1)
in (

let typars1 = (FStar_Syntax_Subst.close_binders typars)
in (

let c1 = (FStar_Syntax_Subst.close_comp typars1 c)
in (

let quals2 = (FStar_All.pipe_right quals1 (FStar_List.filter (fun uu___106_15271 -> (match (uu___106_15271) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| uu____15272 -> begin
true
end))))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((qlid), ([]), (typars1), (c1), ((FStar_List.append cattributes (FStar_Syntax_Util.comp_flags c1))))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))))
end))
end
| uu____15277 -> begin
(

let t1 = (desugar_typ env' t)
in (mk_typ_abbrev qlid [] typars k t1 ((qlid)::[]) quals1 rng))
end))
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se)
in (

let env2 = (FStar_Syntax_DsEnv.push_doc env1 qlid d.FStar_Parser_AST.doc)
in ((env2), ((se)::[])))))))))
end))
end
| (FStar_Parser_AST.TyconRecord (uu____15283))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let uu____15307 = (tycon_record_as_variant trec)
in (match (uu____15307) with
| (t, fs) -> begin
(

let uu____15324 = (

let uu____15327 = (

let uu____15328 = (

let uu____15337 = (

let uu____15340 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Ident.ids_of_lid uu____15340))
in ((uu____15337), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____15328))
in (uu____15327)::quals)
in (desugar_tycon env d uu____15324 ((t)::[])))
end)))
end
| (uu____15345)::uu____15346 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals1 et tc -> (

let uu____15507 = et
in (match (uu____15507) with
| (env1, tcs1) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (uu____15732) -> begin
(

let trec = tc
in (

let uu____15756 = (tycon_record_as_variant trec)
in (match (uu____15756) with
| (t, fs) -> begin
(

let uu____15815 = (

let uu____15818 = (

let uu____15819 = (

let uu____15828 = (

let uu____15831 = (FStar_Syntax_DsEnv.current_module env1)
in (FStar_Ident.ids_of_lid uu____15831))
in ((uu____15828), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____15819))
in (uu____15818)::quals1)
in (collect_tcs uu____15815 ((env1), (tcs1)) t))
end)))
end
| FStar_Parser_AST.TyconVariant (id1, binders, kopt, constructors) -> begin
(

let uu____15918 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id1), (binders), (kopt)))))
in (match (uu____15918) with
| (env2, uu____15978, se, tconstr) -> begin
((env2), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals1))))::tcs1))
end))
end
| FStar_Parser_AST.TyconAbbrev (id1, binders, kopt, t) -> begin
(

let uu____16127 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id1), (binders), (kopt)))))
in (match (uu____16127) with
| (env2, uu____16187, se, tconstr) -> begin
((env2), ((FStar_Util.Inr (((se), (binders), (t), (quals1))))::tcs1))
end))
end
| uu____16312 -> begin
(failwith "Unrecognized mutual type definition")
end)
end)))
in (

let uu____16359 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (uu____16359) with
| (env1, tcs1) -> begin
(

let tcs2 = (FStar_List.rev tcs1)
in (

let docs_tps_sigelts = (FStar_All.pipe_right tcs2 (FStar_List.collect (fun uu___108_16870 -> (match (uu___108_16870) with
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (id1, uvs, tpars, k, uu____16937, uu____16938); FStar_Syntax_Syntax.sigrng = uu____16939; FStar_Syntax_Syntax.sigquals = uu____16940; FStar_Syntax_Syntax.sigmeta = uu____16941; FStar_Syntax_Syntax.sigattrs = uu____16942}, binders, t, quals1) -> begin
(

let t1 = (

let uu____17003 = (typars_of_binders env1 binders)
in (match (uu____17003) with
| (env2, tpars1) -> begin
(

let uu____17034 = (push_tparams env2 tpars1)
in (match (uu____17034) with
| (env_tps, tpars2) -> begin
(

let t1 = (desugar_typ env_tps t)
in (

let tpars3 = (FStar_Syntax_Subst.close_binders tpars2)
in (FStar_Syntax_Subst.close tpars3 t1)))
end))
end))
in (

let uu____17067 = (

let uu____17088 = (mk_typ_abbrev id1 uvs tpars k t1 ((id1)::[]) quals1 rng)
in ((((id1), (d.FStar_Parser_AST.doc))), ([]), (uu____17088)))
in (uu____17067)::[]))
end
| FStar_Util.Inl ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs1, tpars, k, mutuals1, uu____17156); FStar_Syntax_Syntax.sigrng = uu____17157; FStar_Syntax_Syntax.sigquals = tname_quals; FStar_Syntax_Syntax.sigmeta = uu____17159; FStar_Syntax_Syntax.sigattrs = uu____17160}, constrs, tconstr, quals1) -> begin
(

let mk_tot = (fun t -> (

let tot1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((tot1), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)))
in (

let tycon = ((tname), (tpars), (k))
in (

let uu____17256 = (push_tparams env1 tpars)
in (match (uu____17256) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun uu____17333 -> (match (uu____17333) with
| (x, uu____17347) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let tot_tconstr = (mk_tot tconstr)
in (

let uu____17355 = (

let uu____17384 = (FStar_All.pipe_right constrs (FStar_List.map (fun uu____17498 -> (match (uu____17498) with
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
| uu____17551 -> begin
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

let uu____17554 = (close env_tps t)
in (desugar_term env_tps uu____17554))
in (

let name = (FStar_Syntax_DsEnv.qualify env1 id1)
in (

let quals2 = (FStar_All.pipe_right tname_quals (FStar_List.collect (fun uu___107_17565 -> (match (uu___107_17565) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| uu____17577 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (

let uu____17585 = (

let uu____17606 = (

let uu____17607 = (

let uu____17608 = (

let uu____17623 = (

let uu____17626 = (

let uu____17629 = (FStar_All.pipe_right t1 FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total uu____17629))
in (FStar_Syntax_Util.arrow data_tpars uu____17626))
in ((name), (univs1), (uu____17623), (tname), (ntps), (mutuals1)))
in FStar_Syntax_Syntax.Sig_datacon (uu____17608))
in {FStar_Syntax_Syntax.sigel = uu____17607; FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in ((((name), (doc1))), (tps), (uu____17606)))
in ((name), (uu____17585))))))))
end))))
in (FStar_All.pipe_left FStar_List.split uu____17384))
in (match (uu____17355) with
| (constrNames, constrs1) -> begin
(((((tname), (d.FStar_Parser_AST.doc))), ([]), ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs1), (tpars), (k), (mutuals1), (constrNames))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = tname_quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))::constrs1
end))))
end))))
end
| uu____17868 -> begin
(failwith "impossible")
end))))
in (

let name_docs = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.map (fun uu____18000 -> (match (uu____18000) with
| (name_doc, uu____18028, uu____18029) -> begin
name_doc
end))))
in (

let sigelts = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.map (fun uu____18109 -> (match (uu____18109) with
| (uu____18130, uu____18131, se) -> begin
se
end))))
in (

let uu____18161 = (

let uu____18168 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle sigelts quals uu____18168 rng))
in (match (uu____18161) with
| (bundle, abbrevs) -> begin
(

let env2 = (FStar_Syntax_DsEnv.push_sigelt env0 bundle)
in (

let env3 = (FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env2 abbrevs)
in (

let data_ops = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.collect (fun uu____18234 -> (match (uu____18234) with
| (uu____18257, tps, se) -> begin
(mk_data_projector_names quals env3 se)
end))))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, uu____18308, tps, k, uu____18311, constrs) when ((FStar_List.length constrs) > (Prims.parse_int "1")) -> begin
(

let quals1 = se.FStar_Syntax_Syntax.sigquals
in (

let quals2 = (match ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals1)) with
| true -> begin
(FStar_Syntax_Syntax.Private)::quals1
end
| uu____18329 -> begin
quals1
end)
in (mk_data_discriminators quals2 env3 constrs)))
end
| uu____18330 -> begin
[]
end))))
in (

let ops = (FStar_List.append discs data_ops)
in (

let env4 = (FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env3 ops)
in (

let env5 = (FStar_List.fold_left (fun acc uu____18347 -> (match (uu____18347) with
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

let uu____18382 = (FStar_List.fold_left (fun uu____18405 b -> (match (uu____18405) with
| (env1, binders1) -> begin
(

let uu____18425 = (desugar_binder env1 b)
in (match (uu____18425) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____18442 = (as_binder env1 b.FStar_Parser_AST.aqual ((FStar_Pervasives_Native.Some (a)), (k)))
in (match (uu____18442) with
| (binder, env2) -> begin
((env2), ((binder)::binders1))
end))
end
| uu____18459 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_MissingNameInBinder), ("Missing name in binder")) b.FStar_Parser_AST.brange)
end))
end)) ((env), ([])) binders)
in (match (uu____18382) with
| (env1, binders1) -> begin
((env1), ((FStar_List.rev binders1)))
end)))


let push_reflect_effect : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lid  ->  FStar_Range.range  ->  FStar_Syntax_DsEnv.env = (fun env quals effect_name range -> (

let uu____18504 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___109_18509 -> (match (uu___109_18509) with
| FStar_Syntax_Syntax.Reflectable (uu____18510) -> begin
true
end
| uu____18511 -> begin
false
end))))
in (match (uu____18504) with
| true -> begin
(

let monad_env = (FStar_Syntax_DsEnv.enter_monad_scope env effect_name.FStar_Ident.ident)
in (

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_Syntax_DsEnv.qualify monad_env))
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (effect_name))::[]
in (

let refl_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = range; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (FStar_Syntax_DsEnv.push_sigelt env refl_decl)))))
end
| uu____18520 -> begin
env
end)))


let rec desugar_effect : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.term Prims.list  ->  (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_typ eff_decls attrs -> (

let env0 = env
in (

let monad_env = (FStar_Syntax_DsEnv.enter_monad_scope env eff_name)
in (

let uu____18617 = (desugar_binders monad_env eff_binders)
in (match (uu____18617) with
| (env1, binders) -> begin
(

let eff_t = (desugar_term env1 eff_typ)
in (

let for_free = (

let uu____18638 = (

let uu____18639 = (

let uu____18646 = (FStar_Syntax_Util.arrow_formals eff_t)
in (FStar_Pervasives_Native.fst uu____18646))
in (FStar_List.length uu____18639))
in (Prims.op_Equality uu____18638 (Prims.parse_int "1")))
in (

let mandatory_members = (

let rr_members = ("repr")::("return")::("bind")::[]
in (match (for_free) with
| true -> begin
rr_members
end
| uu____18683 -> begin
(FStar_List.append rr_members (("return_wp")::("bind_wp")::("if_then_else")::("ite_wp")::("stronger")::("close_wp")::("assert_p")::("assume_p")::("null_wp")::("trivial")::[]))
end))
in (

let name_of_eff_decl = (fun decl -> (match (decl.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____18688, ((FStar_Parser_AST.TyconAbbrev (name, uu____18690, uu____18691, uu____18692), uu____18693))::[]) -> begin
(FStar_Ident.text_of_id name)
end
| uu____18726 -> begin
(failwith "Malformed effect member declaration.")
end))
in (

let uu____18727 = (FStar_List.partition (fun decl -> (

let uu____18739 = (name_of_eff_decl decl)
in (FStar_List.mem uu____18739 mandatory_members))) eff_decls)
in (match (uu____18727) with
| (mandatory_members_decls, actions) -> begin
(

let uu____18756 = (FStar_All.pipe_right mandatory_members_decls (FStar_List.fold_left (fun uu____18785 decl -> (match (uu____18785) with
| (env2, out) -> begin
(

let uu____18805 = (desugar_decl env2 decl)
in (match (uu____18805) with
| (env3, ses) -> begin
(

let uu____18818 = (

let uu____18821 = (FStar_List.hd ses)
in (uu____18821)::out)
in ((env3), (uu____18818)))
end))
end)) ((env1), ([]))))
in (match (uu____18756) with
| (env2, decls) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (

let actions_docs = (FStar_All.pipe_right actions (FStar_List.map (fun d1 -> (match (d1.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____18889, ((FStar_Parser_AST.TyconAbbrev (name, action_params, uu____18892, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (uu____18893, ((def, uu____18895))::((cps_type, uu____18897))::[]); FStar_Parser_AST.range = uu____18898; FStar_Parser_AST.level = uu____18899}), doc1))::[]) when (not (for_free)) -> begin
(

let uu____18951 = (desugar_binders env2 action_params)
in (match (uu____18951) with
| (env3, action_params1) -> begin
(

let action_params2 = (FStar_Syntax_Subst.close_binders action_params1)
in (

let uu____18971 = (

let uu____18972 = (FStar_Syntax_DsEnv.qualify env3 name)
in (

let uu____18973 = (

let uu____18974 = (desugar_term env3 def)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____18974))
in (

let uu____18979 = (

let uu____18980 = (desugar_typ env3 cps_type)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____18980))
in {FStar_Syntax_Syntax.action_name = uu____18972; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = action_params2; FStar_Syntax_Syntax.action_defn = uu____18973; FStar_Syntax_Syntax.action_typ = uu____18979})))
in ((uu____18971), (doc1))))
end))
end
| FStar_Parser_AST.Tycon (uu____18987, ((FStar_Parser_AST.TyconAbbrev (name, action_params, uu____18990, defn), doc1))::[]) when for_free -> begin
(

let uu____19025 = (desugar_binders env2 action_params)
in (match (uu____19025) with
| (env3, action_params1) -> begin
(

let action_params2 = (FStar_Syntax_Subst.close_binders action_params1)
in (

let uu____19045 = (

let uu____19046 = (FStar_Syntax_DsEnv.qualify env3 name)
in (

let uu____19047 = (

let uu____19048 = (desugar_term env3 defn)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____19048))
in {FStar_Syntax_Syntax.action_name = uu____19046; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = action_params2; FStar_Syntax_Syntax.action_defn = uu____19047; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
in ((uu____19045), (doc1))))
end))
end
| uu____19055 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_MalformedActionDeclaration), ("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).")) d1.FStar_Parser_AST.drange)
end))))
in (

let actions1 = (FStar_List.map FStar_Pervasives_Native.fst actions_docs)
in (

let eff_t1 = (FStar_Syntax_Subst.close binders1 eff_t)
in (

let lookup1 = (fun s -> (

let l = (FStar_Syntax_DsEnv.qualify env2 (FStar_Ident.mk_ident ((s), (d.FStar_Parser_AST.drange))))
in (

let uu____19085 = (

let uu____19086 = (FStar_Syntax_DsEnv.fail_or env2 (FStar_Syntax_DsEnv.try_lookup_definition env2) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders1) uu____19086))
in (([]), (uu____19085)))))
in (

let mname = (FStar_Syntax_DsEnv.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange (FStar_Pervasives_Native.Some (mname))) quals)
in (

let se = (match (for_free) with
| true -> begin
(

let dummy_tscheme = (

let uu____19103 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (([]), (uu____19103)))
in (

let uu____19110 = (

let uu____19111 = (

let uu____19112 = (

let uu____19113 = (lookup1 "repr")
in (FStar_Pervasives_Native.snd uu____19113))
in (

let uu____19122 = (lookup1 "return")
in (

let uu____19123 = (lookup1 "bind")
in (

let uu____19124 = (FStar_List.map (desugar_term env2) attrs)
in {FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = eff_t1; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = uu____19112; FStar_Syntax_Syntax.return_repr = uu____19122; FStar_Syntax_Syntax.bind_repr = uu____19123; FStar_Syntax_Syntax.actions = actions1; FStar_Syntax_Syntax.eff_attrs = uu____19124}))))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____19111))
in {FStar_Syntax_Syntax.sigel = uu____19110; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qualifiers; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))
end
| uu____19127 -> begin
(

let rr = (FStar_Util.for_some (fun uu___110_19130 -> (match (uu___110_19130) with
| FStar_Syntax_Syntax.Reifiable -> begin
true
end
| FStar_Syntax_Syntax.Reflectable (uu____19131) -> begin
true
end
| uu____19132 -> begin
false
end)) qualifiers)
in (

let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in (

let uu____19142 = (

let uu____19143 = (

let uu____19144 = (lookup1 "return_wp")
in (

let uu____19145 = (lookup1 "bind_wp")
in (

let uu____19146 = (lookup1 "if_then_else")
in (

let uu____19147 = (lookup1 "ite_wp")
in (

let uu____19148 = (lookup1 "stronger")
in (

let uu____19149 = (lookup1 "close_wp")
in (

let uu____19150 = (lookup1 "assert_p")
in (

let uu____19151 = (lookup1 "assume_p")
in (

let uu____19152 = (lookup1 "null_wp")
in (

let uu____19153 = (lookup1 "trivial")
in (

let uu____19154 = (match (rr) with
| true -> begin
(

let uu____19155 = (lookup1 "repr")
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____19155))
end
| uu____19170 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let uu____19171 = (match (rr) with
| true -> begin
(lookup1 "return")
end
| uu____19172 -> begin
un_ts
end)
in (

let uu____19173 = (match (rr) with
| true -> begin
(lookup1 "bind")
end
| uu____19174 -> begin
un_ts
end)
in (

let uu____19175 = (FStar_List.map (desugar_term env2) attrs)
in {FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = eff_t1; FStar_Syntax_Syntax.ret_wp = uu____19144; FStar_Syntax_Syntax.bind_wp = uu____19145; FStar_Syntax_Syntax.if_then_else = uu____19146; FStar_Syntax_Syntax.ite_wp = uu____19147; FStar_Syntax_Syntax.stronger = uu____19148; FStar_Syntax_Syntax.close_wp = uu____19149; FStar_Syntax_Syntax.assert_p = uu____19150; FStar_Syntax_Syntax.assume_p = uu____19151; FStar_Syntax_Syntax.null_wp = uu____19152; FStar_Syntax_Syntax.trivial = uu____19153; FStar_Syntax_Syntax.repr = uu____19154; FStar_Syntax_Syntax.return_repr = uu____19171; FStar_Syntax_Syntax.bind_repr = uu____19173; FStar_Syntax_Syntax.actions = actions1; FStar_Syntax_Syntax.eff_attrs = uu____19175}))))))))))))))
in FStar_Syntax_Syntax.Sig_new_effect (uu____19143))
in {FStar_Syntax_Syntax.sigel = uu____19142; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qualifiers; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))
end)
in (

let env3 = (FStar_Syntax_DsEnv.push_sigelt env0 se)
in (

let env4 = (FStar_Syntax_DsEnv.push_doc env3 mname d.FStar_Parser_AST.doc)
in (

let env5 = (FStar_All.pipe_right actions_docs (FStar_List.fold_left (fun env5 uu____19201 -> (match (uu____19201) with
| (a, doc1) -> begin
(

let env6 = (

let uu____19215 = (FStar_Syntax_Util.action_as_lb mname a a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_DsEnv.push_sigelt env5 uu____19215))
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
and desugar_redefine_effect : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.decl  ->  (FStar_Ident.lident FStar_Pervasives_Native.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier)  ->  FStar_Parser_AST.qualifier Prims.list  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d trans_qual1 quals eff_name eff_binders defn -> (

let env0 = env
in (

let env1 = (FStar_Syntax_DsEnv.enter_monad_scope env eff_name)
in (

let uu____19239 = (desugar_binders env1 eff_binders)
in (match (uu____19239) with
| (env2, binders) -> begin
(

let uu____19258 = (

let uu____19277 = (head_and_args defn)
in (match (uu____19277) with
| (head1, args) -> begin
(

let lid = (match (head1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
l
end
| uu____19322 -> begin
(

let uu____19323 = (

let uu____19328 = (

let uu____19329 = (

let uu____19330 = (FStar_Parser_AST.term_to_string head1)
in (Prims.strcat uu____19330 " not found"))
in (Prims.strcat "Effect " uu____19329))
in ((FStar_Errors.Fatal_EffectNotFound), (uu____19328)))
in (FStar_Errors.raise_error uu____19323 d.FStar_Parser_AST.drange))
end)
in (

let ed = (FStar_Syntax_DsEnv.fail_or env2 (FStar_Syntax_DsEnv.try_lookup_effect_defn env2) lid)
in (

let uu____19332 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____19362))::args_rev -> begin
(

let uu____19374 = (

let uu____19375 = (unparen last_arg)
in uu____19375.FStar_Parser_AST.tm)
in (match (uu____19374) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____19403 -> begin
(([]), (args))
end))
end
| uu____19412 -> begin
(([]), (args))
end)
in (match (uu____19332) with
| (cattributes, args1) -> begin
(

let uu____19463 = (desugar_args env2 args1)
in (

let uu____19472 = (desugar_attributes env2 cattributes)
in ((lid), (ed), (uu____19463), (uu____19472))))
end))))
end))
in (match (uu____19258) with
| (ed_lid, ed, args, cattributes) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in ((match ((Prims.op_disEquality (FStar_List.length args) (FStar_List.length ed.FStar_Syntax_Syntax.binders))) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ArgumentLengthMismatch), ("Unexpected number of arguments to effect constructor")) defn.FStar_Parser_AST.range)
end
| uu____19527 -> begin
()
end);
(

let uu____19528 = (FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit)
in (match (uu____19528) with
| (ed_binders, uu____19542, ed_binders_opening) -> begin
(

let sub1 = (fun uu____19553 -> (match (uu____19553) with
| (us, x) -> begin
(

let x1 = (

let uu____19567 = (FStar_Syntax_Subst.shift_subst (FStar_List.length us) ed_binders_opening)
in (FStar_Syntax_Subst.subst uu____19567 x))
in (

let s = (FStar_Syntax_Util.subst_of_list ed_binders args)
in (

let uu____19571 = (

let uu____19572 = (FStar_Syntax_Subst.subst s x1)
in ((us), (uu____19572)))
in (FStar_Syntax_Subst.close_tscheme binders1 uu____19571))))
end))
in (

let mname = (FStar_Syntax_DsEnv.qualify env0 eff_name)
in (

let ed1 = (

let uu____19577 = (

let uu____19578 = (sub1 (([]), (ed.FStar_Syntax_Syntax.signature)))
in (FStar_Pervasives_Native.snd uu____19578))
in (

let uu____19589 = (sub1 ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____19590 = (sub1 ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____19591 = (sub1 ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____19592 = (sub1 ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____19593 = (sub1 ed.FStar_Syntax_Syntax.stronger)
in (

let uu____19594 = (sub1 ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____19595 = (sub1 ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____19596 = (sub1 ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____19597 = (sub1 ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____19598 = (sub1 ed.FStar_Syntax_Syntax.trivial)
in (

let uu____19599 = (

let uu____19600 = (sub1 (([]), (ed.FStar_Syntax_Syntax.repr)))
in (FStar_Pervasives_Native.snd uu____19600))
in (

let uu____19611 = (sub1 ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____19612 = (sub1 ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____19613 = (FStar_List.map (fun action -> (

let uu____19621 = (FStar_Syntax_DsEnv.qualify env2 action.FStar_Syntax_Syntax.action_unqualified_name)
in (

let uu____19622 = (

let uu____19623 = (sub1 (([]), (action.FStar_Syntax_Syntax.action_defn)))
in (FStar_Pervasives_Native.snd uu____19623))
in (

let uu____19634 = (

let uu____19635 = (sub1 (([]), (action.FStar_Syntax_Syntax.action_typ)))
in (FStar_Pervasives_Native.snd uu____19635))
in {FStar_Syntax_Syntax.action_name = uu____19621; FStar_Syntax_Syntax.action_unqualified_name = action.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = action.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = uu____19622; FStar_Syntax_Syntax.action_typ = uu____19634})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = cattributes; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = ed.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = uu____19577; FStar_Syntax_Syntax.ret_wp = uu____19589; FStar_Syntax_Syntax.bind_wp = uu____19590; FStar_Syntax_Syntax.if_then_else = uu____19591; FStar_Syntax_Syntax.ite_wp = uu____19592; FStar_Syntax_Syntax.stronger = uu____19593; FStar_Syntax_Syntax.close_wp = uu____19594; FStar_Syntax_Syntax.assert_p = uu____19595; FStar_Syntax_Syntax.assume_p = uu____19596; FStar_Syntax_Syntax.null_wp = uu____19597; FStar_Syntax_Syntax.trivial = uu____19598; FStar_Syntax_Syntax.repr = uu____19599; FStar_Syntax_Syntax.return_repr = uu____19611; FStar_Syntax_Syntax.bind_repr = uu____19612; FStar_Syntax_Syntax.actions = uu____19613; FStar_Syntax_Syntax.eff_attrs = ed.FStar_Syntax_Syntax.eff_attrs})))))))))))))))
in (

let se = (

let for_free = (

let uu____19648 = (

let uu____19649 = (

let uu____19656 = (FStar_Syntax_Util.arrow_formals ed1.FStar_Syntax_Syntax.signature)
in (FStar_Pervasives_Native.fst uu____19656))
in (FStar_List.length uu____19649))
in (Prims.op_Equality uu____19648 (Prims.parse_int "1")))
in (

let uu____19685 = (

let uu____19688 = (trans_qual1 (FStar_Pervasives_Native.Some (mname)))
in (FStar_List.map uu____19688 quals))
in {FStar_Syntax_Syntax.sigel = (match (for_free) with
| true -> begin
FStar_Syntax_Syntax.Sig_new_effect_for_free (ed1)
end
| uu____19691 -> begin
FStar_Syntax_Syntax.Sig_new_effect (ed1)
end); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = uu____19685; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))
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

let uu____19708 = (FStar_Syntax_Util.action_as_lb mname a a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_DsEnv.push_sigelt env5 uu____19708))
in (FStar_Syntax_DsEnv.push_doc env6 a.FStar_Syntax_Syntax.action_name doc1)))) env4))
in (

let env6 = (

let uu____19710 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____19710) with
| true -> begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_Syntax_DsEnv.qualify monad_env))
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]
in (

let refl_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (FStar_Syntax_DsEnv.push_sigelt env5 refl_decl))))
end
| uu____19720 -> begin
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

let uu____19725 = (match (d.FStar_Parser_AST.doc) with
| FStar_Pervasives_Native.None -> begin
((""), ([]))
end
| FStar_Pervasives_Native.Some (fsdoc) -> begin
fsdoc
end)
in (match (uu____19725) with
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
| FStar_Pervasives_Native.Some (uu____19776) -> begin
(

let uu____19777 = (

let uu____19778 = (FStar_Parser_ToDocument.signature_to_document d)
in (FStar_Pprint.pretty_string 0.950000 (Prims.parse_int "80") uu____19778))
in (Prims.strcat "\n  " uu____19777))
end
| uu____19779 -> begin
""
end)
in (

let other = (FStar_List.filter_map (fun uu____19792 -> (match (uu____19792) with
| (k, v1) -> begin
(match (((Prims.op_disEquality k "summary") && (Prims.op_disEquality k "type"))) with
| true -> begin
FStar_Pervasives_Native.Some ((Prims.strcat k (Prims.strcat ": " v1)))
end
| uu____19803 -> begin
FStar_Pervasives_Native.None
end)
end)) kv)
in (

let other1 = (match ((Prims.op_disEquality other [])) with
| true -> begin
(Prims.strcat (FStar_String.concat "\n" other) "\n")
end
| uu____19807 -> begin
""
end)
in (

let str = (Prims.strcat summary (Prims.strcat pp (Prims.strcat other1 text)))
in (

let fv = (

let uu____19810 = (FStar_Ident.lid_of_str "FStar.Pervasives.Comment")
in (FStar_Syntax_Syntax.fvar uu____19810 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in (

let arg = (FStar_Syntax_Util.exp_string str)
in (

let uu____19812 = (

let uu____19821 = (FStar_Syntax_Syntax.as_arg arg)
in (uu____19821)::[])
in (FStar_Syntax_Util.mk_app fv uu____19812)))))))))
end)))
and desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (

let uu____19828 = (desugar_decl_noattrs env d)
in (match (uu____19828) with
| (env1, sigelts) -> begin
(

let attrs = d.FStar_Parser_AST.attrs
in (

let attrs1 = (FStar_List.map (desugar_term env1) attrs)
in (

let attrs2 = (

let uu____19848 = (mk_comment_attr d)
in (uu____19848)::attrs1)
in (

let s = (FStar_List.fold_left (fun s a -> (

let uu____19859 = (

let uu____19860 = (FStar_Syntax_Print.term_to_string a)
in (Prims.strcat "; " uu____19860))
in (Prims.strcat s uu____19859))) "" attrs2)
in (

let uu____19861 = (FStar_List.map (fun sigelt -> (

let uu___137_19867 = sigelt
in {FStar_Syntax_Syntax.sigel = uu___137_19867.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___137_19867.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___137_19867.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___137_19867.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = attrs2})) sigelts)
in ((env1), (uu____19861)))))))
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
| uu____19890 -> begin
()
end);
((env), ((se)::[]));
))
end
| FStar_Parser_AST.Fsdoc (uu____19893) -> begin
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

let uu____19909 = (FStar_Syntax_DsEnv.push_module_abbrev env x l)
in ((uu____19909), ([])))
end
| FStar_Parser_AST.Tycon (is_effect, tcs) -> begin
(

let quals = (match (is_effect) with
| true -> begin
(FStar_Parser_AST.Effect_qual)::d.FStar_Parser_AST.quals
end
| uu____19935 -> begin
d.FStar_Parser_AST.quals
end)
in (

let tcs1 = (FStar_List.map (fun uu____19948 -> (match (uu____19948) with
| (x, uu____19956) -> begin
x
end)) tcs)
in (

let uu____19961 = (FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals)
in (desugar_tycon env d uu____19961 tcs1))))
end
| FStar_Parser_AST.TopLevelLet (isrec, lets) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let expand_toplevel_pattern = ((Prims.op_Equality isrec FStar_Parser_AST.NoLetQualifier) && (match (lets) with
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatOp (uu____19983); FStar_Parser_AST.prange = uu____19984}, uu____19985))::[] -> begin
false
end
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____19994); FStar_Parser_AST.prange = uu____19995}, uu____19996))::[] -> begin
false
end
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____20011); FStar_Parser_AST.prange = uu____20012}, uu____20013); FStar_Parser_AST.prange = uu____20014}, uu____20015))::[] -> begin
false
end
| ((p, uu____20043))::[] -> begin
(

let uu____20052 = (is_app_pattern p)
in (not (uu____20052)))
end
| uu____20053 -> begin
false
end))
in (match ((not (expand_toplevel_pattern))) with
| true -> begin
(

let lets1 = (FStar_List.map (fun x -> ((FStar_Pervasives_Native.None), (x))) lets)
in (

let as_inner_let = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets1), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)
in (

let uu____20126 = (desugar_term_maybe_top true env as_inner_let)
in (match (uu____20126) with
| (ds_lets, aq) -> begin
((check_no_aq aq);
(

let uu____20138 = (

let uu____20139 = (FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets)
in uu____20139.FStar_Syntax_Syntax.n)
in (match (uu____20138) with
| FStar_Syntax_Syntax.Tm_let (lbs, uu____20147) -> begin
(

let fvs = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals1 = (match (quals) with
| (uu____20180)::uu____20181 -> begin
(FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals)
end
| uu____20184 -> begin
(FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.collect (fun uu___111_20199 -> (match (uu___111_20199) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (uu____20202); FStar_Syntax_Syntax.lbunivs = uu____20203; FStar_Syntax_Syntax.lbtyp = uu____20204; FStar_Syntax_Syntax.lbeff = uu____20205; FStar_Syntax_Syntax.lbdef = uu____20206; FStar_Syntax_Syntax.lbattrs = uu____20207; FStar_Syntax_Syntax.lbpos = uu____20208} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____20220; FStar_Syntax_Syntax.lbtyp = uu____20221; FStar_Syntax_Syntax.lbeff = uu____20222; FStar_Syntax_Syntax.lbdef = uu____20223; FStar_Syntax_Syntax.lbattrs = uu____20224; FStar_Syntax_Syntax.lbpos = uu____20225} -> begin
(FStar_Syntax_DsEnv.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals2 = (

let uu____20239 = (FStar_All.pipe_right lets1 (FStar_Util.for_some (fun uu____20270 -> (match (uu____20270) with
| (uu____20283, (uu____20284, t)) -> begin
(Prims.op_Equality t.FStar_Parser_AST.level FStar_Parser_AST.Formula)
end))))
in (match (uu____20239) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals1
end
| uu____20300 -> begin
quals1
end))
in (

let lbs1 = (

let uu____20308 = (FStar_All.pipe_right quals2 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____20308) with
| true -> begin
(

let uu____20317 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu___138_20331 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let uu___139_20333 = fv
in {FStar_Syntax_Syntax.fv_name = uu___139_20333.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = uu___139_20333.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = uu___138_20331.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___138_20331.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___138_20331.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___138_20331.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___138_20331.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___138_20331.FStar_Syntax_Syntax.lbpos})))))
in (((FStar_Pervasives_Native.fst lbs)), (uu____20317)))
end
| uu____20338 -> begin
lbs
end))
in (

let names1 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (

let attrs = (FStar_List.map (desugar_term env) d.FStar_Parser_AST.attrs)
in (

let s = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((lbs1), (names1))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = attrs}
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env s)
in (

let env2 = (FStar_List.fold_left (fun env2 id1 -> (FStar_Syntax_DsEnv.push_doc env2 id1 d.FStar_Parser_AST.doc)) env1 names1)
in ((env2), ((s)::[])))))))))))
end
| uu____20368 -> begin
(failwith "Desugaring a let did not produce a let")
end));
)
end))))
end
| uu____20373 -> begin
(

let uu____20374 = (match (lets) with
| ((pat, body))::[] -> begin
((pat), (body))
end
| uu____20393 -> begin
(failwith "expand_toplevel_pattern should only allow single definition lets")
end)
in (match (uu____20374) with
| (pat, body) -> begin
(

let fresh_toplevel_name = (FStar_Ident.gen FStar_Range.dummyRange)
in (

let fresh_pat = (

let var_pat = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((fresh_toplevel_name), (FStar_Pervasives_Native.None)))) FStar_Range.dummyRange)
in (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat1, ty) -> begin
(

let uu___140_20429 = pat1
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed (((var_pat), (ty))); FStar_Parser_AST.prange = uu___140_20429.FStar_Parser_AST.prange})
end
| uu____20436 -> begin
var_pat
end))
in (

let main_let = (desugar_decl env (

let uu___141_20443 = d
in {FStar_Parser_AST.d = FStar_Parser_AST.TopLevelLet (((isrec), ((((fresh_pat), (body)))::[]))); FStar_Parser_AST.drange = uu___141_20443.FStar_Parser_AST.drange; FStar_Parser_AST.doc = uu___141_20443.FStar_Parser_AST.doc; FStar_Parser_AST.quals = (FStar_Parser_AST.Private)::d.FStar_Parser_AST.quals; FStar_Parser_AST.attrs = uu___141_20443.FStar_Parser_AST.attrs}))
in (

let build_projection = (fun uu____20475 id1 -> (match (uu____20475) with
| (env1, ses) -> begin
(

let main = (

let uu____20496 = (

let uu____20497 = (FStar_Ident.lid_of_ids ((fresh_toplevel_name)::[]))
in FStar_Parser_AST.Var (uu____20497))
in (FStar_Parser_AST.mk_term uu____20496 FStar_Range.dummyRange FStar_Parser_AST.Expr))
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

let uu____20547 = (desugar_decl env1 id_decl)
in (match (uu____20547) with
| (env2, ses') -> begin
((env2), ((FStar_List.append ses ses')))
end))))))))
end))
in (

let bvs = (

let uu____20565 = (gather_pattern_bound_vars pat)
in (FStar_All.pipe_right uu____20565 FStar_Util.set_elements))
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

let uu____20596 = (close_fun env t)
in (desugar_term env uu____20596))
in (

let quals1 = (

let uu____20600 = ((FStar_Syntax_DsEnv.iface env) && (FStar_Syntax_DsEnv.admitted_iface env))
in (match (uu____20600) with
| true -> begin
(FStar_Parser_AST.Assumption)::quals
end
| uu____20603 -> begin
quals
end))
in (

let lid = (FStar_Syntax_DsEnv.qualify env id1)
in (

let se = (

let uu____20606 = (FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals1)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), ([]), (t1))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = uu____20606; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se)
in (

let env2 = (FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc)
in ((env2), ((se)::[])))))))))
end
| FStar_Parser_AST.Exception (id1, FStar_Pervasives_Native.None) -> begin
(

let uu____20618 = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_lid env) FStar_Parser_Const.exn_lid)
in (match (uu____20618) with
| (t, uu____20632) -> begin
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

let uu____20666 = (

let uu____20673 = (FStar_Syntax_Syntax.null_binder t)
in (uu____20673)::[])
in (

let uu____20674 = (

let uu____20677 = (

let uu____20678 = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_lid env) FStar_Parser_Const.exn_lid)
in (FStar_Pervasives_Native.fst uu____20678))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____20677))
in (FStar_Syntax_Util.arrow uu____20666 uu____20674)))
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

let uu____20741 = (FStar_Syntax_DsEnv.try_lookup_effect_name env l1)
in (match (uu____20741) with
| FStar_Pervasives_Native.None -> begin
(

let uu____20744 = (

let uu____20749 = (

let uu____20750 = (

let uu____20751 = (FStar_Syntax_Print.lid_to_string l1)
in (Prims.strcat uu____20751 " not found"))
in (Prims.strcat "Effect name " uu____20750))
in ((FStar_Errors.Fatal_EffectNotFound), (uu____20749)))
in (FStar_Errors.raise_error uu____20744 d.FStar_Parser_AST.drange))
end
| FStar_Pervasives_Native.Some (l2) -> begin
l2
end)))
in (

let src = (lookup1 l.FStar_Parser_AST.msource)
in (

let dst = (lookup1 l.FStar_Parser_AST.mdest)
in (

let uu____20755 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(

let uu____20797 = (

let uu____20806 = (

let uu____20813 = (desugar_term env t)
in (([]), (uu____20813)))
in FStar_Pervasives_Native.Some (uu____20806))
in ((uu____20797), (FStar_Pervasives_Native.None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(

let uu____20846 = (

let uu____20855 = (

let uu____20862 = (desugar_term env wp)
in (([]), (uu____20862)))
in FStar_Pervasives_Native.Some (uu____20855))
in (

let uu____20871 = (

let uu____20880 = (

let uu____20887 = (desugar_term env t)
in (([]), (uu____20887)))
in FStar_Pervasives_Native.Some (uu____20880))
in ((uu____20846), (uu____20871))))
end
| FStar_Parser_AST.LiftForFree (t) -> begin
(

let uu____20913 = (

let uu____20922 = (

let uu____20929 = (desugar_term env t)
in (([]), (uu____20929)))
in FStar_Pervasives_Native.Some (uu____20922))
in ((FStar_Pervasives_Native.None), (uu____20913)))
end)
in (match (uu____20755) with
| (lift_wp, lift) -> begin
(

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect ({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift}); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in ((env), ((se)::[])))
end)))))
end
| FStar_Parser_AST.Splice (t) -> begin
(

let t1 = (desugar_term env t)
in (

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_splice (t1); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in ((env), ((se)::[]))))
end)))


let desugar_decls : env_t  ->  FStar_Parser_AST.decl Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env decls -> (

let uu____21022 = (FStar_List.fold_left (fun uu____21042 d -> (match (uu____21042) with
| (env1, sigelts) -> begin
(

let uu____21062 = (desugar_decl env1 d)
in (match (uu____21062) with
| (env2, se) -> begin
((env2), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls)
in (match (uu____21022) with
| (env1, sigelts) -> begin
(

let rec forward = (fun acc uu___113_21103 -> (match (uu___113_21103) with
| (se1)::(se2)::sigelts1 -> begin
(match (((se1.FStar_Syntax_Syntax.sigel), (se2.FStar_Syntax_Syntax.sigel))) with
| (FStar_Syntax_Syntax.Sig_declare_typ (uu____21117), FStar_Syntax_Syntax.Sig_let (uu____21118)) -> begin
(

let uu____21131 = (

let uu____21134 = (

let uu___142_21135 = se2
in (

let uu____21136 = (

let uu____21139 = (FStar_List.filter (fun uu___112_21153 -> (match (uu___112_21153) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____21157; FStar_Syntax_Syntax.vars = uu____21158}, uu____21159); FStar_Syntax_Syntax.pos = uu____21160; FStar_Syntax_Syntax.vars = uu____21161} when (

let uu____21184 = (

let uu____21185 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____21185))
in (Prims.op_Equality uu____21184 "FStar.Pervasives.Comment")) -> begin
true
end
| uu____21186 -> begin
false
end)) se1.FStar_Syntax_Syntax.sigattrs)
in (FStar_List.append uu____21139 se2.FStar_Syntax_Syntax.sigattrs))
in {FStar_Syntax_Syntax.sigel = uu___142_21135.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___142_21135.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___142_21135.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___142_21135.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu____21136}))
in (uu____21134)::(se1)::acc)
in (forward uu____21131 sigelts1))
end
| uu____21191 -> begin
(forward ((se1)::acc) ((se2)::sigelts1))
end)
end
| sigelts1 -> begin
(FStar_List.rev_append acc sigelts1)
end))
in (

let uu____21199 = (forward [] sigelts)
in ((env1), (uu____21199))))
end)))


let open_prims_all : (FStar_Parser_AST.decoration Prims.list  ->  FStar_Parser_AST.decl) Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Parser_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Parser_Const.all_lid)) FStar_Range.dummyRange))::[]


let desugar_modul_common : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let env1 = (match (((curmod), (m))) with
| (FStar_Pervasives_Native.None, uu____21250) -> begin
env
end
| (FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.name = prev_lid; FStar_Syntax_Syntax.declarations = uu____21254; FStar_Syntax_Syntax.exports = uu____21255; FStar_Syntax_Syntax.is_interface = uu____21256}), FStar_Parser_AST.Module (current_lid, uu____21258)) when ((FStar_Ident.lid_equals prev_lid current_lid) && (FStar_Options.interactive ())) -> begin
env
end
| (FStar_Pervasives_Native.Some (prev_mod), uu____21266) -> begin
(

let uu____21269 = (FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod)
in (FStar_Pervasives_Native.fst uu____21269))
end)
in (

let uu____21274 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(

let uu____21310 = (FStar_Syntax_DsEnv.prepare_module_or_interface true admitted env1 mname FStar_Syntax_DsEnv.default_mii)
in ((uu____21310), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(

let uu____21327 = (FStar_Syntax_DsEnv.prepare_module_or_interface false false env1 mname FStar_Syntax_DsEnv.default_mii)
in ((uu____21327), (mname), (decls), (false)))
end)
in (match (uu____21274) with
| ((env2, pop_when_done), mname, decls, intf) -> begin
(

let uu____21357 = (desugar_decls env2 decls)
in (match (uu____21357) with
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

let uu____21411 = ((FStar_Options.interactive ()) && (

let uu____21413 = (

let uu____21414 = (

let uu____21415 = (FStar_Options.file_list ())
in (FStar_List.hd uu____21415))
in (FStar_Util.get_file_extension uu____21414))
in (FStar_List.mem uu____21413 (("fsti")::("fsi")::[]))))
in (match (uu____21411) with
| true -> begin
(as_interface m)
end
| uu____21418 -> begin
m
end))
in (

let uu____21419 = (desugar_modul_common curmod env m1)
in (match (uu____21419) with
| (x, y, pop_when_done) -> begin
((match (pop_when_done) with
| true -> begin
(

let uu____21434 = (FStar_Syntax_DsEnv.pop ())
in ())
end
| uu____21435 -> begin
()
end);
((x), (y));
)
end))))


let desugar_modul : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (

let uu____21450 = (desugar_modul_common FStar_Pervasives_Native.None env m)
in (match (uu____21450) with
| (env1, modul, pop_when_done) -> begin
(

let uu____21464 = (FStar_Syntax_DsEnv.finish_module_or_interface env1 modul)
in (match (uu____21464) with
| (env2, modul1) -> begin
((

let uu____21476 = (FStar_Options.dump_module modul1.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____21476) with
| true -> begin
(

let uu____21477 = (FStar_Syntax_Print.modul_to_string modul1)
in (FStar_Util.print1 "Module after desugaring:\n%s\n" uu____21477))
end
| uu____21478 -> begin
()
end));
(

let uu____21479 = (match (pop_when_done) with
| true -> begin
(FStar_Syntax_DsEnv.export_interface modul1.FStar_Syntax_Syntax.name env2)
end
| uu____21480 -> begin
env2
end)
in ((uu____21479), (modul1)));
)
end))
end)))


let ast_modul_to_modul : FStar_Parser_AST.modul  ->  FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv = (fun modul env -> (

let uu____21493 = (desugar_modul env modul)
in (match (uu____21493) with
| (env1, modul1) -> begin
((modul1), (env1))
end)))


let decls_to_sigelts : FStar_Parser_AST.decl Prims.list  ->  FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv = (fun decls env -> (

let uu____21520 = (desugar_decls env decls)
in (match (uu____21520) with
| (env1, sigelts) -> begin
((sigelts), (env1))
end)))


let partial_ast_modul_to_modul : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Parser_AST.modul  ->  FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv = (fun modul a_modul env -> (

let uu____21558 = (desugar_partial_modul modul env a_modul)
in (match (uu____21558) with
| (env1, modul1) -> begin
((modul1), (env1))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Syntax_DsEnv.module_inclusion_info  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  Prims.unit FStar_Syntax_DsEnv.withenv = (fun m mii erase_univs en -> (

let erase_univs_ed = (fun ed -> (

let erase_binders = (fun bs -> (match (bs) with
| [] -> begin
[]
end
| uu____21632 -> begin
(

let t = (

let uu____21640 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (FStar_Syntax_Syntax.t_unit), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (erase_univs uu____21640))
in (

let uu____21649 = (

let uu____21650 = (FStar_Syntax_Subst.compress t)
in uu____21650.FStar_Syntax_Syntax.n)
in (match (uu____21649) with
| FStar_Syntax_Syntax.Tm_abs (bs1, uu____21660, uu____21661) -> begin
bs1
end
| uu____21682 -> begin
(failwith "Impossible")
end)))
end))
in (

let uu____21689 = (

let uu____21696 = (erase_binders ed.FStar_Syntax_Syntax.binders)
in (FStar_Syntax_Subst.open_term' uu____21696 FStar_Syntax_Syntax.t_unit))
in (match (uu____21689) with
| (binders, uu____21698, binders_opening) -> begin
(

let erase_term = (fun t -> (

let uu____21704 = (

let uu____21705 = (FStar_Syntax_Subst.subst binders_opening t)
in (erase_univs uu____21705))
in (FStar_Syntax_Subst.close binders uu____21704)))
in (

let erase_tscheme = (fun uu____21721 -> (match (uu____21721) with
| (us, t) -> begin
(

let t1 = (

let uu____21741 = (FStar_Syntax_Subst.shift_subst (FStar_List.length us) binders_opening)
in (FStar_Syntax_Subst.subst uu____21741 t))
in (

let uu____21744 = (

let uu____21745 = (erase_univs t1)
in (FStar_Syntax_Subst.close binders uu____21745))
in (([]), (uu____21744))))
end))
in (

let erase_action = (fun action -> (

let opening = (FStar_Syntax_Subst.shift_subst (FStar_List.length action.FStar_Syntax_Syntax.action_univs) binders_opening)
in (

let erased_action_params = (match (action.FStar_Syntax_Syntax.action_params) with
| [] -> begin
[]
end
| uu____21774 -> begin
(

let bs = (

let uu____21782 = (FStar_Syntax_Subst.subst_binders opening action.FStar_Syntax_Syntax.action_params)
in (FStar_All.pipe_left erase_binders uu____21782))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (FStar_Syntax_Syntax.t_unit), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____21812 = (

let uu____21813 = (

let uu____21816 = (FStar_Syntax_Subst.close binders t)
in (FStar_Syntax_Subst.compress uu____21816))
in uu____21813.FStar_Syntax_Syntax.n)
in (match (uu____21812) with
| FStar_Syntax_Syntax.Tm_abs (bs1, uu____21824, uu____21825) -> begin
bs1
end
| uu____21846 -> begin
(failwith "Impossible")
end))))
end)
in (

let erase_term1 = (fun t -> (

let uu____21857 = (

let uu____21858 = (FStar_Syntax_Subst.subst opening t)
in (erase_univs uu____21858))
in (FStar_Syntax_Subst.close binders uu____21857)))
in (

let uu___143_21859 = action
in (

let uu____21860 = (erase_term1 action.FStar_Syntax_Syntax.action_defn)
in (

let uu____21861 = (erase_term1 action.FStar_Syntax_Syntax.action_typ)
in {FStar_Syntax_Syntax.action_name = uu___143_21859.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___143_21859.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = erased_action_params; FStar_Syntax_Syntax.action_defn = uu____21860; FStar_Syntax_Syntax.action_typ = uu____21861})))))))
in (

let uu___144_21862 = ed
in (

let uu____21863 = (FStar_Syntax_Subst.close_binders binders)
in (

let uu____21864 = (erase_term ed.FStar_Syntax_Syntax.signature)
in (

let uu____21865 = (erase_tscheme ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____21866 = (erase_tscheme ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____21867 = (erase_tscheme ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____21868 = (erase_tscheme ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____21869 = (erase_tscheme ed.FStar_Syntax_Syntax.stronger)
in (

let uu____21870 = (erase_tscheme ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____21871 = (erase_tscheme ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____21872 = (erase_tscheme ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____21873 = (erase_tscheme ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____21874 = (erase_tscheme ed.FStar_Syntax_Syntax.trivial)
in (

let uu____21875 = (erase_term ed.FStar_Syntax_Syntax.repr)
in (

let uu____21876 = (erase_tscheme ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____21877 = (erase_tscheme ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____21878 = (FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = uu___144_21862.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___144_21862.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = uu____21863; FStar_Syntax_Syntax.signature = uu____21864; FStar_Syntax_Syntax.ret_wp = uu____21865; FStar_Syntax_Syntax.bind_wp = uu____21866; FStar_Syntax_Syntax.if_then_else = uu____21867; FStar_Syntax_Syntax.ite_wp = uu____21868; FStar_Syntax_Syntax.stronger = uu____21869; FStar_Syntax_Syntax.close_wp = uu____21870; FStar_Syntax_Syntax.assert_p = uu____21871; FStar_Syntax_Syntax.assume_p = uu____21872; FStar_Syntax_Syntax.null_wp = uu____21873; FStar_Syntax_Syntax.trivial = uu____21874; FStar_Syntax_Syntax.repr = uu____21875; FStar_Syntax_Syntax.return_repr = uu____21876; FStar_Syntax_Syntax.bind_repr = uu____21877; FStar_Syntax_Syntax.actions = uu____21878; FStar_Syntax_Syntax.eff_attrs = uu___144_21862.FStar_Syntax_Syntax.eff_attrs}))))))))))))))))))))
end))))
in (

let push_sigelt1 = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let se' = (

let uu___145_21890 = se
in (

let uu____21891 = (

let uu____21892 = (erase_univs_ed ed)
in FStar_Syntax_Syntax.Sig_new_effect (uu____21892))
in {FStar_Syntax_Syntax.sigel = uu____21891; FStar_Syntax_Syntax.sigrng = uu___145_21890.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___145_21890.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___145_21890.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___145_21890.FStar_Syntax_Syntax.sigattrs}))
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se')
in (push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng)))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed) -> begin
(

let se' = (

let uu___146_21896 = se
in (

let uu____21897 = (

let uu____21898 = (erase_univs_ed ed)
in FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____21898))
in {FStar_Syntax_Syntax.sigel = uu____21897; FStar_Syntax_Syntax.sigrng = uu___146_21896.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___146_21896.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___146_21896.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___146_21896.FStar_Syntax_Syntax.sigattrs}))
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se')
in (push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng)))
end
| uu____21900 -> begin
(FStar_Syntax_DsEnv.push_sigelt env se)
end))
in (

let uu____21901 = (FStar_Syntax_DsEnv.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name mii)
in (match (uu____21901) with
| (en1, pop_when_done) -> begin
(

let en2 = (

let uu____21913 = (FStar_Syntax_DsEnv.set_current_module en1 m.FStar_Syntax_Syntax.name)
in (FStar_List.fold_left push_sigelt1 uu____21913 m.FStar_Syntax_Syntax.exports))
in (

let env = (FStar_Syntax_DsEnv.finish en2 m)
in (

let uu____21915 = (match (pop_when_done) with
| true -> begin
(FStar_Syntax_DsEnv.export_interface m.FStar_Syntax_Syntax.name env)
end
| uu____21916 -> begin
env
end)
in ((()), (uu____21915)))))
end)))))




