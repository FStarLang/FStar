
open Prims
open FStar_Pervasives

let desugar_disjunctive_pattern : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.branch Prims.list = (fun pats when_opt branch1 -> (FStar_All.pipe_right pats (FStar_List.map (fun pat -> (FStar_Syntax_Util.branch ((pat), (when_opt), (branch1)))))))


let trans_aqual : FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option = (fun uu___84_66 -> (match (uu___84_66) with
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)
end
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality)
end
| uu____71 -> begin
FStar_Pervasives_Native.None
end))


let trans_qual : FStar_Range.range  ->  FStar_Ident.lident FStar_Pervasives_Native.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun r maybe_effect_id uu___85_90 -> (match (uu___85_90) with
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


let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun uu___86_99 -> (match (uu___86_99) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end
| FStar_Parser_AST.LightOff -> begin
FStar_Syntax_Syntax.LightOff
end))


let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option = (fun uu___87_110 -> (match (uu___87_110) with
| FStar_Parser_AST.Hash -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)
end
| uu____113 -> begin
FStar_Pervasives_Native.None
end))


let arg_withimp_e : 'Auu____120 . FStar_Parser_AST.imp  ->  'Auu____120  ->  ('Auu____120 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) = (fun imp t -> ((t), ((as_imp imp))))


let arg_withimp_t : 'Auu____145 . FStar_Parser_AST.imp  ->  'Auu____145  ->  ('Auu____145 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
((t), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end
| uu____164 -> begin
((t), (FStar_Pervasives_Native.None))
end))


let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (uu____181) -> begin
true
end
| uu____186 -> begin
false
end)))))


let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t1) -> begin
(unparen t1)
end
| uu____193 -> begin
t
end))


let tm_type_z : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (

let uu____199 = (

let uu____200 = (FStar_Ident.lid_of_path (("Type0")::[]) r)
in FStar_Parser_AST.Name (uu____200))
in (FStar_Parser_AST.mk_term uu____199 r FStar_Parser_AST.Kind)))


let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (

let uu____206 = (

let uu____207 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (uu____207))
in (FStar_Parser_AST.mk_term uu____206 r FStar_Parser_AST.Kind)))


let rec is_comp_type : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> (

let uu____218 = (

let uu____219 = (unparen t)
in uu____219.FStar_Parser_AST.tm)
in (match (uu____218) with
| FStar_Parser_AST.Name (l) -> begin
(

let uu____221 = (FStar_Syntax_DsEnv.try_lookup_effect_name env l)
in (FStar_All.pipe_right uu____221 FStar_Option.isSome))
end
| FStar_Parser_AST.Construct (l, uu____227) -> begin
(

let uu____240 = (FStar_Syntax_DsEnv.try_lookup_effect_name env l)
in (FStar_All.pipe_right uu____240 FStar_Option.isSome))
end
| FStar_Parser_AST.App (head1, uu____246, uu____247) -> begin
(is_comp_type env head1)
end
| FStar_Parser_AST.Paren (t1) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.Ascribed (t1, uu____250, uu____251) -> begin
(is_comp_type env t1)
end
| FStar_Parser_AST.LetOpen (uu____256, t1) -> begin
(is_comp_type env t1)
end
| uu____258 -> begin
false
end)))


let unit_ty : FStar_Parser_AST.term = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.unit_lid)) FStar_Range.dummyRange FStar_Parser_AST.Type_level)


let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n1 s r -> (

let uu____274 = (

let uu____277 = (

let uu____278 = (

let uu____283 = (FStar_Parser_AST.compile_op n1 s r)
in ((uu____283), (r)))
in (FStar_Ident.mk_ident uu____278))
in (uu____277)::[])
in (FStar_All.pipe_right uu____274 FStar_Ident.lid_of_ids)))


let op_as_term : 'Auu____296 . FStar_Syntax_DsEnv.env  ->  Prims.int  ->  'Auu____296  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env arity rng op -> (

let r = (fun l dd -> (

let uu____332 = (

let uu____333 = (

let uu____334 = (FStar_Ident.set_lid_range l op.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____334 dd FStar_Pervasives_Native.None))
in (FStar_All.pipe_right uu____333 FStar_Syntax_Syntax.fv_to_tm))
in FStar_Pervasives_Native.Some (uu____332)))
in (

let fallback = (fun uu____342 -> (

let uu____343 = (FStar_Ident.text_of_id op)
in (match (uu____343) with
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

let uu____346 = (FStar_Options.ml_ish ())
in (match (uu____346) with
| true -> begin
(r FStar_Parser_Const.list_append_lid FStar_Syntax_Syntax.Delta_equational)
end
| uu____349 -> begin
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
| uu____350 -> begin
FStar_Pervasives_Native.None
end)))
in (

let uu____351 = (

let uu____358 = (compile_op_lid arity op.FStar_Ident.idText op.FStar_Ident.idRange)
in (FStar_Syntax_DsEnv.try_lookup_lid env uu____358))
in (match (uu____351) with
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some ((FStar_Pervasives_Native.fst t))
end
| uu____370 -> begin
(fallback ())
end)))))


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (

let uu____388 = (FStar_Util.remove_dups (fun x y -> (Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) uu____388)))


let rec free_type_vars_b : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (uu____435) -> begin
((env), ([]))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____439 = (FStar_Syntax_DsEnv.push_bv env x)
in (match (uu____439) with
| (env1, uu____451) -> begin
((env1), ((x)::[]))
end))
end
| FStar_Parser_AST.Annotated (uu____454, term) -> begin
(

let uu____456 = (free_type_vars env term)
in ((env), (uu____456)))
end
| FStar_Parser_AST.TAnnotated (id1, uu____462) -> begin
(

let uu____463 = (FStar_Syntax_DsEnv.push_bv env id1)
in (match (uu____463) with
| (env1, uu____475) -> begin
((env1), ([]))
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____479 = (free_type_vars env t)
in ((env), (uu____479)))
end))
and free_type_vars : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (

let uu____486 = (

let uu____487 = (unparen t)
in uu____487.FStar_Parser_AST.tm)
in (match (uu____486) with
| FStar_Parser_AST.Labeled (uu____490) -> begin
(failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____500 = (FStar_Syntax_DsEnv.try_lookup_id env a)
in (match (uu____500) with
| FStar_Pervasives_Native.None -> begin
(a)::[]
end
| uu____513 -> begin
[]
end))
end
| FStar_Parser_AST.Wild -> begin
[]
end
| FStar_Parser_AST.Const (uu____520) -> begin
[]
end
| FStar_Parser_AST.Uvar (uu____521) -> begin
[]
end
| FStar_Parser_AST.Var (uu____522) -> begin
[]
end
| FStar_Parser_AST.Projector (uu____523) -> begin
[]
end
| FStar_Parser_AST.Discrim (uu____528) -> begin
[]
end
| FStar_Parser_AST.Name (uu____529) -> begin
[]
end
| FStar_Parser_AST.Requires (t1, uu____531) -> begin
(free_type_vars env t1)
end
| FStar_Parser_AST.Ensures (t1, uu____537) -> begin
(free_type_vars env t1)
end
| FStar_Parser_AST.NamedTyp (uu____542, t1) -> begin
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
| FStar_Parser_AST.Construct (uu____560, ts) -> begin
(FStar_List.collect (fun uu____581 -> (match (uu____581) with
| (t1, uu____589) -> begin
(free_type_vars env t1)
end)) ts)
end
| FStar_Parser_AST.Op (uu____590, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, uu____598) -> begin
(

let uu____599 = (free_type_vars env t1)
in (

let uu____602 = (free_type_vars env t2)
in (FStar_List.append uu____599 uu____602)))
end
| FStar_Parser_AST.Refine (b, t1) -> begin
(

let uu____607 = (free_type_vars_b env b)
in (match (uu____607) with
| (env1, f) -> begin
(

let uu____622 = (free_type_vars env1 t1)
in (FStar_List.append f uu____622))
end))
end
| FStar_Parser_AST.Product (binders, body) -> begin
(

let uu____631 = (FStar_List.fold_left (fun uu____651 binder -> (match (uu____651) with
| (env1, free) -> begin
(

let uu____671 = (free_type_vars_b env1 binder)
in (match (uu____671) with
| (env2, f) -> begin
((env2), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (uu____631) with
| (env1, free) -> begin
(

let uu____702 = (free_type_vars env1 body)
in (FStar_List.append free uu____702))
end))
end
| FStar_Parser_AST.Sum (binders, body) -> begin
(

let uu____711 = (FStar_List.fold_left (fun uu____731 binder -> (match (uu____731) with
| (env1, free) -> begin
(

let uu____751 = (free_type_vars_b env1 binder)
in (match (uu____751) with
| (env2, f) -> begin
((env2), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (uu____711) with
| (env1, free) -> begin
(

let uu____782 = (free_type_vars env1 body)
in (FStar_List.append free uu____782))
end))
end
| FStar_Parser_AST.Project (t1, uu____786) -> begin
(free_type_vars env t1)
end
| FStar_Parser_AST.Attributes (cattributes) -> begin
(FStar_List.collect (free_type_vars env) cattributes)
end
| FStar_Parser_AST.Abs (uu____790) -> begin
[]
end
| FStar_Parser_AST.Let (uu____797) -> begin
[]
end
| FStar_Parser_AST.LetOpen (uu____818) -> begin
[]
end
| FStar_Parser_AST.If (uu____823) -> begin
[]
end
| FStar_Parser_AST.QForall (uu____830) -> begin
[]
end
| FStar_Parser_AST.QExists (uu____843) -> begin
[]
end
| FStar_Parser_AST.Record (uu____856) -> begin
[]
end
| FStar_Parser_AST.Match (uu____869) -> begin
[]
end
| FStar_Parser_AST.TryWith (uu____884) -> begin
[]
end
| FStar_Parser_AST.Bind (uu____899) -> begin
[]
end
| FStar_Parser_AST.Quote (uu____906) -> begin
[]
end
| FStar_Parser_AST.VQuote (uu____911) -> begin
[]
end
| FStar_Parser_AST.Antiquote (uu____912) -> begin
[]
end
| FStar_Parser_AST.Seq (uu____917) -> begin
[]
end)))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (

let rec aux = (fun args t1 -> (

let uu____970 = (

let uu____971 = (unparen t1)
in uu____971.FStar_Parser_AST.tm)
in (match (uu____970) with
| FStar_Parser_AST.App (t2, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t2)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t1.FStar_Parser_AST.range; FStar_Parser_AST.level = t1.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| uu____1013 -> begin
((t1), (args))
end)))
in (aux [] t)))


let close : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (

let uu____1037 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv uu____1037))
in (match ((Prims.op_Equality (FStar_List.length ftv) (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____1044 -> begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (

let uu____1055 = (

let uu____1056 = (

let uu____1061 = (tm_type x.FStar_Ident.idRange)
in ((x), (uu____1061)))
in FStar_Parser_AST.TAnnotated (uu____1056))
in (FStar_Parser_AST.mk_binder uu____1055 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end)))


let close_fun : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (

let uu____1078 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv uu____1078))
in (match ((Prims.op_Equality (FStar_List.length ftv) (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____1085 -> begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (

let uu____1096 = (

let uu____1097 = (

let uu____1102 = (tm_type x.FStar_Ident.idRange)
in ((x), (uu____1102)))
in FStar_Parser_AST.TAnnotated (uu____1097))
in (FStar_Parser_AST.mk_binder uu____1096 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))))))
in (

let t1 = (

let uu____1104 = (

let uu____1105 = (unparen t)
in uu____1105.FStar_Parser_AST.tm)
in (match (uu____1104) with
| FStar_Parser_AST.Product (uu____1106) -> begin
t
end
| uu____1113 -> begin
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
| uu____1149 -> begin
((bs), (t))
end))


let rec is_var_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatWild -> begin
true
end
| FStar_Parser_AST.PatTvar (uu____1157, uu____1158) -> begin
true
end
| FStar_Parser_AST.PatVar (uu____1163, uu____1164) -> begin
true
end
| FStar_Parser_AST.PatAscribed (p1, uu____1170) -> begin
(is_var_pattern p1)
end
| uu____1183 -> begin
false
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p1, uu____1190) -> begin
(is_app_pattern p1)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____1203); FStar_Parser_AST.prange = uu____1204}, uu____1205) -> begin
true
end
| uu____1216 -> begin
false
end))


let replace_unit_pattern : FStar_Parser_AST.pattern  ->  FStar_Parser_AST.pattern = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatConst (FStar_Const.Const_unit) -> begin
(FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatAscribed ((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)), (((unit_ty), (FStar_Pervasives_Native.None)))))) p.FStar_Parser_AST.prange)
end
| uu____1230 -> begin
p
end))


let rec destruct_app_pattern : FStar_Syntax_DsEnv.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * (FStar_Parser_AST.term * FStar_Parser_AST.term FStar_Pervasives_Native.option) FStar_Pervasives_Native.option) = (fun env is_top_level1 p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p1, t) -> begin
(

let uu____1300 = (destruct_app_pattern env is_top_level1 p1)
in (match (uu____1300) with
| (name, args, uu____1343) -> begin
((name), (args), (FStar_Pervasives_Native.Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id1, uu____1393); FStar_Parser_AST.prange = uu____1394}, args) when is_top_level1 -> begin
(

let uu____1404 = (

let uu____1409 = (FStar_Syntax_DsEnv.qualify env id1)
in FStar_Util.Inr (uu____1409))
in ((uu____1404), (args), (FStar_Pervasives_Native.None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id1, uu____1431); FStar_Parser_AST.prange = uu____1432}, args) -> begin
((FStar_Util.Inl (id1)), (args), (FStar_Pervasives_Native.None))
end
| uu____1462 -> begin
(failwith "Not an app pattern")
end))


let rec gather_pattern_bound_vars_maybe_top : FStar_Ident.ident FStar_Util.set  ->  FStar_Parser_AST.pattern  ->  FStar_Ident.ident FStar_Util.set = (fun acc p -> (

let gather_pattern_bound_vars_from_list = (FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc)
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatWild -> begin
acc
end
| FStar_Parser_AST.PatConst (uu____1512) -> begin
acc
end
| FStar_Parser_AST.PatVar (uu____1513, FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)) -> begin
acc
end
| FStar_Parser_AST.PatName (uu____1516) -> begin
acc
end
| FStar_Parser_AST.PatTvar (uu____1517) -> begin
acc
end
| FStar_Parser_AST.PatOp (uu____1524) -> begin
acc
end
| FStar_Parser_AST.PatApp (phead, pats) -> begin
(gather_pattern_bound_vars_from_list ((phead)::pats))
end
| FStar_Parser_AST.PatVar (x, uu____1532) -> begin
(FStar_Util.set_add x acc)
end
| FStar_Parser_AST.PatList (pats) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatTuple (pats, uu____1541) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatOr (pats) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatRecord (guarded_pats) -> begin
(

let uu____1556 = (FStar_List.map FStar_Pervasives_Native.snd guarded_pats)
in (gather_pattern_bound_vars_from_list uu____1556))
end
| FStar_Parser_AST.PatAscribed (pat, uu____1564) -> begin
(gather_pattern_bound_vars_maybe_top acc pat)
end)))


let gather_pattern_bound_vars : FStar_Parser_AST.pattern  ->  FStar_Ident.ident FStar_Util.set = (

let acc = (FStar_Util.new_set (fun id1 id2 -> (match ((Prims.op_Equality id1.FStar_Ident.idText id2.FStar_Ident.idText)) with
| true -> begin
(Prims.parse_int "0")
end
| uu____1590 -> begin
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
| uu____1626 -> begin
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
| uu____1662 -> begin
false
end))


let __proj__LetBinder__item___0 : bnd  ->  (FStar_Ident.lident * (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)) = (fun projectee -> (match (projectee) with
| LetBinder (_0) -> begin
_0
end))


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun uu___88_1708 -> (match (uu___88_1708) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| uu____1715 -> begin
(failwith "Impossible")
end))


let as_binder : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  (FStar_Ident.ident FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_DsEnv.env) = (fun env imp uu___89_1746 -> (match (uu___89_1746) with
| (FStar_Pervasives_Native.None, k) -> begin
(

let uu____1762 = (FStar_Syntax_Syntax.null_binder k)
in ((uu____1762), (env)))
end
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____1767 = (FStar_Syntax_DsEnv.push_bv env a)
in (match (uu____1767) with
| (env1, a1) -> begin
(((((

let uu___113_1787 = a1
in {FStar_Syntax_Syntax.ppname = uu___113_1787.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___113_1787.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), ((trans_aqual imp)))), (env1))
end))
end))


type env_t =
FStar_Syntax_DsEnv.env


type lenv_t =
FStar_Syntax_Syntax.bv Prims.list


let mk_lb : (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list * (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)  ->  FStar_Syntax_Syntax.letbinding = (fun uu____1816 -> (match (uu____1816) with
| (attrs, n1, t, e, pos) -> begin
{FStar_Syntax_Syntax.lbname = n1; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = attrs; FStar_Syntax_Syntax.lbpos = pos}
end))


let no_annot_abs : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs t -> (FStar_Syntax_Util.abs bs t FStar_Pervasives_Native.None))


let mk_ref_read : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun tm -> (

let tm' = (

let uu____1896 = (

let uu____1911 = (

let uu____1914 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____1914))
in (

let uu____1915 = (

let uu____1924 = (

let uu____1931 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (uu____1931)))
in (uu____1924)::[])
in ((uu____1911), (uu____1915))))
in FStar_Syntax_Syntax.Tm_app (uu____1896))
in (FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_alloc : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun tm -> (

let tm' = (

let uu____1968 = (

let uu____1983 = (

let uu____1986 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____1986))
in (

let uu____1987 = (

let uu____1996 = (

let uu____2003 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (uu____2003)))
in (uu____1996)::[])
in ((uu____1983), (uu____1987))))
in FStar_Syntax_Syntax.Tm_app (uu____1968))
in (FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_assign : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t1 t2 pos -> (

let tm = (

let uu____2054 = (

let uu____2069 = (

let uu____2072 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____2072))
in (

let uu____2073 = (

let uu____2082 = (

let uu____2089 = (FStar_Syntax_Syntax.as_implicit false)
in ((t1), (uu____2089)))
in (

let uu____2092 = (

let uu____2101 = (

let uu____2108 = (FStar_Syntax_Syntax.as_implicit false)
in ((t2), (uu____2108)))
in (uu____2101)::[])
in (uu____2082)::uu____2092))
in ((uu____2069), (uu____2073))))
in FStar_Syntax_Syntax.Tm_app (uu____2054))
in (FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos)))


let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun uu___90_2143 -> (match (uu___90_2143) with
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
| uu____2144 -> begin
false
end))


let rec sum_to_universe : FStar_Syntax_Syntax.universe  ->  Prims.int  ->  FStar_Syntax_Syntax.universe = (fun u n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
u
end
| uu____2155 -> begin
(

let uu____2156 = (sum_to_universe u (n1 - (Prims.parse_int "1")))
in FStar_Syntax_Syntax.U_succ (uu____2156))
end))


let int_to_universe : Prims.int  ->  FStar_Syntax_Syntax.universe = (fun n1 -> (sum_to_universe FStar_Syntax_Syntax.U_zero n1))


let rec desugar_maybe_non_constant_universe : FStar_Parser_AST.term  ->  (Prims.int, FStar_Syntax_Syntax.universe) FStar_Util.either = (fun t -> (

let uu____2175 = (

let uu____2176 = (unparen t)
in uu____2176.FStar_Parser_AST.tm)
in (match (uu____2175) with
| FStar_Parser_AST.Wild -> begin
(

let uu____2181 = (

let uu____2182 = (FStar_Syntax_Unionfind.univ_fresh ())
in FStar_Syntax_Syntax.U_unif (uu____2182))
in FStar_Util.Inr (uu____2181))
end
| FStar_Parser_AST.Uvar (u) -> begin
FStar_Util.Inr (FStar_Syntax_Syntax.U_name (u))
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (repr, uu____2193)) -> begin
(

let n1 = (FStar_Util.int_of_string repr)
in ((match ((n1 < (Prims.parse_int "0"))) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_NegativeUniverseConstFatal_NotSupported), ((Prims.strcat "Negative universe constant  are not supported : " repr))) t.FStar_Parser_AST.range)
end
| uu____2208 -> begin
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

let uu____2258 = (sum_to_universe u n1)
in FStar_Util.Inr (uu____2258))
end
| (FStar_Util.Inr (u), FStar_Util.Inl (n1)) -> begin
(

let uu____2269 = (sum_to_universe u n1)
in FStar_Util.Inr (uu____2269))
end
| (FStar_Util.Inr (u11), FStar_Util.Inr (u21)) -> begin
(

let uu____2280 = (

let uu____2285 = (

let uu____2286 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "This universe might contain a sum of two universe variables " uu____2286))
in ((FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars), (uu____2285)))
in (FStar_Errors.raise_error uu____2280 t.FStar_Parser_AST.range))
end)))
end
| FStar_Parser_AST.App (uu____2291) -> begin
(

let rec aux = (fun t1 univargs -> (

let uu____2325 = (

let uu____2326 = (unparen t1)
in uu____2326.FStar_Parser_AST.tm)
in (match (uu____2325) with
| FStar_Parser_AST.App (t2, targ, uu____2333) -> begin
(

let uarg = (desugar_maybe_non_constant_universe targ)
in (aux t2 ((uarg)::univargs)))
end
| FStar_Parser_AST.Var (max_lid1) -> begin
(match ((FStar_List.existsb (fun uu___91_2356 -> (match (uu___91_2356) with
| FStar_Util.Inr (uu____2361) -> begin
true
end
| uu____2362 -> begin
false
end)) univargs)) with
| true -> begin
(

let uu____2367 = (

let uu____2368 = (FStar_List.map (fun uu___92_2377 -> (match (uu___92_2377) with
| FStar_Util.Inl (n1) -> begin
(int_to_universe n1)
end
| FStar_Util.Inr (u) -> begin
u
end)) univargs)
in FStar_Syntax_Syntax.U_max (uu____2368))
in FStar_Util.Inr (uu____2367))
end
| uu____2384 -> begin
(

let nargs = (FStar_List.map (fun uu___93_2394 -> (match (uu___93_2394) with
| FStar_Util.Inl (n1) -> begin
n1
end
| FStar_Util.Inr (uu____2400) -> begin
(failwith "impossible")
end)) univargs)
in (

let uu____2401 = (FStar_List.fold_left (fun m n1 -> (match ((m > n1)) with
| true -> begin
m
end
| uu____2406 -> begin
n1
end)) (Prims.parse_int "0") nargs)
in FStar_Util.Inl (uu____2401)))
end)
end
| uu____2407 -> begin
(

let uu____2408 = (

let uu____2413 = (

let uu____2414 = (

let uu____2415 = (FStar_Parser_AST.term_to_string t1)
in (Prims.strcat uu____2415 " in universe context"))
in (Prims.strcat "Unexpected term " uu____2414))
in ((FStar_Errors.Fatal_UnexpectedTermInUniverse), (uu____2413)))
in (FStar_Errors.raise_error uu____2408 t1.FStar_Parser_AST.range))
end)))
in (aux t []))
end
| uu____2424 -> begin
(

let uu____2425 = (

let uu____2430 = (

let uu____2431 = (

let uu____2432 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat uu____2432 " in universe context"))
in (Prims.strcat "Unexpected term " uu____2431))
in ((FStar_Errors.Fatal_UnexpectedTermInUniverse), (uu____2430)))
in (FStar_Errors.raise_error uu____2425 t.FStar_Parser_AST.range))
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
| ((bv, b, e))::uu____2465 -> begin
(

let uu____2488 = (

let uu____2493 = (

let uu____2494 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected antiquotation: %s(%s)" (match (b) with
| true -> begin
"`@"
end
| uu____2495 -> begin
"`#"
end) uu____2494))
in ((FStar_Errors.Fatal_UnexpectedAntiquotation), (uu____2493)))
in (FStar_Errors.raise_error uu____2488 e.FStar_Syntax_Syntax.pos))
end))


let check_fields : 'Auu____2504 . FStar_Syntax_DsEnv.env  ->  (FStar_Ident.lident * 'Auu____2504) Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_DsEnv.record_or_dc = (fun env fields rg -> (

let uu____2532 = (FStar_List.hd fields)
in (match (uu____2532) with
| (f, uu____2542) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f);
(

let record = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f)
in (

let check_field = (fun uu____2554 -> (match (uu____2554) with
| (f', uu____2560) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f');
(

let uu____2562 = (FStar_Syntax_DsEnv.belongs_to_record env f' record)
in (match (uu____2562) with
| true -> begin
()
end
| uu____2563 -> begin
(

let msg = (FStar_Util.format3 "Field %s belongs to record type %s, whereas field %s does not" f.FStar_Ident.str record.FStar_Syntax_DsEnv.typename.FStar_Ident.str f'.FStar_Ident.str)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_FieldsNotBelongToSameRecordType), (msg)) rg))
end));
)
end))
in ((

let uu____2566 = (FStar_List.tl fields)
in (FStar_List.iter check_field uu____2566));
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
| FStar_Syntax_Syntax.Pat_dot_term (uu____2925) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_wild (uu____2932) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_constant (uu____2933) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (uu____2935, pats1) -> begin
(

let aux = (fun out uu____2973 -> (match (uu____2973) with
| (p2, uu____2985) -> begin
(

let intersection = (

let uu____2993 = (pat_vars p2)
in (FStar_Util.set_intersect uu____2993 out))
in (

let uu____2996 = (FStar_Util.set_is_empty intersection)
in (match (uu____2996) with
| true -> begin
(

let uu____2999 = (pat_vars p2)
in (FStar_Util.set_union out uu____2999))
end
| uu____3002 -> begin
(

let duplicate_bv = (

let uu____3004 = (FStar_Util.set_elements intersection)
in (FStar_List.hd uu____3004))
in (

let uu____3007 = (

let uu____3012 = (FStar_Util.format1 "Non-linear patterns are not permitted. %s appears more than once in this pattern." duplicate_bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in ((FStar_Errors.Fatal_NonLinearPatternNotPermitted), (uu____3012)))
in (FStar_Errors.raise_error uu____3007 r)))
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

let uu____3032 = (pat_vars p1)
in (FStar_All.pipe_right uu____3032 (fun a238 -> ())))
end
| (p1)::ps -> begin
(

let pvars = (pat_vars p1)
in (

let aux = (fun p2 -> (

let uu____3060 = (

let uu____3061 = (pat_vars p2)
in (FStar_Util.set_eq pvars uu____3061))
in (match (uu____3060) with
| true -> begin
()
end
| uu____3064 -> begin
(

let nonlinear_vars = (

let uu____3068 = (pat_vars p2)
in (FStar_Util.set_symmetric_difference pvars uu____3068))
in (

let first_nonlinear_var = (

let uu____3072 = (FStar_Util.set_elements nonlinear_vars)
in (FStar_List.hd uu____3072))
in (

let uu____3075 = (

let uu____3080 = (FStar_Util.format1 "Patterns in this match are incoherent, variable %s is bound in some but not all patterns." first_nonlinear_var.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in ((FStar_Errors.Fatal_IncoherentPatterns), (uu____3080)))
in (FStar_Errors.raise_error uu____3075 r))))
end)))
in (FStar_List.iter aux ps)))
end)))
in ((match (((is_mut), (p.FStar_Parser_AST.pat))) with
| (false, uu____3084) -> begin
()
end
| (true, FStar_Parser_AST.PatVar (uu____3085)) -> begin
()
end
| (true, uu____3092) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_LetMutableForVariablesOnly), ("let-mutable is for variables only")) p.FStar_Parser_AST.prange)
end);
(

let resolvex = (fun l e x -> (

let uu____3115 = (FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (Prims.op_Equality y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText x.FStar_Ident.idText))))
in (match (uu____3115) with
| FStar_Pervasives_Native.Some (y) -> begin
((l), (e), (y))
end
| uu____3131 -> begin
(

let uu____3134 = (match (is_mut) with
| true -> begin
(FStar_Syntax_DsEnv.push_bv_mutable e x)
end
| uu____3143 -> begin
(FStar_Syntax_DsEnv.push_bv e x)
end)
in (match (uu____3134) with
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
| FStar_Parser_AST.PatOr (uu____3246) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.PatOp (op) -> begin
(

let uu____3262 = (

let uu____3263 = (

let uu____3264 = (

let uu____3271 = (

let uu____3272 = (

let uu____3277 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") op.FStar_Ident.idText op.FStar_Ident.idRange)
in ((uu____3277), (op.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____3272))
in ((uu____3271), (FStar_Pervasives_Native.None)))
in FStar_Parser_AST.PatVar (uu____3264))
in {FStar_Parser_AST.pat = uu____3263; FStar_Parser_AST.prange = p1.FStar_Parser_AST.prange})
in (aux loc env1 uu____3262))
end
| FStar_Parser_AST.PatAscribed (p2, (t, tacopt)) -> begin
((match (tacopt) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (uu____3294) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly), ("Type ascriptions within patterns are cannot be associated with a tactic")) orig.FStar_Parser_AST.prange)
end);
(

let uu____3295 = (aux loc env1 p2)
in (match (uu____3295) with
| (loc1, env', binder, p3, imp) -> begin
(

let annot_pat_var = (fun p4 t1 -> (match (p4.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu___114_3353 = p4
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var ((

let uu___115_3358 = x
in {FStar_Syntax_Syntax.ppname = uu___115_3358.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___115_3358.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})); FStar_Syntax_Syntax.p = uu___114_3353.FStar_Syntax_Syntax.p})
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu___116_3360 = p4
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild ((

let uu___117_3365 = x
in {FStar_Syntax_Syntax.ppname = uu___117_3365.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___117_3365.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})); FStar_Syntax_Syntax.p = uu___116_3360.FStar_Syntax_Syntax.p})
end
| uu____3366 when top -> begin
p4
end
| uu____3367 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly), ("Type ascriptions within patterns are only allowed on variables")) orig.FStar_Parser_AST.prange)
end))
in (

let uu____3370 = (match (binder) with
| LetBinder (uu____3383) -> begin
(failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t1 = (

let uu____3403 = (close_fun env1 t)
in (desugar_term env1 uu____3403))
in ((match ((match (x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
false
end
| uu____3405 -> begin
true
end)) with
| true -> begin
(

let uu____3406 = (

let uu____3411 = (

let uu____3412 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____3413 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____3414 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n" uu____3412 uu____3413 uu____3414))))
in ((FStar_Errors.Warning_MultipleAscriptions), (uu____3411)))
in (FStar_Errors.log_issue orig.FStar_Parser_AST.prange uu____3406))
end
| uu____3415 -> begin
()
end);
(

let uu____3416 = (annot_pat_var p3 t1)
in ((uu____3416), (LocalBinder ((((

let uu___118_3422 = x
in {FStar_Syntax_Syntax.ppname = uu___118_3422.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___118_3422.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})), (aq))))));
))
end)
in (match (uu____3370) with
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

let uu____3444 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3444), (false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____3453 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3453), (false))))
end
| FStar_Parser_AST.PatTvar (x, aq) -> begin
(

let imp = (Prims.op_Equality aq (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))
in (

let aq1 = (trans_aqual aq)
in (

let uu____3472 = (resolvex loc env1 x)
in (match (uu____3472) with
| (loc1, env2, xbv) -> begin
(

let uu____3494 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc1), (env2), (LocalBinder (((xbv), (aq1)))), (uu____3494), (imp)))
end))))
end
| FStar_Parser_AST.PatVar (x, aq) -> begin
(

let imp = (Prims.op_Equality aq (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))
in (

let aq1 = (trans_aqual aq)
in (

let uu____3513 = (resolvex loc env1 x)
in (match (uu____3513) with
| (loc1, env2, xbv) -> begin
(

let uu____3535 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc1), (env2), (LocalBinder (((xbv), (aq1)))), (uu____3535), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l1 = (FStar_Syntax_DsEnv.fail_or env1 (FStar_Syntax_DsEnv.try_lookup_datacon env1) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____3545 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), ([])))))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3545), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = uu____3567}, args) -> begin
(

let uu____3573 = (FStar_List.fold_right (fun arg uu____3614 -> (match (uu____3614) with
| (loc1, env2, args1) -> begin
(

let uu____3662 = (aux loc1 env2 arg)
in (match (uu____3662) with
| (loc2, env3, uu____3691, arg1, imp) -> begin
((loc2), (env3), ((((arg1), (imp)))::args1))
end))
end)) args ((loc), (env1), ([])))
in (match (uu____3573) with
| (loc1, env2, args1) -> begin
(

let l1 = (FStar_Syntax_DsEnv.fail_or env2 (FStar_Syntax_DsEnv.try_lookup_datacon env2) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____3761 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args1)))))
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3761), (false)))))
end))
end
| FStar_Parser_AST.PatApp (uu____3776) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedPattern), ("Unexpected pattern")) p1.FStar_Parser_AST.prange)
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____3798 = (FStar_List.fold_right (fun pat uu____3831 -> (match (uu____3831) with
| (loc1, env2, pats1) -> begin
(

let uu____3863 = (aux loc1 env2 pat)
in (match (uu____3863) with
| (loc2, env3, uu____3888, pat1, uu____3890) -> begin
((loc2), (env3), ((pat1)::pats1))
end))
end)) pats ((loc), (env1), ([])))
in (match (uu____3798) with
| (loc1, env2, pats1) -> begin
(

let pat = (

let uu____3933 = (

let uu____3936 = (

let uu____3943 = (FStar_Range.end_range p1.FStar_Parser_AST.prange)
in (pos_r uu____3943))
in (

let uu____3944 = (

let uu____3945 = (

let uu____3958 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____3958), ([])))
in FStar_Syntax_Syntax.Pat_cons (uu____3945))
in (FStar_All.pipe_left uu____3936 uu____3944)))
in (FStar_List.fold_right (fun hd1 tl1 -> (

let r = (FStar_Range.union_ranges hd1.FStar_Syntax_Syntax.p tl1.FStar_Syntax_Syntax.p)
in (

let uu____3990 = (

let uu____3991 = (

let uu____4004 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____4004), ((((hd1), (false)))::(((tl1), (false)))::[])))
in FStar_Syntax_Syntax.Pat_cons (uu____3991))
in (FStar_All.pipe_left (pos_r r) uu____3990)))) pats1 uu____3933))
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep1) -> begin
(

let uu____4046 = (FStar_List.fold_left (fun uu____4086 p2 -> (match (uu____4086) with
| (loc1, env2, pats) -> begin
(

let uu____4135 = (aux loc1 env2 p2)
in (match (uu____4135) with
| (loc2, env3, uu____4164, pat, uu____4166) -> begin
((loc2), (env3), ((((pat), (false)))::pats))
end))
end)) ((loc), (env1), ([])) args)
in (match (uu____4046) with
| (loc1, env2, args1) -> begin
(

let args2 = (FStar_List.rev args1)
in (

let l = (match (dep1) with
| true -> begin
(FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end
| uu____4254 -> begin
(FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end)
in (

let uu____4261 = (FStar_Syntax_DsEnv.fail_or env2 (FStar_Syntax_DsEnv.try_lookup_lid env2) l)
in (match (uu____4261) with
| (constr, uu____4283) -> begin
(

let l1 = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____4286 -> begin
(failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____4288 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args2)))))
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____4288), (false)))))
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

let fields1 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____4357 -> (match (uu____4357) with
| (f, p2) -> begin
((f.FStar_Ident.ident), (p2))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map (fun uu____4387 -> (match (uu____4387) with
| (f, uu____4393) -> begin
(

let uu____4394 = (FStar_All.pipe_right fields1 (FStar_List.tryFind (fun uu____4420 -> (match (uu____4420) with
| (g, uu____4426) -> begin
(Prims.op_Equality f.FStar_Ident.idText g.FStar_Ident.idText)
end))))
in (match (uu____4394) with
| FStar_Pervasives_Native.None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p1.FStar_Parser_AST.prange)
end
| FStar_Pervasives_Native.Some (uu____4431, p2) -> begin
p2
end))
end))))
in (

let app = (

let uu____4438 = (

let uu____4439 = (

let uu____4446 = (

let uu____4447 = (

let uu____4448 = (FStar_Ident.lid_of_ids (FStar_List.append record.FStar_Syntax_DsEnv.typename.FStar_Ident.ns ((record.FStar_Syntax_DsEnv.constrname)::[])))
in FStar_Parser_AST.PatName (uu____4448))
in (FStar_Parser_AST.mk_pattern uu____4447 p1.FStar_Parser_AST.prange))
in ((uu____4446), (args)))
in FStar_Parser_AST.PatApp (uu____4439))
in (FStar_Parser_AST.mk_pattern uu____4438 p1.FStar_Parser_AST.prange))
in (

let uu____4451 = (aux loc env1 app)
in (match (uu____4451) with
| (env2, e, b, p2, uu____4480) -> begin
(

let p3 = (match (p2.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args1) -> begin
(

let uu____4508 = (

let uu____4509 = (

let uu____4522 = (

let uu___119_4523 = fv
in (

let uu____4524 = (

let uu____4527 = (

let uu____4528 = (

let uu____4535 = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map FStar_Pervasives_Native.fst))
in ((record.FStar_Syntax_DsEnv.typename), (uu____4535)))
in FStar_Syntax_Syntax.Record_ctor (uu____4528))
in FStar_Pervasives_Native.Some (uu____4527))
in {FStar_Syntax_Syntax.fv_name = uu___119_4523.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = uu___119_4523.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu____4524}))
in ((uu____4522), (args1)))
in FStar_Syntax_Syntax.Pat_cons (uu____4509))
in (FStar_All.pipe_left pos uu____4508))
end
| uu____4562 -> begin
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

let uu____4616 = (aux' true loc env1 p2)
in (match (uu____4616) with
| (loc1, env2, var, p3, uu____4643) -> begin
(

let uu____4648 = (FStar_List.fold_left (fun uu____4680 p4 -> (match (uu____4680) with
| (loc2, env3, ps1) -> begin
(

let uu____4713 = (aux' true loc2 env3 p4)
in (match (uu____4713) with
| (loc3, env4, uu____4738, p5, uu____4740) -> begin
((loc3), (env4), ((p5)::ps1))
end))
end)) ((loc1), (env2), ([])) ps)
in (match (uu____4648) with
| (loc2, env3, ps1) -> begin
(

let pats = (p3)::(FStar_List.rev ps1)
in ((env3), (var), (pats)))
end))
end))
end
| uu____4791 -> begin
(

let uu____4792 = (aux' true loc env1 p1)
in (match (uu____4792) with
| (loc1, env2, vars, pat, b) -> begin
((env2), (vars), ((pat)::[]))
end))
end)))
in (

let uu____4832 = (aux_maybe_or env p)
in (match (uu____4832) with
| (env1, b, pats) -> begin
((check_linear_pattern_variables pats p.FStar_Parser_AST.prange);
((env1), (b), (pats));
)
end)))));
)))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.list) = (fun top env p is_mut -> (

let mklet = (fun x -> (

let uu____4891 = (

let uu____4892 = (

let uu____4903 = (FStar_Syntax_DsEnv.qualify env x)
in ((uu____4903), (((FStar_Syntax_Syntax.tun), (FStar_Pervasives_Native.None)))))
in LetBinder (uu____4892))
in ((env), (uu____4891), ([]))))
in (match (top) with
| true -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(

let uu____4931 = (

let uu____4932 = (

let uu____4937 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") x.FStar_Ident.idText x.FStar_Ident.idRange)
in ((uu____4937), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____4932))
in (mklet uu____4931))
end
| FStar_Parser_AST.PatVar (x, uu____4939) -> begin
(mklet x)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____4945); FStar_Parser_AST.prange = uu____4946}, (t, tacopt)) -> begin
(

let tacopt1 = (FStar_Util.map_opt tacopt (desugar_term env))
in (

let uu____4966 = (

let uu____4967 = (

let uu____4978 = (FStar_Syntax_DsEnv.qualify env x)
in (

let uu____4979 = (

let uu____4986 = (desugar_term env t)
in ((uu____4986), (tacopt1)))
in ((uu____4978), (uu____4979))))
in LetBinder (uu____4967))
in ((env), (uu____4966), ([]))))
end
| uu____4997 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedPattern), ("Unexpected pattern at the top-level")) p.FStar_Parser_AST.prange)
end)
end
| uu____5006 -> begin
(

let uu____5007 = (desugar_data_pat env p is_mut)
in (match (uu____5007) with
| (env1, binder, p1) -> begin
(

let p2 = (match (p1) with
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (uu____5036); FStar_Syntax_Syntax.p = uu____5037})::[] -> begin
[]
end
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (uu____5038); FStar_Syntax_Syntax.p = uu____5039})::[] -> begin
[]
end
| uu____5040 -> begin
p1
end)
in ((env1), (binder), (p2)))
end))
end)))
and desugar_binding_pat : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.list) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat Prims.list) = (fun uu____5047 env pat -> (

let uu____5050 = (desugar_data_pat env pat false)
in (match (uu____5050) with
| (env1, uu____5066, pat1) -> begin
((env1), (pat1))
end)))
and desugar_match_pat : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat Prims.list) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term_aq : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations) = (fun env e -> (

let env1 = (FStar_Syntax_DsEnv.set_expect_typ env false)
in (desugar_term_maybe_top false env1 e)))
and desugar_term : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let uu____5085 = (desugar_term_aq env e)
in (match (uu____5085) with
| (t, aq) -> begin
((check_no_aq aq);
t;
)
end)))
and desugar_typ_aq : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations) = (fun env e -> (

let env1 = (FStar_Syntax_DsEnv.set_expect_typ env true)
in (desugar_term_maybe_top false env1 e)))
and desugar_typ : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let uu____5102 = (desugar_typ_aq env e)
in (match (uu____5102) with
| (t, aq) -> begin
((check_no_aq aq);
t;
)
end)))
and desugar_machine_integer : FStar_Syntax_DsEnv.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun env repr uu____5112 range -> (match (uu____5112) with
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

let uu____5122 = (

let uu____5123 = (FStar_Const.within_bounds repr signedness width)
in (not (uu____5123)))
in (match (uu____5122) with
| true -> begin
(

let uu____5124 = (

let uu____5129 = (FStar_Util.format2 "%s is not in the expected range for %s" repr tnm)
in ((FStar_Errors.Error_OutOfRange), (uu____5129)))
in (FStar_Errors.log_issue range uu____5124))
end
| uu____5130 -> begin
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

let uu____5134 = (FStar_Ident.path_of_text intro_nm)
in (FStar_Ident.lid_of_path uu____5134 range))
in (

let lid1 = (

let uu____5138 = (FStar_Syntax_DsEnv.try_lookup_lid env lid)
in (match (uu____5138) with
| FStar_Pervasives_Native.Some (intro_term, uu____5148) -> begin
(match (intro_term.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let private_lid = (

let uu____5157 = (FStar_Ident.path_of_text private_intro_nm)
in (FStar_Ident.lid_of_path uu____5157 range))
in (

let private_fv = (

let uu____5159 = (FStar_Syntax_Util.incr_delta_depth fv.FStar_Syntax_Syntax.fv_delta)
in (FStar_Syntax_Syntax.lid_as_fv private_lid uu____5159 fv.FStar_Syntax_Syntax.fv_qual))
in (

let uu___120_5160 = intro_term
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (private_fv); FStar_Syntax_Syntax.pos = uu___120_5160.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___120_5160.FStar_Syntax_Syntax.vars})))
end
| uu____5161 -> begin
(failwith (Prims.strcat "Unexpected non-fvar for " intro_nm))
end)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5168 = (

let uu____5173 = (FStar_Util.format1 "Unexpected numeric literal.  Restart F* to load %s." tnm)
in ((FStar_Errors.Fatal_UnexpectedNumericLiteral), (uu____5173)))
in (FStar_Errors.raise_error uu____5168 range))
end))
in (

let repr1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (FStar_Pervasives_Native.None))))) FStar_Pervasives_Native.None range)
in (

let uu____5189 = (

let uu____5196 = (

let uu____5197 = (

let uu____5212 = (

let uu____5221 = (

let uu____5228 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr1), (uu____5228)))
in (uu____5221)::[])
in ((lid1), (uu____5212)))
in FStar_Syntax_Syntax.Tm_app (uu____5197))
in (FStar_Syntax_Syntax.mk uu____5196))
in (uu____5189 FStar_Pervasives_Native.None range)))))));
))
end))
and desugar_name : (FStar_Syntax_Syntax.term'  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  env_t  ->  Prims.bool  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.term = (fun mk1 setpos env resolve l -> (

let uu____5267 = (

let uu____5276 = ((match (resolve) with
| true -> begin
FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
end
| uu____5291 -> begin
FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve
end) env)
in (FStar_Syntax_DsEnv.fail_or env uu____5276 l))
in (match (uu____5267) with
| (tm, mut, attrs) -> begin
(

let warn_if_deprecated = (fun attrs1 -> (FStar_List.iter (fun a -> (match (a.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____5331; FStar_Syntax_Syntax.vars = uu____5332}, args) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v FStar_Parser_Const.deprecated_attr) -> begin
(

let msg = (

let uu____5355 = (FStar_Syntax_Print.term_to_string tm)
in (Prims.strcat uu____5355 " is deprecated"))
in (

let msg1 = (match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5363 = (

let uu____5364 = (

let uu____5367 = (FStar_List.hd args)
in (FStar_Pervasives_Native.fst uu____5367))
in uu____5364.FStar_Syntax_Syntax.n)
in (match (uu____5363) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____5383)) when (not ((Prims.op_Equality (FStar_Util.trim_string s) ""))) -> begin
(Prims.strcat msg (Prims.strcat ", use " (Prims.strcat s " instead")))
end
| uu____5384 -> begin
msg
end))
end
| uu____5385 -> begin
msg
end)
in (

let uu____5386 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.log_issue uu____5386 ((FStar_Errors.Warning_DeprecatedDefinition), (msg1))))))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v FStar_Parser_Const.deprecated_attr) -> begin
(

let msg = (

let uu____5389 = (FStar_Syntax_Print.term_to_string tm)
in (Prims.strcat uu____5389 " is deprecated"))
in (

let uu____5390 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.log_issue uu____5390 ((FStar_Errors.Warning_DeprecatedDefinition), (msg)))))
end
| uu____5391 -> begin
()
end)) attrs1))
in ((warn_if_deprecated attrs);
(

let tm1 = (setpos tm)
in (match (mut) with
| true -> begin
(

let uu____5396 = (

let uu____5397 = (

let uu____5404 = (mk_ref_read tm1)
in ((uu____5404), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval))))
in FStar_Syntax_Syntax.Tm_meta (uu____5397))
in (FStar_All.pipe_left mk1 uu____5396))
end
| uu____5409 -> begin
tm1
end));
))
end)))
and desugar_attributes : env_t  ->  FStar_Parser_AST.term Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun env cattributes -> (

let desugar_attribute = (fun t -> (

let uu____5422 = (

let uu____5423 = (unparen t)
in uu____5423.FStar_Parser_AST.tm)
in (match (uu____5422) with
| FStar_Parser_AST.Var ({FStar_Ident.ns = uu____5424; FStar_Ident.ident = uu____5425; FStar_Ident.nsstr = uu____5426; FStar_Ident.str = "cps"}) -> begin
FStar_Syntax_Syntax.CPS
end
| uu____5429 -> begin
(

let uu____5430 = (

let uu____5435 = (

let uu____5436 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "Unknown attribute " uu____5436))
in ((FStar_Errors.Fatal_UnknownAttribute), (uu____5435)))
in (FStar_Errors.raise_error uu____5430 t.FStar_Parser_AST.range))
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

let uu___121_5531 = e
in {FStar_Syntax_Syntax.n = uu___121_5531.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___121_5531.FStar_Syntax_Syntax.vars}))
in (

let uu____5534 = (

let uu____5535 = (unparen top)
in uu____5535.FStar_Parser_AST.tm)
in (match (uu____5534) with
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

let uu____5554 = (desugar_formula env t)
in ((uu____5554), (noaqs)))
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(

let uu____5561 = (desugar_formula env t)
in ((uu____5561), (noaqs)))
end
| FStar_Parser_AST.Attributes (ts) -> begin
(failwith "Attributes should not be desugared by desugar_term_maybe_top")
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (i, FStar_Pervasives_Native.Some (size))) -> begin
(

let uu____5585 = (desugar_machine_integer env i size top.FStar_Parser_AST.range)
in ((uu____5585), (noaqs)))
end
| FStar_Parser_AST.Const (c) -> begin
(

let uu____5587 = (mk1 (FStar_Syntax_Syntax.Tm_constant (c)))
in ((uu____5587), (noaqs)))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "=!="; FStar_Ident.idRange = r}, args) -> begin
(

let e = (

let uu____5595 = (

let uu____5596 = (

let uu____5603 = (FStar_Ident.mk_ident (("=="), (r)))
in ((uu____5603), (args)))
in FStar_Parser_AST.Op (uu____5596))
in (FStar_Parser_AST.mk_term uu____5595 top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
in (

let uu____5606 = (

let uu____5607 = (

let uu____5608 = (

let uu____5615 = (FStar_Ident.mk_ident (("~"), (r)))
in ((uu____5615), ((e)::[])))
in FStar_Parser_AST.Op (uu____5608))
in (FStar_Parser_AST.mk_term uu____5607 top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
in (desugar_term_aq env uu____5606)))
end
| FStar_Parser_AST.Op (op_star, (uu____5619)::(uu____5620)::[]) when ((

let uu____5625 = (FStar_Ident.text_of_id op_star)
in (Prims.op_Equality uu____5625 "*")) && (

let uu____5627 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range op_star)
in (FStar_All.pipe_right uu____5627 FStar_Option.isNone))) -> begin
(

let rec flatten1 = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____5642}, (t1)::(t2)::[]) -> begin
(

let uu____5647 = (flatten1 t1)
in (FStar_List.append uu____5647 ((t2)::[])))
end
| uu____5650 -> begin
(t)::[]
end))
in (

let uu____5651 = (

let uu____5660 = (

let uu____5667 = (

let uu____5670 = (unparen top)
in (flatten1 uu____5670))
in (FStar_All.pipe_right uu____5667 (FStar_List.map (fun t -> (

let uu____5689 = (desugar_typ_aq env t)
in (match (uu____5689) with
| (t', aq) -> begin
(

let uu____5700 = (FStar_Syntax_Syntax.as_arg t')
in ((uu____5700), (aq)))
end))))))
in (FStar_All.pipe_right uu____5660 FStar_List.unzip))
in (match (uu____5651) with
| (targs, aqs) -> begin
(

let uu____5729 = (

let uu____5734 = (FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_lid env) uu____5734))
in (match (uu____5729) with
| (tup, uu____5744) -> begin
(

let uu____5745 = (mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
in ((uu____5745), ((join_aqs aqs))))
end))
end)))
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____5757 = (

let uu____5758 = (

let uu____5761 = (FStar_Syntax_DsEnv.fail_or2 (FStar_Syntax_DsEnv.try_lookup_id env) a)
in (FStar_Pervasives_Native.fst uu____5761))
in (FStar_All.pipe_left setpos uu____5758))
in ((uu____5757), (noaqs)))
end
| FStar_Parser_AST.Uvar (u) -> begin
(

let uu____5775 = (

let uu____5780 = (

let uu____5781 = (

let uu____5782 = (FStar_Ident.text_of_id u)
in (Prims.strcat uu____5782 " in non-universe context"))
in (Prims.strcat "Unexpected universe variable " uu____5781))
in ((FStar_Errors.Fatal_UnexpectedUniverseVariable), (uu____5780)))
in (FStar_Errors.raise_error uu____5775 top.FStar_Parser_AST.range))
end
| FStar_Parser_AST.Op (s, args) -> begin
(

let uu____5793 = (op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)
in (match (uu____5793) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5800 = (

let uu____5805 = (

let uu____5806 = (FStar_Ident.text_of_id s)
in (Prims.strcat "Unexpected or unbound operator: " uu____5806))
in ((FStar_Errors.Fatal_UnepxectedOrUnboundOperator), (uu____5805)))
in (FStar_Errors.raise_error uu____5800 top.FStar_Parser_AST.range))
end
| FStar_Pervasives_Native.Some (op) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5816 = (

let uu____5841 = (FStar_All.pipe_right args (FStar_List.map (fun t -> (

let uu____5893 = (desugar_term_aq env t)
in (match (uu____5893) with
| (t', s1) -> begin
((((t'), (FStar_Pervasives_Native.None))), (s1))
end)))))
in (FStar_All.pipe_right uu____5841 FStar_List.unzip))
in (match (uu____5816) with
| (args1, aqs) -> begin
(

let uu____6026 = (mk1 (FStar_Syntax_Syntax.Tm_app (((op), (args1)))))
in ((uu____6026), ((join_aqs aqs))))
end))
end
| uu____6037 -> begin
((op), (noaqs))
end)
end))
end
| FStar_Parser_AST.Construct (n1, ((a, uu____6040))::[]) when (Prims.op_Equality n1.FStar_Ident.str "SMTPat") -> begin
(

let uu____6055 = (

let uu___122_6056 = top
in (

let uu____6057 = (

let uu____6058 = (

let uu____6065 = (

let uu___123_6066 = top
in (

let uu____6067 = (

let uu____6068 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____6068))
in {FStar_Parser_AST.tm = uu____6067; FStar_Parser_AST.range = uu___123_6066.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___123_6066.FStar_Parser_AST.level}))
in ((uu____6065), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____6058))
in {FStar_Parser_AST.tm = uu____6057; FStar_Parser_AST.range = uu___122_6056.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___122_6056.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____6055))
end
| FStar_Parser_AST.Construct (n1, ((a, uu____6071))::[]) when (Prims.op_Equality n1.FStar_Ident.str "SMTPatT") -> begin
((FStar_Errors.log_issue top.FStar_Parser_AST.range ((FStar_Errors.Warning_SMTPatTDeprecated), ("SMTPatT is deprecated; please just use SMTPat")));
(

let uu____6087 = (

let uu___124_6088 = top
in (

let uu____6089 = (

let uu____6090 = (

let uu____6097 = (

let uu___125_6098 = top
in (

let uu____6099 = (

let uu____6100 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____6100))
in {FStar_Parser_AST.tm = uu____6099; FStar_Parser_AST.range = uu___125_6098.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___125_6098.FStar_Parser_AST.level}))
in ((uu____6097), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____6090))
in {FStar_Parser_AST.tm = uu____6089; FStar_Parser_AST.range = uu___124_6088.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___124_6088.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____6087));
)
end
| FStar_Parser_AST.Construct (n1, ((a, uu____6103))::[]) when (Prims.op_Equality n1.FStar_Ident.str "SMTPatOr") -> begin
(

let uu____6118 = (

let uu___126_6119 = top
in (

let uu____6120 = (

let uu____6121 = (

let uu____6128 = (

let uu___127_6129 = top
in (

let uu____6130 = (

let uu____6131 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat_or")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____6131))
in {FStar_Parser_AST.tm = uu____6130; FStar_Parser_AST.range = uu___127_6129.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___127_6129.FStar_Parser_AST.level}))
in ((uu____6128), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____6121))
in {FStar_Parser_AST.tm = uu____6120; FStar_Parser_AST.range = uu___126_6119.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___126_6119.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____6118))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____6132; FStar_Ident.ident = uu____6133; FStar_Ident.nsstr = uu____6134; FStar_Ident.str = "Type0"}) -> begin
(

let uu____6137 = (mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
in ((uu____6137), (noaqs)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____6138; FStar_Ident.ident = uu____6139; FStar_Ident.nsstr = uu____6140; FStar_Ident.str = "Type"}) -> begin
(

let uu____6143 = (mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
in ((uu____6143), (noaqs)))
end
| FStar_Parser_AST.Construct ({FStar_Ident.ns = uu____6144; FStar_Ident.ident = uu____6145; FStar_Ident.nsstr = uu____6146; FStar_Ident.str = "Type"}, ((t, FStar_Parser_AST.UnivApp))::[]) -> begin
(

let uu____6164 = (

let uu____6165 = (

let uu____6166 = (desugar_universe t)
in FStar_Syntax_Syntax.Tm_type (uu____6166))
in (mk1 uu____6165))
in ((uu____6164), (noaqs)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____6167; FStar_Ident.ident = uu____6168; FStar_Ident.nsstr = uu____6169; FStar_Ident.str = "Effect"}) -> begin
(

let uu____6172 = (mk1 (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
in ((uu____6172), (noaqs)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____6173; FStar_Ident.ident = uu____6174; FStar_Ident.nsstr = uu____6175; FStar_Ident.str = "True"}) -> begin
(

let uu____6178 = (

let uu____6179 = (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar uu____6179 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in ((uu____6178), (noaqs)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____6180; FStar_Ident.ident = uu____6181; FStar_Ident.nsstr = uu____6182; FStar_Ident.str = "False"}) -> begin
(

let uu____6185 = (

let uu____6186 = (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar uu____6186 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in ((uu____6185), (noaqs)))
end
| FStar_Parser_AST.Projector (eff_name, {FStar_Ident.idText = txt; FStar_Ident.idRange = uu____6189}) when ((is_special_effect_combinator txt) && (FStar_Syntax_DsEnv.is_effect_name env eff_name)) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name);
(

let uu____6191 = (FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name)
in (match (uu____6191) with
| FStar_Pervasives_Native.Some (ed) -> begin
(

let lid = (FStar_Syntax_Util.dm4f_lid ed txt)
in (

let uu____6200 = (FStar_Syntax_Syntax.fvar lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in ((uu____6200), (noaqs))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____6201 = (

let uu____6202 = (FStar_Ident.text_of_lid eff_name)
in (FStar_Util.format2 "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)" uu____6202 txt))
in (failwith uu____6201))
end));
)
end
| FStar_Parser_AST.Var (l) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l);
(

let uu____6209 = (desugar_name mk1 setpos env true l)
in ((uu____6209), (noaqs)));
)
end
| FStar_Parser_AST.Name (l) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l);
(

let uu____6212 = (desugar_name mk1 setpos env true l)
in ((uu____6212), (noaqs)));
)
end
| FStar_Parser_AST.Projector (l, i) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l);
(

let name = (

let uu____6223 = (FStar_Syntax_DsEnv.try_lookup_datacon env l)
in (match (uu____6223) with
| FStar_Pervasives_Native.Some (uu____6232) -> begin
FStar_Pervasives_Native.Some (((true), (l)))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____6237 = (FStar_Syntax_DsEnv.try_lookup_root_effect_name env l)
in (match (uu____6237) with
| FStar_Pervasives_Native.Some (new_name) -> begin
FStar_Pervasives_Native.Some (((false), (new_name)))
end
| uu____6251 -> begin
FStar_Pervasives_Native.None
end))
end))
in (match (name) with
| FStar_Pervasives_Native.Some (resolve, new_name) -> begin
(

let uu____6268 = (

let uu____6269 = (FStar_Syntax_Util.mk_field_projector_name_from_ident new_name i)
in (desugar_name mk1 setpos env resolve uu____6269))
in ((uu____6268), (noaqs)))
end
| uu____6270 -> begin
(

let uu____6277 = (

let uu____6282 = (FStar_Util.format1 "Data constructor or effect %s not found" l.FStar_Ident.str)
in ((FStar_Errors.Fatal_EffectNotFound), (uu____6282)))
in (FStar_Errors.raise_error uu____6277 top.FStar_Parser_AST.range))
end));
)
end
| FStar_Parser_AST.Discrim (lid) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid);
(

let uu____6289 = (FStar_Syntax_DsEnv.try_lookup_datacon env lid)
in (match (uu____6289) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6296 = (

let uu____6301 = (FStar_Util.format1 "Data constructor %s not found" lid.FStar_Ident.str)
in ((FStar_Errors.Fatal_DataContructorNotFound), (uu____6301)))
in (FStar_Errors.raise_error uu____6296 top.FStar_Parser_AST.range))
end
| uu____6306 -> begin
(

let lid' = (FStar_Syntax_Util.mk_discriminator lid)
in (

let uu____6310 = (desugar_name mk1 setpos env true lid')
in ((uu____6310), (noaqs))))
end));
)
end
| FStar_Parser_AST.Construct (l, args) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l);
(

let uu____6326 = (FStar_Syntax_DsEnv.try_lookup_datacon env l)
in (match (uu____6326) with
| FStar_Pervasives_Native.Some (head1) -> begin
(

let head2 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (head1)))
in (match (args) with
| [] -> begin
((head2), (noaqs))
end
| uu____6345 -> begin
(

let uu____6352 = (FStar_Util.take (fun uu____6376 -> (match (uu____6376) with
| (uu____6381, imp) -> begin
(Prims.op_Equality imp FStar_Parser_AST.UnivApp)
end)) args)
in (match (uu____6352) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun x -> (desugar_universe (FStar_Pervasives_Native.fst x))) universes)
in (

let uu____6426 = (

let uu____6441 = (FStar_List.map (fun uu____6474 -> (match (uu____6474) with
| (t, imp) -> begin
(

let uu____6491 = (desugar_term_aq env t)
in (match (uu____6491) with
| (te, aq) -> begin
(((arg_withimp_e imp te)), (aq))
end))
end)) args1)
in (FStar_All.pipe_right uu____6441 FStar_List.unzip))
in (match (uu____6426) with
| (args2, aqs) -> begin
(

let head3 = (match ((Prims.op_Equality universes1 [])) with
| true -> begin
head2
end
| uu____6579 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_uinst (((head2), (universes1)))))
end)
in (

let uu____6582 = (mk1 (FStar_Syntax_Syntax.Tm_app (((head3), (args2)))))
in ((uu____6582), ((join_aqs aqs)))))
end)))
end))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let err = (

let uu____6598 = (FStar_Syntax_DsEnv.try_lookup_effect_name env l)
in (match (uu____6598) with
| FStar_Pervasives_Native.None -> begin
((FStar_Errors.Fatal_ConstructorNotFound), ((Prims.strcat "Constructor " (Prims.strcat l.FStar_Ident.str " not found"))))
end
| FStar_Pervasives_Native.Some (uu____6605) -> begin
((FStar_Errors.Fatal_UnexpectedEffect), ((Prims.strcat "Effect " (Prims.strcat l.FStar_Ident.str " used at an unexpected position"))))
end))
in (FStar_Errors.raise_error err top.FStar_Parser_AST.range))
end));
)
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let uu____6616 = (FStar_List.fold_left (fun uu____6645 b -> (match (uu____6645) with
| (env1, tparams, typs) -> begin
(

let uu____6670 = (desugar_binder env1 b)
in (match (uu____6670) with
| (xopt, t1) -> begin
(

let uu____6691 = (match (xopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6700 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env1), (uu____6700)))
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_DsEnv.push_bv env1 x)
end)
in (match (uu____6691) with
| (env2, x) -> begin
(

let uu____6712 = (

let uu____6715 = (

let uu____6718 = (

let uu____6719 = (no_annot_abs tparams t1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____6719))
in (uu____6718)::[])
in (FStar_List.append typs uu____6715))
in ((env2), ((FStar_List.append tparams (((((

let uu___128_6737 = x
in {FStar_Syntax_Syntax.ppname = uu___128_6737.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___128_6737.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})), (FStar_Pervasives_Native.None)))::[]))), (uu____6712)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type_level FStar_Pervasives_Native.None))::[])))
in (match (uu____6616) with
| (env1, uu____6755, targs) -> begin
(

let uu____6761 = (

let uu____6766 = (FStar_Parser_Const.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Syntax_DsEnv.fail_or env1 (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____6766))
in (match (uu____6761) with
| (tup, uu____6776) -> begin
(

let uu____6777 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
in ((uu____6777), (noaqs)))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let uu____6796 = (uncurry binders t)
in (match (uu____6796) with
| (bs, t1) -> begin
(

let rec aux = (fun env1 bs1 uu___94_6838 -> (match (uu___94_6838) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range env1 t1)
in (

let uu____6852 = (FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod)
in (FStar_All.pipe_left setpos uu____6852)))
end
| (hd1)::tl1 -> begin
(

let bb = (desugar_binder env1 hd1)
in (

let uu____6874 = (as_binder env1 hd1.FStar_Parser_AST.aqual bb)
in (match (uu____6874) with
| (b, env2) -> begin
(aux env2 ((b)::bs1) tl1)
end)))
end))
in (

let uu____6883 = (aux env [] bs)
in ((uu____6883), (noaqs))))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(

let uu____6890 = (desugar_binder env b)
in (match (uu____6890) with
| (FStar_Pervasives_Native.None, uu____6901) -> begin
(failwith "Missing binder in refinement")
end
| b1 -> begin
(

let uu____6915 = (as_binder env FStar_Pervasives_Native.None b1)
in (match (uu____6915) with
| ((x, uu____6925), env1) -> begin
(

let f1 = (desugar_formula env1 f)
in (

let uu____6928 = (

let uu____6929 = (FStar_Syntax_Util.refine x f1)
in (FStar_All.pipe_left setpos uu____6929))
in ((uu____6928), (noaqs))))
end))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let binders1 = (FStar_All.pipe_right binders (FStar_List.map replace_unit_pattern))
in (

let uu____6949 = (FStar_List.fold_left (fun uu____6969 pat -> (match (uu____6969) with
| (env1, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (uu____6995, (t, FStar_Pervasives_Native.None)) -> begin
(

let uu____7005 = (

let uu____7008 = (free_type_vars env1 t)
in (FStar_List.append uu____7008 ftvs))
in ((env1), (uu____7005)))
end
| FStar_Parser_AST.PatAscribed (uu____7013, (t, FStar_Pervasives_Native.Some (tac))) -> begin
(

let uu____7024 = (

let uu____7027 = (free_type_vars env1 t)
in (

let uu____7030 = (

let uu____7033 = (free_type_vars env1 tac)
in (FStar_List.append uu____7033 ftvs))
in (FStar_List.append uu____7027 uu____7030)))
in ((env1), (uu____7024)))
end
| uu____7038 -> begin
((env1), (ftvs))
end)
end)) ((env), ([])) binders1)
in (match (uu____6949) with
| (uu____7047, ftv) -> begin
(

let ftv1 = (sort_ftv ftv)
in (

let binders2 = (

let uu____7059 = (FStar_All.pipe_right ftv1 (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append uu____7059 binders1))
in (

let rec aux = (fun env1 bs sc_pat_opt uu___95_7112 -> (match (uu___95_7112) with
| [] -> begin
(

let uu____7135 = (desugar_term_aq env1 body)
in (match (uu____7135) with
| (body1, aq) -> begin
(

let body2 = (match (sc_pat_opt) with
| FStar_Pervasives_Native.Some (sc, pat) -> begin
(

let body2 = (

let uu____7166 = (

let uu____7167 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right uu____7167 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close uu____7166 body1))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (FStar_Pervasives_Native.None), (body2)))::[])))) FStar_Pervasives_Native.None body2.FStar_Syntax_Syntax.pos))
end
| FStar_Pervasives_Native.None -> begin
body1
end)
in (

let uu____7230 = (

let uu____7233 = (no_annot_abs (FStar_List.rev bs) body2)
in (setpos uu____7233))
in ((uu____7230), (aq))))
end))
end
| (p)::rest -> begin
(

let uu____7246 = (desugar_binding_pat env1 p)
in (match (uu____7246) with
| (env2, b, pat) -> begin
(

let pat1 = (match (pat) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (p1)::[] -> begin
FStar_Pervasives_Native.Some (p1)
end
| uu____7274 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnsupportedDisjuctivePatterns), ("Disjunctive patterns are not supported in abstractions")) p.FStar_Parser_AST.prange)
end)
in (

let uu____7279 = (match (b) with
| LetBinder (uu____7312) -> begin
(failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt1 = (match (((pat1), (sc_pat_opt))) with
| (FStar_Pervasives_Native.None, uu____7370) -> begin
sc_pat_opt
end
| (FStar_Pervasives_Native.Some (p1), FStar_Pervasives_Native.None) -> begin
(

let uu____7416 = (

let uu____7423 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____7423), (p1)))
in FStar_Pervasives_Native.Some (uu____7416))
end
| (FStar_Pervasives_Native.Some (p1), FStar_Pervasives_Native.Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (uu____7469), uu____7470) -> begin
(

let tup2 = (

let uu____7472 = (FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____7472 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____7476 = (

let uu____7483 = (

let uu____7484 = (

let uu____7499 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (

let uu____7502 = (

let uu____7511 = (FStar_Syntax_Syntax.as_arg sc)
in (

let uu____7512 = (

let uu____7515 = (

let uu____7516 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____7516))
in (uu____7515)::[])
in (uu____7511)::uu____7512))
in ((uu____7499), (uu____7502))))
in FStar_Syntax_Syntax.Tm_app (uu____7484))
in (FStar_Syntax_Syntax.mk uu____7483))
in (uu____7476 FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
in (

let p2 = (

let uu____7533 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p1), (false)))::[])))) uu____7533))
in FStar_Pervasives_Native.Some (((sc1), (p2))))))
end
| (FStar_Syntax_Syntax.Tm_app (uu____7576, args), FStar_Syntax_Syntax.Pat_cons (uu____7578, pats)) -> begin
(

let tupn = (

let uu____7617 = (FStar_Parser_Const.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____7617 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____7627 = (

let uu____7628 = (

let uu____7643 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (

let uu____7646 = (

let uu____7655 = (

let uu____7664 = (

let uu____7671 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____7671))
in (uu____7664)::[])
in (FStar_List.append args uu____7655))
in ((uu____7643), (uu____7646))))
in FStar_Syntax_Syntax.Tm_app (uu____7628))
in (mk1 uu____7627))
in (

let p2 = (

let uu____7703 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p1), (false)))::[])))))) uu____7703))
in FStar_Pervasives_Native.Some (((sc1), (p2))))))
end
| uu____7744 -> begin
(failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt1)))
end)
in (match (uu____7279) with
| (b1, sc_pat_opt1) -> begin
(aux env2 ((b1)::bs) sc_pat_opt1 rest)
end)))
end))
end))
in (aux env [] FStar_Pervasives_Native.None binders2))))
end)))
end
| FStar_Parser_AST.App (uu____7815, uu____7816, FStar_Parser_AST.UnivApp) -> begin
(

let rec aux = (fun universes e -> (

let uu____7838 = (

let uu____7839 = (unparen e)
in uu____7839.FStar_Parser_AST.tm)
in (match (uu____7838) with
| FStar_Parser_AST.App (e1, t, FStar_Parser_AST.UnivApp) -> begin
(

let univ_arg = (desugar_universe t)
in (aux ((univ_arg)::universes) e1))
end
| uu____7849 -> begin
(

let uu____7850 = (desugar_term_aq env e)
in (match (uu____7850) with
| (head1, aq) -> begin
(

let uu____7863 = (mk1 (FStar_Syntax_Syntax.Tm_uinst (((head1), (universes)))))
in ((uu____7863), (aq)))
end))
end)))
in (aux [] top))
end
| FStar_Parser_AST.App (uu____7870) -> begin
(

let rec aux = (fun args aqs e -> (

let uu____7929 = (

let uu____7930 = (unparen e)
in uu____7930.FStar_Parser_AST.tm)
in (match (uu____7929) with
| FStar_Parser_AST.App (e1, t, imp) when (Prims.op_disEquality imp FStar_Parser_AST.UnivApp) -> begin
(

let uu____7950 = (desugar_term_aq env t)
in (match (uu____7950) with
| (t1, aq) -> begin
(

let arg = (arg_withimp_e imp t1)
in (aux ((arg)::args) ((aq)::aqs) e1))
end))
end
| uu____7986 -> begin
(

let uu____7987 = (desugar_term_aq env e)
in (match (uu____7987) with
| (head1, aq) -> begin
(

let uu____8010 = (mk1 (FStar_Syntax_Syntax.Tm_app (((head1), (args)))))
in ((uu____8010), ((join_aqs ((aq)::aqs)))))
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

let uu____8062 = (FStar_Parser_AST.mkExplicitApp bind1 ((t1)::(k)::[]) top.FStar_Parser_AST.range)
in (desugar_term_aq env uu____8062))))))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(

let t = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), ((((FStar_Pervasives_Native.None), ((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
in (

let uu____8114 = (desugar_term_aq env t)
in (match (uu____8114) with
| (tm, s) -> begin
(

let uu____8125 = (mk1 (FStar_Syntax_Syntax.Tm_meta (((tm), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))))
in ((uu____8125), (s)))
end)))
end
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(

let env1 = (FStar_Syntax_DsEnv.push_namespace env lid)
in (

let uu____8131 = (

let uu____8144 = (FStar_Syntax_DsEnv.expect_typ env1)
in (match (uu____8144) with
| true -> begin
desugar_typ_aq
end
| uu____8155 -> begin
desugar_term_aq
end))
in (uu____8131 env1 e)))
end
| FStar_Parser_AST.Let (qual, lbs, body) -> begin
(

let is_rec = (Prims.op_Equality qual FStar_Parser_AST.Rec)
in (

let ds_let_rec_or_app = (fun uu____8199 -> (

let bindings = lbs
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun uu____8342 -> (match (uu____8342) with
| (attr_opt, (p, def)) -> begin
(

let uu____8400 = (is_app_pattern p)
in (match (uu____8400) with
| true -> begin
(

let uu____8431 = (destruct_app_pattern env top_level p)
in ((attr_opt), (uu____8431), (def)))
end
| uu____8476 -> begin
(match ((FStar_Parser_AST.un_function p def)) with
| FStar_Pervasives_Native.Some (p1, def1) -> begin
(

let uu____8513 = (destruct_app_pattern env top_level p1)
in ((attr_opt), (uu____8513), (def1)))
end
| uu____8558 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id1, uu____8596); FStar_Parser_AST.prange = uu____8597}, t) -> begin
(match (top_level) with
| true -> begin
(

let uu____8645 = (

let uu____8666 = (

let uu____8671 = (FStar_Syntax_DsEnv.qualify env id1)
in FStar_Util.Inr (uu____8671))
in ((uu____8666), ([]), (FStar_Pervasives_Native.Some (t))))
in ((attr_opt), (uu____8645), (def)))
end
| uu____8716 -> begin
((attr_opt), (((FStar_Util.Inl (id1)), ([]), (FStar_Pervasives_Native.Some (t)))), (def))
end)
end
| FStar_Parser_AST.PatVar (id1, uu____8762) -> begin
(match (top_level) with
| true -> begin
(

let uu____8797 = (

let uu____8818 = (

let uu____8823 = (FStar_Syntax_DsEnv.qualify env id1)
in FStar_Util.Inr (uu____8823))
in ((uu____8818), ([]), (FStar_Pervasives_Native.None)))
in ((attr_opt), (uu____8797), (def)))
end
| uu____8868 -> begin
((attr_opt), (((FStar_Util.Inl (id1)), ([]), (FStar_Pervasives_Native.None))), (def))
end)
end
| uu____8913 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedLetBinding), ("Unexpected let binding")) p.FStar_Parser_AST.prange)
end)
end)
end))
end))))
in (

let uu____8944 = (FStar_List.fold_left (fun uu____9017 uu____9018 -> (match (((uu____9017), (uu____9018))) with
| ((env1, fnames, rec_bindings), (_attr_opt, (f, uu____9126, uu____9127), uu____9128)) -> begin
(

let uu____9245 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let uu____9271 = (FStar_Syntax_DsEnv.push_bv env1 x)
in (match (uu____9271) with
| (env2, xx) -> begin
(

let uu____9290 = (

let uu____9293 = (FStar_Syntax_Syntax.mk_binder xx)
in (uu____9293)::rec_bindings)
in ((env2), (FStar_Util.Inl (xx)), (uu____9290)))
end))
end
| FStar_Util.Inr (l) -> begin
(

let uu____9301 = (FStar_Syntax_DsEnv.push_top_level_rec_binding env1 l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in ((uu____9301), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (uu____9245) with
| (env2, lbname, rec_bindings1) -> begin
((env2), ((lbname)::fnames), (rec_bindings1))
end))
end)) ((env), ([]), ([])) funs)
in (match (uu____8944) with
| (env', fnames, rec_bindings) -> begin
(

let fnames1 = (FStar_List.rev fnames)
in (

let rec_bindings1 = (FStar_List.rev rec_bindings)
in (

let desugar_one_def = (fun env1 lbname uu____9449 -> (match (uu____9449) with
| (attrs_opt, (uu____9485, args, result_t), def) -> begin
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

let uu____9573 = (is_comp_type env1 t)
in (match (uu____9573) with
| true -> begin
((

let uu____9575 = (FStar_All.pipe_right args1 (FStar_List.tryFind (fun x -> (

let uu____9585 = (is_var_pattern x)
in (not (uu____9585))))))
in (match (uu____9575) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (p) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ComputationTypeNotAllowed), ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")) p.FStar_Parser_AST.prange)
end));
t;
)
end
| uu____9587 -> begin
(

let uu____9588 = (((FStar_Options.ml_ish ()) && (

let uu____9590 = (FStar_Syntax_DsEnv.try_lookup_effect_name env1 FStar_Parser_Const.effect_ML_lid)
in (FStar_Option.isSome uu____9590))) && ((not (is_rec)) || (Prims.op_disEquality (FStar_List.length args1) (Prims.parse_int "0"))))
in (match (uu____9588) with
| true -> begin
(FStar_Parser_AST.ml_comp t)
end
| uu____9593 -> begin
(FStar_Parser_AST.tot_comp t)
end))
end))
in (

let uu____9594 = (FStar_Range.union_ranges t1.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t1), (tacopt)))) uu____9594 FStar_Parser_AST.Expr)))
end)
in (

let def2 = (match (args1) with
| [] -> begin
def1
end
| uu____9598 -> begin
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

let uu____9613 = (

let uu____9614 = (FStar_Syntax_Util.incr_delta_qualifier body1)
in (FStar_Syntax_Syntax.lid_as_fv l uu____9614 FStar_Pervasives_Native.None))
in FStar_Util.Inr (uu____9613))
end)
in (

let body2 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.close rec_bindings1 body1)
end
| uu____9616 -> begin
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
| uu____9678 -> begin
env
end)) fnames1 funs)
in (

let uu____9679 = (desugar_term_aq env' body)
in (match (uu____9679) with
| (body1, aq) -> begin
(

let uu____9692 = (

let uu____9695 = (

let uu____9696 = (

let uu____9709 = (FStar_Syntax_Subst.close rec_bindings1 body1)
in ((((is_rec), (lbs1))), (uu____9709)))
in FStar_Syntax_Syntax.Tm_let (uu____9696))
in (FStar_All.pipe_left mk1 uu____9695))
in ((uu____9692), (aq)))
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
| uu____9786 -> begin
t11
end)
in (

let uu____9787 = (desugar_binding_pat_maybe_top top_level env pat is_mutable)
in (match (uu____9787) with
| (env1, binder, pat1) -> begin
(

let uu____9809 = (match (binder) with
| LetBinder (l, (t, _tacopt)) -> begin
(

let uu____9835 = (desugar_term_aq env1 t2)
in (match (uu____9835) with
| (body1, aq) -> begin
(

let fv = (

let uu____9849 = (FStar_Syntax_Util.incr_delta_qualifier t12)
in (FStar_Syntax_Syntax.lid_as_fv l uu____9849 FStar_Pervasives_Native.None))
in (

let uu____9850 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_let (((((false), (((mk_lb ((attrs), (FStar_Util.Inr (fv)), (t), (t12), (t12.FStar_Syntax_Syntax.pos))))::[]))), (body1)))))
in ((uu____9850), (aq))))
end))
end
| LocalBinder (x, uu____9880) -> begin
(

let uu____9881 = (desugar_term_aq env1 t2)
in (match (uu____9881) with
| (body1, aq) -> begin
(

let body2 = (match (pat1) with
| [] -> begin
body1
end
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (uu____9895); FStar_Syntax_Syntax.p = uu____9896})::[] -> begin
body1
end
| uu____9897 -> begin
(

let uu____9900 = (

let uu____9907 = (

let uu____9908 = (

let uu____9931 = (FStar_Syntax_Syntax.bv_to_name x)
in (

let uu____9934 = (desugar_disjunctive_pattern pat1 FStar_Pervasives_Native.None body1)
in ((uu____9931), (uu____9934))))
in FStar_Syntax_Syntax.Tm_match (uu____9908))
in (FStar_Syntax_Syntax.mk uu____9907))
in (uu____9900 FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
end)
in (

let uu____9974 = (

let uu____9977 = (

let uu____9978 = (

let uu____9991 = (

let uu____9994 = (

let uu____9995 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____9995)::[])
in (FStar_Syntax_Subst.close uu____9994 body2))
in ((((false), (((mk_lb ((attrs), (FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t12), (t12.FStar_Syntax_Syntax.pos))))::[]))), (uu____9991)))
in FStar_Syntax_Syntax.Tm_let (uu____9978))
in (FStar_All.pipe_left mk1 uu____9977))
in ((uu____9974), (aq))))
end))
end)
in (match (uu____9809) with
| (tm, aq) -> begin
(match (is_mutable) with
| true -> begin
(

let uu____10052 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((tm), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc))))))
in ((uu____10052), (aq)))
end
| uu____10061 -> begin
((tm), (aq))
end)
end))
end)))))))
in (

let uu____10064 = (FStar_List.hd lbs)
in (match (uu____10064) with
| (attrs, (head_pat, defn)) -> begin
(

let uu____10108 = (is_rec || (is_app_pattern head_pat))
in (match (uu____10108) with
| true -> begin
(ds_let_rec_or_app ())
end
| uu____10113 -> begin
(ds_non_rec attrs head_pat defn body)
end))
end)))))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (

let t_bool1 = (

let uu____10121 = (

let uu____10122 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Syntax_Syntax.Tm_fvar (uu____10122))
in (mk1 uu____10121))
in (

let uu____10123 = (desugar_term_aq env t1)
in (match (uu____10123) with
| (t1', aq1) -> begin
(

let uu____10134 = (desugar_term_aq env t2)
in (match (uu____10134) with
| (t2', aq2) -> begin
(

let uu____10145 = (desugar_term_aq env t3)
in (match (uu____10145) with
| (t3', aq3) -> begin
(

let uu____10156 = (

let uu____10157 = (

let uu____10158 = (

let uu____10181 = (FStar_Syntax_Util.ascribe t1' ((FStar_Util.Inl (t_bool1)), (FStar_Pervasives_Native.None)))
in (

let uu____10202 = (

let uu____10219 = (

let uu____10232 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) t2.FStar_Parser_AST.range)
in ((uu____10232), (FStar_Pervasives_Native.None), (t2')))
in (

let uu____10243 = (

let uu____10258 = (

let uu____10271 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) t3.FStar_Parser_AST.range)
in ((uu____10271), (FStar_Pervasives_Native.None), (t3')))
in (uu____10258)::[])
in (uu____10219)::uu____10243))
in ((uu____10181), (uu____10202))))
in FStar_Syntax_Syntax.Tm_match (uu____10158))
in (mk1 uu____10157))
in ((uu____10156), ((join_aqs ((aq1)::(aq2)::(aq3)::[])))))
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

let desugar_branch = (fun uu____10462 -> (match (uu____10462) with
| (pat, wopt, b) -> begin
(

let uu____10484 = (desugar_match_pat env pat)
in (match (uu____10484) with
| (env1, pat1) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (e1) -> begin
(

let uu____10509 = (desugar_term env1 e1)
in FStar_Pervasives_Native.Some (uu____10509))
end)
in (

let uu____10510 = (desugar_term_aq env1 b)
in (match (uu____10510) with
| (b1, aq) -> begin
(

let uu____10523 = (desugar_disjunctive_pattern pat1 wopt1 b1)
in ((uu____10523), (aq)))
end)))
end))
end))
in (

let uu____10528 = (desugar_term_aq env e)
in (match (uu____10528) with
| (e1, aq) -> begin
(

let uu____10539 = (

let uu____10562 = (

let uu____10587 = (FStar_List.map desugar_branch branches)
in (FStar_All.pipe_right uu____10587 FStar_List.unzip))
in (FStar_All.pipe_right uu____10562 (fun uu____10679 -> (match (uu____10679) with
| (x, y) -> begin
(((FStar_List.flatten x)), (y))
end))))
in (match (uu____10539) with
| (brs, aqs) -> begin
(

let uu____10842 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_match (((e1), (brs)))))
in ((uu____10842), ((join_aqs ((aq)::aqs)))))
end))
end)))
end
| FStar_Parser_AST.Ascribed (e, t, tac_opt) -> begin
(

let annot = (

let uu____10887 = (is_comp_type env t)
in (match (uu____10887) with
| true -> begin
(

let uu____10894 = (desugar_comp t.FStar_Parser_AST.range env t)
in FStar_Util.Inr (uu____10894))
end
| uu____10899 -> begin
(

let uu____10900 = (desugar_term env t)
in FStar_Util.Inl (uu____10900))
end))
in (

let tac_opt1 = (FStar_Util.map_opt tac_opt (desugar_term env))
in (

let uu____10910 = (desugar_term_aq env e)
in (match (uu____10910) with
| (e1, aq) -> begin
(

let uu____10921 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_ascribed (((e1), (((annot), (tac_opt1))), (FStar_Pervasives_Native.None)))))
in ((uu____10921), (aq)))
end))))
end
| FStar_Parser_AST.Record (uu____10956, []) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedEmptyRecord), ("Unexpected empty record")) top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let record = (check_fields env fields top.FStar_Parser_AST.range)
in (

let user_ns = (

let uu____10997 = (FStar_List.hd fields)
in (match (uu____10997) with
| (f, uu____11009) -> begin
f.FStar_Ident.ns
end))
in (

let get_field = (fun xopt f -> (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun uu____11055 -> (match (uu____11055) with
| (g, uu____11061) -> begin
(Prims.op_Equality f.FStar_Ident.idText g.FStar_Ident.ident.FStar_Ident.idText)
end))))
in (

let fn = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((f)::[])))
in (match (found) with
| FStar_Pervasives_Native.Some (uu____11067, e) -> begin
((fn), (e))
end
| FStar_Pervasives_Native.None -> begin
(match (xopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____11081 = (

let uu____11086 = (FStar_Util.format2 "Field %s of record type %s is missing" f.FStar_Ident.idText record.FStar_Syntax_DsEnv.typename.FStar_Ident.str)
in ((FStar_Errors.Fatal_MissingFieldInRecord), (uu____11086)))
in (FStar_Errors.raise_error uu____11081 top.FStar_Parser_AST.range))
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

let uu____11094 = (

let uu____11105 = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map (fun uu____11136 -> (match (uu____11136) with
| (f, uu____11146) -> begin
(

let uu____11147 = (

let uu____11148 = (get_field FStar_Pervasives_Native.None f)
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____11148))
in ((uu____11147), (FStar_Parser_AST.Nothing)))
end))))
in ((user_constrname), (uu____11105)))
in FStar_Parser_AST.Construct (uu____11094))
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (

let uu____11166 = (

let uu____11167 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____11167))
in (FStar_Parser_AST.mk_term uu____11166 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record1 = (

let uu____11169 = (

let uu____11182 = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map (fun uu____11212 -> (match (uu____11212) with
| (f, uu____11222) -> begin
(get_field (FStar_Pervasives_Native.Some (xterm)) f)
end))))
in ((FStar_Pervasives_Native.None), (uu____11182)))
in FStar_Parser_AST.Record (uu____11169))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), ((((FStar_Pervasives_Native.None), ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (FStar_Pervasives_Native.None)))) x.FStar_Ident.idRange)), (e)))))::[]), ((FStar_Parser_AST.mk_term record1 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm1 = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let uu____11282 = (desugar_term_aq env recterm1)
in (match (uu____11282) with
| (e, s) -> begin
(match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____11298; FStar_Syntax_Syntax.vars = uu____11299}, args) -> begin
(

let uu____11321 = (

let uu____11322 = (

let uu____11323 = (

let uu____11338 = (

let uu____11341 = (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos)
in (

let uu____11342 = (

let uu____11345 = (

let uu____11346 = (

let uu____11353 = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map FStar_Pervasives_Native.fst))
in ((record.FStar_Syntax_DsEnv.typename), (uu____11353)))
in FStar_Syntax_Syntax.Record_ctor (uu____11346))
in FStar_Pervasives_Native.Some (uu____11345))
in (FStar_Syntax_Syntax.fvar uu____11341 FStar_Syntax_Syntax.Delta_constant uu____11342)))
in ((uu____11338), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____11323))
in (FStar_All.pipe_left mk1 uu____11322))
in ((uu____11321), (s)))
end
| uu____11382 -> begin
((e), (s))
end)
end))))))))
end
| FStar_Parser_AST.Project (e, f) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f);
(

let uu____11386 = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f)
in (match (uu____11386) with
| (constrname, is_rec) -> begin
(

let uu____11401 = (desugar_term_aq env e)
in (match (uu____11401) with
| (e1, s) -> begin
(

let projname = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname f.FStar_Ident.ident)
in (

let qual = (match (is_rec) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (((constrname), (f.FStar_Ident.ident))))
end
| uu____11418 -> begin
FStar_Pervasives_Native.None
end)
in (

let uu____11419 = (

let uu____11420 = (

let uu____11421 = (

let uu____11436 = (

let uu____11439 = (

let uu____11440 = (FStar_Ident.range_of_lid f)
in (FStar_Ident.set_lid_range projname uu____11440))
in (FStar_Syntax_Syntax.fvar uu____11439 FStar_Syntax_Syntax.Delta_equational qual))
in (

let uu____11441 = (

let uu____11450 = (FStar_Syntax_Syntax.as_arg e1)
in (uu____11450)::[])
in ((uu____11436), (uu____11441))))
in FStar_Syntax_Syntax.Tm_app (uu____11421))
in (FStar_All.pipe_left mk1 uu____11420))
in ((uu____11419), (s)))))
end))
end));
)
end
| FStar_Parser_AST.NamedTyp (uu____11463, e) -> begin
(desugar_term_aq env e)
end
| FStar_Parser_AST.Paren (e) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.VQuote (e) -> begin
(

let tm = (desugar_term env e)
in (

let uu____11472 = (

let uu____11473 = (FStar_Syntax_Subst.compress tm)
in uu____11473.FStar_Syntax_Syntax.n)
in (match (uu____11472) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____11481 = (

let uu___129_11482 = (

let uu____11483 = (

let uu____11484 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____11484))
in (FStar_Syntax_Util.exp_string uu____11483))
in {FStar_Syntax_Syntax.n = uu___129_11482.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = e.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___129_11482.FStar_Syntax_Syntax.vars})
in ((uu____11481), (noaqs)))
end
| uu____11485 -> begin
(

let uu____11486 = (

let uu____11491 = (

let uu____11492 = (FStar_Syntax_Print.term_to_string tm)
in (Prims.strcat "VQuote, expected an fvar, got: " uu____11492))
in ((FStar_Errors.Fatal_UnexpectedTermVQuote), (uu____11491)))
in (FStar_Errors.raise_error uu____11486 top.FStar_Parser_AST.range))
end)))
end
| FStar_Parser_AST.Quote (e, FStar_Parser_AST.Static) -> begin
(

let uu____11498 = (desugar_term_aq env e)
in (match (uu____11498) with
| (tm, vts) -> begin
(

let qi = {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = vts}
in (

let uu____11510 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_quoted (((tm), (qi)))))
in ((uu____11510), (noaqs))))
end))
end
| FStar_Parser_AST.Antiquote (b, e) -> begin
(

let bv = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (

let uu____11518 = (FStar_Syntax_Syntax.bv_to_name bv)
in (

let uu____11519 = (

let uu____11520 = (

let uu____11527 = (desugar_term env e)
in ((bv), (b), (uu____11527)))
in (uu____11520)::[])
in ((uu____11518), (uu____11519)))))
end
| FStar_Parser_AST.Quote (e, FStar_Parser_AST.Dynamic) -> begin
(

let qi = {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = []}
in (

let uu____11550 = (

let uu____11551 = (

let uu____11552 = (

let uu____11559 = (desugar_term env e)
in ((uu____11559), (qi)))
in FStar_Syntax_Syntax.Tm_quoted (uu____11552))
in (FStar_All.pipe_left mk1 uu____11551))
in ((uu____11550), (noaqs))))
end
| uu____11566 when (Prims.op_Equality top.FStar_Parser_AST.level FStar_Parser_AST.Formula) -> begin
(

let uu____11567 = (desugar_formula env top)
in ((uu____11567), (noaqs)))
end
| uu____11568 -> begin
(

let uu____11569 = (

let uu____11574 = (

let uu____11575 = (FStar_Parser_AST.term_to_string top)
in (Prims.strcat "Unexpected term: " uu____11575))
in ((FStar_Errors.Fatal_UnexpectedTerm), (uu____11574)))
in (FStar_Errors.raise_error uu____11569 top.FStar_Parser_AST.range))
end)))))))
and not_ascribed : FStar_Parser_AST.term  ->  Prims.bool = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Ascribed (uu____11581) -> begin
false
end
| uu____11590 -> begin
true
end))
and is_synth_by_tactic : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun e t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (l, r, FStar_Parser_AST.Hash) -> begin
(is_synth_by_tactic e l)
end
| FStar_Parser_AST.Var (lid) -> begin
(

let uu____11596 = (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name e lid)
in (match (uu____11596) with
| FStar_Pervasives_Native.Some (lid1) -> begin
(FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid)
end
| FStar_Pervasives_Native.None -> begin
false
end))
end
| uu____11600 -> begin
false
end))
and desugar_args : FStar_Syntax_DsEnv.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____11637 -> (match (uu____11637) with
| (a, imp) -> begin
(

let uu____11650 = (desugar_term env a)
in (arg_withimp_e imp uu____11650))
end)))))
and desugar_comp : FStar_Range.range  ->  FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun r env t -> (

let fail1 = (fun err -> (FStar_Errors.raise_error err r))
in (

let is_requires = (fun uu____11682 -> (match (uu____11682) with
| (t1, uu____11688) -> begin
(

let uu____11689 = (

let uu____11690 = (unparen t1)
in uu____11690.FStar_Parser_AST.tm)
in (match (uu____11689) with
| FStar_Parser_AST.Requires (uu____11691) -> begin
true
end
| uu____11698 -> begin
false
end))
end))
in (

let is_ensures = (fun uu____11708 -> (match (uu____11708) with
| (t1, uu____11714) -> begin
(

let uu____11715 = (

let uu____11716 = (unparen t1)
in uu____11716.FStar_Parser_AST.tm)
in (match (uu____11715) with
| FStar_Parser_AST.Ensures (uu____11717) -> begin
true
end
| uu____11724 -> begin
false
end))
end))
in (

let is_app = (fun head1 uu____11739 -> (match (uu____11739) with
| (t1, uu____11745) -> begin
(

let uu____11746 = (

let uu____11747 = (unparen t1)
in uu____11747.FStar_Parser_AST.tm)
in (match (uu____11746) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = uu____11749; FStar_Parser_AST.level = uu____11750}, uu____11751, uu____11752) -> begin
(Prims.op_Equality d.FStar_Ident.ident.FStar_Ident.idText head1)
end
| uu____11753 -> begin
false
end))
end))
in (

let is_smt_pat = (fun uu____11763 -> (match (uu____11763) with
| (t1, uu____11769) -> begin
(

let uu____11770 = (

let uu____11771 = (unparen t1)
in uu____11771.FStar_Parser_AST.tm)
in (match (uu____11770) with
| FStar_Parser_AST.Construct (cons1, (({FStar_Parser_AST.tm = FStar_Parser_AST.Construct (smtpat, uu____11774); FStar_Parser_AST.range = uu____11775; FStar_Parser_AST.level = uu____11776}, uu____11777))::(uu____11778)::[]) -> begin
((FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid) && (FStar_Util.for_some (fun s -> (Prims.op_Equality smtpat.FStar_Ident.str s)) (("SMTPat")::("SMTPatT")::("SMTPatOr")::[])))
end
| FStar_Parser_AST.Construct (cons1, (({FStar_Parser_AST.tm = FStar_Parser_AST.Var (smtpat); FStar_Parser_AST.range = uu____11817; FStar_Parser_AST.level = uu____11818}, uu____11819))::(uu____11820)::[]) -> begin
((FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid) && (FStar_Util.for_some (fun s -> (Prims.op_Equality smtpat.FStar_Ident.str s)) (("smt_pat")::("smt_pat_or")::[])))
end
| uu____11845 -> begin
false
end))
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t1 -> (

let uu____11877 = (head_and_args t1)
in (match (uu____11877) with
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

let thunk_ens = (fun uu____11975 -> (match (uu____11975) with
| (e, i) -> begin
(

let uu____11986 = (thunk_ens_ e)
in ((uu____11986), (i)))
end))
in (

let fail_lemma = (fun uu____11998 -> (

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

let uu____12078 = (

let uu____12085 = (

let uu____12092 = (thunk_ens ens)
in (uu____12092)::(nil_pat)::[])
in (req_true)::uu____12085)
in (unit_tm)::uu____12078)
end
| (req)::(ens)::[] when ((is_requires req) && (is_ensures ens)) -> begin
(

let uu____12139 = (

let uu____12146 = (

let uu____12153 = (thunk_ens ens)
in (uu____12153)::(nil_pat)::[])
in (req)::uu____12146)
in (unit_tm)::uu____12139)
end
| (ens)::(smtpat)::[] when ((((

let uu____12202 = (is_requires ens)
in (not (uu____12202))) && (

let uu____12204 = (is_smt_pat ens)
in (not (uu____12204)))) && (

let uu____12206 = (is_decreases ens)
in (not (uu____12206)))) && (is_smt_pat smtpat)) -> begin
(

let uu____12207 = (

let uu____12214 = (

let uu____12221 = (thunk_ens ens)
in (uu____12221)::(smtpat)::[])
in (req_true)::uu____12214)
in (unit_tm)::uu____12207)
end
| (ens)::(dec)::[] when ((is_ensures ens) && (is_decreases dec)) -> begin
(

let uu____12268 = (

let uu____12275 = (

let uu____12282 = (thunk_ens ens)
in (uu____12282)::(nil_pat)::(dec)::[])
in (req_true)::uu____12275)
in (unit_tm)::uu____12268)
end
| (ens)::(dec)::(smtpat)::[] when (((is_ensures ens) && (is_decreases dec)) && (is_smt_pat smtpat)) -> begin
(

let uu____12342 = (

let uu____12349 = (

let uu____12356 = (thunk_ens ens)
in (uu____12356)::(smtpat)::(dec)::[])
in (req_true)::uu____12349)
in (unit_tm)::uu____12342)
end
| (req)::(ens)::(dec)::[] when (((is_requires req) && (is_ensures ens)) && (is_decreases dec)) -> begin
(

let uu____12416 = (

let uu____12423 = (

let uu____12430 = (thunk_ens ens)
in (uu____12430)::(nil_pat)::(dec)::[])
in (req)::uu____12423)
in (unit_tm)::uu____12416)
end
| (req)::(ens)::(smtpat)::[] when (((is_requires req) && (is_ensures ens)) && (is_smt_pat smtpat)) -> begin
(

let uu____12490 = (

let uu____12497 = (

let uu____12504 = (thunk_ens ens)
in (uu____12504)::(smtpat)::[])
in (req)::uu____12497)
in (unit_tm)::uu____12490)
end
| (req)::(ens)::(dec)::(smtpat)::[] when ((((is_requires req) && (is_ensures ens)) && (is_smt_pat smtpat)) && (is_decreases dec)) -> begin
(

let uu____12569 = (

let uu____12576 = (

let uu____12583 = (thunk_ens ens)
in (uu____12583)::(dec)::(smtpat)::[])
in (req)::uu____12576)
in (unit_tm)::uu____12569)
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

let uu____12645 = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes env) l)
in ((uu____12645), (args)))
end
| FStar_Parser_AST.Name (l) when ((

let uu____12673 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Ident.lid_equals uu____12673 FStar_Parser_Const.prims_lid)) && (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Tot")) -> begin
(

let uu____12674 = (

let uu____12681 = (FStar_Ident.set_lid_range FStar_Parser_Const.effect_Tot_lid head1.FStar_Parser_AST.range)
in ((uu____12681), ([])))
in ((uu____12674), (args)))
end
| FStar_Parser_AST.Name (l) when ((

let uu____12699 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Ident.lid_equals uu____12699 FStar_Parser_Const.prims_lid)) && (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "GTot")) -> begin
(

let uu____12700 = (

let uu____12707 = (FStar_Ident.set_lid_range FStar_Parser_Const.effect_GTot_lid head1.FStar_Parser_AST.range)
in ((uu____12707), ([])))
in ((uu____12700), (args)))
end
| FStar_Parser_AST.Name (l) when (((Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Type") || (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Type0")) || (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Effect")) -> begin
(

let uu____12723 = (

let uu____12730 = (FStar_Ident.set_lid_range FStar_Parser_Const.effect_Tot_lid head1.FStar_Parser_AST.range)
in ((uu____12730), ([])))
in ((uu____12723), ((((t1), (FStar_Parser_AST.Nothing)))::[])))
end
| uu____12753 -> begin
(

let default_effect = (

let uu____12755 = (FStar_Options.ml_ish ())
in (match (uu____12755) with
| true -> begin
FStar_Parser_Const.effect_ML_lid
end
| uu____12756 -> begin
((

let uu____12758 = (FStar_Options.warn_default_effects ())
in (match (uu____12758) with
| true -> begin
(FStar_Errors.log_issue head1.FStar_Parser_AST.range ((FStar_Errors.Warning_UseDefaultEffect), ("Using default effect Tot")))
end
| uu____12759 -> begin
()
end));
FStar_Parser_Const.effect_Tot_lid;
)
end))
in (

let uu____12760 = (

let uu____12767 = (FStar_Ident.set_lid_range default_effect head1.FStar_Parser_AST.range)
in ((uu____12767), ([])))
in ((uu____12760), ((((t1), (FStar_Parser_AST.Nothing)))::[]))))
end)
end)))
in (

let uu____12790 = (pre_process_comp_typ t)
in (match (uu____12790) with
| ((eff, cattributes), args) -> begin
((match ((Prims.op_Equality (FStar_List.length args) (Prims.parse_int "0"))) with
| true -> begin
(

let uu____12839 = (

let uu____12844 = (

let uu____12845 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" uu____12845))
in ((FStar_Errors.Fatal_NotEnoughArgsToEffect), (uu____12844)))
in (fail1 uu____12839))
end
| uu____12846 -> begin
()
end);
(

let is_universe = (fun uu____12856 -> (match (uu____12856) with
| (uu____12861, imp) -> begin
(Prims.op_Equality imp FStar_Parser_AST.UnivApp)
end))
in (

let uu____12863 = (FStar_Util.take is_universe args)
in (match (uu____12863) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun uu____12922 -> (match (uu____12922) with
| (u, imp) -> begin
(desugar_universe u)
end)) universes)
in (

let uu____12929 = (

let uu____12944 = (FStar_List.hd args1)
in (

let uu____12953 = (FStar_List.tl args1)
in ((uu____12944), (uu____12953))))
in (match (uu____12929) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (FStar_Pervasives_Native.fst result_arg))
in (

let rest1 = (desugar_args env rest)
in (

let uu____13008 = (

let is_decrease = (fun uu____13046 -> (match (uu____13046) with
| (t1, uu____13056) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____13066; FStar_Syntax_Syntax.vars = uu____13067}, (uu____13068)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.decreases_lid)
end
| uu____13099 -> begin
false
end)
end))
in (FStar_All.pipe_right rest1 (FStar_List.partition is_decrease)))
in (match (uu____13008) with
| (dec, rest2) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun uu____13213 -> (match (uu____13213) with
| (t1, uu____13223) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____13232, ((arg, uu____13234))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| uu____13263 -> begin
(failwith "impos")
end)
end))))
in (

let no_additional_args = (

let is_empty = (fun l -> (match (l) with
| [] -> begin
true
end
| uu____13280 -> begin
false
end))
in ((((is_empty decreases_clause) && (is_empty rest2)) && (is_empty cattributes)) && (is_empty universes1)))
in (

let uu____13291 = (no_additional_args && (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid))
in (match (uu____13291) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end
| uu____13294 -> begin
(

let uu____13295 = (no_additional_args && (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid))
in (match (uu____13295) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end
| uu____13298 -> begin
(

let flags1 = (

let uu____13302 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Lemma_lid)
in (match (uu____13302) with
| true -> begin
(FStar_Syntax_Syntax.LEMMA)::[]
end
| uu____13305 -> begin
(

let uu____13306 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid)
in (match (uu____13306) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____13309 -> begin
(

let uu____13310 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_ML_lid)
in (match (uu____13310) with
| true -> begin
(FStar_Syntax_Syntax.MLEFFECT)::[]
end
| uu____13313 -> begin
(

let uu____13314 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid)
in (match (uu____13314) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____13317 -> begin
[]
end))
end))
end))
end))
in (

let flags2 = (FStar_List.append flags1 cattributes)
in (

let rest3 = (

let uu____13332 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Lemma_lid)
in (match (uu____13332) with
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

let uu____13421 = (FStar_Ident.set_lid_range FStar_Parser_Const.pattern_lid pat.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar uu____13421 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.mk_Tm_app nil ((((pattern), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::[]) FStar_Pervasives_Native.None pat.FStar_Syntax_Syntax.pos)))
end
| uu____13436 -> begin
pat
end)
in (

let uu____13437 = (

let uu____13448 = (

let uu____13459 = (

let uu____13468 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat1), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) FStar_Pervasives_Native.None pat1.FStar_Syntax_Syntax.pos)
in ((uu____13468), (aq)))
in (uu____13459)::[])
in (ens)::uu____13448)
in (req)::uu____13437))
end
| uu____13509 -> begin
rest2
end)
end
| uu____13520 -> begin
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
| uu____13533 -> begin
FStar_Pervasives_Native.None
end))
in (

let mk1 = (fun t -> (FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let uu___130_13554 = t
in {FStar_Syntax_Syntax.n = uu___130_13554.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___130_13554.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let uu___131_13596 = b
in {FStar_Parser_AST.b = uu___131_13596.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___131_13596.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___131_13596.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env1 pats1 -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (

let uu____13659 = (desugar_term env1 e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) uu____13659)))))) pats1))
in (match (tk) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____13672 = (FStar_Syntax_DsEnv.push_bv env a)
in (match (uu____13672) with
| (env1, a1) -> begin
(

let a2 = (

let uu___132_13682 = a1
in {FStar_Syntax_Syntax.ppname = uu___132_13682.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___132_13682.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats1 = (desugar_pats env1 pats)
in (

let body1 = (desugar_formula env1 body)
in (

let body2 = (match (pats1) with
| [] -> begin
body1
end
| uu____13704 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_meta (((body1), (FStar_Syntax_Syntax.Meta_pattern (pats1))))))
end)
in (

let body3 = (

let uu____13720 = (

let uu____13723 = (

let uu____13724 = (FStar_Syntax_Syntax.mk_binder a2)
in (uu____13724)::[])
in (no_annot_abs uu____13723 body2))
in (FStar_All.pipe_left setpos uu____13720))
in (

let uu____13741 = (

let uu____13742 = (

let uu____13757 = (

let uu____13760 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Syntax_Syntax.fvar uu____13760 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None))
in (

let uu____13761 = (

let uu____13770 = (FStar_Syntax_Syntax.as_arg body3)
in (uu____13770)::[])
in ((uu____13757), (uu____13761))))
in FStar_Syntax_Syntax.Tm_app (uu____13742))
in (FStar_All.pipe_left mk1 uu____13741)))))))
end))
end
| uu____13783 -> begin
(failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body1 = (

let uu____13863 = (q ((rest), (pats), (body)))
in (

let uu____13870 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term uu____13863 uu____13870 FStar_Parser_AST.Formula)))
in (

let uu____13871 = (q (((b)::[]), ([]), (body1)))
in (FStar_Parser_AST.mk_term uu____13871 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| uu____13880 -> begin
(failwith "impossible")
end))
in (

let uu____13883 = (

let uu____13884 = (unparen f)
in uu____13884.FStar_Parser_AST.tm)
in (match (uu____13883) with
| FStar_Parser_AST.Labeled (f1, l, p) -> begin
(

let f2 = (desugar_formula env f1)
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((f2), (FStar_Syntax_Syntax.Meta_labeled (((l), (f2.FStar_Syntax_Syntax.pos), (p)))))))))
end
| FStar_Parser_AST.QForall ([], uu____13893, uu____13894) -> begin
(failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QExists ([], uu____13905, uu____13906) -> begin
(failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____13937 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env uu____13937)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____13973 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env uu____13973)))
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
| uu____14016 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list) = (fun env bs -> (

let uu____14021 = (FStar_List.fold_left (fun uu____14057 b -> (match (uu____14057) with
| (env1, out) -> begin
(

let tk = (desugar_binder env1 (

let uu___133_14109 = b
in {FStar_Parser_AST.b = uu___133_14109.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___133_14109.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___133_14109.FStar_Parser_AST.aqual}))
in (match (tk) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____14126 = (FStar_Syntax_DsEnv.push_bv env1 a)
in (match (uu____14126) with
| (env2, a1) -> begin
(

let a2 = (

let uu___134_14146 = a1
in {FStar_Syntax_Syntax.ppname = uu___134_14146.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___134_14146.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in ((env2), ((((a2), ((trans_aqual b.FStar_Parser_AST.aqual))))::out)))
end))
end
| uu____14163 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedBinder), ("Unexpected binder")) b.FStar_Parser_AST.brange)
end))
end)) ((env), ([])) bs)
in (match (uu____14021) with
| (env1, tpars) -> begin
((env1), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.TAnnotated (x, t) -> begin
(

let uu____14250 = (desugar_typ env t)
in ((FStar_Pervasives_Native.Some (x)), (uu____14250)))
end
| FStar_Parser_AST.Annotated (x, t) -> begin
(

let uu____14255 = (desugar_typ env t)
in ((FStar_Pervasives_Native.Some (x)), (uu____14255)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____14259 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) FStar_Pervasives_Native.None x.FStar_Ident.idRange)
in ((FStar_Pervasives_Native.Some (x)), (uu____14259)))
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____14263 = (desugar_typ env t)
in ((FStar_Pervasives_Native.None), (uu____14263)))
end
| FStar_Parser_AST.Variable (x) -> begin
((FStar_Pervasives_Native.Some (x)), (FStar_Syntax_Syntax.tun))
end))


let mk_data_discriminators : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_DsEnv.env  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun quals env datas -> (

let quals1 = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___96_14302 -> (match (uu___96_14302) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____14303 -> begin
false
end))))
in (

let quals2 = (fun q -> (

let uu____14316 = ((

let uu____14319 = (FStar_Syntax_DsEnv.iface env)
in (not (uu____14319))) || (FStar_Syntax_DsEnv.admitted_iface env))
in (match (uu____14316) with
| true -> begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals1)
end
| uu____14322 -> begin
(FStar_List.append q quals1)
end)))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (

let uu____14333 = (FStar_Ident.range_of_lid disc_name)
in (

let uu____14334 = (quals2 ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((disc_name), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = uu____14333; FStar_Syntax_Syntax.sigquals = uu____14334; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))))))))


let mk_indexed_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  FStar_Syntax_DsEnv.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq env lid fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let uu____14373 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____14403 -> (match (uu____14403) with
| (x, uu____14411) -> begin
(

let uu____14412 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____14412) with
| (field_name, uu____14420) -> begin
(

let only_decl = (((

let uu____14424 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____14424)) || (Prims.op_disEquality fvq FStar_Syntax_Syntax.Data_ctor)) || (

let uu____14426 = (

let uu____14427 = (FStar_Syntax_DsEnv.current_module env)
in uu____14427.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____14426)))
in (

let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____14443 = (FStar_List.filter (fun uu___97_14447 -> (match (uu___97_14447) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____14448 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____14443)
end
| uu____14449 -> begin
q
end))
in (

let quals1 = (

let iquals1 = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___98_14461 -> (match (uu___98_14461) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____14462 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals1)))
in (

let decl = (

let uu____14464 = (FStar_Ident.range_of_lid field_name)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = uu____14464; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____14467 -> begin
(

let dd = (

let uu____14469 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____14469) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____14472 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lb = (

let uu____14474 = (

let uu____14479 = (FStar_Syntax_Syntax.lid_as_fv field_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____14479))
in {FStar_Syntax_Syntax.lbname = uu____14474; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbattrs = []; FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange})
in (

let impl = (

let uu____14483 = (

let uu____14484 = (

let uu____14491 = (

let uu____14494 = (

let uu____14495 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____14495 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____14494)::[])
in ((((false), ((lb)::[]))), (uu____14491)))
in FStar_Syntax_Syntax.Sig_let (uu____14484))
in {FStar_Syntax_Syntax.sigel = uu____14483; FStar_Syntax_Syntax.sigrng = p; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____14508 -> begin
(decl)::(impl)::[]
end))))
end))))))
end))
end))))
in (FStar_All.pipe_right uu____14373 FStar_List.flatten))))


let mk_data_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____14539, t, uu____14541, n1, uu____14543) when (

let uu____14548 = (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
in (not (uu____14548))) -> begin
(

let uu____14549 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____14549) with
| (formals, uu____14565) -> begin
(match (formals) with
| [] -> begin
[]
end
| uu____14588 -> begin
(

let filter_records = (fun uu___99_14602 -> (match (uu___99_14602) with
| FStar_Syntax_Syntax.RecordConstructor (uu____14605, fns) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| uu____14617 -> begin
FStar_Pervasives_Native.None
end))
in (

let fv_qual = (

let uu____14619 = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals filter_records)
in (match (uu____14619) with
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
| uu____14628 -> begin
iquals
end)
in (

let uu____14629 = (FStar_Util.first_N n1 formals)
in (match (uu____14629) with
| (uu____14652, rest) -> begin
(mk_indexed_projector_names iquals1 fv_qual env lid rest)
end)))))
end)
end))
end
| uu____14678 -> begin
[]
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (

let dd = (

let uu____14732 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____14732) with
| true -> begin
(

let uu____14735 = (FStar_Syntax_Util.incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (uu____14735))
end
| uu____14736 -> begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end))
in (

let lb = (

let uu____14738 = (

let uu____14743 = (FStar_Syntax_Syntax.lid_as_fv lid dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____14743))
in (

let uu____14744 = (

let uu____14747 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars uu____14747))
in (

let uu____14750 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = uu____14738; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____14744; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____14750; FStar_Syntax_Syntax.lbattrs = []; FStar_Syntax_Syntax.lbpos = rng})))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (lids))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))


let rec desugar_tycon : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.decl  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d quals tcs -> (

let rng = d.FStar_Parser_AST.drange
in (

let tycon_id = (fun uu___100_14801 -> (match (uu___100_14801) with
| FStar_Parser_AST.TyconAbstract (id1, uu____14803, uu____14804) -> begin
id1
end
| FStar_Parser_AST.TyconAbbrev (id1, uu____14814, uu____14815, uu____14816) -> begin
id1
end
| FStar_Parser_AST.TyconRecord (id1, uu____14826, uu____14827, uu____14828) -> begin
id1
end
| FStar_Parser_AST.TyconVariant (id1, uu____14858, uu____14859, uu____14860) -> begin
id1
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (x, uu____14904) -> begin
(

let uu____14905 = (

let uu____14906 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____14906))
in (FStar_Parser_AST.mk_term uu____14905 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| FStar_Parser_AST.Variable (x) -> begin
(

let uu____14908 = (

let uu____14909 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____14909))
in (FStar_Parser_AST.mk_term uu____14908 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| FStar_Parser_AST.TAnnotated (a, uu____14911) -> begin
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
| uu____14942 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (

let uu____14948 = (

let uu____14949 = (

let uu____14956 = (binder_to_term b)
in ((out), (uu____14956), ((imp_of_aqual b))))
in FStar_Parser_AST.App (uu____14949))
in (FStar_Parser_AST.mk_term uu____14948 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun uu___101_14968 -> (match (uu___101_14968) with
| FStar_Parser_AST.TyconRecord (id1, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id1.FStar_Ident.idText)), (id1.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun uu____15024 -> (match (uu____15024) with
| (x, t, uu____15035) -> begin
(

let uu____15040 = (

let uu____15041 = (

let uu____15046 = (FStar_Syntax_Util.mangle_field_name x)
in ((uu____15046), (t)))
in FStar_Parser_AST.Annotated (uu____15041))
in (FStar_Parser_AST.mk_binder uu____15040 x.FStar_Ident.idRange FStar_Parser_AST.Expr FStar_Pervasives_Native.None))
end)) fields)
in (

let result = (

let uu____15048 = (

let uu____15049 = (

let uu____15050 = (FStar_Ident.lid_of_ids ((id1)::[]))
in FStar_Parser_AST.Var (uu____15050))
in (FStar_Parser_AST.mk_term uu____15049 id1.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____15048 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id1.FStar_Ident.idRange FStar_Parser_AST.Type_level)
in (

let uu____15054 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____15081 -> (match (uu____15081) with
| (x, uu____15091, uu____15092) -> begin
(FStar_Syntax_Util.unmangle_field_name x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id1), (parms), (kopt), ((((constrName), (FStar_Pervasives_Native.Some (constrTyp)), (FStar_Pervasives_Native.None), (false)))::[])))), (uu____15054)))))))
end
| uu____15145 -> begin
(failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals1 _env mutuals uu___102_15184 -> (match (uu___102_15184) with
| FStar_Parser_AST.TyconAbstract (id1, binders, kopt) -> begin
(

let uu____15208 = (typars_of_binders _env binders)
in (match (uu____15208) with
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

let uu____15254 = (

let uu____15255 = (

let uu____15256 = (FStar_Ident.lid_of_ids ((id1)::[]))
in FStar_Parser_AST.Var (uu____15256))
in (FStar_Parser_AST.mk_term uu____15255 id1.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____15254 binders))
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
| uu____15267 -> begin
(failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env1 bs -> (

let uu____15315 = (FStar_List.fold_left (fun uu____15355 uu____15356 -> (match (((uu____15355), (uu____15356))) with
| ((env2, tps), (x, imp)) -> begin
(

let uu____15447 = (FStar_Syntax_DsEnv.push_bv env2 x.FStar_Syntax_Syntax.ppname)
in (match (uu____15447) with
| (env3, y) -> begin
((env3), ((((y), (imp)))::tps))
end))
end)) ((env1), ([])) bs)
in (match (uu____15315) with
| (env2, bs1) -> begin
((env2), ((FStar_List.rev bs1)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id1, bs, kopt))::[] -> begin
(

let kopt1 = (match (kopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____15560 = (tm_type_z id1.FStar_Ident.idRange)
in FStar_Pervasives_Native.Some (uu____15560))
end
| uu____15561 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id1), (bs), (kopt1)))
in (

let uu____15569 = (desugar_abstract_tc quals env [] tc)
in (match (uu____15569) with
| (uu____15582, uu____15583, se, uu____15585) -> begin
(

let se1 = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, uu____15588, typars, k, [], []) -> begin
(

let quals1 = se.FStar_Syntax_Syntax.sigquals
in (

let quals2 = (match ((FStar_List.contains FStar_Syntax_Syntax.Assumption quals1)) with
| true -> begin
quals1
end
| uu____15603 -> begin
((

let uu____15605 = (

let uu____15606 = (FStar_Options.ml_ish ())
in (not (uu____15606)))
in (match (uu____15605) with
| true -> begin
(

let uu____15607 = (

let uu____15612 = (

let uu____15613 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Adding an implicit \'assume new\' qualifier on %s" uu____15613))
in ((FStar_Errors.Warning_AddImplicitAssumeNewQualifier), (uu____15612)))
in (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng uu____15607))
end
| uu____15614 -> begin
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
| uu____15620 -> begin
(

let uu____15621 = (

let uu____15628 = (

let uu____15629 = (

let uu____15642 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (uu____15642)))
in FStar_Syntax_Syntax.Tm_arrow (uu____15629))
in (FStar_Syntax_Syntax.mk uu____15628))
in (uu____15621 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
end)
in (

let uu___135_15656 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t))); FStar_Syntax_Syntax.sigrng = uu___135_15656.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = uu___135_15656.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___135_15656.FStar_Syntax_Syntax.sigattrs}))))
end
| uu____15657 -> begin
(failwith "Impossible")
end)
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se1)
in (

let env2 = (

let uu____15660 = (FStar_Syntax_DsEnv.qualify env1 id1)
in (FStar_Syntax_DsEnv.push_doc env1 uu____15660 d.FStar_Parser_AST.doc))
in ((env2), ((se1)::[])))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id1, binders, kopt, t))::[] -> begin
(

let uu____15673 = (typars_of_binders env binders)
in (match (uu____15673) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____15709 = (FStar_Util.for_some (fun uu___103_15711 -> (match (uu___103_15711) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| uu____15712 -> begin
false
end)) quals)
in (match (uu____15709) with
| true -> begin
FStar_Syntax_Syntax.teff
end
| uu____15713 -> begin
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

let uu____15719 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___104_15723 -> (match (uu___104_15723) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| uu____15724 -> begin
false
end))))
in (match (uu____15719) with
| true -> begin
quals
end
| uu____15727 -> begin
(match ((Prims.op_Equality t0.FStar_Parser_AST.level FStar_Parser_AST.Formula)) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals
end
| uu____15730 -> begin
quals
end)
end))
in (

let qlid = (FStar_Syntax_DsEnv.qualify env id1)
in (

let se = (

let uu____15733 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Effect))
in (match (uu____15733) with
| true -> begin
(

let uu____15736 = (

let uu____15743 = (

let uu____15744 = (unparen t)
in uu____15744.FStar_Parser_AST.tm)
in (match (uu____15743) with
| FStar_Parser_AST.Construct (head1, args) -> begin
(

let uu____15765 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____15795))::args_rev -> begin
(

let uu____15807 = (

let uu____15808 = (unparen last_arg)
in uu____15808.FStar_Parser_AST.tm)
in (match (uu____15807) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____15836 -> begin
(([]), (args))
end))
end
| uu____15845 -> begin
(([]), (args))
end)
in (match (uu____15765) with
| (cattributes, args1) -> begin
(

let uu____15884 = (desugar_attributes env cattributes)
in (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((head1), (args1)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (uu____15884)))
end))
end
| uu____15895 -> begin
((t), ([]))
end))
in (match (uu____15736) with
| (t1, cattributes) -> begin
(

let c = (desugar_comp t1.FStar_Parser_AST.range env' t1)
in (

let typars1 = (FStar_Syntax_Subst.close_binders typars)
in (

let c1 = (FStar_Syntax_Subst.close_comp typars1 c)
in (

let quals2 = (FStar_All.pipe_right quals1 (FStar_List.filter (fun uu___105_15917 -> (match (uu___105_15917) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| uu____15918 -> begin
true
end))))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((qlid), ([]), (typars1), (c1), ((FStar_List.append cattributes (FStar_Syntax_Util.comp_flags c1))))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))))
end))
end
| uu____15921 -> begin
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
| (FStar_Parser_AST.TyconRecord (uu____15925))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let uu____15949 = (tycon_record_as_variant trec)
in (match (uu____15949) with
| (t, fs) -> begin
(

let uu____15966 = (

let uu____15969 = (

let uu____15970 = (

let uu____15979 = (

let uu____15982 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Ident.ids_of_lid uu____15982))
in ((uu____15979), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____15970))
in (uu____15969)::quals)
in (desugar_tycon env d uu____15966 ((t)::[])))
end)))
end
| (uu____15987)::uu____15988 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals1 et tc -> (

let uu____16155 = et
in (match (uu____16155) with
| (env1, tcs1) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (uu____16380) -> begin
(

let trec = tc
in (

let uu____16404 = (tycon_record_as_variant trec)
in (match (uu____16404) with
| (t, fs) -> begin
(

let uu____16463 = (

let uu____16466 = (

let uu____16467 = (

let uu____16476 = (

let uu____16479 = (FStar_Syntax_DsEnv.current_module env1)
in (FStar_Ident.ids_of_lid uu____16479))
in ((uu____16476), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____16467))
in (uu____16466)::quals1)
in (collect_tcs uu____16463 ((env1), (tcs1)) t))
end)))
end
| FStar_Parser_AST.TyconVariant (id1, binders, kopt, constructors) -> begin
(

let uu____16566 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id1), (binders), (kopt)))))
in (match (uu____16566) with
| (env2, uu____16626, se, tconstr) -> begin
((env2), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals1))))::tcs1))
end))
end
| FStar_Parser_AST.TyconAbbrev (id1, binders, kopt, t) -> begin
(

let uu____16775 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id1), (binders), (kopt)))))
in (match (uu____16775) with
| (env2, uu____16835, se, tconstr) -> begin
((env2), ((FStar_Util.Inr (((se), (binders), (t), (quals1))))::tcs1))
end))
end
| uu____16960 -> begin
(failwith "Unrecognized mutual type definition")
end)
end)))
in (

let uu____17007 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (uu____17007) with
| (env1, tcs1) -> begin
(

let tcs2 = (FStar_List.rev tcs1)
in (

let docs_tps_sigelts = (FStar_All.pipe_right tcs2 (FStar_List.collect (fun uu___107_17518 -> (match (uu___107_17518) with
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (id1, uvs, tpars, k, uu____17585, uu____17586); FStar_Syntax_Syntax.sigrng = uu____17587; FStar_Syntax_Syntax.sigquals = uu____17588; FStar_Syntax_Syntax.sigmeta = uu____17589; FStar_Syntax_Syntax.sigattrs = uu____17590}, binders, t, quals1) -> begin
(

let t1 = (

let uu____17651 = (typars_of_binders env1 binders)
in (match (uu____17651) with
| (env2, tpars1) -> begin
(

let uu____17682 = (push_tparams env2 tpars1)
in (match (uu____17682) with
| (env_tps, tpars2) -> begin
(

let t1 = (desugar_typ env_tps t)
in (

let tpars3 = (FStar_Syntax_Subst.close_binders tpars2)
in (FStar_Syntax_Subst.close tpars3 t1)))
end))
end))
in (

let uu____17715 = (

let uu____17736 = (mk_typ_abbrev id1 uvs tpars k t1 ((id1)::[]) quals1 rng)
in ((((id1), (d.FStar_Parser_AST.doc))), ([]), (uu____17736)))
in (uu____17715)::[]))
end
| FStar_Util.Inl ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs1, tpars, k, mutuals1, uu____17804); FStar_Syntax_Syntax.sigrng = uu____17805; FStar_Syntax_Syntax.sigquals = tname_quals; FStar_Syntax_Syntax.sigmeta = uu____17807; FStar_Syntax_Syntax.sigattrs = uu____17808}, constrs, tconstr, quals1) -> begin
(

let mk_tot = (fun t -> (

let tot1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((tot1), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)))
in (

let tycon = ((tname), (tpars), (k))
in (

let uu____17906 = (push_tparams env1 tpars)
in (match (uu____17906) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun uu____17983 -> (match (uu____17983) with
| (x, uu____17997) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let tot_tconstr = (mk_tot tconstr)
in (

let uu____18005 = (

let uu____18034 = (FStar_All.pipe_right constrs (FStar_List.map (fun uu____18148 -> (match (uu____18148) with
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
| uu____18201 -> begin
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

let uu____18204 = (close env_tps t)
in (desugar_term env_tps uu____18204))
in (

let name = (FStar_Syntax_DsEnv.qualify env1 id1)
in (

let quals2 = (FStar_All.pipe_right tname_quals (FStar_List.collect (fun uu___106_18215 -> (match (uu___106_18215) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| uu____18227 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (

let uu____18235 = (

let uu____18256 = (

let uu____18257 = (

let uu____18258 = (

let uu____18273 = (

let uu____18274 = (

let uu____18277 = (FStar_All.pipe_right t1 FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total uu____18277))
in (FStar_Syntax_Util.arrow data_tpars uu____18274))
in ((name), (univs1), (uu____18273), (tname), (ntps), (mutuals1)))
in FStar_Syntax_Syntax.Sig_datacon (uu____18258))
in {FStar_Syntax_Syntax.sigel = uu____18257; FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in ((((name), (doc1))), (tps), (uu____18256)))
in ((name), (uu____18235))))))))
end))))
in (FStar_All.pipe_left FStar_List.split uu____18034))
in (match (uu____18005) with
| (constrNames, constrs1) -> begin
(((((tname), (d.FStar_Parser_AST.doc))), ([]), ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs1), (tpars), (k), (mutuals1), (constrNames))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = tname_quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))::constrs1
end))))
end))))
end
| uu____18514 -> begin
(failwith "impossible")
end))))
in (

let name_docs = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.map (fun uu____18646 -> (match (uu____18646) with
| (name_doc, uu____18674, uu____18675) -> begin
name_doc
end))))
in (

let sigelts = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.map (fun uu____18755 -> (match (uu____18755) with
| (uu____18776, uu____18777, se) -> begin
se
end))))
in (

let uu____18807 = (

let uu____18814 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle sigelts quals uu____18814 rng))
in (match (uu____18807) with
| (bundle, abbrevs) -> begin
(

let env2 = (FStar_Syntax_DsEnv.push_sigelt env0 bundle)
in (

let env3 = (FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env2 abbrevs)
in (

let data_ops = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.collect (fun uu____18880 -> (match (uu____18880) with
| (uu____18903, tps, se) -> begin
(mk_data_projector_names quals env3 se)
end))))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, uu____18954, tps, k, uu____18957, constrs) when ((FStar_List.length constrs) > (Prims.parse_int "1")) -> begin
(

let quals1 = se.FStar_Syntax_Syntax.sigquals
in (

let quals2 = (match ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals1)) with
| true -> begin
(FStar_Syntax_Syntax.Private)::quals1
end
| uu____18975 -> begin
quals1
end)
in (mk_data_discriminators quals2 env3 constrs)))
end
| uu____18976 -> begin
[]
end))))
in (

let ops = (FStar_List.append discs data_ops)
in (

let env4 = (FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env3 ops)
in (

let env5 = (FStar_List.fold_left (fun acc uu____18993 -> (match (uu____18993) with
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

let uu____19030 = (FStar_List.fold_left (fun uu____19053 b -> (match (uu____19053) with
| (env1, binders1) -> begin
(

let uu____19073 = (desugar_binder env1 b)
in (match (uu____19073) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____19090 = (as_binder env1 b.FStar_Parser_AST.aqual ((FStar_Pervasives_Native.Some (a)), (k)))
in (match (uu____19090) with
| (binder, env2) -> begin
((env2), ((binder)::binders1))
end))
end
| uu____19107 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_MissingNameInBinder), ("Missing name in binder")) b.FStar_Parser_AST.brange)
end))
end)) ((env), ([])) binders)
in (match (uu____19030) with
| (env1, binders1) -> begin
((env1), ((FStar_List.rev binders1)))
end)))


let push_reflect_effect : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lid  ->  FStar_Range.range  ->  FStar_Syntax_DsEnv.env = (fun env quals effect_name range -> (

let uu____19160 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___108_19165 -> (match (uu___108_19165) with
| FStar_Syntax_Syntax.Reflectable (uu____19166) -> begin
true
end
| uu____19167 -> begin
false
end))))
in (match (uu____19160) with
| true -> begin
(

let monad_env = (FStar_Syntax_DsEnv.enter_monad_scope env effect_name.FStar_Ident.ident)
in (

let reflect_lid = (

let uu____19170 = (FStar_Ident.id_of_text "reflect")
in (FStar_All.pipe_right uu____19170 (FStar_Syntax_DsEnv.qualify monad_env)))
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (effect_name))::[]
in (

let refl_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = range; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (FStar_Syntax_DsEnv.push_sigelt env refl_decl)))))
end
| uu____19175 -> begin
env
end)))


let rec desugar_effect : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.term Prims.list  ->  (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_typ eff_decls attrs -> (

let env0 = env
in (

let monad_env = (FStar_Syntax_DsEnv.enter_monad_scope env eff_name)
in (

let uu____19312 = (desugar_binders monad_env eff_binders)
in (match (uu____19312) with
| (env1, binders) -> begin
(

let eff_t = (desugar_term env1 eff_typ)
in (

let for_free = (

let uu____19333 = (

let uu____19334 = (

let uu____19341 = (FStar_Syntax_Util.arrow_formals eff_t)
in (FStar_Pervasives_Native.fst uu____19341))
in (FStar_List.length uu____19334))
in (Prims.op_Equality uu____19333 (Prims.parse_int "1")))
in (

let mandatory_members = (

let rr_members = ("repr")::("return")::("bind")::[]
in (match (for_free) with
| true -> begin
rr_members
end
| uu____19378 -> begin
(FStar_List.append rr_members (("return_wp")::("bind_wp")::("if_then_else")::("ite_wp")::("stronger")::("close_wp")::("assert_p")::("assume_p")::("null_wp")::("trivial")::[]))
end))
in (

let name_of_eff_decl = (fun decl -> (match (decl.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____19385, ((FStar_Parser_AST.TyconAbbrev (name, uu____19387, uu____19388, uu____19389), uu____19390))::[]) -> begin
(FStar_Ident.text_of_id name)
end
| uu____19423 -> begin
(failwith "Malformed effect member declaration.")
end))
in (

let uu____19424 = (FStar_List.partition (fun decl -> (

let uu____19436 = (name_of_eff_decl decl)
in (FStar_List.mem uu____19436 mandatory_members))) eff_decls)
in (match (uu____19424) with
| (mandatory_members_decls, actions) -> begin
(

let uu____19453 = (FStar_All.pipe_right mandatory_members_decls (FStar_List.fold_left (fun uu____19482 decl -> (match (uu____19482) with
| (env2, out) -> begin
(

let uu____19502 = (desugar_decl env2 decl)
in (match (uu____19502) with
| (env3, ses) -> begin
(

let uu____19515 = (

let uu____19518 = (FStar_List.hd ses)
in (uu____19518)::out)
in ((env3), (uu____19515)))
end))
end)) ((env1), ([]))))
in (match (uu____19453) with
| (env2, decls) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (

let actions_docs = (FStar_All.pipe_right actions (FStar_List.map (fun d1 -> (match (d1.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____19586, ((FStar_Parser_AST.TyconAbbrev (name, action_params, uu____19589, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (uu____19590, ((def, uu____19592))::((cps_type, uu____19594))::[]); FStar_Parser_AST.range = uu____19595; FStar_Parser_AST.level = uu____19596}), doc1))::[]) when (not (for_free)) -> begin
(

let uu____19648 = (desugar_binders env2 action_params)
in (match (uu____19648) with
| (env3, action_params1) -> begin
(

let action_params2 = (FStar_Syntax_Subst.close_binders action_params1)
in (

let uu____19668 = (

let uu____19669 = (FStar_Syntax_DsEnv.qualify env3 name)
in (

let uu____19670 = (

let uu____19671 = (desugar_term env3 def)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____19671))
in (

let uu____19676 = (

let uu____19677 = (desugar_typ env3 cps_type)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____19677))
in {FStar_Syntax_Syntax.action_name = uu____19669; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = action_params2; FStar_Syntax_Syntax.action_defn = uu____19670; FStar_Syntax_Syntax.action_typ = uu____19676})))
in ((uu____19668), (doc1))))
end))
end
| FStar_Parser_AST.Tycon (uu____19684, ((FStar_Parser_AST.TyconAbbrev (name, action_params, uu____19687, defn), doc1))::[]) when for_free -> begin
(

let uu____19722 = (desugar_binders env2 action_params)
in (match (uu____19722) with
| (env3, action_params1) -> begin
(

let action_params2 = (FStar_Syntax_Subst.close_binders action_params1)
in (

let uu____19742 = (

let uu____19743 = (FStar_Syntax_DsEnv.qualify env3 name)
in (

let uu____19744 = (

let uu____19745 = (desugar_term env3 defn)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____19745))
in {FStar_Syntax_Syntax.action_name = uu____19743; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = action_params2; FStar_Syntax_Syntax.action_defn = uu____19744; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
in ((uu____19742), (doc1))))
end))
end
| uu____19752 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_MalformedActionDeclaration), ("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).")) d1.FStar_Parser_AST.drange)
end))))
in (

let actions1 = (FStar_List.map FStar_Pervasives_Native.fst actions_docs)
in (

let eff_t1 = (FStar_Syntax_Subst.close binders1 eff_t)
in (

let lookup1 = (fun s -> (

let l = (

let uu____19784 = (FStar_Ident.mk_ident ((s), (d.FStar_Parser_AST.drange)))
in (FStar_Syntax_DsEnv.qualify env2 uu____19784))
in (

let uu____19785 = (

let uu____19786 = (FStar_Syntax_DsEnv.fail_or env2 (FStar_Syntax_DsEnv.try_lookup_definition env2) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders1) uu____19786))
in (([]), (uu____19785)))))
in (

let mname = (FStar_Syntax_DsEnv.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange (FStar_Pervasives_Native.Some (mname))) quals)
in (

let se = (match (for_free) with
| true -> begin
(

let dummy_tscheme = (

let uu____19803 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (([]), (uu____19803)))
in (

let uu____19810 = (

let uu____19811 = (

let uu____19812 = (

let uu____19813 = (lookup1 "repr")
in (FStar_Pervasives_Native.snd uu____19813))
in (

let uu____19822 = (lookup1 "return")
in (

let uu____19823 = (lookup1 "bind")
in (

let uu____19824 = (FStar_List.map (desugar_term env2) attrs)
in {FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = eff_t1; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = uu____19812; FStar_Syntax_Syntax.return_repr = uu____19822; FStar_Syntax_Syntax.bind_repr = uu____19823; FStar_Syntax_Syntax.actions = actions1; FStar_Syntax_Syntax.eff_attrs = uu____19824}))))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____19811))
in {FStar_Syntax_Syntax.sigel = uu____19810; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qualifiers; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))
end
| uu____19827 -> begin
(

let rr = (FStar_Util.for_some (fun uu___109_19830 -> (match (uu___109_19830) with
| FStar_Syntax_Syntax.Reifiable -> begin
true
end
| FStar_Syntax_Syntax.Reflectable (uu____19831) -> begin
true
end
| uu____19832 -> begin
false
end)) qualifiers)
in (

let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in (

let uu____19846 = (

let uu____19847 = (

let uu____19848 = (lookup1 "return_wp")
in (

let uu____19849 = (lookup1 "bind_wp")
in (

let uu____19850 = (lookup1 "if_then_else")
in (

let uu____19851 = (lookup1 "ite_wp")
in (

let uu____19852 = (lookup1 "stronger")
in (

let uu____19853 = (lookup1 "close_wp")
in (

let uu____19854 = (lookup1 "assert_p")
in (

let uu____19855 = (lookup1 "assume_p")
in (

let uu____19856 = (lookup1 "null_wp")
in (

let uu____19857 = (lookup1 "trivial")
in (

let uu____19858 = (match (rr) with
| true -> begin
(

let uu____19859 = (lookup1 "repr")
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____19859))
end
| uu____19874 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let uu____19875 = (match (rr) with
| true -> begin
(lookup1 "return")
end
| uu____19876 -> begin
un_ts
end)
in (

let uu____19877 = (match (rr) with
| true -> begin
(lookup1 "bind")
end
| uu____19878 -> begin
un_ts
end)
in (

let uu____19879 = (FStar_List.map (desugar_term env2) attrs)
in {FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = eff_t1; FStar_Syntax_Syntax.ret_wp = uu____19848; FStar_Syntax_Syntax.bind_wp = uu____19849; FStar_Syntax_Syntax.if_then_else = uu____19850; FStar_Syntax_Syntax.ite_wp = uu____19851; FStar_Syntax_Syntax.stronger = uu____19852; FStar_Syntax_Syntax.close_wp = uu____19853; FStar_Syntax_Syntax.assert_p = uu____19854; FStar_Syntax_Syntax.assume_p = uu____19855; FStar_Syntax_Syntax.null_wp = uu____19856; FStar_Syntax_Syntax.trivial = uu____19857; FStar_Syntax_Syntax.repr = uu____19858; FStar_Syntax_Syntax.return_repr = uu____19875; FStar_Syntax_Syntax.bind_repr = uu____19877; FStar_Syntax_Syntax.actions = actions1; FStar_Syntax_Syntax.eff_attrs = uu____19879}))))))))))))))
in FStar_Syntax_Syntax.Sig_new_effect (uu____19847))
in {FStar_Syntax_Syntax.sigel = uu____19846; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qualifiers; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))
end)
in (

let env3 = (FStar_Syntax_DsEnv.push_sigelt env0 se)
in (

let env4 = (FStar_Syntax_DsEnv.push_doc env3 mname d.FStar_Parser_AST.doc)
in (

let env5 = (FStar_All.pipe_right actions_docs (FStar_List.fold_left (fun env5 uu____19905 -> (match (uu____19905) with
| (a, doc1) -> begin
(

let env6 = (

let uu____19919 = (FStar_Syntax_Util.action_as_lb mname a a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_DsEnv.push_sigelt env5 uu____19919))
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

let uu____19943 = (desugar_binders env1 eff_binders)
in (match (uu____19943) with
| (env2, binders) -> begin
(

let uu____19962 = (

let uu____19981 = (head_and_args defn)
in (match (uu____19981) with
| (head1, args) -> begin
(

let lid = (match (head1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
l
end
| uu____20026 -> begin
(

let uu____20027 = (

let uu____20032 = (

let uu____20033 = (

let uu____20034 = (FStar_Parser_AST.term_to_string head1)
in (Prims.strcat uu____20034 " not found"))
in (Prims.strcat "Effect " uu____20033))
in ((FStar_Errors.Fatal_EffectNotFound), (uu____20032)))
in (FStar_Errors.raise_error uu____20027 d.FStar_Parser_AST.drange))
end)
in (

let ed = (FStar_Syntax_DsEnv.fail_or env2 (FStar_Syntax_DsEnv.try_lookup_effect_defn env2) lid)
in (

let uu____20036 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____20066))::args_rev -> begin
(

let uu____20078 = (

let uu____20079 = (unparen last_arg)
in uu____20079.FStar_Parser_AST.tm)
in (match (uu____20078) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____20107 -> begin
(([]), (args))
end))
end
| uu____20116 -> begin
(([]), (args))
end)
in (match (uu____20036) with
| (cattributes, args1) -> begin
(

let uu____20167 = (desugar_args env2 args1)
in (

let uu____20176 = (desugar_attributes env2 cattributes)
in ((lid), (ed), (uu____20167), (uu____20176))))
end))))
end))
in (match (uu____19962) with
| (ed_lid, ed, args, cattributes) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in ((match ((Prims.op_disEquality (FStar_List.length args) (FStar_List.length ed.FStar_Syntax_Syntax.binders))) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ArgumentLengthMismatch), ("Unexpected number of arguments to effect constructor")) defn.FStar_Parser_AST.range)
end
| uu____20231 -> begin
()
end);
(

let uu____20232 = (FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit)
in (match (uu____20232) with
| (ed_binders, uu____20246, ed_binders_opening) -> begin
(

let sub1 = (fun uu____20259 -> (match (uu____20259) with
| (us, x) -> begin
(

let x1 = (

let uu____20273 = (FStar_Syntax_Subst.shift_subst (FStar_List.length us) ed_binders_opening)
in (FStar_Syntax_Subst.subst uu____20273 x))
in (

let s = (FStar_Syntax_Util.subst_of_list ed_binders args)
in (

let uu____20277 = (

let uu____20278 = (FStar_Syntax_Subst.subst s x1)
in ((us), (uu____20278)))
in (FStar_Syntax_Subst.close_tscheme binders1 uu____20277))))
end))
in (

let mname = (FStar_Syntax_DsEnv.qualify env0 eff_name)
in (

let ed1 = (

let uu____20287 = (

let uu____20288 = (sub1 (([]), (ed.FStar_Syntax_Syntax.signature)))
in (FStar_Pervasives_Native.snd uu____20288))
in (

let uu____20303 = (sub1 ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____20304 = (sub1 ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____20305 = (sub1 ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____20306 = (sub1 ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____20307 = (sub1 ed.FStar_Syntax_Syntax.stronger)
in (

let uu____20308 = (sub1 ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____20309 = (sub1 ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____20310 = (sub1 ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____20311 = (sub1 ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____20312 = (sub1 ed.FStar_Syntax_Syntax.trivial)
in (

let uu____20313 = (

let uu____20314 = (sub1 (([]), (ed.FStar_Syntax_Syntax.repr)))
in (FStar_Pervasives_Native.snd uu____20314))
in (

let uu____20329 = (sub1 ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____20330 = (sub1 ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____20331 = (FStar_List.map (fun action -> (

let uu____20339 = (FStar_Syntax_DsEnv.qualify env2 action.FStar_Syntax_Syntax.action_unqualified_name)
in (

let uu____20340 = (

let uu____20341 = (sub1 (([]), (action.FStar_Syntax_Syntax.action_defn)))
in (FStar_Pervasives_Native.snd uu____20341))
in (

let uu____20356 = (

let uu____20357 = (sub1 (([]), (action.FStar_Syntax_Syntax.action_typ)))
in (FStar_Pervasives_Native.snd uu____20357))
in {FStar_Syntax_Syntax.action_name = uu____20339; FStar_Syntax_Syntax.action_unqualified_name = action.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = action.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = uu____20340; FStar_Syntax_Syntax.action_typ = uu____20356})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = cattributes; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = ed.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = uu____20287; FStar_Syntax_Syntax.ret_wp = uu____20303; FStar_Syntax_Syntax.bind_wp = uu____20304; FStar_Syntax_Syntax.if_then_else = uu____20305; FStar_Syntax_Syntax.ite_wp = uu____20306; FStar_Syntax_Syntax.stronger = uu____20307; FStar_Syntax_Syntax.close_wp = uu____20308; FStar_Syntax_Syntax.assert_p = uu____20309; FStar_Syntax_Syntax.assume_p = uu____20310; FStar_Syntax_Syntax.null_wp = uu____20311; FStar_Syntax_Syntax.trivial = uu____20312; FStar_Syntax_Syntax.repr = uu____20313; FStar_Syntax_Syntax.return_repr = uu____20329; FStar_Syntax_Syntax.bind_repr = uu____20330; FStar_Syntax_Syntax.actions = uu____20331; FStar_Syntax_Syntax.eff_attrs = ed.FStar_Syntax_Syntax.eff_attrs})))))))))))))))
in (

let se = (

let for_free = (

let uu____20374 = (

let uu____20375 = (

let uu____20382 = (FStar_Syntax_Util.arrow_formals ed1.FStar_Syntax_Syntax.signature)
in (FStar_Pervasives_Native.fst uu____20382))
in (FStar_List.length uu____20375))
in (Prims.op_Equality uu____20374 (Prims.parse_int "1")))
in (

let uu____20411 = (

let uu____20414 = (trans_qual1 (FStar_Pervasives_Native.Some (mname)))
in (FStar_List.map uu____20414 quals))
in {FStar_Syntax_Syntax.sigel = (match (for_free) with
| true -> begin
FStar_Syntax_Syntax.Sig_new_effect_for_free (ed1)
end
| uu____20419 -> begin
FStar_Syntax_Syntax.Sig_new_effect (ed1)
end); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = uu____20411; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))
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

let uu____20436 = (FStar_Syntax_Util.action_as_lb mname a a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_DsEnv.push_sigelt env5 uu____20436))
in (FStar_Syntax_DsEnv.push_doc env6 a.FStar_Syntax_Syntax.action_name doc1)))) env4))
in (

let env6 = (

let uu____20438 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____20438) with
| true -> begin
(

let reflect_lid = (

let uu____20442 = (FStar_Ident.id_of_text "reflect")
in (FStar_All.pipe_right uu____20442 (FStar_Syntax_DsEnv.qualify monad_env)))
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]
in (

let refl_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (FStar_Syntax_DsEnv.push_sigelt env5 refl_decl))))
end
| uu____20447 -> begin
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

let uu____20452 = (match (d.FStar_Parser_AST.doc) with
| FStar_Pervasives_Native.None -> begin
((""), ([]))
end
| FStar_Pervasives_Native.Some (fsdoc) -> begin
fsdoc
end)
in (match (uu____20452) with
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
| FStar_Pervasives_Native.Some (uu____20503) -> begin
(

let uu____20504 = (

let uu____20505 = (FStar_Parser_ToDocument.signature_to_document d)
in (FStar_Pprint.pretty_string 0.950000 (Prims.parse_int "80") uu____20505))
in (Prims.strcat "\n  " uu____20504))
end
| uu____20506 -> begin
""
end)
in (

let other = (FStar_List.filter_map (fun uu____20519 -> (match (uu____20519) with
| (k, v1) -> begin
(match (((Prims.op_disEquality k "summary") && (Prims.op_disEquality k "type"))) with
| true -> begin
FStar_Pervasives_Native.Some ((Prims.strcat k (Prims.strcat ": " v1)))
end
| uu____20530 -> begin
FStar_Pervasives_Native.None
end)
end)) kv)
in (

let other1 = (match ((Prims.op_disEquality other [])) with
| true -> begin
(Prims.strcat (FStar_String.concat "\n" other) "\n")
end
| uu____20534 -> begin
""
end)
in (

let str = (Prims.strcat summary (Prims.strcat pp (Prims.strcat other1 text)))
in (

let fv = (

let uu____20537 = (FStar_Ident.lid_of_str "FStar.Pervasives.Comment")
in (FStar_Syntax_Syntax.fvar uu____20537 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in (

let arg = (FStar_Syntax_Util.exp_string str)
in (

let uu____20539 = (

let uu____20548 = (FStar_Syntax_Syntax.as_arg arg)
in (uu____20548)::[])
in (FStar_Syntax_Util.mk_app fv uu____20539)))))))))
end)))
and desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (

let uu____20573 = (desugar_decl_noattrs env d)
in (match (uu____20573) with
| (env1, sigelts) -> begin
(

let attrs = d.FStar_Parser_AST.attrs
in (

let attrs1 = (FStar_List.map (desugar_term env1) attrs)
in (

let attrs2 = (

let uu____20591 = (mk_comment_attr d)
in (uu____20591)::attrs1)
in (

let uu____20592 = (FStar_List.map (fun sigelt -> (

let uu___136_20596 = sigelt
in {FStar_Syntax_Syntax.sigel = uu___136_20596.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___136_20596.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___136_20596.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___136_20596.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = attrs2})) sigelts)
in ((env1), (uu____20592))))))
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
| uu____20621 -> begin
()
end);
((env), ((se)::[]));
))
end
| FStar_Parser_AST.Fsdoc (uu____20622) -> begin
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

let uu____20630 = (FStar_Syntax_DsEnv.push_module_abbrev env x l)
in ((uu____20630), ([])))
end
| FStar_Parser_AST.Tycon (is_effect, tcs) -> begin
(

let quals = (match (is_effect) with
| true -> begin
(FStar_Parser_AST.Effect_qual)::d.FStar_Parser_AST.quals
end
| uu____20654 -> begin
d.FStar_Parser_AST.quals
end)
in (

let tcs1 = (FStar_List.map (fun uu____20667 -> (match (uu____20667) with
| (x, uu____20675) -> begin
x
end)) tcs)
in (

let uu____20680 = (FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals)
in (desugar_tycon env d uu____20680 tcs1))))
end
| FStar_Parser_AST.TopLevelLet (isrec, lets) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let expand_toplevel_pattern = ((Prims.op_Equality isrec FStar_Parser_AST.NoLetQualifier) && (match (lets) with
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatOp (uu____20702); FStar_Parser_AST.prange = uu____20703}, uu____20704))::[] -> begin
false
end
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____20713); FStar_Parser_AST.prange = uu____20714}, uu____20715))::[] -> begin
false
end
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____20730); FStar_Parser_AST.prange = uu____20731}, uu____20732); FStar_Parser_AST.prange = uu____20733}, uu____20734))::[] -> begin
false
end
| ((p, uu____20762))::[] -> begin
(

let uu____20771 = (is_app_pattern p)
in (not (uu____20771)))
end
| uu____20772 -> begin
false
end))
in (match ((not (expand_toplevel_pattern))) with
| true -> begin
(

let lets1 = (FStar_List.map (fun x -> ((FStar_Pervasives_Native.None), (x))) lets)
in (

let as_inner_let = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets1), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)
in (

let uu____20845 = (desugar_term_maybe_top true env as_inner_let)
in (match (uu____20845) with
| (ds_lets, aq) -> begin
((check_no_aq aq);
(

let uu____20857 = (

let uu____20858 = (FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets)
in uu____20858.FStar_Syntax_Syntax.n)
in (match (uu____20857) with
| FStar_Syntax_Syntax.Tm_let (lbs, uu____20866) -> begin
(

let fvs = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals1 = (match (quals) with
| (uu____20899)::uu____20900 -> begin
(FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals)
end
| uu____20903 -> begin
(FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.collect (fun uu___110_20918 -> (match (uu___110_20918) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (uu____20921); FStar_Syntax_Syntax.lbunivs = uu____20922; FStar_Syntax_Syntax.lbtyp = uu____20923; FStar_Syntax_Syntax.lbeff = uu____20924; FStar_Syntax_Syntax.lbdef = uu____20925; FStar_Syntax_Syntax.lbattrs = uu____20926; FStar_Syntax_Syntax.lbpos = uu____20927} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____20939; FStar_Syntax_Syntax.lbtyp = uu____20940; FStar_Syntax_Syntax.lbeff = uu____20941; FStar_Syntax_Syntax.lbdef = uu____20942; FStar_Syntax_Syntax.lbattrs = uu____20943; FStar_Syntax_Syntax.lbpos = uu____20944} -> begin
(FStar_Syntax_DsEnv.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals2 = (

let uu____20958 = (FStar_All.pipe_right lets1 (FStar_Util.for_some (fun uu____20989 -> (match (uu____20989) with
| (uu____21002, (uu____21003, t)) -> begin
(Prims.op_Equality t.FStar_Parser_AST.level FStar_Parser_AST.Formula)
end))))
in (match (uu____20958) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals1
end
| uu____21019 -> begin
quals1
end))
in (

let lbs1 = (

let uu____21027 = (FStar_All.pipe_right quals2 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____21027) with
| true -> begin
(

let uu____21036 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu___137_21050 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let uu___138_21052 = fv
in {FStar_Syntax_Syntax.fv_name = uu___138_21052.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = uu___138_21052.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = uu___137_21050.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___137_21050.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___137_21050.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___137_21050.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___137_21050.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___137_21050.FStar_Syntax_Syntax.lbpos})))))
in (((FStar_Pervasives_Native.fst lbs)), (uu____21036)))
end
| uu____21057 -> begin
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
| uu____21079 -> begin
(failwith "Desugaring a let did not produce a let")
end));
)
end))))
end
| uu____21084 -> begin
(

let uu____21085 = (match (lets) with
| ((pat, body))::[] -> begin
((pat), (body))
end
| uu____21104 -> begin
(failwith "expand_toplevel_pattern should only allow single definition lets")
end)
in (match (uu____21085) with
| (pat, body) -> begin
(

let fresh_toplevel_name = (FStar_Ident.gen FStar_Range.dummyRange)
in (

let fresh_pat = (

let var_pat = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((fresh_toplevel_name), (FStar_Pervasives_Native.None)))) FStar_Range.dummyRange)
in (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat1, ty) -> begin
(

let uu___139_21140 = pat1
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed (((var_pat), (ty))); FStar_Parser_AST.prange = uu___139_21140.FStar_Parser_AST.prange})
end
| uu____21147 -> begin
var_pat
end))
in (

let main_let = (desugar_decl env (

let uu___140_21154 = d
in {FStar_Parser_AST.d = FStar_Parser_AST.TopLevelLet (((isrec), ((((fresh_pat), (body)))::[]))); FStar_Parser_AST.drange = uu___140_21154.FStar_Parser_AST.drange; FStar_Parser_AST.doc = uu___140_21154.FStar_Parser_AST.doc; FStar_Parser_AST.quals = (FStar_Parser_AST.Private)::d.FStar_Parser_AST.quals; FStar_Parser_AST.attrs = uu___140_21154.FStar_Parser_AST.attrs}))
in (

let build_projection = (fun uu____21190 id1 -> (match (uu____21190) with
| (env1, ses) -> begin
(

let main = (

let uu____21211 = (

let uu____21212 = (FStar_Ident.lid_of_ids ((fresh_toplevel_name)::[]))
in FStar_Parser_AST.Var (uu____21212))
in (FStar_Parser_AST.mk_term uu____21211 FStar_Range.dummyRange FStar_Parser_AST.Expr))
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

let uu____21262 = (desugar_decl env1 id_decl)
in (match (uu____21262) with
| (env2, ses') -> begin
((env2), ((FStar_List.append ses ses')))
end))))))))
end))
in (

let bvs = (

let uu____21280 = (gather_pattern_bound_vars pat)
in (FStar_All.pipe_right uu____21280 FStar_Util.set_elements))
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

let uu____21305 = (close_fun env t)
in (desugar_term env uu____21305))
in (

let quals1 = (

let uu____21309 = ((FStar_Syntax_DsEnv.iface env) && (FStar_Syntax_DsEnv.admitted_iface env))
in (match (uu____21309) with
| true -> begin
(FStar_Parser_AST.Assumption)::quals
end
| uu____21312 -> begin
quals
end))
in (

let lid = (FStar_Syntax_DsEnv.qualify env id1)
in (

let se = (

let uu____21315 = (FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals1)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), ([]), (t1))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = uu____21315; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se)
in (

let env2 = (FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc)
in ((env2), ((se)::[])))))))))
end
| FStar_Parser_AST.Exception (id1, FStar_Pervasives_Native.None) -> begin
(

let uu____21323 = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_lid env) FStar_Parser_Const.exn_lid)
in (match (uu____21323) with
| (t, uu____21337) -> begin
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

let uu____21367 = (

let uu____21374 = (FStar_Syntax_Syntax.null_binder t)
in (uu____21374)::[])
in (

let uu____21387 = (

let uu____21390 = (

let uu____21391 = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_lid env) FStar_Parser_Const.exn_lid)
in (FStar_Pervasives_Native.fst uu____21391))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____21390))
in (FStar_Syntax_Util.arrow uu____21367 uu____21387)))
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

let uu____21450 = (FStar_Syntax_DsEnv.try_lookup_effect_name env l1)
in (match (uu____21450) with
| FStar_Pervasives_Native.None -> begin
(

let uu____21453 = (

let uu____21458 = (

let uu____21459 = (

let uu____21460 = (FStar_Syntax_Print.lid_to_string l1)
in (Prims.strcat uu____21460 " not found"))
in (Prims.strcat "Effect name " uu____21459))
in ((FStar_Errors.Fatal_EffectNotFound), (uu____21458)))
in (FStar_Errors.raise_error uu____21453 d.FStar_Parser_AST.drange))
end
| FStar_Pervasives_Native.Some (l2) -> begin
l2
end)))
in (

let src = (lookup1 l.FStar_Parser_AST.msource)
in (

let dst = (lookup1 l.FStar_Parser_AST.mdest)
in (

let uu____21464 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(

let uu____21482 = (

let uu____21491 = (

let uu____21498 = (desugar_term env t)
in (([]), (uu____21498)))
in FStar_Pervasives_Native.Some (uu____21491))
in ((uu____21482), (FStar_Pervasives_Native.None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(

let uu____21519 = (

let uu____21528 = (

let uu____21535 = (desugar_term env wp)
in (([]), (uu____21535)))
in FStar_Pervasives_Native.Some (uu____21528))
in (

let uu____21544 = (

let uu____21553 = (

let uu____21560 = (desugar_term env t)
in (([]), (uu____21560)))
in FStar_Pervasives_Native.Some (uu____21553))
in ((uu____21519), (uu____21544))))
end
| FStar_Parser_AST.LiftForFree (t) -> begin
(

let uu____21586 = (

let uu____21595 = (

let uu____21602 = (desugar_term env t)
in (([]), (uu____21602)))
in FStar_Pervasives_Native.Some (uu____21595))
in ((FStar_Pervasives_Native.None), (uu____21586)))
end)
in (match (uu____21464) with
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

let uu____21644 = (

let uu____21645 = (

let uu____21652 = (FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids)
in ((uu____21652), (t1)))
in FStar_Syntax_Syntax.Sig_splice (uu____21645))
in {FStar_Syntax_Syntax.sigel = uu____21644; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se)
in ((env1), ((se)::[])))))
end)))


let desugar_decls : env_t  ->  FStar_Parser_AST.decl Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env decls -> (

let uu____21678 = (FStar_List.fold_left (fun uu____21698 d -> (match (uu____21698) with
| (env1, sigelts) -> begin
(

let uu____21718 = (desugar_decl env1 d)
in (match (uu____21718) with
| (env2, se) -> begin
((env2), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls)
in (match (uu____21678) with
| (env1, sigelts) -> begin
(

let rec forward = (fun acc uu___112_21763 -> (match (uu___112_21763) with
| (se1)::(se2)::sigelts1 -> begin
(match (((se1.FStar_Syntax_Syntax.sigel), (se2.FStar_Syntax_Syntax.sigel))) with
| (FStar_Syntax_Syntax.Sig_declare_typ (uu____21777), FStar_Syntax_Syntax.Sig_let (uu____21778)) -> begin
(

let uu____21791 = (

let uu____21794 = (

let uu___141_21795 = se2
in (

let uu____21796 = (

let uu____21799 = (FStar_List.filter (fun uu___111_21813 -> (match (uu___111_21813) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____21817; FStar_Syntax_Syntax.vars = uu____21818}, uu____21819); FStar_Syntax_Syntax.pos = uu____21820; FStar_Syntax_Syntax.vars = uu____21821} when (

let uu____21844 = (

let uu____21845 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____21845))
in (Prims.op_Equality uu____21844 "FStar.Pervasives.Comment")) -> begin
true
end
| uu____21846 -> begin
false
end)) se1.FStar_Syntax_Syntax.sigattrs)
in (FStar_List.append uu____21799 se2.FStar_Syntax_Syntax.sigattrs))
in {FStar_Syntax_Syntax.sigel = uu___141_21795.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___141_21795.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___141_21795.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___141_21795.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu____21796}))
in (uu____21794)::(se1)::acc)
in (forward uu____21791 sigelts1))
end
| uu____21851 -> begin
(forward ((se1)::acc) ((se2)::sigelts1))
end)
end
| sigelts1 -> begin
(FStar_List.rev_append acc sigelts1)
end))
in (

let uu____21859 = (forward [] sigelts)
in ((env1), (uu____21859))))
end)))


let open_prims_all : (FStar_Parser_AST.decoration Prims.list  ->  FStar_Parser_AST.decl) Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Parser_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Parser_Const.all_lid)) FStar_Range.dummyRange))::[]


let generalize_annotated_univs : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun s -> (

let bs_univnames = (fun bs -> (

let uu____21901 = (

let uu____21914 = (FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name)
in (FStar_List.fold_left (fun uvs uu____21931 -> (match (uu____21931) with
| ({FStar_Syntax_Syntax.ppname = uu____21940; FStar_Syntax_Syntax.index = uu____21941; FStar_Syntax_Syntax.sort = t}, uu____21943) -> begin
(

let uu____21946 = (FStar_Syntax_Free.univnames t)
in (FStar_Util.set_union uvs uu____21946))
end)) uu____21914))
in (FStar_All.pipe_right bs uu____21901)))
in (

let empty_set = (FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name)
in (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____21960) -> begin
(failwith "Impossible: collect_annotated_universes: bare data/type constructor")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____21977) -> begin
(failwith "Impossible: collect_annotated_universes: bare data/type constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (sigs, lids) -> begin
(

let uvs = (

let uu____22003 = (FStar_All.pipe_right sigs (FStar_List.fold_left (fun uvs se -> (

let se_univs = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____22024, uu____22025, bs, t, uu____22028, uu____22029) -> begin
(

let uu____22038 = (bs_univnames bs)
in (

let uu____22041 = (FStar_Syntax_Free.univnames t)
in (FStar_Util.set_union uu____22038 uu____22041)))
end
| FStar_Syntax_Syntax.Sig_datacon (uu____22044, uu____22045, t, uu____22047, uu____22048, uu____22049) -> begin
(FStar_Syntax_Free.univnames t)
end
| uu____22054 -> begin
(failwith "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt")
end)
in (FStar_Util.set_union uvs se_univs))) empty_set))
in (FStar_All.pipe_right uu____22003 FStar_Util.set_elements))
in (

let usubst = (FStar_Syntax_Subst.univ_var_closing uvs)
in (

let uu___142_22062 = s
in (

let uu____22063 = (

let uu____22064 = (

let uu____22073 = (FStar_All.pipe_right sigs (FStar_List.map (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____22091, bs, t, lids1, lids2) -> begin
(

let uu___143_22104 = se
in (

let uu____22105 = (

let uu____22106 = (

let uu____22123 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let uu____22124 = (

let uu____22125 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst uu____22125 t))
in ((lid), (uvs), (uu____22123), (uu____22124), (lids1), (lids2))))
in FStar_Syntax_Syntax.Sig_inductive_typ (uu____22106))
in {FStar_Syntax_Syntax.sigel = uu____22105; FStar_Syntax_Syntax.sigrng = uu___143_22104.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___143_22104.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___143_22104.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___143_22104.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____22137, t, tlid, n1, lids1) -> begin
(

let uu___144_22146 = se
in (

let uu____22147 = (

let uu____22148 = (

let uu____22163 = (FStar_Syntax_Subst.subst usubst t)
in ((lid), (uvs), (uu____22163), (tlid), (n1), (lids1)))
in FStar_Syntax_Syntax.Sig_datacon (uu____22148))
in {FStar_Syntax_Syntax.sigel = uu____22147; FStar_Syntax_Syntax.sigrng = uu___144_22146.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___144_22146.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___144_22146.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___144_22146.FStar_Syntax_Syntax.sigattrs}))
end
| uu____22166 -> begin
(failwith "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt")
end))))
in ((uu____22073), (lids)))
in FStar_Syntax_Syntax.Sig_bundle (uu____22064))
in {FStar_Syntax_Syntax.sigel = uu____22063; FStar_Syntax_Syntax.sigrng = uu___142_22062.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___142_22062.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___142_22062.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___142_22062.FStar_Syntax_Syntax.sigattrs}))))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____22172, t) -> begin
(

let uvs = (

let uu____22177 = (FStar_Syntax_Free.univnames t)
in (FStar_All.pipe_right uu____22177 FStar_Util.set_elements))
in (

let uu___145_22184 = s
in (

let uu____22185 = (

let uu____22186 = (

let uu____22193 = (FStar_Syntax_Subst.close_univ_vars uvs t)
in ((lid), (uvs), (uu____22193)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____22186))
in {FStar_Syntax_Syntax.sigel = uu____22185; FStar_Syntax_Syntax.sigrng = uu___145_22184.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___145_22184.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___145_22184.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___145_22184.FStar_Syntax_Syntax.sigattrs})))
end
| FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) -> begin
(

let lb_univnames = (fun lb -> (

let uu____22215 = (FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____22218 = (match (lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, e, uu____22225) -> begin
(

let uvs1 = (bs_univnames bs)
in (

let uvs2 = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (uu____22254, (FStar_Util.Inl (t), uu____22256), uu____22257) -> begin
(FStar_Syntax_Free.univnames t)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____22304, (FStar_Util.Inr (c), uu____22306), uu____22307) -> begin
(FStar_Syntax_Free.univnames_comp c)
end
| uu____22354 -> begin
empty_set
end)
in (FStar_Util.set_union uvs1 uvs2)))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____22355, (FStar_Util.Inl (t), uu____22357), uu____22358) -> begin
(FStar_Syntax_Free.univnames t)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____22405, (FStar_Util.Inr (c), uu____22407), uu____22408) -> begin
(FStar_Syntax_Free.univnames_comp c)
end
| uu____22455 -> begin
empty_set
end)
in (FStar_Util.set_union uu____22215 uu____22218))))
in (

let all_lb_univs = (

let uu____22459 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun uvs lb -> (

let uu____22475 = (lb_univnames lb)
in (FStar_Util.set_union uvs uu____22475))) empty_set))
in (FStar_All.pipe_right uu____22459 FStar_Util.set_elements))
in (

let usubst = (FStar_Syntax_Subst.univ_var_closing all_lb_univs)
in (

let uu___146_22485 = s
in (

let uu____22486 = (

let uu____22487 = (

let uu____22494 = (

let uu____22495 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu___147_22507 = lb
in (

let uu____22508 = (FStar_Syntax_Subst.subst usubst lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____22511 = (FStar_Syntax_Subst.subst usubst lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___147_22507.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = all_lb_univs; FStar_Syntax_Syntax.lbtyp = uu____22508; FStar_Syntax_Syntax.lbeff = uu___147_22507.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____22511; FStar_Syntax_Syntax.lbattrs = uu___147_22507.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___147_22507.FStar_Syntax_Syntax.lbpos}))))))
in ((b), (uu____22495)))
in ((uu____22494), (lids)))
in FStar_Syntax_Syntax.Sig_let (uu____22487))
in {FStar_Syntax_Syntax.sigel = uu____22486; FStar_Syntax_Syntax.sigrng = uu___146_22485.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___146_22485.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___146_22485.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___146_22485.FStar_Syntax_Syntax.sigattrs})))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____22519, fml) -> begin
(

let uvs = (

let uu____22524 = (FStar_Syntax_Free.univnames fml)
in (FStar_All.pipe_right uu____22524 FStar_Util.set_elements))
in (

let uu___148_22531 = s
in (

let uu____22532 = (

let uu____22533 = (

let uu____22540 = (FStar_Syntax_Subst.close_univ_vars uvs fml)
in ((lid), (uvs), (uu____22540)))
in FStar_Syntax_Syntax.Sig_assume (uu____22533))
in {FStar_Syntax_Syntax.sigel = uu____22532; FStar_Syntax_Syntax.sigrng = uu___148_22531.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___148_22531.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___148_22531.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___148_22531.FStar_Syntax_Syntax.sigattrs})))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uu____22542, bs, c, flags1) -> begin
(

let uvs = (

let uu____22553 = (

let uu____22556 = (bs_univnames bs)
in (

let uu____22559 = (FStar_Syntax_Free.univnames_comp c)
in (FStar_Util.set_union uu____22556 uu____22559)))
in (FStar_All.pipe_right uu____22553 FStar_Util.set_elements))
in (

let usubst = (FStar_Syntax_Subst.univ_var_closing uvs)
in (

let uu___149_22569 = s
in (

let uu____22570 = (

let uu____22571 = (

let uu____22584 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let uu____22585 = (FStar_Syntax_Subst.subst_comp usubst c)
in ((lid), (uvs), (uu____22584), (uu____22585), (flags1))))
in FStar_Syntax_Syntax.Sig_effect_abbrev (uu____22571))
in {FStar_Syntax_Syntax.sigel = uu____22570; FStar_Syntax_Syntax.sigrng = uu___149_22569.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___149_22569.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___149_22569.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___149_22569.FStar_Syntax_Syntax.sigattrs}))))
end
| uu____22588 -> begin
s
end))))


let desugar_modul_common : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let env1 = (match (((curmod), (m))) with
| (FStar_Pervasives_Native.None, uu____22623) -> begin
env
end
| (FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.name = prev_lid; FStar_Syntax_Syntax.declarations = uu____22627; FStar_Syntax_Syntax.exports = uu____22628; FStar_Syntax_Syntax.is_interface = uu____22629}), FStar_Parser_AST.Module (current_lid, uu____22631)) when ((FStar_Ident.lid_equals prev_lid current_lid) && (FStar_Options.interactive ())) -> begin
env
end
| (FStar_Pervasives_Native.Some (prev_mod), uu____22639) -> begin
(

let uu____22642 = (FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod)
in (FStar_Pervasives_Native.fst uu____22642))
end)
in (

let uu____22647 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(

let uu____22683 = (FStar_Syntax_DsEnv.prepare_module_or_interface true admitted env1 mname FStar_Syntax_DsEnv.default_mii)
in ((uu____22683), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(

let uu____22700 = (FStar_Syntax_DsEnv.prepare_module_or_interface false false env1 mname FStar_Syntax_DsEnv.default_mii)
in ((uu____22700), (mname), (decls), (false)))
end)
in (match (uu____22647) with
| ((env2, pop_when_done), mname, decls, intf) -> begin
(

let uu____22730 = (desugar_decls env2 decls)
in (match (uu____22730) with
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

let uu____22799 = ((FStar_Options.interactive ()) && (

let uu____22801 = (

let uu____22802 = (

let uu____22803 = (FStar_Options.file_list ())
in (FStar_List.hd uu____22803))
in (FStar_Util.get_file_extension uu____22802))
in (FStar_List.mem uu____22801 (("fsti")::("fsi")::[]))))
in (match (uu____22799) with
| true -> begin
(as_interface m)
end
| uu____22806 -> begin
m
end))
in (

let uu____22807 = (desugar_modul_common curmod env m1)
in (match (uu____22807) with
| (x, y, pop_when_done) -> begin
((match (pop_when_done) with
| true -> begin
(

let uu____22822 = (FStar_Syntax_DsEnv.pop ())
in ())
end
| uu____22823 -> begin
()
end);
((x), (y));
)
end))))


let desugar_modul : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (

let uu____22842 = (desugar_modul_common FStar_Pervasives_Native.None env m)
in (match (uu____22842) with
| (env1, modul, pop_when_done) -> begin
(

let uu____22856 = (FStar_Syntax_DsEnv.finish_module_or_interface env1 modul)
in (match (uu____22856) with
| (env2, modul1) -> begin
((

let uu____22868 = (FStar_Options.dump_module modul1.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____22868) with
| true -> begin
(

let uu____22869 = (FStar_Syntax_Print.modul_to_string modul1)
in (FStar_Util.print1 "Module after desugaring:\n%s\n" uu____22869))
end
| uu____22870 -> begin
()
end));
(

let uu____22871 = (match (pop_when_done) with
| true -> begin
(FStar_Syntax_DsEnv.export_interface modul1.FStar_Syntax_Syntax.name env2)
end
| uu____22872 -> begin
env2
end)
in ((uu____22871), (modul1)));
)
end))
end)))


let ast_modul_to_modul : FStar_Parser_AST.modul  ->  FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv = (fun modul env -> (

let uu____22889 = (desugar_modul env modul)
in (match (uu____22889) with
| (env1, modul1) -> begin
((modul1), (env1))
end)))


let decls_to_sigelts : FStar_Parser_AST.decl Prims.list  ->  FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv = (fun decls env -> (

let uu____22920 = (desugar_decls env decls)
in (match (uu____22920) with
| (env1, sigelts) -> begin
((sigelts), (env1))
end)))


let partial_ast_modul_to_modul : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Parser_AST.modul  ->  FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv = (fun modul a_modul env -> (

let uu____22962 = (desugar_partial_modul modul env a_modul)
in (match (uu____22962) with
| (env1, modul1) -> begin
((modul1), (env1))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Syntax_DsEnv.module_inclusion_info  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  unit FStar_Syntax_DsEnv.withenv = (fun m mii erase_univs en -> (

let erase_univs_ed = (fun ed -> (

let erase_binders = (fun bs -> (match (bs) with
| [] -> begin
[]
end
| uu____23048 -> begin
(

let t = (

let uu____23056 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (FStar_Syntax_Syntax.t_unit), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (erase_univs uu____23056))
in (

let uu____23067 = (

let uu____23068 = (FStar_Syntax_Subst.compress t)
in uu____23068.FStar_Syntax_Syntax.n)
in (match (uu____23067) with
| FStar_Syntax_Syntax.Tm_abs (bs1, uu____23078, uu____23079) -> begin
bs1
end
| uu____23100 -> begin
(failwith "Impossible")
end)))
end))
in (

let uu____23107 = (

let uu____23114 = (erase_binders ed.FStar_Syntax_Syntax.binders)
in (FStar_Syntax_Subst.open_term' uu____23114 FStar_Syntax_Syntax.t_unit))
in (match (uu____23107) with
| (binders, uu____23116, binders_opening) -> begin
(

let erase_term = (fun t -> (

let uu____23124 = (

let uu____23125 = (FStar_Syntax_Subst.subst binders_opening t)
in (erase_univs uu____23125))
in (FStar_Syntax_Subst.close binders uu____23124)))
in (

let erase_tscheme = (fun uu____23143 -> (match (uu____23143) with
| (us, t) -> begin
(

let t1 = (

let uu____23163 = (FStar_Syntax_Subst.shift_subst (FStar_List.length us) binders_opening)
in (FStar_Syntax_Subst.subst uu____23163 t))
in (

let uu____23166 = (

let uu____23167 = (erase_univs t1)
in (FStar_Syntax_Subst.close binders uu____23167))
in (([]), (uu____23166))))
end))
in (

let erase_action = (fun action -> (

let opening = (FStar_Syntax_Subst.shift_subst (FStar_List.length action.FStar_Syntax_Syntax.action_univs) binders_opening)
in (

let erased_action_params = (match (action.FStar_Syntax_Syntax.action_params) with
| [] -> begin
[]
end
| uu____23198 -> begin
(

let bs = (

let uu____23206 = (FStar_Syntax_Subst.subst_binders opening action.FStar_Syntax_Syntax.action_params)
in (FStar_All.pipe_left erase_binders uu____23206))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (FStar_Syntax_Syntax.t_unit), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____23238 = (

let uu____23239 = (

let uu____23242 = (FStar_Syntax_Subst.close binders t)
in (FStar_Syntax_Subst.compress uu____23242))
in uu____23239.FStar_Syntax_Syntax.n)
in (match (uu____23238) with
| FStar_Syntax_Syntax.Tm_abs (bs1, uu____23250, uu____23251) -> begin
bs1
end
| uu____23272 -> begin
(failwith "Impossible")
end))))
end)
in (

let erase_term1 = (fun t -> (

let uu____23285 = (

let uu____23286 = (FStar_Syntax_Subst.subst opening t)
in (erase_univs uu____23286))
in (FStar_Syntax_Subst.close binders uu____23285)))
in (

let uu___150_23287 = action
in (

let uu____23288 = (erase_term1 action.FStar_Syntax_Syntax.action_defn)
in (

let uu____23289 = (erase_term1 action.FStar_Syntax_Syntax.action_typ)
in {FStar_Syntax_Syntax.action_name = uu___150_23287.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___150_23287.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = erased_action_params; FStar_Syntax_Syntax.action_defn = uu____23288; FStar_Syntax_Syntax.action_typ = uu____23289})))))))
in (

let uu___151_23290 = ed
in (

let uu____23291 = (FStar_Syntax_Subst.close_binders binders)
in (

let uu____23292 = (erase_term ed.FStar_Syntax_Syntax.signature)
in (

let uu____23293 = (erase_tscheme ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____23294 = (erase_tscheme ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____23295 = (erase_tscheme ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____23296 = (erase_tscheme ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____23297 = (erase_tscheme ed.FStar_Syntax_Syntax.stronger)
in (

let uu____23298 = (erase_tscheme ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____23299 = (erase_tscheme ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____23300 = (erase_tscheme ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____23301 = (erase_tscheme ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____23302 = (erase_tscheme ed.FStar_Syntax_Syntax.trivial)
in (

let uu____23303 = (erase_term ed.FStar_Syntax_Syntax.repr)
in (

let uu____23304 = (erase_tscheme ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____23305 = (erase_tscheme ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____23306 = (FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = uu___151_23290.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___151_23290.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = uu____23291; FStar_Syntax_Syntax.signature = uu____23292; FStar_Syntax_Syntax.ret_wp = uu____23293; FStar_Syntax_Syntax.bind_wp = uu____23294; FStar_Syntax_Syntax.if_then_else = uu____23295; FStar_Syntax_Syntax.ite_wp = uu____23296; FStar_Syntax_Syntax.stronger = uu____23297; FStar_Syntax_Syntax.close_wp = uu____23298; FStar_Syntax_Syntax.assert_p = uu____23299; FStar_Syntax_Syntax.assume_p = uu____23300; FStar_Syntax_Syntax.null_wp = uu____23301; FStar_Syntax_Syntax.trivial = uu____23302; FStar_Syntax_Syntax.repr = uu____23303; FStar_Syntax_Syntax.return_repr = uu____23304; FStar_Syntax_Syntax.bind_repr = uu____23305; FStar_Syntax_Syntax.actions = uu____23306; FStar_Syntax_Syntax.eff_attrs = uu___151_23290.FStar_Syntax_Syntax.eff_attrs}))))))))))))))))))))
end))))
in (

let push_sigelt1 = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let se' = (

let uu___152_23322 = se
in (

let uu____23323 = (

let uu____23324 = (erase_univs_ed ed)
in FStar_Syntax_Syntax.Sig_new_effect (uu____23324))
in {FStar_Syntax_Syntax.sigel = uu____23323; FStar_Syntax_Syntax.sigrng = uu___152_23322.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___152_23322.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___152_23322.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___152_23322.FStar_Syntax_Syntax.sigattrs}))
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se')
in (push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng)))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed) -> begin
(

let se' = (

let uu___153_23328 = se
in (

let uu____23329 = (

let uu____23330 = (erase_univs_ed ed)
in FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____23330))
in {FStar_Syntax_Syntax.sigel = uu____23329; FStar_Syntax_Syntax.sigrng = uu___153_23328.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___153_23328.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___153_23328.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___153_23328.FStar_Syntax_Syntax.sigattrs}))
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se')
in (push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng)))
end
| uu____23332 -> begin
(FStar_Syntax_DsEnv.push_sigelt env se)
end))
in (

let uu____23333 = (FStar_Syntax_DsEnv.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name mii)
in (match (uu____23333) with
| (en1, pop_when_done) -> begin
(

let en2 = (

let uu____23345 = (FStar_Syntax_DsEnv.set_current_module en1 m.FStar_Syntax_Syntax.name)
in (FStar_List.fold_left push_sigelt1 uu____23345 m.FStar_Syntax_Syntax.exports))
in (

let env = (FStar_Syntax_DsEnv.finish en2 m)
in (

let uu____23347 = (match (pop_when_done) with
| true -> begin
(FStar_Syntax_DsEnv.export_interface m.FStar_Syntax_Syntax.name env)
end
| uu____23348 -> begin
env
end)
in ((()), (uu____23347)))))
end)))))




