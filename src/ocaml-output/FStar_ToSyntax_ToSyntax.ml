
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
| uu____1045 -> begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (

let uu____1056 = (

let uu____1057 = (

let uu____1062 = (tm_type x.FStar_Ident.idRange)
in ((x), (uu____1062)))
in FStar_Parser_AST.TAnnotated (uu____1057))
in (FStar_Parser_AST.mk_binder uu____1056 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end)))


let close_fun : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (

let uu____1079 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv uu____1079))
in (match ((Prims.op_Equality (FStar_List.length ftv) (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____1087 -> begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (

let uu____1098 = (

let uu____1099 = (

let uu____1104 = (tm_type x.FStar_Ident.idRange)
in ((x), (uu____1104)))
in FStar_Parser_AST.TAnnotated (uu____1099))
in (FStar_Parser_AST.mk_binder uu____1098 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))))))
in (

let t1 = (

let uu____1106 = (

let uu____1107 = (unparen t)
in uu____1107.FStar_Parser_AST.tm)
in (match (uu____1106) with
| FStar_Parser_AST.Product (uu____1108) -> begin
t
end
| uu____1115 -> begin
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
| uu____1151 -> begin
((bs), (t))
end))


let rec is_var_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatWild -> begin
true
end
| FStar_Parser_AST.PatTvar (uu____1159, uu____1160) -> begin
true
end
| FStar_Parser_AST.PatVar (uu____1165, uu____1166) -> begin
true
end
| FStar_Parser_AST.PatAscribed (p1, uu____1172) -> begin
(is_var_pattern p1)
end
| uu____1185 -> begin
false
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p1, uu____1192) -> begin
(is_app_pattern p1)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____1205); FStar_Parser_AST.prange = uu____1206}, uu____1207) -> begin
true
end
| uu____1218 -> begin
false
end))


let replace_unit_pattern : FStar_Parser_AST.pattern  ->  FStar_Parser_AST.pattern = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatConst (FStar_Const.Const_unit) -> begin
(FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatAscribed ((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)), (((unit_ty), (FStar_Pervasives_Native.None)))))) p.FStar_Parser_AST.prange)
end
| uu____1232 -> begin
p
end))


let rec destruct_app_pattern : FStar_Syntax_DsEnv.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * (FStar_Parser_AST.term * FStar_Parser_AST.term FStar_Pervasives_Native.option) FStar_Pervasives_Native.option) = (fun env is_top_level1 p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p1, t) -> begin
(

let uu____1302 = (destruct_app_pattern env is_top_level1 p1)
in (match (uu____1302) with
| (name, args, uu____1345) -> begin
((name), (args), (FStar_Pervasives_Native.Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id1, uu____1395); FStar_Parser_AST.prange = uu____1396}, args) when is_top_level1 -> begin
(

let uu____1406 = (

let uu____1411 = (FStar_Syntax_DsEnv.qualify env id1)
in FStar_Util.Inr (uu____1411))
in ((uu____1406), (args), (FStar_Pervasives_Native.None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id1, uu____1433); FStar_Parser_AST.prange = uu____1434}, args) -> begin
((FStar_Util.Inl (id1)), (args), (FStar_Pervasives_Native.None))
end
| uu____1464 -> begin
(failwith "Not an app pattern")
end))


let rec gather_pattern_bound_vars_maybe_top : FStar_Ident.ident FStar_Util.set  ->  FStar_Parser_AST.pattern  ->  FStar_Ident.ident FStar_Util.set = (fun acc p -> (

let gather_pattern_bound_vars_from_list = (FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc)
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatWild -> begin
acc
end
| FStar_Parser_AST.PatConst (uu____1514) -> begin
acc
end
| FStar_Parser_AST.PatVar (uu____1515, FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)) -> begin
acc
end
| FStar_Parser_AST.PatName (uu____1518) -> begin
acc
end
| FStar_Parser_AST.PatTvar (uu____1519) -> begin
acc
end
| FStar_Parser_AST.PatOp (uu____1526) -> begin
acc
end
| FStar_Parser_AST.PatApp (phead, pats) -> begin
(gather_pattern_bound_vars_from_list ((phead)::pats))
end
| FStar_Parser_AST.PatVar (x, uu____1534) -> begin
(FStar_Util.set_add x acc)
end
| FStar_Parser_AST.PatList (pats) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatTuple (pats, uu____1543) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatOr (pats) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatRecord (guarded_pats) -> begin
(

let uu____1558 = (FStar_List.map FStar_Pervasives_Native.snd guarded_pats)
in (gather_pattern_bound_vars_from_list uu____1558))
end
| FStar_Parser_AST.PatAscribed (pat, uu____1566) -> begin
(gather_pattern_bound_vars_maybe_top acc pat)
end)))


let gather_pattern_bound_vars : FStar_Parser_AST.pattern  ->  FStar_Ident.ident FStar_Util.set = (

let acc = (FStar_Util.new_set (fun id1 id2 -> (match ((Prims.op_Equality id1.FStar_Ident.idText id2.FStar_Ident.idText)) with
| true -> begin
(Prims.parse_int "0")
end
| uu____1592 -> begin
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
| uu____1628 -> begin
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
| uu____1664 -> begin
false
end))


let __proj__LetBinder__item___0 : bnd  ->  (FStar_Ident.lident * (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)) = (fun projectee -> (match (projectee) with
| LetBinder (_0) -> begin
_0
end))


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun uu___88_1710 -> (match (uu___88_1710) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| uu____1717 -> begin
(failwith "Impossible")
end))


let as_binder : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  (FStar_Ident.ident FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.binder * FStar_Syntax_DsEnv.env) = (fun env imp uu___89_1750 -> (match (uu___89_1750) with
| (FStar_Pervasives_Native.None, k) -> begin
(

let uu____1772 = (FStar_Syntax_Syntax.null_binder k)
in ((uu____1772), (env)))
end
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____1781 = (FStar_Syntax_DsEnv.push_bv env a)
in (match (uu____1781) with
| (env1, a1) -> begin
(((((

let uu___113_1801 = a1
in {FStar_Syntax_Syntax.ppname = uu___113_1801.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___113_1801.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), ((trans_aqual imp)))), (env1))
end))
end))


type env_t =
FStar_Syntax_DsEnv.env


type lenv_t =
FStar_Syntax_Syntax.bv Prims.list


let mk_lb : (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list * (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)  ->  FStar_Syntax_Syntax.letbinding = (fun uu____1830 -> (match (uu____1830) with
| (attrs, n1, t, e, pos) -> begin
{FStar_Syntax_Syntax.lbname = n1; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = attrs; FStar_Syntax_Syntax.lbpos = pos}
end))


let no_annot_abs : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs t -> (FStar_Syntax_Util.abs bs t FStar_Pervasives_Native.None))


let mk_ref_read : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun tm -> (

let tm' = (

let uu____1910 = (

let uu____1925 = (

let uu____1928 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____1928))
in (

let uu____1929 = (

let uu____1938 = (

let uu____1945 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (uu____1945)))
in (uu____1938)::[])
in ((uu____1925), (uu____1929))))
in FStar_Syntax_Syntax.Tm_app (uu____1910))
in (FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_alloc : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun tm -> (

let tm' = (

let uu____1982 = (

let uu____1997 = (

let uu____2000 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____2000))
in (

let uu____2001 = (

let uu____2010 = (

let uu____2017 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (uu____2017)))
in (uu____2010)::[])
in ((uu____1997), (uu____2001))))
in FStar_Syntax_Syntax.Tm_app (uu____1982))
in (FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_assign : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t1 t2 pos -> (

let tm = (

let uu____2068 = (

let uu____2083 = (

let uu____2086 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____2086))
in (

let uu____2087 = (

let uu____2096 = (

let uu____2103 = (FStar_Syntax_Syntax.as_implicit false)
in ((t1), (uu____2103)))
in (

let uu____2106 = (

let uu____2115 = (

let uu____2122 = (FStar_Syntax_Syntax.as_implicit false)
in ((t2), (uu____2122)))
in (uu____2115)::[])
in (uu____2096)::uu____2106))
in ((uu____2083), (uu____2087))))
in FStar_Syntax_Syntax.Tm_app (uu____2068))
in (FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos)))


let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun uu___90_2157 -> (match (uu___90_2157) with
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
| uu____2158 -> begin
false
end))


let rec sum_to_universe : FStar_Syntax_Syntax.universe  ->  Prims.int  ->  FStar_Syntax_Syntax.universe = (fun u n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
u
end
| uu____2169 -> begin
(

let uu____2170 = (sum_to_universe u (n1 - (Prims.parse_int "1")))
in FStar_Syntax_Syntax.U_succ (uu____2170))
end))


let int_to_universe : Prims.int  ->  FStar_Syntax_Syntax.universe = (fun n1 -> (sum_to_universe FStar_Syntax_Syntax.U_zero n1))


let rec desugar_maybe_non_constant_universe : FStar_Parser_AST.term  ->  (Prims.int, FStar_Syntax_Syntax.universe) FStar_Util.either = (fun t -> (

let uu____2189 = (

let uu____2190 = (unparen t)
in uu____2190.FStar_Parser_AST.tm)
in (match (uu____2189) with
| FStar_Parser_AST.Wild -> begin
(

let uu____2195 = (

let uu____2196 = (FStar_Syntax_Unionfind.univ_fresh ())
in FStar_Syntax_Syntax.U_unif (uu____2196))
in FStar_Util.Inr (uu____2195))
end
| FStar_Parser_AST.Uvar (u) -> begin
FStar_Util.Inr (FStar_Syntax_Syntax.U_name (u))
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (repr, uu____2207)) -> begin
(

let n1 = (FStar_Util.int_of_string repr)
in ((match ((n1 < (Prims.parse_int "0"))) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_NegativeUniverseConstFatal_NotSupported), ((Prims.strcat "Negative universe constant  are not supported : " repr))) t.FStar_Parser_AST.range)
end
| uu____2222 -> begin
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

let uu____2272 = (sum_to_universe u n1)
in FStar_Util.Inr (uu____2272))
end
| (FStar_Util.Inr (u), FStar_Util.Inl (n1)) -> begin
(

let uu____2283 = (sum_to_universe u n1)
in FStar_Util.Inr (uu____2283))
end
| (FStar_Util.Inr (u11), FStar_Util.Inr (u21)) -> begin
(

let uu____2294 = (

let uu____2299 = (

let uu____2300 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "This universe might contain a sum of two universe variables " uu____2300))
in ((FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars), (uu____2299)))
in (FStar_Errors.raise_error uu____2294 t.FStar_Parser_AST.range))
end)))
end
| FStar_Parser_AST.App (uu____2305) -> begin
(

let rec aux = (fun t1 univargs -> (

let uu____2339 = (

let uu____2340 = (unparen t1)
in uu____2340.FStar_Parser_AST.tm)
in (match (uu____2339) with
| FStar_Parser_AST.App (t2, targ, uu____2347) -> begin
(

let uarg = (desugar_maybe_non_constant_universe targ)
in (aux t2 ((uarg)::univargs)))
end
| FStar_Parser_AST.Var (max_lid1) -> begin
(match ((FStar_List.existsb (fun uu___91_2370 -> (match (uu___91_2370) with
| FStar_Util.Inr (uu____2375) -> begin
true
end
| uu____2376 -> begin
false
end)) univargs)) with
| true -> begin
(

let uu____2381 = (

let uu____2382 = (FStar_List.map (fun uu___92_2391 -> (match (uu___92_2391) with
| FStar_Util.Inl (n1) -> begin
(int_to_universe n1)
end
| FStar_Util.Inr (u) -> begin
u
end)) univargs)
in FStar_Syntax_Syntax.U_max (uu____2382))
in FStar_Util.Inr (uu____2381))
end
| uu____2398 -> begin
(

let nargs = (FStar_List.map (fun uu___93_2408 -> (match (uu___93_2408) with
| FStar_Util.Inl (n1) -> begin
n1
end
| FStar_Util.Inr (uu____2414) -> begin
(failwith "impossible")
end)) univargs)
in (

let uu____2415 = (FStar_List.fold_left (fun m n1 -> (match ((m > n1)) with
| true -> begin
m
end
| uu____2420 -> begin
n1
end)) (Prims.parse_int "0") nargs)
in FStar_Util.Inl (uu____2415)))
end)
end
| uu____2421 -> begin
(

let uu____2422 = (

let uu____2427 = (

let uu____2428 = (

let uu____2429 = (FStar_Parser_AST.term_to_string t1)
in (Prims.strcat uu____2429 " in universe context"))
in (Prims.strcat "Unexpected term " uu____2428))
in ((FStar_Errors.Fatal_UnexpectedTermInUniverse), (uu____2427)))
in (FStar_Errors.raise_error uu____2422 t1.FStar_Parser_AST.range))
end)))
in (aux t []))
end
| uu____2438 -> begin
(

let uu____2439 = (

let uu____2444 = (

let uu____2445 = (

let uu____2446 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat uu____2446 " in universe context"))
in (Prims.strcat "Unexpected term " uu____2445))
in ((FStar_Errors.Fatal_UnexpectedTermInUniverse), (uu____2444)))
in (FStar_Errors.raise_error uu____2439 t.FStar_Parser_AST.range))
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
| ((bv, b, e))::uu____2479 -> begin
(

let uu____2502 = (

let uu____2507 = (

let uu____2508 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format2 "Unexpected antiquotation: %s(%s)" (match (b) with
| true -> begin
"`@"
end
| uu____2509 -> begin
"`#"
end) uu____2508))
in ((FStar_Errors.Fatal_UnexpectedAntiquotation), (uu____2507)))
in (FStar_Errors.raise_error uu____2502 e.FStar_Syntax_Syntax.pos))
end))


let check_fields : 'Auu____2518 . FStar_Syntax_DsEnv.env  ->  (FStar_Ident.lident * 'Auu____2518) Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_DsEnv.record_or_dc = (fun env fields rg -> (

let uu____2546 = (FStar_List.hd fields)
in (match (uu____2546) with
| (f, uu____2556) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f);
(

let record = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f)
in (

let check_field = (fun uu____2568 -> (match (uu____2568) with
| (f', uu____2574) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f');
(

let uu____2576 = (FStar_Syntax_DsEnv.belongs_to_record env f' record)
in (match (uu____2576) with
| true -> begin
()
end
| uu____2577 -> begin
(

let msg = (FStar_Util.format3 "Field %s belongs to record type %s, whereas field %s does not" f.FStar_Ident.str record.FStar_Syntax_DsEnv.typename.FStar_Ident.str f'.FStar_Ident.str)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_FieldsNotBelongToSameRecordType), (msg)) rg))
end));
)
end))
in ((

let uu____2580 = (FStar_List.tl fields)
in (FStar_List.iter check_field uu____2580));
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
| FStar_Syntax_Syntax.Pat_dot_term (uu____2939) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_wild (uu____2946) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_constant (uu____2947) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (uu____2949, pats1) -> begin
(

let aux = (fun out uu____2987 -> (match (uu____2987) with
| (p2, uu____2999) -> begin
(

let intersection = (

let uu____3007 = (pat_vars p2)
in (FStar_Util.set_intersect uu____3007 out))
in (

let uu____3010 = (FStar_Util.set_is_empty intersection)
in (match (uu____3010) with
| true -> begin
(

let uu____3013 = (pat_vars p2)
in (FStar_Util.set_union out uu____3013))
end
| uu____3016 -> begin
(

let duplicate_bv = (

let uu____3018 = (FStar_Util.set_elements intersection)
in (FStar_List.hd uu____3018))
in (

let uu____3021 = (

let uu____3026 = (FStar_Util.format1 "Non-linear patterns are not permitted. %s appears more than once in this pattern." duplicate_bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in ((FStar_Errors.Fatal_NonLinearPatternNotPermitted), (uu____3026)))
in (FStar_Errors.raise_error uu____3021 r)))
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

let uu____3046 = (pat_vars p1)
in (FStar_All.pipe_right uu____3046 (fun a238 -> ())))
end
| (p1)::ps -> begin
(

let pvars = (pat_vars p1)
in (

let aux = (fun p2 -> (

let uu____3074 = (

let uu____3075 = (pat_vars p2)
in (FStar_Util.set_eq pvars uu____3075))
in (match (uu____3074) with
| true -> begin
()
end
| uu____3078 -> begin
(

let nonlinear_vars = (

let uu____3082 = (pat_vars p2)
in (FStar_Util.set_symmetric_difference pvars uu____3082))
in (

let first_nonlinear_var = (

let uu____3086 = (FStar_Util.set_elements nonlinear_vars)
in (FStar_List.hd uu____3086))
in (

let uu____3089 = (

let uu____3094 = (FStar_Util.format1 "Patterns in this match are incoherent, variable %s is bound in some but not all patterns." first_nonlinear_var.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in ((FStar_Errors.Fatal_IncoherentPatterns), (uu____3094)))
in (FStar_Errors.raise_error uu____3089 r))))
end)))
in (FStar_List.iter aux ps)))
end)))
in ((match (((is_mut), (p.FStar_Parser_AST.pat))) with
| (false, uu____3098) -> begin
()
end
| (true, FStar_Parser_AST.PatVar (uu____3099)) -> begin
()
end
| (true, uu____3106) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_LetMutableForVariablesOnly), ("let-mutable is for variables only")) p.FStar_Parser_AST.prange)
end);
(

let resolvex = (fun l e x -> (

let uu____3129 = (FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (Prims.op_Equality y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText x.FStar_Ident.idText))))
in (match (uu____3129) with
| FStar_Pervasives_Native.Some (y) -> begin
((l), (e), (y))
end
| uu____3145 -> begin
(

let uu____3148 = (match (is_mut) with
| true -> begin
(FStar_Syntax_DsEnv.push_bv_mutable e x)
end
| uu____3157 -> begin
(FStar_Syntax_DsEnv.push_bv e x)
end)
in (match (uu____3148) with
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
| FStar_Parser_AST.PatOr (uu____3260) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.PatOp (op) -> begin
(

let uu____3276 = (

let uu____3277 = (

let uu____3278 = (

let uu____3285 = (

let uu____3286 = (

let uu____3291 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") op.FStar_Ident.idText op.FStar_Ident.idRange)
in ((uu____3291), (op.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____3286))
in ((uu____3285), (FStar_Pervasives_Native.None)))
in FStar_Parser_AST.PatVar (uu____3278))
in {FStar_Parser_AST.pat = uu____3277; FStar_Parser_AST.prange = p1.FStar_Parser_AST.prange})
in (aux loc env1 uu____3276))
end
| FStar_Parser_AST.PatAscribed (p2, (t, tacopt)) -> begin
((match (tacopt) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (uu____3308) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly), ("Type ascriptions within patterns are cannot be associated with a tactic")) orig.FStar_Parser_AST.prange)
end);
(

let uu____3309 = (aux loc env1 p2)
in (match (uu____3309) with
| (loc1, env', binder, p3, imp) -> begin
(

let annot_pat_var = (fun p4 t1 -> (match (p4.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu___114_3367 = p4
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var ((

let uu___115_3372 = x
in {FStar_Syntax_Syntax.ppname = uu___115_3372.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___115_3372.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})); FStar_Syntax_Syntax.p = uu___114_3367.FStar_Syntax_Syntax.p})
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu___116_3374 = p4
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild ((

let uu___117_3379 = x
in {FStar_Syntax_Syntax.ppname = uu___117_3379.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___117_3379.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})); FStar_Syntax_Syntax.p = uu___116_3374.FStar_Syntax_Syntax.p})
end
| uu____3380 when top -> begin
p4
end
| uu____3381 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly), ("Type ascriptions within patterns are only allowed on variables")) orig.FStar_Parser_AST.prange)
end))
in (

let uu____3384 = (match (binder) with
| LetBinder (uu____3397) -> begin
(failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t1 = (

let uu____3417 = (close_fun env1 t)
in (desugar_term env1 uu____3417))
in ((match ((match (x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
false
end
| uu____3419 -> begin
true
end)) with
| true -> begin
(

let uu____3420 = (

let uu____3425 = (

let uu____3426 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____3427 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____3428 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.format3 "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n" uu____3426 uu____3427 uu____3428))))
in ((FStar_Errors.Warning_MultipleAscriptions), (uu____3425)))
in (FStar_Errors.log_issue orig.FStar_Parser_AST.prange uu____3420))
end
| uu____3429 -> begin
()
end);
(

let uu____3430 = (annot_pat_var p3 t1)
in ((uu____3430), (LocalBinder ((((

let uu___118_3436 = x
in {FStar_Syntax_Syntax.ppname = uu___118_3436.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___118_3436.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})), (aq))))));
))
end)
in (match (uu____3384) with
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

let uu____3458 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3458), (false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____3467 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3467), (false))))
end
| FStar_Parser_AST.PatTvar (x, aq) -> begin
(

let imp = (Prims.op_Equality aq (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))
in (

let aq1 = (trans_aqual aq)
in (

let uu____3486 = (resolvex loc env1 x)
in (match (uu____3486) with
| (loc1, env2, xbv) -> begin
(

let uu____3508 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc1), (env2), (LocalBinder (((xbv), (aq1)))), (uu____3508), (imp)))
end))))
end
| FStar_Parser_AST.PatVar (x, aq) -> begin
(

let imp = (Prims.op_Equality aq (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))
in (

let aq1 = (trans_aqual aq)
in (

let uu____3527 = (resolvex loc env1 x)
in (match (uu____3527) with
| (loc1, env2, xbv) -> begin
(

let uu____3549 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc1), (env2), (LocalBinder (((xbv), (aq1)))), (uu____3549), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l1 = (FStar_Syntax_DsEnv.fail_or env1 (FStar_Syntax_DsEnv.try_lookup_datacon env1) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____3559 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), ([])))))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3559), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = uu____3581}, args) -> begin
(

let uu____3587 = (FStar_List.fold_right (fun arg uu____3628 -> (match (uu____3628) with
| (loc1, env2, args1) -> begin
(

let uu____3676 = (aux loc1 env2 arg)
in (match (uu____3676) with
| (loc2, env3, uu____3705, arg1, imp) -> begin
((loc2), (env3), ((((arg1), (imp)))::args1))
end))
end)) args ((loc), (env1), ([])))
in (match (uu____3587) with
| (loc1, env2, args1) -> begin
(

let l1 = (FStar_Syntax_DsEnv.fail_or env2 (FStar_Syntax_DsEnv.try_lookup_datacon env2) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____3775 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args1)))))
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3775), (false)))))
end))
end
| FStar_Parser_AST.PatApp (uu____3790) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedPattern), ("Unexpected pattern")) p1.FStar_Parser_AST.prange)
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____3812 = (FStar_List.fold_right (fun pat uu____3845 -> (match (uu____3845) with
| (loc1, env2, pats1) -> begin
(

let uu____3877 = (aux loc1 env2 pat)
in (match (uu____3877) with
| (loc2, env3, uu____3902, pat1, uu____3904) -> begin
((loc2), (env3), ((pat1)::pats1))
end))
end)) pats ((loc), (env1), ([])))
in (match (uu____3812) with
| (loc1, env2, pats1) -> begin
(

let pat = (

let uu____3947 = (

let uu____3950 = (

let uu____3957 = (FStar_Range.end_range p1.FStar_Parser_AST.prange)
in (pos_r uu____3957))
in (

let uu____3958 = (

let uu____3959 = (

let uu____3972 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____3972), ([])))
in FStar_Syntax_Syntax.Pat_cons (uu____3959))
in (FStar_All.pipe_left uu____3950 uu____3958)))
in (FStar_List.fold_right (fun hd1 tl1 -> (

let r = (FStar_Range.union_ranges hd1.FStar_Syntax_Syntax.p tl1.FStar_Syntax_Syntax.p)
in (

let uu____4004 = (

let uu____4005 = (

let uu____4018 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____4018), ((((hd1), (false)))::(((tl1), (false)))::[])))
in FStar_Syntax_Syntax.Pat_cons (uu____4005))
in (FStar_All.pipe_left (pos_r r) uu____4004)))) pats1 uu____3947))
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep1) -> begin
(

let uu____4060 = (FStar_List.fold_left (fun uu____4100 p2 -> (match (uu____4100) with
| (loc1, env2, pats) -> begin
(

let uu____4149 = (aux loc1 env2 p2)
in (match (uu____4149) with
| (loc2, env3, uu____4178, pat, uu____4180) -> begin
((loc2), (env3), ((((pat), (false)))::pats))
end))
end)) ((loc), (env1), ([])) args)
in (match (uu____4060) with
| (loc1, env2, args1) -> begin
(

let args2 = (FStar_List.rev args1)
in (

let l = (match (dep1) with
| true -> begin
(FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end
| uu____4268 -> begin
(FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end)
in (

let uu____4275 = (FStar_Syntax_DsEnv.fail_or env2 (FStar_Syntax_DsEnv.try_lookup_lid env2) l)
in (match (uu____4275) with
| (constr, uu____4297) -> begin
(

let l1 = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____4300 -> begin
(failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____4302 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args2)))))
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____4302), (false)))))
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

let fields1 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____4371 -> (match (uu____4371) with
| (f, p2) -> begin
((f.FStar_Ident.ident), (p2))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map (fun uu____4401 -> (match (uu____4401) with
| (f, uu____4407) -> begin
(

let uu____4408 = (FStar_All.pipe_right fields1 (FStar_List.tryFind (fun uu____4434 -> (match (uu____4434) with
| (g, uu____4440) -> begin
(Prims.op_Equality f.FStar_Ident.idText g.FStar_Ident.idText)
end))))
in (match (uu____4408) with
| FStar_Pervasives_Native.None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p1.FStar_Parser_AST.prange)
end
| FStar_Pervasives_Native.Some (uu____4445, p2) -> begin
p2
end))
end))))
in (

let app = (

let uu____4452 = (

let uu____4453 = (

let uu____4460 = (

let uu____4461 = (

let uu____4462 = (FStar_Ident.lid_of_ids (FStar_List.append record.FStar_Syntax_DsEnv.typename.FStar_Ident.ns ((record.FStar_Syntax_DsEnv.constrname)::[])))
in FStar_Parser_AST.PatName (uu____4462))
in (FStar_Parser_AST.mk_pattern uu____4461 p1.FStar_Parser_AST.prange))
in ((uu____4460), (args)))
in FStar_Parser_AST.PatApp (uu____4453))
in (FStar_Parser_AST.mk_pattern uu____4452 p1.FStar_Parser_AST.prange))
in (

let uu____4465 = (aux loc env1 app)
in (match (uu____4465) with
| (env2, e, b, p2, uu____4494) -> begin
(

let p3 = (match (p2.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args1) -> begin
(

let uu____4522 = (

let uu____4523 = (

let uu____4536 = (

let uu___119_4537 = fv
in (

let uu____4538 = (

let uu____4541 = (

let uu____4542 = (

let uu____4549 = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map FStar_Pervasives_Native.fst))
in ((record.FStar_Syntax_DsEnv.typename), (uu____4549)))
in FStar_Syntax_Syntax.Record_ctor (uu____4542))
in FStar_Pervasives_Native.Some (uu____4541))
in {FStar_Syntax_Syntax.fv_name = uu___119_4537.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = uu___119_4537.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu____4538}))
in ((uu____4536), (args1)))
in FStar_Syntax_Syntax.Pat_cons (uu____4523))
in (FStar_All.pipe_left pos uu____4522))
end
| uu____4576 -> begin
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

let uu____4630 = (aux' true loc env1 p2)
in (match (uu____4630) with
| (loc1, env2, var, p3, uu____4657) -> begin
(

let uu____4662 = (FStar_List.fold_left (fun uu____4694 p4 -> (match (uu____4694) with
| (loc2, env3, ps1) -> begin
(

let uu____4727 = (aux' true loc2 env3 p4)
in (match (uu____4727) with
| (loc3, env4, uu____4752, p5, uu____4754) -> begin
((loc3), (env4), ((p5)::ps1))
end))
end)) ((loc1), (env2), ([])) ps)
in (match (uu____4662) with
| (loc2, env3, ps1) -> begin
(

let pats = (p3)::(FStar_List.rev ps1)
in ((env3), (var), (pats)))
end))
end))
end
| uu____4805 -> begin
(

let uu____4806 = (aux' true loc env1 p1)
in (match (uu____4806) with
| (loc1, env2, vars, pat, b) -> begin
((env2), (vars), ((pat)::[]))
end))
end)))
in (

let uu____4846 = (aux_maybe_or env p)
in (match (uu____4846) with
| (env1, b, pats) -> begin
((check_linear_pattern_variables pats p.FStar_Parser_AST.prange);
((env1), (b), (pats));
)
end)))));
)))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.list) = (fun top env p is_mut -> (

let mklet = (fun x -> (

let uu____4905 = (

let uu____4906 = (

let uu____4917 = (FStar_Syntax_DsEnv.qualify env x)
in ((uu____4917), (((FStar_Syntax_Syntax.tun), (FStar_Pervasives_Native.None)))))
in LetBinder (uu____4906))
in ((env), (uu____4905), ([]))))
in (match (top) with
| true -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(

let uu____4945 = (

let uu____4946 = (

let uu____4951 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") x.FStar_Ident.idText x.FStar_Ident.idRange)
in ((uu____4951), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____4946))
in (mklet uu____4945))
end
| FStar_Parser_AST.PatVar (x, uu____4953) -> begin
(mklet x)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____4959); FStar_Parser_AST.prange = uu____4960}, (t, tacopt)) -> begin
(

let tacopt1 = (FStar_Util.map_opt tacopt (desugar_term env))
in (

let uu____4980 = (

let uu____4981 = (

let uu____4992 = (FStar_Syntax_DsEnv.qualify env x)
in (

let uu____4993 = (

let uu____5000 = (desugar_term env t)
in ((uu____5000), (tacopt1)))
in ((uu____4992), (uu____4993))))
in LetBinder (uu____4981))
in ((env), (uu____4980), ([]))))
end
| uu____5011 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedPattern), ("Unexpected pattern at the top-level")) p.FStar_Parser_AST.prange)
end)
end
| uu____5020 -> begin
(

let uu____5021 = (desugar_data_pat env p is_mut)
in (match (uu____5021) with
| (env1, binder, p1) -> begin
(

let p2 = (match (p1) with
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (uu____5050); FStar_Syntax_Syntax.p = uu____5051})::[] -> begin
[]
end
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (uu____5052); FStar_Syntax_Syntax.p = uu____5053})::[] -> begin
[]
end
| uu____5054 -> begin
p1
end)
in ((env1), (binder), (p2)))
end))
end)))
and desugar_binding_pat : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.list) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat Prims.list) = (fun uu____5061 env pat -> (

let uu____5064 = (desugar_data_pat env pat false)
in (match (uu____5064) with
| (env1, uu____5080, pat1) -> begin
((env1), (pat1))
end)))
and desugar_match_pat : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat Prims.list) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term_aq : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations) = (fun env e -> (

let env1 = (FStar_Syntax_DsEnv.set_expect_typ env false)
in (desugar_term_maybe_top false env1 e)))
and desugar_term : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let uu____5099 = (desugar_term_aq env e)
in (match (uu____5099) with
| (t, aq) -> begin
((check_no_aq aq);
t;
)
end)))
and desugar_typ_aq : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations) = (fun env e -> (

let env1 = (FStar_Syntax_DsEnv.set_expect_typ env true)
in (desugar_term_maybe_top false env1 e)))
and desugar_typ : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let uu____5116 = (desugar_typ_aq env e)
in (match (uu____5116) with
| (t, aq) -> begin
((check_no_aq aq);
t;
)
end)))
and desugar_machine_integer : FStar_Syntax_DsEnv.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun env repr uu____5126 range -> (match (uu____5126) with
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

let uu____5136 = (

let uu____5137 = (FStar_Const.within_bounds repr signedness width)
in (not (uu____5137)))
in (match (uu____5136) with
| true -> begin
(

let uu____5138 = (

let uu____5143 = (FStar_Util.format2 "%s is not in the expected range for %s" repr tnm)
in ((FStar_Errors.Error_OutOfRange), (uu____5143)))
in (FStar_Errors.log_issue range uu____5138))
end
| uu____5144 -> begin
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

let uu____5148 = (FStar_Ident.path_of_text intro_nm)
in (FStar_Ident.lid_of_path uu____5148 range))
in (

let lid1 = (

let uu____5152 = (FStar_Syntax_DsEnv.try_lookup_lid env lid)
in (match (uu____5152) with
| FStar_Pervasives_Native.Some (intro_term, uu____5162) -> begin
(match (intro_term.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let private_lid = (

let uu____5171 = (FStar_Ident.path_of_text private_intro_nm)
in (FStar_Ident.lid_of_path uu____5171 range))
in (

let private_fv = (

let uu____5173 = (FStar_Syntax_Util.incr_delta_depth fv.FStar_Syntax_Syntax.fv_delta)
in (FStar_Syntax_Syntax.lid_as_fv private_lid uu____5173 fv.FStar_Syntax_Syntax.fv_qual))
in (

let uu___120_5174 = intro_term
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (private_fv); FStar_Syntax_Syntax.pos = uu___120_5174.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___120_5174.FStar_Syntax_Syntax.vars})))
end
| uu____5175 -> begin
(failwith (Prims.strcat "Unexpected non-fvar for " intro_nm))
end)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5182 = (

let uu____5187 = (FStar_Util.format1 "Unexpected numeric literal.  Restart F* to load %s." tnm)
in ((FStar_Errors.Fatal_UnexpectedNumericLiteral), (uu____5187)))
in (FStar_Errors.raise_error uu____5182 range))
end))
in (

let repr1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (FStar_Pervasives_Native.None))))) FStar_Pervasives_Native.None range)
in (

let uu____5203 = (

let uu____5210 = (

let uu____5211 = (

let uu____5226 = (

let uu____5235 = (

let uu____5242 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr1), (uu____5242)))
in (uu____5235)::[])
in ((lid1), (uu____5226)))
in FStar_Syntax_Syntax.Tm_app (uu____5211))
in (FStar_Syntax_Syntax.mk uu____5210))
in (uu____5203 FStar_Pervasives_Native.None range)))))));
))
end))
and desugar_name : (FStar_Syntax_Syntax.term'  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  env_t  ->  Prims.bool  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.term = (fun mk1 setpos env resolve l -> (

let uu____5281 = (

let uu____5290 = ((match (resolve) with
| true -> begin
FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
end
| uu____5305 -> begin
FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve
end) env)
in (FStar_Syntax_DsEnv.fail_or env uu____5290 l))
in (match (uu____5281) with
| (tm, mut, attrs) -> begin
(

let warn_if_deprecated = (fun attrs1 -> (FStar_List.iter (fun a -> (match (a.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____5345; FStar_Syntax_Syntax.vars = uu____5346}, args) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v FStar_Parser_Const.deprecated_attr) -> begin
(

let msg = (

let uu____5369 = (FStar_Syntax_Print.term_to_string tm)
in (Prims.strcat uu____5369 " is deprecated"))
in (

let msg1 = (match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5377 = (

let uu____5378 = (

let uu____5381 = (FStar_List.hd args)
in (FStar_Pervasives_Native.fst uu____5381))
in uu____5378.FStar_Syntax_Syntax.n)
in (match (uu____5377) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____5397)) when (not ((Prims.op_Equality (FStar_Util.trim_string s) ""))) -> begin
(Prims.strcat msg (Prims.strcat ", use " (Prims.strcat s " instead")))
end
| uu____5398 -> begin
msg
end))
end
| uu____5399 -> begin
msg
end)
in (

let uu____5400 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.log_issue uu____5400 ((FStar_Errors.Warning_DeprecatedDefinition), (msg1))))))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v FStar_Parser_Const.deprecated_attr) -> begin
(

let msg = (

let uu____5403 = (FStar_Syntax_Print.term_to_string tm)
in (Prims.strcat uu____5403 " is deprecated"))
in (

let uu____5404 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.log_issue uu____5404 ((FStar_Errors.Warning_DeprecatedDefinition), (msg)))))
end
| uu____5405 -> begin
()
end)) attrs1))
in ((warn_if_deprecated attrs);
(

let tm1 = (setpos tm)
in (match (mut) with
| true -> begin
(

let uu____5410 = (

let uu____5411 = (

let uu____5418 = (mk_ref_read tm1)
in ((uu____5418), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval))))
in FStar_Syntax_Syntax.Tm_meta (uu____5411))
in (FStar_All.pipe_left mk1 uu____5410))
end
| uu____5423 -> begin
tm1
end));
))
end)))
and desugar_attributes : env_t  ->  FStar_Parser_AST.term Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun env cattributes -> (

let desugar_attribute = (fun t -> (

let uu____5436 = (

let uu____5437 = (unparen t)
in uu____5437.FStar_Parser_AST.tm)
in (match (uu____5436) with
| FStar_Parser_AST.Var ({FStar_Ident.ns = uu____5438; FStar_Ident.ident = uu____5439; FStar_Ident.nsstr = uu____5440; FStar_Ident.str = "cps"}) -> begin
FStar_Syntax_Syntax.CPS
end
| uu____5443 -> begin
(

let uu____5444 = (

let uu____5449 = (

let uu____5450 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "Unknown attribute " uu____5450))
in ((FStar_Errors.Fatal_UnknownAttribute), (uu____5449)))
in (FStar_Errors.raise_error uu____5444 t.FStar_Parser_AST.range))
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

let uu___121_5545 = e
in {FStar_Syntax_Syntax.n = uu___121_5545.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___121_5545.FStar_Syntax_Syntax.vars}))
in (

let uu____5548 = (

let uu____5549 = (unparen top)
in uu____5549.FStar_Parser_AST.tm)
in (match (uu____5548) with
| FStar_Parser_AST.Wild -> begin
(((setpos FStar_Syntax_Syntax.tun)), (noaqs))
end
| FStar_Parser_AST.Labeled (uu____5554) -> begin
(

let uu____5561 = (desugar_formula env top)
in ((uu____5561), (noaqs)))
end
| FStar_Parser_AST.Requires (t, lopt) -> begin
(

let uu____5568 = (desugar_formula env t)
in ((uu____5568), (noaqs)))
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(

let uu____5575 = (desugar_formula env t)
in ((uu____5575), (noaqs)))
end
| FStar_Parser_AST.Attributes (ts) -> begin
(failwith "Attributes should not be desugared by desugar_term_maybe_top")
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (i, FStar_Pervasives_Native.Some (size))) -> begin
(

let uu____5599 = (desugar_machine_integer env i size top.FStar_Parser_AST.range)
in ((uu____5599), (noaqs)))
end
| FStar_Parser_AST.Const (c) -> begin
(

let uu____5601 = (mk1 (FStar_Syntax_Syntax.Tm_constant (c)))
in ((uu____5601), (noaqs)))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "=!="; FStar_Ident.idRange = r}, args) -> begin
(

let e = (

let uu____5609 = (

let uu____5610 = (

let uu____5617 = (FStar_Ident.mk_ident (("=="), (r)))
in ((uu____5617), (args)))
in FStar_Parser_AST.Op (uu____5610))
in (FStar_Parser_AST.mk_term uu____5609 top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
in (

let uu____5620 = (

let uu____5621 = (

let uu____5622 = (

let uu____5629 = (FStar_Ident.mk_ident (("~"), (r)))
in ((uu____5629), ((e)::[])))
in FStar_Parser_AST.Op (uu____5622))
in (FStar_Parser_AST.mk_term uu____5621 top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
in (desugar_term_aq env uu____5620)))
end
| FStar_Parser_AST.Op (op_star, (uu____5633)::(uu____5634)::[]) when ((

let uu____5639 = (FStar_Ident.text_of_id op_star)
in (Prims.op_Equality uu____5639 "*")) && (

let uu____5641 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range op_star)
in (FStar_All.pipe_right uu____5641 FStar_Option.isNone))) -> begin
(

let rec flatten1 = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____5656}, (t1)::(t2)::[]) -> begin
(

let uu____5661 = (flatten1 t1)
in (FStar_List.append uu____5661 ((t2)::[])))
end
| uu____5664 -> begin
(t)::[]
end))
in (

let uu____5665 = (

let uu____5690 = (

let uu____5713 = (

let uu____5716 = (unparen top)
in (flatten1 uu____5716))
in (FStar_All.pipe_right uu____5713 (FStar_List.map (fun t -> (

let uu____5751 = (desugar_typ_aq env t)
in (match (uu____5751) with
| (t', aq) -> begin
(

let uu____5762 = (FStar_Syntax_Syntax.as_arg t')
in ((uu____5762), (aq)))
end))))))
in (FStar_All.pipe_right uu____5690 FStar_List.unzip))
in (match (uu____5665) with
| (targs, aqs) -> begin
(

let uu____5871 = (

let uu____5876 = (FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_lid env) uu____5876))
in (match (uu____5871) with
| (tup, uu____5892) -> begin
(

let uu____5893 = (mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
in ((uu____5893), ((join_aqs aqs))))
end))
end)))
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____5905 = (

let uu____5906 = (

let uu____5909 = (FStar_Syntax_DsEnv.fail_or2 (FStar_Syntax_DsEnv.try_lookup_id env) a)
in (FStar_Pervasives_Native.fst uu____5909))
in (FStar_All.pipe_left setpos uu____5906))
in ((uu____5905), (noaqs)))
end
| FStar_Parser_AST.Uvar (u) -> begin
(

let uu____5921 = (

let uu____5926 = (

let uu____5927 = (

let uu____5928 = (FStar_Ident.text_of_id u)
in (Prims.strcat uu____5928 " in non-universe context"))
in (Prims.strcat "Unexpected universe variable " uu____5927))
in ((FStar_Errors.Fatal_UnexpectedUniverseVariable), (uu____5926)))
in (FStar_Errors.raise_error uu____5921 top.FStar_Parser_AST.range))
end
| FStar_Parser_AST.Op (s, args) -> begin
(

let uu____5939 = (op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)
in (match (uu____5939) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5946 = (

let uu____5951 = (

let uu____5952 = (FStar_Ident.text_of_id s)
in (Prims.strcat "Unexpected or unbound operator: " uu____5952))
in ((FStar_Errors.Fatal_UnepxectedOrUnboundOperator), (uu____5951)))
in (FStar_Errors.raise_error uu____5946 top.FStar_Parser_AST.range))
end
| FStar_Pervasives_Native.Some (op) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____5962 = (

let uu____5987 = (FStar_All.pipe_right args (FStar_List.map (fun t -> (

let uu____6049 = (desugar_term_aq env t)
in (match (uu____6049) with
| (t', s1) -> begin
((((t'), (FStar_Pervasives_Native.None))), (s1))
end)))))
in (FStar_All.pipe_right uu____5987 FStar_List.unzip))
in (match (uu____5962) with
| (args1, aqs) -> begin
(

let uu____6182 = (mk1 (FStar_Syntax_Syntax.Tm_app (((op), (args1)))))
in ((uu____6182), ((join_aqs aqs))))
end))
end
| uu____6193 -> begin
((op), (noaqs))
end)
end))
end
| FStar_Parser_AST.Construct (n1, ((a, uu____6196))::[]) when (Prims.op_Equality n1.FStar_Ident.str "SMTPat") -> begin
(

let uu____6211 = (

let uu___122_6212 = top
in (

let uu____6213 = (

let uu____6214 = (

let uu____6221 = (

let uu___123_6222 = top
in (

let uu____6223 = (

let uu____6224 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____6224))
in {FStar_Parser_AST.tm = uu____6223; FStar_Parser_AST.range = uu___123_6222.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___123_6222.FStar_Parser_AST.level}))
in ((uu____6221), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____6214))
in {FStar_Parser_AST.tm = uu____6213; FStar_Parser_AST.range = uu___122_6212.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___122_6212.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____6211))
end
| FStar_Parser_AST.Construct (n1, ((a, uu____6227))::[]) when (Prims.op_Equality n1.FStar_Ident.str "SMTPatT") -> begin
((FStar_Errors.log_issue top.FStar_Parser_AST.range ((FStar_Errors.Warning_SMTPatTDeprecated), ("SMTPatT is deprecated; please just use SMTPat")));
(

let uu____6243 = (

let uu___124_6244 = top
in (

let uu____6245 = (

let uu____6246 = (

let uu____6253 = (

let uu___125_6254 = top
in (

let uu____6255 = (

let uu____6256 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____6256))
in {FStar_Parser_AST.tm = uu____6255; FStar_Parser_AST.range = uu___125_6254.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___125_6254.FStar_Parser_AST.level}))
in ((uu____6253), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____6246))
in {FStar_Parser_AST.tm = uu____6245; FStar_Parser_AST.range = uu___124_6244.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___124_6244.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____6243));
)
end
| FStar_Parser_AST.Construct (n1, ((a, uu____6259))::[]) when (Prims.op_Equality n1.FStar_Ident.str "SMTPatOr") -> begin
(

let uu____6274 = (

let uu___126_6275 = top
in (

let uu____6276 = (

let uu____6277 = (

let uu____6284 = (

let uu___127_6285 = top
in (

let uu____6286 = (

let uu____6287 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat_or")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____6287))
in {FStar_Parser_AST.tm = uu____6286; FStar_Parser_AST.range = uu___127_6285.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___127_6285.FStar_Parser_AST.level}))
in ((uu____6284), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____6277))
in {FStar_Parser_AST.tm = uu____6276; FStar_Parser_AST.range = uu___126_6275.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___126_6275.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____6274))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____6288; FStar_Ident.ident = uu____6289; FStar_Ident.nsstr = uu____6290; FStar_Ident.str = "Type0"}) -> begin
(

let uu____6293 = (mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
in ((uu____6293), (noaqs)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____6294; FStar_Ident.ident = uu____6295; FStar_Ident.nsstr = uu____6296; FStar_Ident.str = "Type"}) -> begin
(

let uu____6299 = (mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
in ((uu____6299), (noaqs)))
end
| FStar_Parser_AST.Construct ({FStar_Ident.ns = uu____6300; FStar_Ident.ident = uu____6301; FStar_Ident.nsstr = uu____6302; FStar_Ident.str = "Type"}, ((t, FStar_Parser_AST.UnivApp))::[]) -> begin
(

let uu____6320 = (

let uu____6321 = (

let uu____6322 = (desugar_universe t)
in FStar_Syntax_Syntax.Tm_type (uu____6322))
in (mk1 uu____6321))
in ((uu____6320), (noaqs)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____6323; FStar_Ident.ident = uu____6324; FStar_Ident.nsstr = uu____6325; FStar_Ident.str = "Effect"}) -> begin
(

let uu____6328 = (mk1 (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
in ((uu____6328), (noaqs)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____6329; FStar_Ident.ident = uu____6330; FStar_Ident.nsstr = uu____6331; FStar_Ident.str = "True"}) -> begin
(

let uu____6334 = (

let uu____6335 = (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar uu____6335 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in ((uu____6334), (noaqs)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____6336; FStar_Ident.ident = uu____6337; FStar_Ident.nsstr = uu____6338; FStar_Ident.str = "False"}) -> begin
(

let uu____6341 = (

let uu____6342 = (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar uu____6342 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in ((uu____6341), (noaqs)))
end
| FStar_Parser_AST.Projector (eff_name, {FStar_Ident.idText = txt; FStar_Ident.idRange = uu____6345}) when ((is_special_effect_combinator txt) && (FStar_Syntax_DsEnv.is_effect_name env eff_name)) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name);
(

let uu____6347 = (FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name)
in (match (uu____6347) with
| FStar_Pervasives_Native.Some (ed) -> begin
(

let lid = (FStar_Syntax_Util.dm4f_lid ed txt)
in (

let uu____6356 = (FStar_Syntax_Syntax.fvar lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in ((uu____6356), (noaqs))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____6357 = (

let uu____6358 = (FStar_Ident.text_of_lid eff_name)
in (FStar_Util.format2 "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)" uu____6358 txt))
in (failwith uu____6357))
end));
)
end
| FStar_Parser_AST.Var (l) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l);
(

let uu____6365 = (desugar_name mk1 setpos env true l)
in ((uu____6365), (noaqs)));
)
end
| FStar_Parser_AST.Name (l) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l);
(

let uu____6368 = (desugar_name mk1 setpos env true l)
in ((uu____6368), (noaqs)));
)
end
| FStar_Parser_AST.Projector (l, i) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l);
(

let name = (

let uu____6379 = (FStar_Syntax_DsEnv.try_lookup_datacon env l)
in (match (uu____6379) with
| FStar_Pervasives_Native.Some (uu____6388) -> begin
FStar_Pervasives_Native.Some (((true), (l)))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____6393 = (FStar_Syntax_DsEnv.try_lookup_root_effect_name env l)
in (match (uu____6393) with
| FStar_Pervasives_Native.Some (new_name) -> begin
FStar_Pervasives_Native.Some (((false), (new_name)))
end
| uu____6407 -> begin
FStar_Pervasives_Native.None
end))
end))
in (match (name) with
| FStar_Pervasives_Native.Some (resolve, new_name) -> begin
(

let uu____6424 = (

let uu____6425 = (FStar_Syntax_Util.mk_field_projector_name_from_ident new_name i)
in (desugar_name mk1 setpos env resolve uu____6425))
in ((uu____6424), (noaqs)))
end
| uu____6426 -> begin
(

let uu____6433 = (

let uu____6438 = (FStar_Util.format1 "Data constructor or effect %s not found" l.FStar_Ident.str)
in ((FStar_Errors.Fatal_EffectNotFound), (uu____6438)))
in (FStar_Errors.raise_error uu____6433 top.FStar_Parser_AST.range))
end));
)
end
| FStar_Parser_AST.Discrim (lid) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid);
(

let uu____6445 = (FStar_Syntax_DsEnv.try_lookup_datacon env lid)
in (match (uu____6445) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6452 = (

let uu____6457 = (FStar_Util.format1 "Data constructor %s not found" lid.FStar_Ident.str)
in ((FStar_Errors.Fatal_DataContructorNotFound), (uu____6457)))
in (FStar_Errors.raise_error uu____6452 top.FStar_Parser_AST.range))
end
| uu____6462 -> begin
(

let lid' = (FStar_Syntax_Util.mk_discriminator lid)
in (

let uu____6466 = (desugar_name mk1 setpos env true lid')
in ((uu____6466), (noaqs))))
end));
)
end
| FStar_Parser_AST.Construct (l, args) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l);
(

let uu____6482 = (FStar_Syntax_DsEnv.try_lookup_datacon env l)
in (match (uu____6482) with
| FStar_Pervasives_Native.Some (head1) -> begin
(

let head2 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (head1)))
in (match (args) with
| [] -> begin
((head2), (noaqs))
end
| uu____6501 -> begin
(

let uu____6508 = (FStar_Util.take (fun uu____6532 -> (match (uu____6532) with
| (uu____6537, imp) -> begin
(Prims.op_Equality imp FStar_Parser_AST.UnivApp)
end)) args)
in (match (uu____6508) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun x -> (desugar_universe (FStar_Pervasives_Native.fst x))) universes)
in (

let uu____6582 = (

let uu____6607 = (FStar_List.map (fun uu____6650 -> (match (uu____6650) with
| (t, imp) -> begin
(

let uu____6667 = (desugar_term_aq env t)
in (match (uu____6667) with
| (te, aq) -> begin
(((arg_withimp_e imp te)), (aq))
end))
end)) args1)
in (FStar_All.pipe_right uu____6607 FStar_List.unzip))
in (match (uu____6582) with
| (args2, aqs) -> begin
(

let head3 = (match ((Prims.op_Equality universes1 [])) with
| true -> begin
head2
end
| uu____6805 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_uinst (((head2), (universes1)))))
end)
in (

let uu____6808 = (mk1 (FStar_Syntax_Syntax.Tm_app (((head3), (args2)))))
in ((uu____6808), ((join_aqs aqs)))))
end)))
end))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let err = (

let uu____6824 = (FStar_Syntax_DsEnv.try_lookup_effect_name env l)
in (match (uu____6824) with
| FStar_Pervasives_Native.None -> begin
((FStar_Errors.Fatal_ConstructorNotFound), ((Prims.strcat "Constructor " (Prims.strcat l.FStar_Ident.str " not found"))))
end
| FStar_Pervasives_Native.Some (uu____6831) -> begin
((FStar_Errors.Fatal_UnexpectedEffect), ((Prims.strcat "Effect " (Prims.strcat l.FStar_Ident.str " used at an unexpected position"))))
end))
in (FStar_Errors.raise_error err top.FStar_Parser_AST.range))
end));
)
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let uu____6842 = (FStar_List.fold_left (fun uu____6887 b -> (match (uu____6887) with
| (env1, tparams, typs) -> begin
(

let uu____6944 = (desugar_binder env1 b)
in (match (uu____6944) with
| (xopt, t1) -> begin
(

let uu____6973 = (match (xopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6982 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env1), (uu____6982)))
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_DsEnv.push_bv env1 x)
end)
in (match (uu____6973) with
| (env2, x) -> begin
(

let uu____7002 = (

let uu____7005 = (

let uu____7008 = (

let uu____7009 = (no_annot_abs tparams t1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____7009))
in (uu____7008)::[])
in (FStar_List.append typs uu____7005))
in ((env2), ((FStar_List.append tparams (((((

let uu___128_7035 = x
in {FStar_Syntax_Syntax.ppname = uu___128_7035.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___128_7035.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})), (FStar_Pervasives_Native.None)))::[]))), (uu____7002)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type_level FStar_Pervasives_Native.None))::[])))
in (match (uu____6842) with
| (env1, uu____7063, targs) -> begin
(

let uu____7085 = (

let uu____7090 = (FStar_Parser_Const.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Syntax_DsEnv.fail_or env1 (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____7090))
in (match (uu____7085) with
| (tup, uu____7100) -> begin
(

let uu____7101 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
in ((uu____7101), (noaqs)))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let uu____7118 = (uncurry binders t)
in (match (uu____7118) with
| (bs, t1) -> begin
(

let rec aux = (fun env1 bs1 uu___94_7160 -> (match (uu___94_7160) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range env1 t1)
in (

let uu____7174 = (FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod)
in (FStar_All.pipe_left setpos uu____7174)))
end
| (hd1)::tl1 -> begin
(

let bb = (desugar_binder env1 hd1)
in (

let uu____7196 = (as_binder env1 hd1.FStar_Parser_AST.aqual bb)
in (match (uu____7196) with
| (b, env2) -> begin
(aux env2 ((b)::bs1) tl1)
end)))
end))
in (

let uu____7205 = (aux env [] bs)
in ((uu____7205), (noaqs))))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(

let uu____7212 = (desugar_binder env b)
in (match (uu____7212) with
| (FStar_Pervasives_Native.None, uu____7223) -> begin
(failwith "Missing binder in refinement")
end
| b1 -> begin
(

let uu____7237 = (as_binder env FStar_Pervasives_Native.None b1)
in (match (uu____7237) with
| ((x, uu____7247), env1) -> begin
(

let f1 = (desugar_formula env1 f)
in (

let uu____7250 = (

let uu____7251 = (FStar_Syntax_Util.refine x f1)
in (FStar_All.pipe_left setpos uu____7251))
in ((uu____7250), (noaqs))))
end))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let binders1 = (FStar_All.pipe_right binders (FStar_List.map replace_unit_pattern))
in (

let uu____7269 = (FStar_List.fold_left (fun uu____7289 pat -> (match (uu____7289) with
| (env1, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (uu____7315, (t, FStar_Pervasives_Native.None)) -> begin
(

let uu____7325 = (

let uu____7328 = (free_type_vars env1 t)
in (FStar_List.append uu____7328 ftvs))
in ((env1), (uu____7325)))
end
| FStar_Parser_AST.PatAscribed (uu____7333, (t, FStar_Pervasives_Native.Some (tac))) -> begin
(

let uu____7344 = (

let uu____7347 = (free_type_vars env1 t)
in (

let uu____7350 = (

let uu____7353 = (free_type_vars env1 tac)
in (FStar_List.append uu____7353 ftvs))
in (FStar_List.append uu____7347 uu____7350)))
in ((env1), (uu____7344)))
end
| uu____7358 -> begin
((env1), (ftvs))
end)
end)) ((env), ([])) binders1)
in (match (uu____7269) with
| (uu____7367, ftv) -> begin
(

let ftv1 = (sort_ftv ftv)
in (

let binders2 = (

let uu____7379 = (FStar_All.pipe_right ftv1 (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append uu____7379 binders1))
in (

let rec aux = (fun env1 bs sc_pat_opt uu___95_7434 -> (match (uu___95_7434) with
| [] -> begin
(

let uu____7459 = (desugar_term_aq env1 body)
in (match (uu____7459) with
| (body1, aq) -> begin
(

let body2 = (match (sc_pat_opt) with
| FStar_Pervasives_Native.Some (sc, pat) -> begin
(

let body2 = (

let uu____7496 = (

let uu____7497 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right uu____7497 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close uu____7496 body1))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (FStar_Pervasives_Native.None), (body2)))::[])))) FStar_Pervasives_Native.None body2.FStar_Syntax_Syntax.pos))
end
| FStar_Pervasives_Native.None -> begin
body1
end)
in (

let uu____7566 = (

let uu____7569 = (no_annot_abs (FStar_List.rev bs) body2)
in (setpos uu____7569))
in ((uu____7566), (aq))))
end))
end
| (p)::rest -> begin
(

let uu____7582 = (desugar_binding_pat env1 p)
in (match (uu____7582) with
| (env2, b, pat) -> begin
(

let pat1 = (match (pat) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (p1)::[] -> begin
FStar_Pervasives_Native.Some (p1)
end
| uu____7616 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnsupportedDisjuctivePatterns), ("Disjunctive patterns are not supported in abstractions")) p.FStar_Parser_AST.prange)
end)
in (

let uu____7623 = (match (b) with
| LetBinder (uu____7660) -> begin
(failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt1 = (match (((pat1), (sc_pat_opt))) with
| (FStar_Pervasives_Native.None, uu____7726) -> begin
sc_pat_opt
end
| (FStar_Pervasives_Native.Some (p1), FStar_Pervasives_Native.None) -> begin
(

let uu____7780 = (

let uu____7787 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____7787), (p1)))
in FStar_Pervasives_Native.Some (uu____7780))
end
| (FStar_Pervasives_Native.Some (p1), FStar_Pervasives_Native.Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (uu____7843), uu____7844) -> begin
(

let tup2 = (

let uu____7846 = (FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____7846 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____7850 = (

let uu____7857 = (

let uu____7858 = (

let uu____7873 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (

let uu____7876 = (

let uu____7885 = (FStar_Syntax_Syntax.as_arg sc)
in (

let uu____7892 = (

let uu____7901 = (

let uu____7908 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____7908))
in (uu____7901)::[])
in (uu____7885)::uu____7892))
in ((uu____7873), (uu____7876))))
in FStar_Syntax_Syntax.Tm_app (uu____7858))
in (FStar_Syntax_Syntax.mk uu____7857))
in (uu____7850 FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
in (

let p2 = (

let uu____7949 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p1), (false)))::[])))) uu____7949))
in FStar_Pervasives_Native.Some (((sc1), (p2))))))
end
| (FStar_Syntax_Syntax.Tm_app (uu____7992, args), FStar_Syntax_Syntax.Pat_cons (uu____7994, pats)) -> begin
(

let tupn = (

let uu____8033 = (FStar_Parser_Const.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____8033 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____8043 = (

let uu____8044 = (

let uu____8059 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (

let uu____8062 = (

let uu____8071 = (

let uu____8080 = (

let uu____8087 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____8087))
in (uu____8080)::[])
in (FStar_List.append args uu____8071))
in ((uu____8059), (uu____8062))))
in FStar_Syntax_Syntax.Tm_app (uu____8044))
in (mk1 uu____8043))
in (

let p2 = (

let uu____8125 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p1), (false)))::[])))))) uu____8125))
in FStar_Pervasives_Native.Some (((sc1), (p2))))))
end
| uu____8166 -> begin
(failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt1)))
end)
in (match (uu____7623) with
| (b1, sc_pat_opt1) -> begin
(aux env2 ((b1)::bs) sc_pat_opt1 rest)
end)))
end))
end))
in (aux env [] FStar_Pervasives_Native.None binders2))))
end)))
end
| FStar_Parser_AST.App (uu____8247, uu____8248, FStar_Parser_AST.UnivApp) -> begin
(

let rec aux = (fun universes e -> (

let uu____8270 = (

let uu____8271 = (unparen e)
in uu____8271.FStar_Parser_AST.tm)
in (match (uu____8270) with
| FStar_Parser_AST.App (e1, t, FStar_Parser_AST.UnivApp) -> begin
(

let univ_arg = (desugar_universe t)
in (aux ((univ_arg)::universes) e1))
end
| uu____8281 -> begin
(

let uu____8282 = (desugar_term_aq env e)
in (match (uu____8282) with
| (head1, aq) -> begin
(

let uu____8295 = (mk1 (FStar_Syntax_Syntax.Tm_uinst (((head1), (universes)))))
in ((uu____8295), (aq)))
end))
end)))
in (aux [] top))
end
| FStar_Parser_AST.App (uu____8302) -> begin
(

let rec aux = (fun args aqs e -> (

let uu____8361 = (

let uu____8362 = (unparen e)
in uu____8362.FStar_Parser_AST.tm)
in (match (uu____8361) with
| FStar_Parser_AST.App (e1, t, imp) when (Prims.op_disEquality imp FStar_Parser_AST.UnivApp) -> begin
(

let uu____8382 = (desugar_term_aq env t)
in (match (uu____8382) with
| (t1, aq) -> begin
(

let arg = (arg_withimp_e imp t1)
in (aux ((arg)::args) ((aq)::aqs) e1))
end))
end
| uu____8418 -> begin
(

let uu____8419 = (desugar_term_aq env e)
in (match (uu____8419) with
| (head1, aq) -> begin
(

let uu____8442 = (mk1 (FStar_Syntax_Syntax.Tm_app (((head1), (args)))))
in ((uu____8442), ((join_aqs ((aq)::aqs)))))
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

let uu____8494 = (FStar_Parser_AST.mkExplicitApp bind1 ((t1)::(k)::[]) top.FStar_Parser_AST.range)
in (desugar_term_aq env uu____8494))))))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(

let t = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), ((((FStar_Pervasives_Native.None), ((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
in (

let uu____8546 = (desugar_term_aq env t)
in (match (uu____8546) with
| (tm, s) -> begin
(

let uu____8557 = (mk1 (FStar_Syntax_Syntax.Tm_meta (((tm), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))))
in ((uu____8557), (s)))
end)))
end
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(

let env1 = (FStar_Syntax_DsEnv.push_namespace env lid)
in (

let uu____8563 = (

let uu____8576 = (FStar_Syntax_DsEnv.expect_typ env1)
in (match (uu____8576) with
| true -> begin
desugar_typ_aq
end
| uu____8587 -> begin
desugar_term_aq
end))
in (uu____8563 env1 e)))
end
| FStar_Parser_AST.Let (qual, lbs, body) -> begin
(

let is_rec = (Prims.op_Equality qual FStar_Parser_AST.Rec)
in (

let ds_let_rec_or_app = (fun uu____8631 -> (

let bindings = lbs
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun uu____8774 -> (match (uu____8774) with
| (attr_opt, (p, def)) -> begin
(

let uu____8832 = (is_app_pattern p)
in (match (uu____8832) with
| true -> begin
(

let uu____8863 = (destruct_app_pattern env top_level p)
in ((attr_opt), (uu____8863), (def)))
end
| uu____8908 -> begin
(match ((FStar_Parser_AST.un_function p def)) with
| FStar_Pervasives_Native.Some (p1, def1) -> begin
(

let uu____8945 = (destruct_app_pattern env top_level p1)
in ((attr_opt), (uu____8945), (def1)))
end
| uu____8990 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id1, uu____9028); FStar_Parser_AST.prange = uu____9029}, t) -> begin
(match (top_level) with
| true -> begin
(

let uu____9077 = (

let uu____9098 = (

let uu____9103 = (FStar_Syntax_DsEnv.qualify env id1)
in FStar_Util.Inr (uu____9103))
in ((uu____9098), ([]), (FStar_Pervasives_Native.Some (t))))
in ((attr_opt), (uu____9077), (def)))
end
| uu____9148 -> begin
((attr_opt), (((FStar_Util.Inl (id1)), ([]), (FStar_Pervasives_Native.Some (t)))), (def))
end)
end
| FStar_Parser_AST.PatVar (id1, uu____9194) -> begin
(match (top_level) with
| true -> begin
(

let uu____9229 = (

let uu____9250 = (

let uu____9255 = (FStar_Syntax_DsEnv.qualify env id1)
in FStar_Util.Inr (uu____9255))
in ((uu____9250), ([]), (FStar_Pervasives_Native.None)))
in ((attr_opt), (uu____9229), (def)))
end
| uu____9300 -> begin
((attr_opt), (((FStar_Util.Inl (id1)), ([]), (FStar_Pervasives_Native.None))), (def))
end)
end
| uu____9345 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedLetBinding), ("Unexpected let binding")) p.FStar_Parser_AST.prange)
end)
end)
end))
end))))
in (

let uu____9376 = (FStar_List.fold_left (fun uu____9449 uu____9450 -> (match (((uu____9449), (uu____9450))) with
| ((env1, fnames, rec_bindings), (_attr_opt, (f, uu____9558, uu____9559), uu____9560)) -> begin
(

let uu____9677 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let uu____9703 = (FStar_Syntax_DsEnv.push_bv env1 x)
in (match (uu____9703) with
| (env2, xx) -> begin
(

let uu____9722 = (

let uu____9725 = (FStar_Syntax_Syntax.mk_binder xx)
in (uu____9725)::rec_bindings)
in ((env2), (FStar_Util.Inl (xx)), (uu____9722)))
end))
end
| FStar_Util.Inr (l) -> begin
(

let uu____9733 = (FStar_Syntax_DsEnv.push_top_level_rec_binding env1 l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in ((uu____9733), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (uu____9677) with
| (env2, lbname, rec_bindings1) -> begin
((env2), ((lbname)::fnames), (rec_bindings1))
end))
end)) ((env), ([]), ([])) funs)
in (match (uu____9376) with
| (env', fnames, rec_bindings) -> begin
(

let fnames1 = (FStar_List.rev fnames)
in (

let rec_bindings1 = (FStar_List.rev rec_bindings)
in (

let desugar_one_def = (fun env1 lbname uu____9881 -> (match (uu____9881) with
| (attrs_opt, (uu____9917, args, result_t), def) -> begin
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

let uu____10005 = (is_comp_type env1 t)
in (match (uu____10005) with
| true -> begin
((

let uu____10007 = (FStar_All.pipe_right args1 (FStar_List.tryFind (fun x -> (

let uu____10017 = (is_var_pattern x)
in (not (uu____10017))))))
in (match (uu____10007) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (p) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ComputationTypeNotAllowed), ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")) p.FStar_Parser_AST.prange)
end));
t;
)
end
| uu____10019 -> begin
(

let uu____10020 = (((FStar_Options.ml_ish ()) && (

let uu____10022 = (FStar_Syntax_DsEnv.try_lookup_effect_name env1 FStar_Parser_Const.effect_ML_lid)
in (FStar_Option.isSome uu____10022))) && ((not (is_rec)) || (Prims.op_disEquality (FStar_List.length args1) (Prims.parse_int "0"))))
in (match (uu____10020) with
| true -> begin
(FStar_Parser_AST.ml_comp t)
end
| uu____10026 -> begin
(FStar_Parser_AST.tot_comp t)
end))
end))
in (

let uu____10027 = (FStar_Range.union_ranges t1.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t1), (tacopt)))) uu____10027 FStar_Parser_AST.Expr)))
end)
in (

let def2 = (match (args1) with
| [] -> begin
def1
end
| uu____10031 -> begin
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

let uu____10046 = (

let uu____10047 = (FStar_Syntax_Util.incr_delta_qualifier body1)
in (FStar_Syntax_Syntax.lid_as_fv l uu____10047 FStar_Pervasives_Native.None))
in FStar_Util.Inr (uu____10046))
end)
in (

let body2 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.close rec_bindings1 body1)
end
| uu____10053 -> begin
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
| uu____10121 -> begin
env
end)) fnames1 funs)
in (

let uu____10122 = (desugar_term_aq env' body)
in (match (uu____10122) with
| (body1, aq) -> begin
(

let uu____10135 = (

let uu____10138 = (

let uu____10139 = (

let uu____10152 = (FStar_Syntax_Subst.close rec_bindings1 body1)
in ((((is_rec), (lbs1))), (uu____10152)))
in FStar_Syntax_Syntax.Tm_let (uu____10139))
in (FStar_All.pipe_left mk1 uu____10138))
in ((uu____10135), (aq)))
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
| uu____10229 -> begin
t11
end)
in (

let uu____10230 = (desugar_binding_pat_maybe_top top_level env pat is_mutable)
in (match (uu____10230) with
| (env1, binder, pat1) -> begin
(

let uu____10252 = (match (binder) with
| LetBinder (l, (t, _tacopt)) -> begin
(

let uu____10278 = (desugar_term_aq env1 t2)
in (match (uu____10278) with
| (body1, aq) -> begin
(

let fv = (

let uu____10292 = (FStar_Syntax_Util.incr_delta_qualifier t12)
in (FStar_Syntax_Syntax.lid_as_fv l uu____10292 FStar_Pervasives_Native.None))
in (

let uu____10293 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_let (((((false), (((mk_lb ((attrs), (FStar_Util.Inr (fv)), (t), (t12), (t12.FStar_Syntax_Syntax.pos))))::[]))), (body1)))))
in ((uu____10293), (aq))))
end))
end
| LocalBinder (x, uu____10323) -> begin
(

let uu____10324 = (desugar_term_aq env1 t2)
in (match (uu____10324) with
| (body1, aq) -> begin
(

let body2 = (match (pat1) with
| [] -> begin
body1
end
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (uu____10338); FStar_Syntax_Syntax.p = uu____10339})::[] -> begin
body1
end
| uu____10340 -> begin
(

let uu____10343 = (

let uu____10350 = (

let uu____10351 = (

let uu____10374 = (FStar_Syntax_Syntax.bv_to_name x)
in (

let uu____10377 = (desugar_disjunctive_pattern pat1 FStar_Pervasives_Native.None body1)
in ((uu____10374), (uu____10377))))
in FStar_Syntax_Syntax.Tm_match (uu____10351))
in (FStar_Syntax_Syntax.mk uu____10350))
in (uu____10343 FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
end)
in (

let uu____10417 = (

let uu____10420 = (

let uu____10421 = (

let uu____10434 = (

let uu____10437 = (

let uu____10438 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____10438)::[])
in (FStar_Syntax_Subst.close uu____10437 body2))
in ((((false), (((mk_lb ((attrs), (FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t12), (t12.FStar_Syntax_Syntax.pos))))::[]))), (uu____10434)))
in FStar_Syntax_Syntax.Tm_let (uu____10421))
in (FStar_All.pipe_left mk1 uu____10420))
in ((uu____10417), (aq))))
end))
end)
in (match (uu____10252) with
| (tm, aq) -> begin
(match (is_mutable) with
| true -> begin
(

let uu____10495 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((tm), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc))))))
in ((uu____10495), (aq)))
end
| uu____10504 -> begin
((tm), (aq))
end)
end))
end)))))))
in (

let uu____10507 = (FStar_List.hd lbs)
in (match (uu____10507) with
| (attrs, (head_pat, defn)) -> begin
(

let uu____10551 = (is_rec || (is_app_pattern head_pat))
in (match (uu____10551) with
| true -> begin
(ds_let_rec_or_app ())
end
| uu____10556 -> begin
(ds_non_rec attrs head_pat defn body)
end))
end)))))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (

let t_bool1 = (

let uu____10564 = (

let uu____10565 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Syntax_Syntax.Tm_fvar (uu____10565))
in (mk1 uu____10564))
in (

let uu____10566 = (desugar_term_aq env t1)
in (match (uu____10566) with
| (t1', aq1) -> begin
(

let uu____10577 = (desugar_term_aq env t2)
in (match (uu____10577) with
| (t2', aq2) -> begin
(

let uu____10588 = (desugar_term_aq env t3)
in (match (uu____10588) with
| (t3', aq3) -> begin
(

let uu____10599 = (

let uu____10600 = (

let uu____10601 = (

let uu____10624 = (FStar_Syntax_Util.ascribe t1' ((FStar_Util.Inl (t_bool1)), (FStar_Pervasives_Native.None)))
in (

let uu____10645 = (

let uu____10662 = (

let uu____10677 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) t2.FStar_Parser_AST.range)
in ((uu____10677), (FStar_Pervasives_Native.None), (t2')))
in (

let uu____10690 = (

let uu____10707 = (

let uu____10722 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) t3.FStar_Parser_AST.range)
in ((uu____10722), (FStar_Pervasives_Native.None), (t3')))
in (uu____10707)::[])
in (uu____10662)::uu____10690))
in ((uu____10624), (uu____10645))))
in FStar_Syntax_Syntax.Tm_match (uu____10601))
in (mk1 uu____10600))
in ((uu____10599), ((join_aqs ((aq1)::(aq2)::(aq3)::[])))))
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

let desugar_branch = (fun uu____10921 -> (match (uu____10921) with
| (pat, wopt, b) -> begin
(

let uu____10943 = (desugar_match_pat env pat)
in (match (uu____10943) with
| (env1, pat1) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (e1) -> begin
(

let uu____10974 = (desugar_term env1 e1)
in FStar_Pervasives_Native.Some (uu____10974))
end)
in (

let uu____10975 = (desugar_term_aq env1 b)
in (match (uu____10975) with
| (b1, aq) -> begin
(

let uu____10988 = (desugar_disjunctive_pattern pat1 wopt1 b1)
in ((uu____10988), (aq)))
end)))
end))
end))
in (

let uu____10993 = (desugar_term_aq env e)
in (match (uu____10993) with
| (e1, aq) -> begin
(

let uu____11004 = (

let uu____11027 = (

let uu____11052 = (FStar_List.map desugar_branch branches)
in (FStar_All.pipe_right uu____11052 FStar_List.unzip))
in (FStar_All.pipe_right uu____11027 (fun uu____11158 -> (match (uu____11158) with
| (x, y) -> begin
(((FStar_List.flatten x)), (y))
end))))
in (match (uu____11004) with
| (brs, aqs) -> begin
(

let uu____11321 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_match (((e1), (brs)))))
in ((uu____11321), ((join_aqs ((aq)::aqs)))))
end))
end)))
end
| FStar_Parser_AST.Ascribed (e, t, tac_opt) -> begin
(

let annot = (

let uu____11366 = (is_comp_type env t)
in (match (uu____11366) with
| true -> begin
(

let uu____11375 = (desugar_comp t.FStar_Parser_AST.range env t)
in FStar_Util.Inr (uu____11375))
end
| uu____11382 -> begin
(

let uu____11383 = (desugar_term env t)
in FStar_Util.Inl (uu____11383))
end))
in (

let tac_opt1 = (FStar_Util.map_opt tac_opt (desugar_term env))
in (

let uu____11393 = (desugar_term_aq env e)
in (match (uu____11393) with
| (e1, aq) -> begin
(

let uu____11404 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_ascribed (((e1), (((annot), (tac_opt1))), (FStar_Pervasives_Native.None)))))
in ((uu____11404), (aq)))
end))))
end
| FStar_Parser_AST.Record (uu____11437, []) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedEmptyRecord), ("Unexpected empty record")) top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let record = (check_fields env fields top.FStar_Parser_AST.range)
in (

let user_ns = (

let uu____11478 = (FStar_List.hd fields)
in (match (uu____11478) with
| (f, uu____11490) -> begin
f.FStar_Ident.ns
end))
in (

let get_field = (fun xopt f -> (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun uu____11536 -> (match (uu____11536) with
| (g, uu____11542) -> begin
(Prims.op_Equality f.FStar_Ident.idText g.FStar_Ident.ident.FStar_Ident.idText)
end))))
in (

let fn = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((f)::[])))
in (match (found) with
| FStar_Pervasives_Native.Some (uu____11548, e) -> begin
((fn), (e))
end
| FStar_Pervasives_Native.None -> begin
(match (xopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____11562 = (

let uu____11567 = (FStar_Util.format2 "Field %s of record type %s is missing" f.FStar_Ident.idText record.FStar_Syntax_DsEnv.typename.FStar_Ident.str)
in ((FStar_Errors.Fatal_MissingFieldInRecord), (uu____11567)))
in (FStar_Errors.raise_error uu____11562 top.FStar_Parser_AST.range))
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

let uu____11575 = (

let uu____11586 = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map (fun uu____11617 -> (match (uu____11617) with
| (f, uu____11627) -> begin
(

let uu____11628 = (

let uu____11629 = (get_field FStar_Pervasives_Native.None f)
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____11629))
in ((uu____11628), (FStar_Parser_AST.Nothing)))
end))))
in ((user_constrname), (uu____11586)))
in FStar_Parser_AST.Construct (uu____11575))
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (

let uu____11647 = (

let uu____11648 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____11648))
in (FStar_Parser_AST.mk_term uu____11647 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record1 = (

let uu____11650 = (

let uu____11663 = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map (fun uu____11693 -> (match (uu____11693) with
| (f, uu____11703) -> begin
(get_field (FStar_Pervasives_Native.Some (xterm)) f)
end))))
in ((FStar_Pervasives_Native.None), (uu____11663)))
in FStar_Parser_AST.Record (uu____11650))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), ((((FStar_Pervasives_Native.None), ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (FStar_Pervasives_Native.None)))) x.FStar_Ident.idRange)), (e)))))::[]), ((FStar_Parser_AST.mk_term record1 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm1 = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let uu____11763 = (desugar_term_aq env recterm1)
in (match (uu____11763) with
| (e, s) -> begin
(match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____11779; FStar_Syntax_Syntax.vars = uu____11780}, args) -> begin
(

let uu____11802 = (

let uu____11803 = (

let uu____11804 = (

let uu____11819 = (

let uu____11822 = (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos)
in (

let uu____11823 = (

let uu____11826 = (

let uu____11827 = (

let uu____11834 = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map FStar_Pervasives_Native.fst))
in ((record.FStar_Syntax_DsEnv.typename), (uu____11834)))
in FStar_Syntax_Syntax.Record_ctor (uu____11827))
in FStar_Pervasives_Native.Some (uu____11826))
in (FStar_Syntax_Syntax.fvar uu____11822 FStar_Syntax_Syntax.Delta_constant uu____11823)))
in ((uu____11819), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____11804))
in (FStar_All.pipe_left mk1 uu____11803))
in ((uu____11802), (s)))
end
| uu____11861 -> begin
((e), (s))
end)
end))))))))
end
| FStar_Parser_AST.Project (e, f) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f);
(

let uu____11865 = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f)
in (match (uu____11865) with
| (constrname, is_rec) -> begin
(

let uu____11880 = (desugar_term_aq env e)
in (match (uu____11880) with
| (e1, s) -> begin
(

let projname = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname f.FStar_Ident.ident)
in (

let qual = (match (is_rec) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (((constrname), (f.FStar_Ident.ident))))
end
| uu____11897 -> begin
FStar_Pervasives_Native.None
end)
in (

let uu____11898 = (

let uu____11899 = (

let uu____11900 = (

let uu____11915 = (

let uu____11918 = (

let uu____11919 = (FStar_Ident.range_of_lid f)
in (FStar_Ident.set_lid_range projname uu____11919))
in (FStar_Syntax_Syntax.fvar uu____11918 FStar_Syntax_Syntax.Delta_equational qual))
in (

let uu____11920 = (

let uu____11929 = (FStar_Syntax_Syntax.as_arg e1)
in (uu____11929)::[])
in ((uu____11915), (uu____11920))))
in FStar_Syntax_Syntax.Tm_app (uu____11900))
in (FStar_All.pipe_left mk1 uu____11899))
in ((uu____11898), (s)))))
end))
end));
)
end
| FStar_Parser_AST.NamedTyp (uu____11958, e) -> begin
(desugar_term_aq env e)
end
| FStar_Parser_AST.Paren (e) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.VQuote (e) -> begin
(

let tm = (desugar_term env e)
in (

let uu____11967 = (

let uu____11968 = (FStar_Syntax_Subst.compress tm)
in uu____11968.FStar_Syntax_Syntax.n)
in (match (uu____11967) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____11976 = (

let uu___129_11977 = (

let uu____11978 = (

let uu____11979 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____11979))
in (FStar_Syntax_Util.exp_string uu____11978))
in {FStar_Syntax_Syntax.n = uu___129_11977.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = e.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___129_11977.FStar_Syntax_Syntax.vars})
in ((uu____11976), (noaqs)))
end
| uu____11980 -> begin
(

let uu____11981 = (

let uu____11986 = (

let uu____11987 = (FStar_Syntax_Print.term_to_string tm)
in (Prims.strcat "VQuote, expected an fvar, got: " uu____11987))
in ((FStar_Errors.Fatal_UnexpectedTermVQuote), (uu____11986)))
in (FStar_Errors.raise_error uu____11981 top.FStar_Parser_AST.range))
end)))
end
| FStar_Parser_AST.Quote (e, FStar_Parser_AST.Static) -> begin
(

let uu____11993 = (desugar_term_aq env e)
in (match (uu____11993) with
| (tm, vts) -> begin
(

let qi = {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = vts}
in (

let uu____12005 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_quoted (((tm), (qi)))))
in ((uu____12005), (noaqs))))
end))
end
| FStar_Parser_AST.Antiquote (b, e) -> begin
(

let bv = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (

let uu____12011 = (FStar_Syntax_Syntax.bv_to_name bv)
in (

let uu____12012 = (

let uu____12013 = (

let uu____12022 = (desugar_term env e)
in ((bv), (b), (uu____12022)))
in (uu____12013)::[])
in ((uu____12011), (uu____12012)))))
end
| FStar_Parser_AST.Quote (e, FStar_Parser_AST.Dynamic) -> begin
(

let qi = {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = []}
in (

let uu____12053 = (

let uu____12054 = (

let uu____12055 = (

let uu____12062 = (desugar_term env e)
in ((uu____12062), (qi)))
in FStar_Syntax_Syntax.Tm_quoted (uu____12055))
in (FStar_All.pipe_left mk1 uu____12054))
in ((uu____12053), (noaqs))))
end
| uu____12067 when (Prims.op_Equality top.FStar_Parser_AST.level FStar_Parser_AST.Formula) -> begin
(

let uu____12068 = (desugar_formula env top)
in ((uu____12068), (noaqs)))
end
| uu____12069 -> begin
(

let uu____12070 = (

let uu____12075 = (

let uu____12076 = (FStar_Parser_AST.term_to_string top)
in (Prims.strcat "Unexpected term: " uu____12076))
in ((FStar_Errors.Fatal_UnexpectedTerm), (uu____12075)))
in (FStar_Errors.raise_error uu____12070 top.FStar_Parser_AST.range))
end)))))))
and not_ascribed : FStar_Parser_AST.term  ->  Prims.bool = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Ascribed (uu____12082) -> begin
false
end
| uu____12091 -> begin
true
end))
and is_synth_by_tactic : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun e t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (l, r, FStar_Parser_AST.Hash) -> begin
(is_synth_by_tactic e l)
end
| FStar_Parser_AST.Var (lid) -> begin
(

let uu____12097 = (FStar_Syntax_DsEnv.resolve_to_fully_qualified_name e lid)
in (match (uu____12097) with
| FStar_Pervasives_Native.Some (lid1) -> begin
(FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid)
end
| FStar_Pervasives_Native.None -> begin
false
end))
end
| uu____12101 -> begin
false
end))
and desugar_args : FStar_Syntax_DsEnv.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____12138 -> (match (uu____12138) with
| (a, imp) -> begin
(

let uu____12151 = (desugar_term env a)
in (arg_withimp_e imp uu____12151))
end)))))
and desugar_comp : FStar_Range.range  ->  FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun r env t -> (

let fail1 = (fun err -> (FStar_Errors.raise_error err r))
in (

let is_requires = (fun uu____12183 -> (match (uu____12183) with
| (t1, uu____12189) -> begin
(

let uu____12190 = (

let uu____12191 = (unparen t1)
in uu____12191.FStar_Parser_AST.tm)
in (match (uu____12190) with
| FStar_Parser_AST.Requires (uu____12192) -> begin
true
end
| uu____12199 -> begin
false
end))
end))
in (

let is_ensures = (fun uu____12209 -> (match (uu____12209) with
| (t1, uu____12215) -> begin
(

let uu____12216 = (

let uu____12217 = (unparen t1)
in uu____12217.FStar_Parser_AST.tm)
in (match (uu____12216) with
| FStar_Parser_AST.Ensures (uu____12218) -> begin
true
end
| uu____12225 -> begin
false
end))
end))
in (

let is_app = (fun head1 uu____12240 -> (match (uu____12240) with
| (t1, uu____12246) -> begin
(

let uu____12247 = (

let uu____12248 = (unparen t1)
in uu____12248.FStar_Parser_AST.tm)
in (match (uu____12247) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = uu____12250; FStar_Parser_AST.level = uu____12251}, uu____12252, uu____12253) -> begin
(Prims.op_Equality d.FStar_Ident.ident.FStar_Ident.idText head1)
end
| uu____12254 -> begin
false
end))
end))
in (

let is_smt_pat = (fun uu____12264 -> (match (uu____12264) with
| (t1, uu____12270) -> begin
(

let uu____12271 = (

let uu____12272 = (unparen t1)
in uu____12272.FStar_Parser_AST.tm)
in (match (uu____12271) with
| FStar_Parser_AST.Construct (cons1, (({FStar_Parser_AST.tm = FStar_Parser_AST.Construct (smtpat, uu____12275); FStar_Parser_AST.range = uu____12276; FStar_Parser_AST.level = uu____12277}, uu____12278))::(uu____12279)::[]) -> begin
((FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid) && (FStar_Util.for_some (fun s -> (Prims.op_Equality smtpat.FStar_Ident.str s)) (("SMTPat")::("SMTPatT")::("SMTPatOr")::[])))
end
| FStar_Parser_AST.Construct (cons1, (({FStar_Parser_AST.tm = FStar_Parser_AST.Var (smtpat); FStar_Parser_AST.range = uu____12318; FStar_Parser_AST.level = uu____12319}, uu____12320))::(uu____12321)::[]) -> begin
((FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid) && (FStar_Util.for_some (fun s -> (Prims.op_Equality smtpat.FStar_Ident.str s)) (("smt_pat")::("smt_pat_or")::[])))
end
| uu____12346 -> begin
false
end))
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t1 -> (

let uu____12378 = (head_and_args t1)
in (match (uu____12378) with
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

let thunk_ens = (fun uu____12476 -> (match (uu____12476) with
| (e, i) -> begin
(

let uu____12487 = (thunk_ens_ e)
in ((uu____12487), (i)))
end))
in (

let fail_lemma = (fun uu____12499 -> (

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

let uu____12579 = (

let uu____12586 = (

let uu____12593 = (thunk_ens ens)
in (uu____12593)::(nil_pat)::[])
in (req_true)::uu____12586)
in (unit_tm)::uu____12579)
end
| (req)::(ens)::[] when ((is_requires req) && (is_ensures ens)) -> begin
(

let uu____12640 = (

let uu____12647 = (

let uu____12654 = (thunk_ens ens)
in (uu____12654)::(nil_pat)::[])
in (req)::uu____12647)
in (unit_tm)::uu____12640)
end
| (ens)::(smtpat)::[] when ((((

let uu____12703 = (is_requires ens)
in (not (uu____12703))) && (

let uu____12705 = (is_smt_pat ens)
in (not (uu____12705)))) && (

let uu____12707 = (is_decreases ens)
in (not (uu____12707)))) && (is_smt_pat smtpat)) -> begin
(

let uu____12708 = (

let uu____12715 = (

let uu____12722 = (thunk_ens ens)
in (uu____12722)::(smtpat)::[])
in (req_true)::uu____12715)
in (unit_tm)::uu____12708)
end
| (ens)::(dec)::[] when ((is_ensures ens) && (is_decreases dec)) -> begin
(

let uu____12769 = (

let uu____12776 = (

let uu____12783 = (thunk_ens ens)
in (uu____12783)::(nil_pat)::(dec)::[])
in (req_true)::uu____12776)
in (unit_tm)::uu____12769)
end
| (ens)::(dec)::(smtpat)::[] when (((is_ensures ens) && (is_decreases dec)) && (is_smt_pat smtpat)) -> begin
(

let uu____12843 = (

let uu____12850 = (

let uu____12857 = (thunk_ens ens)
in (uu____12857)::(smtpat)::(dec)::[])
in (req_true)::uu____12850)
in (unit_tm)::uu____12843)
end
| (req)::(ens)::(dec)::[] when (((is_requires req) && (is_ensures ens)) && (is_decreases dec)) -> begin
(

let uu____12917 = (

let uu____12924 = (

let uu____12931 = (thunk_ens ens)
in (uu____12931)::(nil_pat)::(dec)::[])
in (req)::uu____12924)
in (unit_tm)::uu____12917)
end
| (req)::(ens)::(smtpat)::[] when (((is_requires req) && (is_ensures ens)) && (is_smt_pat smtpat)) -> begin
(

let uu____12991 = (

let uu____12998 = (

let uu____13005 = (thunk_ens ens)
in (uu____13005)::(smtpat)::[])
in (req)::uu____12998)
in (unit_tm)::uu____12991)
end
| (req)::(ens)::(dec)::(smtpat)::[] when ((((is_requires req) && (is_ensures ens)) && (is_smt_pat smtpat)) && (is_decreases dec)) -> begin
(

let uu____13070 = (

let uu____13077 = (

let uu____13084 = (thunk_ens ens)
in (uu____13084)::(dec)::(smtpat)::[])
in (req)::uu____13077)
in (unit_tm)::uu____13070)
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

let uu____13146 = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes env) l)
in ((uu____13146), (args)))
end
| FStar_Parser_AST.Name (l) when ((

let uu____13174 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Ident.lid_equals uu____13174 FStar_Parser_Const.prims_lid)) && (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Tot")) -> begin
(

let uu____13175 = (

let uu____13182 = (FStar_Ident.set_lid_range FStar_Parser_Const.effect_Tot_lid head1.FStar_Parser_AST.range)
in ((uu____13182), ([])))
in ((uu____13175), (args)))
end
| FStar_Parser_AST.Name (l) when ((

let uu____13200 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Ident.lid_equals uu____13200 FStar_Parser_Const.prims_lid)) && (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "GTot")) -> begin
(

let uu____13201 = (

let uu____13208 = (FStar_Ident.set_lid_range FStar_Parser_Const.effect_GTot_lid head1.FStar_Parser_AST.range)
in ((uu____13208), ([])))
in ((uu____13201), (args)))
end
| FStar_Parser_AST.Name (l) when (((Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Type") || (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Type0")) || (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Effect")) -> begin
(

let uu____13224 = (

let uu____13231 = (FStar_Ident.set_lid_range FStar_Parser_Const.effect_Tot_lid head1.FStar_Parser_AST.range)
in ((uu____13231), ([])))
in ((uu____13224), ((((t1), (FStar_Parser_AST.Nothing)))::[])))
end
| uu____13254 -> begin
(

let default_effect = (

let uu____13256 = (FStar_Options.ml_ish ())
in (match (uu____13256) with
| true -> begin
FStar_Parser_Const.effect_ML_lid
end
| uu____13257 -> begin
((

let uu____13259 = (FStar_Options.warn_default_effects ())
in (match (uu____13259) with
| true -> begin
(FStar_Errors.log_issue head1.FStar_Parser_AST.range ((FStar_Errors.Warning_UseDefaultEffect), ("Using default effect Tot")))
end
| uu____13260 -> begin
()
end));
FStar_Parser_Const.effect_Tot_lid;
)
end))
in (

let uu____13261 = (

let uu____13268 = (FStar_Ident.set_lid_range default_effect head1.FStar_Parser_AST.range)
in ((uu____13268), ([])))
in ((uu____13261), ((((t1), (FStar_Parser_AST.Nothing)))::[]))))
end)
end)))
in (

let uu____13291 = (pre_process_comp_typ t)
in (match (uu____13291) with
| ((eff, cattributes), args) -> begin
((match ((Prims.op_Equality (FStar_List.length args) (Prims.parse_int "0"))) with
| true -> begin
(

let uu____13341 = (

let uu____13346 = (

let uu____13347 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" uu____13347))
in ((FStar_Errors.Fatal_NotEnoughArgsToEffect), (uu____13346)))
in (fail1 uu____13341))
end
| uu____13348 -> begin
()
end);
(

let is_universe = (fun uu____13358 -> (match (uu____13358) with
| (uu____13363, imp) -> begin
(Prims.op_Equality imp FStar_Parser_AST.UnivApp)
end))
in (

let uu____13365 = (FStar_Util.take is_universe args)
in (match (uu____13365) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun uu____13424 -> (match (uu____13424) with
| (u, imp) -> begin
(desugar_universe u)
end)) universes)
in (

let uu____13431 = (

let uu____13446 = (FStar_List.hd args1)
in (

let uu____13455 = (FStar_List.tl args1)
in ((uu____13446), (uu____13455))))
in (match (uu____13431) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (FStar_Pervasives_Native.fst result_arg))
in (

let rest1 = (desugar_args env rest)
in (

let uu____13510 = (

let is_decrease = (fun uu____13548 -> (match (uu____13548) with
| (t1, uu____13558) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____13568; FStar_Syntax_Syntax.vars = uu____13569}, (uu____13570)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.decreases_lid)
end
| uu____13601 -> begin
false
end)
end))
in (FStar_All.pipe_right rest1 (FStar_List.partition is_decrease)))
in (match (uu____13510) with
| (dec, rest2) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun uu____13717 -> (match (uu____13717) with
| (t1, uu____13727) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____13736, ((arg, uu____13738))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| uu____13767 -> begin
(failwith "impos")
end)
end))))
in (

let no_additional_args = (

let is_empty = (fun l -> (match (l) with
| [] -> begin
true
end
| uu____13784 -> begin
false
end))
in ((((is_empty decreases_clause) && (is_empty rest2)) && (is_empty cattributes)) && (is_empty universes1)))
in (

let uu____13795 = (no_additional_args && (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid))
in (match (uu____13795) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end
| uu____13798 -> begin
(

let uu____13799 = (no_additional_args && (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid))
in (match (uu____13799) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end
| uu____13802 -> begin
(

let flags1 = (

let uu____13806 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Lemma_lid)
in (match (uu____13806) with
| true -> begin
(FStar_Syntax_Syntax.LEMMA)::[]
end
| uu____13809 -> begin
(

let uu____13810 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid)
in (match (uu____13810) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____13813 -> begin
(

let uu____13814 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_ML_lid)
in (match (uu____13814) with
| true -> begin
(FStar_Syntax_Syntax.MLEFFECT)::[]
end
| uu____13817 -> begin
(

let uu____13818 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid)
in (match (uu____13818) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____13821 -> begin
[]
end))
end))
end))
end))
in (

let flags2 = (FStar_List.append flags1 cattributes)
in (

let rest3 = (

let uu____13834 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Lemma_lid)
in (match (uu____13834) with
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

let uu____13919 = (FStar_Ident.set_lid_range FStar_Parser_Const.pattern_lid pat.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar uu____13919 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.mk_Tm_app nil ((((pattern), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::[]) FStar_Pervasives_Native.None pat.FStar_Syntax_Syntax.pos)))
end
| uu____13934 -> begin
pat
end)
in (

let uu____13935 = (

let uu____13946 = (

let uu____13957 = (

let uu____13966 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat1), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) FStar_Pervasives_Native.None pat1.FStar_Syntax_Syntax.pos)
in ((uu____13966), (aq)))
in (uu____13957)::[])
in (ens)::uu____13946)
in (req)::uu____13935))
end
| uu____14007 -> begin
rest2
end)
end
| uu____14018 -> begin
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
and desugar_formula : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env f -> (

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
| uu____14031 -> begin
FStar_Pervasives_Native.None
end))
in (

let mk1 = (fun t -> (FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let uu___130_14052 = t
in {FStar_Syntax_Syntax.n = uu___130_14052.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___130_14052.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let uu___131_14094 = b
in {FStar_Parser_AST.b = uu___131_14094.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___131_14094.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___131_14094.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env1 pats1 -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (

let uu____14157 = (desugar_term env1 e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) uu____14157)))))) pats1))
in (match (tk) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____14170 = (FStar_Syntax_DsEnv.push_bv env a)
in (match (uu____14170) with
| (env1, a1) -> begin
(

let a2 = (

let uu___132_14180 = a1
in {FStar_Syntax_Syntax.ppname = uu___132_14180.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___132_14180.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats1 = (desugar_pats env1 pats)
in (

let body1 = (desugar_formula env1 body)
in (

let body2 = (match (pats1) with
| [] -> begin
body1
end
| uu____14206 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_meta (((body1), (FStar_Syntax_Syntax.Meta_pattern (pats1))))))
end)
in (

let body3 = (

let uu____14220 = (

let uu____14223 = (

let uu____14224 = (FStar_Syntax_Syntax.mk_binder a2)
in (uu____14224)::[])
in (no_annot_abs uu____14223 body2))
in (FStar_All.pipe_left setpos uu____14220))
in (

let uu____14239 = (

let uu____14240 = (

let uu____14255 = (

let uu____14258 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Syntax_Syntax.fvar uu____14258 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None))
in (

let uu____14259 = (

let uu____14268 = (FStar_Syntax_Syntax.as_arg body3)
in (uu____14268)::[])
in ((uu____14255), (uu____14259))))
in FStar_Syntax_Syntax.Tm_app (uu____14240))
in (FStar_All.pipe_left mk1 uu____14239)))))))
end))
end
| uu____14299 -> begin
(failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body1 = (

let uu____14379 = (q ((rest), (pats), (body)))
in (

let uu____14386 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term uu____14379 uu____14386 FStar_Parser_AST.Formula)))
in (

let uu____14387 = (q (((b)::[]), ([]), (body1)))
in (FStar_Parser_AST.mk_term uu____14387 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| uu____14396 -> begin
(failwith "impossible")
end))
in (

let uu____14399 = (

let uu____14400 = (unparen f)
in uu____14400.FStar_Parser_AST.tm)
in (match (uu____14399) with
| FStar_Parser_AST.Labeled (f1, l, p) -> begin
(

let f2 = (desugar_formula env f1)
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((f2), (FStar_Syntax_Syntax.Meta_labeled (((l), (f2.FStar_Syntax_Syntax.pos), (p)))))))))
end
| FStar_Parser_AST.QForall ([], uu____14407, uu____14408) -> begin
(failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QExists ([], uu____14419, uu____14420) -> begin
(failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____14451 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env uu____14451)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____14487 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env uu____14487)))
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
| uu____14530 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list) = (fun env bs -> (

let uu____14535 = (FStar_List.fold_left (fun uu____14571 b -> (match (uu____14571) with
| (env1, out) -> begin
(

let tk = (desugar_binder env1 (

let uu___133_14623 = b
in {FStar_Parser_AST.b = uu___133_14623.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___133_14623.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___133_14623.FStar_Parser_AST.aqual}))
in (match (tk) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____14640 = (FStar_Syntax_DsEnv.push_bv env1 a)
in (match (uu____14640) with
| (env2, a1) -> begin
(

let a2 = (

let uu___134_14660 = a1
in {FStar_Syntax_Syntax.ppname = uu___134_14660.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___134_14660.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in ((env2), ((((a2), ((trans_aqual b.FStar_Parser_AST.aqual))))::out)))
end))
end
| uu____14677 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedBinder), ("Unexpected binder")) b.FStar_Parser_AST.brange)
end))
end)) ((env), ([])) bs)
in (match (uu____14535) with
| (env1, tpars) -> begin
((env1), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.TAnnotated (x, t) -> begin
(

let uu____14764 = (desugar_typ env t)
in ((FStar_Pervasives_Native.Some (x)), (uu____14764)))
end
| FStar_Parser_AST.Annotated (x, t) -> begin
(

let uu____14769 = (desugar_typ env t)
in ((FStar_Pervasives_Native.Some (x)), (uu____14769)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____14773 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) FStar_Pervasives_Native.None x.FStar_Ident.idRange)
in ((FStar_Pervasives_Native.Some (x)), (uu____14773)))
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____14777 = (desugar_typ env t)
in ((FStar_Pervasives_Native.None), (uu____14777)))
end
| FStar_Parser_AST.Variable (x) -> begin
((FStar_Pervasives_Native.Some (x)), (FStar_Syntax_Syntax.tun))
end))


let mk_data_discriminators : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_DsEnv.env  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun quals env datas -> (

let quals1 = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___96_14816 -> (match (uu___96_14816) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____14817 -> begin
false
end))))
in (

let quals2 = (fun q -> (

let uu____14830 = ((

let uu____14833 = (FStar_Syntax_DsEnv.iface env)
in (not (uu____14833))) || (FStar_Syntax_DsEnv.admitted_iface env))
in (match (uu____14830) with
| true -> begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals1)
end
| uu____14836 -> begin
(FStar_List.append q quals1)
end)))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (

let uu____14847 = (FStar_Ident.range_of_lid disc_name)
in (

let uu____14848 = (quals2 ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((disc_name), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = uu____14847; FStar_Syntax_Syntax.sigquals = uu____14848; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))))))))


let mk_indexed_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  FStar_Syntax_DsEnv.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq env lid fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let uu____14887 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____14921 -> (match (uu____14921) with
| (x, uu____14929) -> begin
(

let uu____14930 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____14930) with
| (field_name, uu____14938) -> begin
(

let only_decl = (((

let uu____14942 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____14942)) || (Prims.op_disEquality fvq FStar_Syntax_Syntax.Data_ctor)) || (

let uu____14944 = (

let uu____14945 = (FStar_Syntax_DsEnv.current_module env)
in uu____14945.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____14944)))
in (

let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____14961 = (FStar_List.filter (fun uu___97_14965 -> (match (uu___97_14965) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____14966 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____14961)
end
| uu____14967 -> begin
q
end))
in (

let quals1 = (

let iquals1 = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___98_14979 -> (match (uu___98_14979) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____14980 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals1)))
in (

let decl = (

let uu____14982 = (FStar_Ident.range_of_lid field_name)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = uu____14982; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____14985 -> begin
(

let dd = (

let uu____14987 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____14987) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____14990 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lb = (

let uu____14992 = (

let uu____14997 = (FStar_Syntax_Syntax.lid_as_fv field_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____14997))
in {FStar_Syntax_Syntax.lbname = uu____14992; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbattrs = []; FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange})
in (

let impl = (

let uu____15001 = (

let uu____15002 = (

let uu____15009 = (

let uu____15012 = (

let uu____15013 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____15013 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____15012)::[])
in ((((false), ((lb)::[]))), (uu____15009)))
in FStar_Syntax_Syntax.Sig_let (uu____15002))
in {FStar_Syntax_Syntax.sigel = uu____15001; FStar_Syntax_Syntax.sigrng = p; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____15026 -> begin
(decl)::(impl)::[]
end))))
end))))))
end))
end))))
in (FStar_All.pipe_right uu____14887 FStar_List.flatten))))


let mk_data_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____15057, t, uu____15059, n1, uu____15061) when (

let uu____15066 = (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
in (not (uu____15066))) -> begin
(

let uu____15067 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____15067) with
| (formals, uu____15083) -> begin
(match (formals) with
| [] -> begin
[]
end
| uu____15106 -> begin
(

let filter_records = (fun uu___99_15120 -> (match (uu___99_15120) with
| FStar_Syntax_Syntax.RecordConstructor (uu____15123, fns) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| uu____15135 -> begin
FStar_Pervasives_Native.None
end))
in (

let fv_qual = (

let uu____15137 = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals filter_records)
in (match (uu____15137) with
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
| uu____15146 -> begin
iquals
end)
in (

let uu____15147 = (FStar_Util.first_N n1 formals)
in (match (uu____15147) with
| (uu____15170, rest) -> begin
(mk_indexed_projector_names iquals1 fv_qual env lid rest)
end)))))
end)
end))
end
| uu____15196 -> begin
[]
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (

let dd = (

let uu____15266 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____15266) with
| true -> begin
(

let uu____15269 = (FStar_Syntax_Util.incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (uu____15269))
end
| uu____15270 -> begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end))
in (

let lb = (

let uu____15272 = (

let uu____15277 = (FStar_Syntax_Syntax.lid_as_fv lid dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____15277))
in (

let uu____15278 = (

let uu____15281 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars uu____15281))
in (

let uu____15284 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = uu____15272; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____15278; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____15284; FStar_Syntax_Syntax.lbattrs = []; FStar_Syntax_Syntax.lbpos = rng})))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (lids))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))


let rec desugar_tycon : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.decl  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d quals tcs -> (

let rng = d.FStar_Parser_AST.drange
in (

let tycon_id = (fun uu___100_15335 -> (match (uu___100_15335) with
| FStar_Parser_AST.TyconAbstract (id1, uu____15337, uu____15338) -> begin
id1
end
| FStar_Parser_AST.TyconAbbrev (id1, uu____15348, uu____15349, uu____15350) -> begin
id1
end
| FStar_Parser_AST.TyconRecord (id1, uu____15360, uu____15361, uu____15362) -> begin
id1
end
| FStar_Parser_AST.TyconVariant (id1, uu____15392, uu____15393, uu____15394) -> begin
id1
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (x, uu____15438) -> begin
(

let uu____15439 = (

let uu____15440 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____15440))
in (FStar_Parser_AST.mk_term uu____15439 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| FStar_Parser_AST.Variable (x) -> begin
(

let uu____15442 = (

let uu____15443 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____15443))
in (FStar_Parser_AST.mk_term uu____15442 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| FStar_Parser_AST.TAnnotated (a, uu____15445) -> begin
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
| uu____15476 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (

let uu____15482 = (

let uu____15483 = (

let uu____15490 = (binder_to_term b)
in ((out), (uu____15490), ((imp_of_aqual b))))
in FStar_Parser_AST.App (uu____15483))
in (FStar_Parser_AST.mk_term uu____15482 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun uu___101_15502 -> (match (uu___101_15502) with
| FStar_Parser_AST.TyconRecord (id1, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id1.FStar_Ident.idText)), (id1.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun uu____15558 -> (match (uu____15558) with
| (x, t, uu____15569) -> begin
(

let uu____15574 = (

let uu____15575 = (

let uu____15580 = (FStar_Syntax_Util.mangle_field_name x)
in ((uu____15580), (t)))
in FStar_Parser_AST.Annotated (uu____15575))
in (FStar_Parser_AST.mk_binder uu____15574 x.FStar_Ident.idRange FStar_Parser_AST.Expr FStar_Pervasives_Native.None))
end)) fields)
in (

let result = (

let uu____15582 = (

let uu____15583 = (

let uu____15584 = (FStar_Ident.lid_of_ids ((id1)::[]))
in FStar_Parser_AST.Var (uu____15584))
in (FStar_Parser_AST.mk_term uu____15583 id1.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____15582 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id1.FStar_Ident.idRange FStar_Parser_AST.Type_level)
in (

let uu____15588 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____15615 -> (match (uu____15615) with
| (x, uu____15625, uu____15626) -> begin
(FStar_Syntax_Util.unmangle_field_name x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id1), (parms), (kopt), ((((constrName), (FStar_Pervasives_Native.Some (constrTyp)), (FStar_Pervasives_Native.None), (false)))::[])))), (uu____15588)))))))
end
| uu____15679 -> begin
(failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals1 _env mutuals uu___102_15718 -> (match (uu___102_15718) with
| FStar_Parser_AST.TyconAbstract (id1, binders, kopt) -> begin
(

let uu____15742 = (typars_of_binders _env binders)
in (match (uu____15742) with
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

let uu____15784 = (

let uu____15785 = (

let uu____15786 = (FStar_Ident.lid_of_ids ((id1)::[]))
in FStar_Parser_AST.Var (uu____15786))
in (FStar_Parser_AST.mk_term uu____15785 id1.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____15784 binders))
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
| uu____15797 -> begin
(failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env1 bs -> (

let uu____15845 = (FStar_List.fold_left (fun uu____15885 uu____15886 -> (match (((uu____15885), (uu____15886))) with
| ((env2, tps), (x, imp)) -> begin
(

let uu____15977 = (FStar_Syntax_DsEnv.push_bv env2 x.FStar_Syntax_Syntax.ppname)
in (match (uu____15977) with
| (env3, y) -> begin
((env3), ((((y), (imp)))::tps))
end))
end)) ((env1), ([])) bs)
in (match (uu____15845) with
| (env2, bs1) -> begin
((env2), ((FStar_List.rev bs1)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id1, bs, kopt))::[] -> begin
(

let kopt1 = (match (kopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____16090 = (tm_type_z id1.FStar_Ident.idRange)
in FStar_Pervasives_Native.Some (uu____16090))
end
| uu____16091 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id1), (bs), (kopt1)))
in (

let uu____16099 = (desugar_abstract_tc quals env [] tc)
in (match (uu____16099) with
| (uu____16112, uu____16113, se, uu____16115) -> begin
(

let se1 = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, uu____16118, typars, k, [], []) -> begin
(

let quals1 = se.FStar_Syntax_Syntax.sigquals
in (

let quals2 = (match ((FStar_List.contains FStar_Syntax_Syntax.Assumption quals1)) with
| true -> begin
quals1
end
| uu____16133 -> begin
((

let uu____16135 = (

let uu____16136 = (FStar_Options.ml_ish ())
in (not (uu____16136)))
in (match (uu____16135) with
| true -> begin
(

let uu____16137 = (

let uu____16142 = (

let uu____16143 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Adding an implicit \'assume new\' qualifier on %s" uu____16143))
in ((FStar_Errors.Warning_AddImplicitAssumeNewQualifier), (uu____16142)))
in (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng uu____16137))
end
| uu____16144 -> begin
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
| uu____16150 -> begin
(

let uu____16151 = (

let uu____16158 = (

let uu____16159 = (

let uu____16172 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (uu____16172)))
in FStar_Syntax_Syntax.Tm_arrow (uu____16159))
in (FStar_Syntax_Syntax.mk uu____16158))
in (uu____16151 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
end)
in (

let uu___135_16186 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t))); FStar_Syntax_Syntax.sigrng = uu___135_16186.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = uu___135_16186.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___135_16186.FStar_Syntax_Syntax.sigattrs}))))
end
| uu____16187 -> begin
(failwith "Impossible")
end)
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se1)
in (

let env2 = (

let uu____16190 = (FStar_Syntax_DsEnv.qualify env1 id1)
in (FStar_Syntax_DsEnv.push_doc env1 uu____16190 d.FStar_Parser_AST.doc))
in ((env2), ((se1)::[])))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id1, binders, kopt, t))::[] -> begin
(

let uu____16203 = (typars_of_binders env binders)
in (match (uu____16203) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____16239 = (FStar_Util.for_some (fun uu___103_16241 -> (match (uu___103_16241) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| uu____16242 -> begin
false
end)) quals)
in (match (uu____16239) with
| true -> begin
FStar_Syntax_Syntax.teff
end
| uu____16243 -> begin
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

let uu____16249 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___104_16253 -> (match (uu___104_16253) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| uu____16254 -> begin
false
end))))
in (match (uu____16249) with
| true -> begin
quals
end
| uu____16257 -> begin
(match ((Prims.op_Equality t0.FStar_Parser_AST.level FStar_Parser_AST.Formula)) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals
end
| uu____16260 -> begin
quals
end)
end))
in (

let qlid = (FStar_Syntax_DsEnv.qualify env id1)
in (

let se = (

let uu____16263 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Effect))
in (match (uu____16263) with
| true -> begin
(

let uu____16266 = (

let uu____16273 = (

let uu____16274 = (unparen t)
in uu____16274.FStar_Parser_AST.tm)
in (match (uu____16273) with
| FStar_Parser_AST.Construct (head1, args) -> begin
(

let uu____16295 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____16325))::args_rev -> begin
(

let uu____16337 = (

let uu____16338 = (unparen last_arg)
in uu____16338.FStar_Parser_AST.tm)
in (match (uu____16337) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____16366 -> begin
(([]), (args))
end))
end
| uu____16375 -> begin
(([]), (args))
end)
in (match (uu____16295) with
| (cattributes, args1) -> begin
(

let uu____16414 = (desugar_attributes env cattributes)
in (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((head1), (args1)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (uu____16414)))
end))
end
| uu____16425 -> begin
((t), ([]))
end))
in (match (uu____16266) with
| (t1, cattributes) -> begin
(

let c = (desugar_comp t1.FStar_Parser_AST.range env' t1)
in (

let typars1 = (FStar_Syntax_Subst.close_binders typars)
in (

let c1 = (FStar_Syntax_Subst.close_comp typars1 c)
in (

let quals2 = (FStar_All.pipe_right quals1 (FStar_List.filter (fun uu___105_16447 -> (match (uu___105_16447) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| uu____16448 -> begin
true
end))))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((qlid), ([]), (typars1), (c1), ((FStar_List.append cattributes (FStar_Syntax_Util.comp_flags c1))))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))))
end))
end
| uu____16451 -> begin
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
| (FStar_Parser_AST.TyconRecord (uu____16455))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let uu____16479 = (tycon_record_as_variant trec)
in (match (uu____16479) with
| (t, fs) -> begin
(

let uu____16496 = (

let uu____16499 = (

let uu____16500 = (

let uu____16509 = (

let uu____16512 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Ident.ids_of_lid uu____16512))
in ((uu____16509), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____16500))
in (uu____16499)::quals)
in (desugar_tycon env d uu____16496 ((t)::[])))
end)))
end
| (uu____16517)::uu____16518 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals1 et tc -> (

let uu____16685 = et
in (match (uu____16685) with
| (env1, tcs1) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (uu____16910) -> begin
(

let trec = tc
in (

let uu____16934 = (tycon_record_as_variant trec)
in (match (uu____16934) with
| (t, fs) -> begin
(

let uu____16993 = (

let uu____16996 = (

let uu____16997 = (

let uu____17006 = (

let uu____17009 = (FStar_Syntax_DsEnv.current_module env1)
in (FStar_Ident.ids_of_lid uu____17009))
in ((uu____17006), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____16997))
in (uu____16996)::quals1)
in (collect_tcs uu____16993 ((env1), (tcs1)) t))
end)))
end
| FStar_Parser_AST.TyconVariant (id1, binders, kopt, constructors) -> begin
(

let uu____17096 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id1), (binders), (kopt)))))
in (match (uu____17096) with
| (env2, uu____17156, se, tconstr) -> begin
((env2), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals1))))::tcs1))
end))
end
| FStar_Parser_AST.TyconAbbrev (id1, binders, kopt, t) -> begin
(

let uu____17305 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id1), (binders), (kopt)))))
in (match (uu____17305) with
| (env2, uu____17365, se, tconstr) -> begin
((env2), ((FStar_Util.Inr (((se), (binders), (t), (quals1))))::tcs1))
end))
end
| uu____17490 -> begin
(failwith "Unrecognized mutual type definition")
end)
end)))
in (

let uu____17537 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (uu____17537) with
| (env1, tcs1) -> begin
(

let tcs2 = (FStar_List.rev tcs1)
in (

let docs_tps_sigelts = (FStar_All.pipe_right tcs2 (FStar_List.collect (fun uu___107_18048 -> (match (uu___107_18048) with
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (id1, uvs, tpars, k, uu____18115, uu____18116); FStar_Syntax_Syntax.sigrng = uu____18117; FStar_Syntax_Syntax.sigquals = uu____18118; FStar_Syntax_Syntax.sigmeta = uu____18119; FStar_Syntax_Syntax.sigattrs = uu____18120}, binders, t, quals1) -> begin
(

let t1 = (

let uu____18181 = (typars_of_binders env1 binders)
in (match (uu____18181) with
| (env2, tpars1) -> begin
(

let uu____18212 = (push_tparams env2 tpars1)
in (match (uu____18212) with
| (env_tps, tpars2) -> begin
(

let t1 = (desugar_typ env_tps t)
in (

let tpars3 = (FStar_Syntax_Subst.close_binders tpars2)
in (FStar_Syntax_Subst.close tpars3 t1)))
end))
end))
in (

let uu____18245 = (

let uu____18266 = (mk_typ_abbrev id1 uvs tpars k t1 ((id1)::[]) quals1 rng)
in ((((id1), (d.FStar_Parser_AST.doc))), ([]), (uu____18266)))
in (uu____18245)::[]))
end
| FStar_Util.Inl ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs1, tpars, k, mutuals1, uu____18334); FStar_Syntax_Syntax.sigrng = uu____18335; FStar_Syntax_Syntax.sigquals = tname_quals; FStar_Syntax_Syntax.sigmeta = uu____18337; FStar_Syntax_Syntax.sigattrs = uu____18338}, constrs, tconstr, quals1) -> begin
(

let mk_tot = (fun t -> (

let tot1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((tot1), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)))
in (

let tycon = ((tname), (tpars), (k))
in (

let uu____18436 = (push_tparams env1 tpars)
in (match (uu____18436) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun uu____18513 -> (match (uu____18513) with
| (x, uu____18527) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let tot_tconstr = (mk_tot tconstr)
in (

let uu____18535 = (

let uu____18564 = (FStar_All.pipe_right constrs (FStar_List.map (fun uu____18678 -> (match (uu____18678) with
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
| uu____18731 -> begin
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

let uu____18734 = (close env_tps t)
in (desugar_term env_tps uu____18734))
in (

let name = (FStar_Syntax_DsEnv.qualify env1 id1)
in (

let quals2 = (FStar_All.pipe_right tname_quals (FStar_List.collect (fun uu___106_18745 -> (match (uu___106_18745) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| uu____18757 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (

let uu____18765 = (

let uu____18786 = (

let uu____18787 = (

let uu____18788 = (

let uu____18803 = (

let uu____18804 = (

let uu____18807 = (FStar_All.pipe_right t1 FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total uu____18807))
in (FStar_Syntax_Util.arrow data_tpars uu____18804))
in ((name), (univs1), (uu____18803), (tname), (ntps), (mutuals1)))
in FStar_Syntax_Syntax.Sig_datacon (uu____18788))
in {FStar_Syntax_Syntax.sigel = uu____18787; FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in ((((name), (doc1))), (tps), (uu____18786)))
in ((name), (uu____18765))))))))
end))))
in (FStar_All.pipe_left FStar_List.split uu____18564))
in (match (uu____18535) with
| (constrNames, constrs1) -> begin
(((((tname), (d.FStar_Parser_AST.doc))), ([]), ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs1), (tpars), (k), (mutuals1), (constrNames))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = tname_quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))::constrs1
end))))
end))))
end
| uu____19044 -> begin
(failwith "impossible")
end))))
in (

let name_docs = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.map (fun uu____19176 -> (match (uu____19176) with
| (name_doc, uu____19204, uu____19205) -> begin
name_doc
end))))
in (

let sigelts = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.map (fun uu____19285 -> (match (uu____19285) with
| (uu____19306, uu____19307, se) -> begin
se
end))))
in (

let uu____19337 = (

let uu____19344 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle sigelts quals uu____19344 rng))
in (match (uu____19337) with
| (bundle, abbrevs) -> begin
(

let env2 = (FStar_Syntax_DsEnv.push_sigelt env0 bundle)
in (

let env3 = (FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env2 abbrevs)
in (

let data_ops = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.collect (fun uu____19410 -> (match (uu____19410) with
| (uu____19433, tps, se) -> begin
(mk_data_projector_names quals env3 se)
end))))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, uu____19484, tps, k, uu____19487, constrs) when ((FStar_List.length constrs) > (Prims.parse_int "1")) -> begin
(

let quals1 = se.FStar_Syntax_Syntax.sigquals
in (

let quals2 = (match ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals1)) with
| true -> begin
(FStar_Syntax_Syntax.Private)::quals1
end
| uu____19505 -> begin
quals1
end)
in (mk_data_discriminators quals2 env3 constrs)))
end
| uu____19506 -> begin
[]
end))))
in (

let ops = (FStar_List.append discs data_ops)
in (

let env4 = (FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env3 ops)
in (

let env5 = (FStar_List.fold_left (fun acc uu____19523 -> (match (uu____19523) with
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

let uu____19560 = (FStar_List.fold_left (fun uu____19583 b -> (match (uu____19583) with
| (env1, binders1) -> begin
(

let uu____19603 = (desugar_binder env1 b)
in (match (uu____19603) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____19620 = (as_binder env1 b.FStar_Parser_AST.aqual ((FStar_Pervasives_Native.Some (a)), (k)))
in (match (uu____19620) with
| (binder, env2) -> begin
((env2), ((binder)::binders1))
end))
end
| uu____19639 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_MissingNameInBinder), ("Missing name in binder")) b.FStar_Parser_AST.brange)
end))
end)) ((env), ([])) binders)
in (match (uu____19560) with
| (env1, binders1) -> begin
((env1), ((FStar_List.rev binders1)))
end)))


let push_reflect_effect : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lid  ->  FStar_Range.range  ->  FStar_Syntax_DsEnv.env = (fun env quals effect_name range -> (

let uu____19692 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___108_19697 -> (match (uu___108_19697) with
| FStar_Syntax_Syntax.Reflectable (uu____19698) -> begin
true
end
| uu____19699 -> begin
false
end))))
in (match (uu____19692) with
| true -> begin
(

let monad_env = (FStar_Syntax_DsEnv.enter_monad_scope env effect_name.FStar_Ident.ident)
in (

let reflect_lid = (

let uu____19702 = (FStar_Ident.id_of_text "reflect")
in (FStar_All.pipe_right uu____19702 (FStar_Syntax_DsEnv.qualify monad_env)))
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (effect_name))::[]
in (

let refl_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = range; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (FStar_Syntax_DsEnv.push_sigelt env refl_decl)))))
end
| uu____19707 -> begin
env
end)))


let rec desugar_effect : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.term Prims.list  ->  (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_typ eff_decls attrs -> (

let env0 = env
in (

let monad_env = (FStar_Syntax_DsEnv.enter_monad_scope env eff_name)
in (

let uu____19844 = (desugar_binders monad_env eff_binders)
in (match (uu____19844) with
| (env1, binders) -> begin
(

let eff_t = (desugar_term env1 eff_typ)
in (

let for_free = (

let uu____19865 = (

let uu____19867 = (

let uu____19874 = (FStar_Syntax_Util.arrow_formals eff_t)
in (FStar_Pervasives_Native.fst uu____19874))
in (FStar_List.length uu____19867))
in (Prims.op_Equality uu____19865 (Prims.parse_int "1")))
in (

let mandatory_members = (

let rr_members = ("repr")::("return")::("bind")::[]
in (match (for_free) with
| true -> begin
rr_members
end
| uu____19908 -> begin
(FStar_List.append rr_members (("return_wp")::("bind_wp")::("if_then_else")::("ite_wp")::("stronger")::("close_wp")::("assert_p")::("assume_p")::("null_wp")::("trivial")::[]))
end))
in (

let name_of_eff_decl = (fun decl -> (match (decl.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____19915, ((FStar_Parser_AST.TyconAbbrev (name, uu____19917, uu____19918, uu____19919), uu____19920))::[]) -> begin
(FStar_Ident.text_of_id name)
end
| uu____19953 -> begin
(failwith "Malformed effect member declaration.")
end))
in (

let uu____19954 = (FStar_List.partition (fun decl -> (

let uu____19966 = (name_of_eff_decl decl)
in (FStar_List.mem uu____19966 mandatory_members))) eff_decls)
in (match (uu____19954) with
| (mandatory_members_decls, actions) -> begin
(

let uu____19983 = (FStar_All.pipe_right mandatory_members_decls (FStar_List.fold_left (fun uu____20012 decl -> (match (uu____20012) with
| (env2, out) -> begin
(

let uu____20032 = (desugar_decl env2 decl)
in (match (uu____20032) with
| (env3, ses) -> begin
(

let uu____20045 = (

let uu____20048 = (FStar_List.hd ses)
in (uu____20048)::out)
in ((env3), (uu____20045)))
end))
end)) ((env1), ([]))))
in (match (uu____19983) with
| (env2, decls) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (

let actions_docs = (FStar_All.pipe_right actions (FStar_List.map (fun d1 -> (match (d1.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____20116, ((FStar_Parser_AST.TyconAbbrev (name, action_params, uu____20119, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (uu____20120, ((def, uu____20122))::((cps_type, uu____20124))::[]); FStar_Parser_AST.range = uu____20125; FStar_Parser_AST.level = uu____20126}), doc1))::[]) when (not (for_free)) -> begin
(

let uu____20178 = (desugar_binders env2 action_params)
in (match (uu____20178) with
| (env3, action_params1) -> begin
(

let action_params2 = (FStar_Syntax_Subst.close_binders action_params1)
in (

let uu____20198 = (

let uu____20199 = (FStar_Syntax_DsEnv.qualify env3 name)
in (

let uu____20200 = (

let uu____20201 = (desugar_term env3 def)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____20201))
in (

let uu____20206 = (

let uu____20207 = (desugar_typ env3 cps_type)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____20207))
in {FStar_Syntax_Syntax.action_name = uu____20199; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = action_params2; FStar_Syntax_Syntax.action_defn = uu____20200; FStar_Syntax_Syntax.action_typ = uu____20206})))
in ((uu____20198), (doc1))))
end))
end
| FStar_Parser_AST.Tycon (uu____20214, ((FStar_Parser_AST.TyconAbbrev (name, action_params, uu____20217, defn), doc1))::[]) when for_free -> begin
(

let uu____20252 = (desugar_binders env2 action_params)
in (match (uu____20252) with
| (env3, action_params1) -> begin
(

let action_params2 = (FStar_Syntax_Subst.close_binders action_params1)
in (

let uu____20272 = (

let uu____20273 = (FStar_Syntax_DsEnv.qualify env3 name)
in (

let uu____20274 = (

let uu____20275 = (desugar_term env3 defn)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____20275))
in {FStar_Syntax_Syntax.action_name = uu____20273; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = action_params2; FStar_Syntax_Syntax.action_defn = uu____20274; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
in ((uu____20272), (doc1))))
end))
end
| uu____20282 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_MalformedActionDeclaration), ("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).")) d1.FStar_Parser_AST.drange)
end))))
in (

let actions1 = (FStar_List.map FStar_Pervasives_Native.fst actions_docs)
in (

let eff_t1 = (FStar_Syntax_Subst.close binders1 eff_t)
in (

let lookup1 = (fun s -> (

let l = (

let uu____20314 = (FStar_Ident.mk_ident ((s), (d.FStar_Parser_AST.drange)))
in (FStar_Syntax_DsEnv.qualify env2 uu____20314))
in (

let uu____20315 = (

let uu____20316 = (FStar_Syntax_DsEnv.fail_or env2 (FStar_Syntax_DsEnv.try_lookup_definition env2) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders1) uu____20316))
in (([]), (uu____20315)))))
in (

let mname = (FStar_Syntax_DsEnv.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange (FStar_Pervasives_Native.Some (mname))) quals)
in (

let se = (match (for_free) with
| true -> begin
(

let dummy_tscheme = (

let uu____20333 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (([]), (uu____20333)))
in (

let uu____20340 = (

let uu____20341 = (

let uu____20342 = (

let uu____20343 = (lookup1 "repr")
in (FStar_Pervasives_Native.snd uu____20343))
in (

let uu____20352 = (lookup1 "return")
in (

let uu____20353 = (lookup1 "bind")
in (

let uu____20354 = (FStar_List.map (desugar_term env2) attrs)
in {FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = eff_t1; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = uu____20342; FStar_Syntax_Syntax.return_repr = uu____20352; FStar_Syntax_Syntax.bind_repr = uu____20353; FStar_Syntax_Syntax.actions = actions1; FStar_Syntax_Syntax.eff_attrs = uu____20354}))))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____20341))
in {FStar_Syntax_Syntax.sigel = uu____20340; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qualifiers; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))
end
| uu____20357 -> begin
(

let rr = (FStar_Util.for_some (fun uu___109_20360 -> (match (uu___109_20360) with
| FStar_Syntax_Syntax.Reifiable -> begin
true
end
| FStar_Syntax_Syntax.Reflectable (uu____20361) -> begin
true
end
| uu____20362 -> begin
false
end)) qualifiers)
in (

let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in (

let uu____20376 = (

let uu____20377 = (

let uu____20378 = (lookup1 "return_wp")
in (

let uu____20379 = (lookup1 "bind_wp")
in (

let uu____20380 = (lookup1 "if_then_else")
in (

let uu____20381 = (lookup1 "ite_wp")
in (

let uu____20382 = (lookup1 "stronger")
in (

let uu____20383 = (lookup1 "close_wp")
in (

let uu____20384 = (lookup1 "assert_p")
in (

let uu____20385 = (lookup1 "assume_p")
in (

let uu____20386 = (lookup1 "null_wp")
in (

let uu____20387 = (lookup1 "trivial")
in (

let uu____20388 = (match (rr) with
| true -> begin
(

let uu____20389 = (lookup1 "repr")
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____20389))
end
| uu____20404 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let uu____20405 = (match (rr) with
| true -> begin
(lookup1 "return")
end
| uu____20406 -> begin
un_ts
end)
in (

let uu____20407 = (match (rr) with
| true -> begin
(lookup1 "bind")
end
| uu____20408 -> begin
un_ts
end)
in (

let uu____20409 = (FStar_List.map (desugar_term env2) attrs)
in {FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = eff_t1; FStar_Syntax_Syntax.ret_wp = uu____20378; FStar_Syntax_Syntax.bind_wp = uu____20379; FStar_Syntax_Syntax.if_then_else = uu____20380; FStar_Syntax_Syntax.ite_wp = uu____20381; FStar_Syntax_Syntax.stronger = uu____20382; FStar_Syntax_Syntax.close_wp = uu____20383; FStar_Syntax_Syntax.assert_p = uu____20384; FStar_Syntax_Syntax.assume_p = uu____20385; FStar_Syntax_Syntax.null_wp = uu____20386; FStar_Syntax_Syntax.trivial = uu____20387; FStar_Syntax_Syntax.repr = uu____20388; FStar_Syntax_Syntax.return_repr = uu____20405; FStar_Syntax_Syntax.bind_repr = uu____20407; FStar_Syntax_Syntax.actions = actions1; FStar_Syntax_Syntax.eff_attrs = uu____20409}))))))))))))))
in FStar_Syntax_Syntax.Sig_new_effect (uu____20377))
in {FStar_Syntax_Syntax.sigel = uu____20376; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qualifiers; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))
end)
in (

let env3 = (FStar_Syntax_DsEnv.push_sigelt env0 se)
in (

let env4 = (FStar_Syntax_DsEnv.push_doc env3 mname d.FStar_Parser_AST.doc)
in (

let env5 = (FStar_All.pipe_right actions_docs (FStar_List.fold_left (fun env5 uu____20435 -> (match (uu____20435) with
| (a, doc1) -> begin
(

let env6 = (

let uu____20449 = (FStar_Syntax_Util.action_as_lb mname a a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_DsEnv.push_sigelt env5 uu____20449))
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

let uu____20473 = (desugar_binders env1 eff_binders)
in (match (uu____20473) with
| (env2, binders) -> begin
(

let uu____20492 = (

let uu____20511 = (head_and_args defn)
in (match (uu____20511) with
| (head1, args) -> begin
(

let lid = (match (head1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
l
end
| uu____20556 -> begin
(

let uu____20557 = (

let uu____20562 = (

let uu____20563 = (

let uu____20564 = (FStar_Parser_AST.term_to_string head1)
in (Prims.strcat uu____20564 " not found"))
in (Prims.strcat "Effect " uu____20563))
in ((FStar_Errors.Fatal_EffectNotFound), (uu____20562)))
in (FStar_Errors.raise_error uu____20557 d.FStar_Parser_AST.drange))
end)
in (

let ed = (FStar_Syntax_DsEnv.fail_or env2 (FStar_Syntax_DsEnv.try_lookup_effect_defn env2) lid)
in (

let uu____20566 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____20596))::args_rev -> begin
(

let uu____20608 = (

let uu____20609 = (unparen last_arg)
in uu____20609.FStar_Parser_AST.tm)
in (match (uu____20608) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____20637 -> begin
(([]), (args))
end))
end
| uu____20646 -> begin
(([]), (args))
end)
in (match (uu____20566) with
| (cattributes, args1) -> begin
(

let uu____20697 = (desugar_args env2 args1)
in (

let uu____20706 = (desugar_attributes env2 cattributes)
in ((lid), (ed), (uu____20697), (uu____20706))))
end))))
end))
in (match (uu____20492) with
| (ed_lid, ed, args, cattributes) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in ((match ((Prims.op_disEquality (FStar_List.length args) (FStar_List.length ed.FStar_Syntax_Syntax.binders))) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ArgumentLengthMismatch), ("Unexpected number of arguments to effect constructor")) defn.FStar_Parser_AST.range)
end
| uu____20761 -> begin
()
end);
(

let uu____20762 = (FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit)
in (match (uu____20762) with
| (ed_binders, uu____20776, ed_binders_opening) -> begin
(

let sub1 = (fun uu____20789 -> (match (uu____20789) with
| (us, x) -> begin
(

let x1 = (

let uu____20803 = (FStar_Syntax_Subst.shift_subst (FStar_List.length us) ed_binders_opening)
in (FStar_Syntax_Subst.subst uu____20803 x))
in (

let s = (FStar_Syntax_Util.subst_of_list ed_binders args)
in (

let uu____20807 = (

let uu____20808 = (FStar_Syntax_Subst.subst s x1)
in ((us), (uu____20808)))
in (FStar_Syntax_Subst.close_tscheme binders1 uu____20807))))
end))
in (

let mname = (FStar_Syntax_DsEnv.qualify env0 eff_name)
in (

let ed1 = (

let uu____20817 = (

let uu____20818 = (sub1 (([]), (ed.FStar_Syntax_Syntax.signature)))
in (FStar_Pervasives_Native.snd uu____20818))
in (

let uu____20833 = (sub1 ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____20834 = (sub1 ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____20835 = (sub1 ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____20836 = (sub1 ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____20837 = (sub1 ed.FStar_Syntax_Syntax.stronger)
in (

let uu____20838 = (sub1 ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____20839 = (sub1 ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____20840 = (sub1 ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____20841 = (sub1 ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____20842 = (sub1 ed.FStar_Syntax_Syntax.trivial)
in (

let uu____20843 = (

let uu____20844 = (sub1 (([]), (ed.FStar_Syntax_Syntax.repr)))
in (FStar_Pervasives_Native.snd uu____20844))
in (

let uu____20859 = (sub1 ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____20860 = (sub1 ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____20861 = (FStar_List.map (fun action -> (

let uu____20869 = (FStar_Syntax_DsEnv.qualify env2 action.FStar_Syntax_Syntax.action_unqualified_name)
in (

let uu____20870 = (

let uu____20871 = (sub1 (([]), (action.FStar_Syntax_Syntax.action_defn)))
in (FStar_Pervasives_Native.snd uu____20871))
in (

let uu____20886 = (

let uu____20887 = (sub1 (([]), (action.FStar_Syntax_Syntax.action_typ)))
in (FStar_Pervasives_Native.snd uu____20887))
in {FStar_Syntax_Syntax.action_name = uu____20869; FStar_Syntax_Syntax.action_unqualified_name = action.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = action.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = uu____20870; FStar_Syntax_Syntax.action_typ = uu____20886})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = cattributes; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = ed.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = uu____20817; FStar_Syntax_Syntax.ret_wp = uu____20833; FStar_Syntax_Syntax.bind_wp = uu____20834; FStar_Syntax_Syntax.if_then_else = uu____20835; FStar_Syntax_Syntax.ite_wp = uu____20836; FStar_Syntax_Syntax.stronger = uu____20837; FStar_Syntax_Syntax.close_wp = uu____20838; FStar_Syntax_Syntax.assert_p = uu____20839; FStar_Syntax_Syntax.assume_p = uu____20840; FStar_Syntax_Syntax.null_wp = uu____20841; FStar_Syntax_Syntax.trivial = uu____20842; FStar_Syntax_Syntax.repr = uu____20843; FStar_Syntax_Syntax.return_repr = uu____20859; FStar_Syntax_Syntax.bind_repr = uu____20860; FStar_Syntax_Syntax.actions = uu____20861; FStar_Syntax_Syntax.eff_attrs = ed.FStar_Syntax_Syntax.eff_attrs})))))))))))))))
in (

let se = (

let for_free = (

let uu____20904 = (

let uu____20906 = (

let uu____20913 = (FStar_Syntax_Util.arrow_formals ed1.FStar_Syntax_Syntax.signature)
in (FStar_Pervasives_Native.fst uu____20913))
in (FStar_List.length uu____20906))
in (Prims.op_Equality uu____20904 (Prims.parse_int "1")))
in (

let uu____20939 = (

let uu____20942 = (trans_qual1 (FStar_Pervasives_Native.Some (mname)))
in (FStar_List.map uu____20942 quals))
in {FStar_Syntax_Syntax.sigel = (match (for_free) with
| true -> begin
FStar_Syntax_Syntax.Sig_new_effect_for_free (ed1)
end
| uu____20947 -> begin
FStar_Syntax_Syntax.Sig_new_effect (ed1)
end); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = uu____20939; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))
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

let uu____20964 = (FStar_Syntax_Util.action_as_lb mname a a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_DsEnv.push_sigelt env5 uu____20964))
in (FStar_Syntax_DsEnv.push_doc env6 a.FStar_Syntax_Syntax.action_name doc1)))) env4))
in (

let env6 = (

let uu____20966 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____20966) with
| true -> begin
(

let reflect_lid = (

let uu____20970 = (FStar_Ident.id_of_text "reflect")
in (FStar_All.pipe_right uu____20970 (FStar_Syntax_DsEnv.qualify monad_env)))
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]
in (

let refl_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (FStar_Syntax_DsEnv.push_sigelt env5 refl_decl))))
end
| uu____20975 -> begin
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

let uu____20980 = (match (d.FStar_Parser_AST.doc) with
| FStar_Pervasives_Native.None -> begin
((""), ([]))
end
| FStar_Pervasives_Native.Some (fsdoc) -> begin
fsdoc
end)
in (match (uu____20980) with
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
| FStar_Pervasives_Native.Some (uu____21031) -> begin
(

let uu____21032 = (

let uu____21033 = (FStar_Parser_ToDocument.signature_to_document d)
in (FStar_Pprint.pretty_string 0.950000 (Prims.parse_int "80") uu____21033))
in (Prims.strcat "\n  " uu____21032))
end
| uu____21034 -> begin
""
end)
in (

let other = (FStar_List.filter_map (fun uu____21047 -> (match (uu____21047) with
| (k, v1) -> begin
(match (((Prims.op_disEquality k "summary") && (Prims.op_disEquality k "type"))) with
| true -> begin
FStar_Pervasives_Native.Some ((Prims.strcat k (Prims.strcat ": " v1)))
end
| uu____21058 -> begin
FStar_Pervasives_Native.None
end)
end)) kv)
in (

let other1 = (match ((Prims.op_disEquality other [])) with
| true -> begin
(Prims.strcat (FStar_String.concat "\n" other) "\n")
end
| uu____21062 -> begin
""
end)
in (

let str = (Prims.strcat summary (Prims.strcat pp (Prims.strcat other1 text)))
in (

let fv = (

let uu____21065 = (FStar_Ident.lid_of_str "FStar.Pervasives.Comment")
in (FStar_Syntax_Syntax.fvar uu____21065 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in (

let arg = (FStar_Syntax_Util.exp_string str)
in (

let uu____21067 = (

let uu____21076 = (FStar_Syntax_Syntax.as_arg arg)
in (uu____21076)::[])
in (FStar_Syntax_Util.mk_app fv uu____21067)))))))))
end)))
and desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (

let uu____21101 = (desugar_decl_noattrs env d)
in (match (uu____21101) with
| (env1, sigelts) -> begin
(

let attrs = d.FStar_Parser_AST.attrs
in (

let attrs1 = (FStar_List.map (desugar_term env1) attrs)
in (

let attrs2 = (

let uu____21119 = (mk_comment_attr d)
in (uu____21119)::attrs1)
in (

let uu____21120 = (FStar_List.map (fun sigelt -> (

let uu___136_21124 = sigelt
in {FStar_Syntax_Syntax.sigel = uu___136_21124.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___136_21124.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___136_21124.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___136_21124.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = attrs2})) sigelts)
in ((env1), (uu____21120))))))
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
| uu____21149 -> begin
()
end);
((env), ((se)::[]));
))
end
| FStar_Parser_AST.Fsdoc (uu____21150) -> begin
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

let uu____21158 = (FStar_Syntax_DsEnv.push_module_abbrev env x l)
in ((uu____21158), ([])))
end
| FStar_Parser_AST.Tycon (is_effect, tcs) -> begin
(

let quals = (match (is_effect) with
| true -> begin
(FStar_Parser_AST.Effect_qual)::d.FStar_Parser_AST.quals
end
| uu____21182 -> begin
d.FStar_Parser_AST.quals
end)
in (

let tcs1 = (FStar_List.map (fun uu____21195 -> (match (uu____21195) with
| (x, uu____21203) -> begin
x
end)) tcs)
in (

let uu____21208 = (FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals)
in (desugar_tycon env d uu____21208 tcs1))))
end
| FStar_Parser_AST.TopLevelLet (isrec, lets) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let expand_toplevel_pattern = ((Prims.op_Equality isrec FStar_Parser_AST.NoLetQualifier) && (match (lets) with
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatOp (uu____21230); FStar_Parser_AST.prange = uu____21231}, uu____21232))::[] -> begin
false
end
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____21241); FStar_Parser_AST.prange = uu____21242}, uu____21243))::[] -> begin
false
end
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____21258); FStar_Parser_AST.prange = uu____21259}, uu____21260); FStar_Parser_AST.prange = uu____21261}, uu____21262))::[] -> begin
false
end
| ((p, uu____21290))::[] -> begin
(

let uu____21299 = (is_app_pattern p)
in (not (uu____21299)))
end
| uu____21300 -> begin
false
end))
in (match ((not (expand_toplevel_pattern))) with
| true -> begin
(

let lets1 = (FStar_List.map (fun x -> ((FStar_Pervasives_Native.None), (x))) lets)
in (

let as_inner_let = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets1), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)
in (

let uu____21373 = (desugar_term_maybe_top true env as_inner_let)
in (match (uu____21373) with
| (ds_lets, aq) -> begin
((check_no_aq aq);
(

let uu____21385 = (

let uu____21386 = (FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets)
in uu____21386.FStar_Syntax_Syntax.n)
in (match (uu____21385) with
| FStar_Syntax_Syntax.Tm_let (lbs, uu____21396) -> begin
(

let fvs = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals1 = (match (quals) with
| (uu____21429)::uu____21430 -> begin
(FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals)
end
| uu____21433 -> begin
(FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.collect (fun uu___110_21448 -> (match (uu___110_21448) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (uu____21451); FStar_Syntax_Syntax.lbunivs = uu____21452; FStar_Syntax_Syntax.lbtyp = uu____21453; FStar_Syntax_Syntax.lbeff = uu____21454; FStar_Syntax_Syntax.lbdef = uu____21455; FStar_Syntax_Syntax.lbattrs = uu____21456; FStar_Syntax_Syntax.lbpos = uu____21457} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____21469; FStar_Syntax_Syntax.lbtyp = uu____21470; FStar_Syntax_Syntax.lbeff = uu____21471; FStar_Syntax_Syntax.lbdef = uu____21472; FStar_Syntax_Syntax.lbattrs = uu____21473; FStar_Syntax_Syntax.lbpos = uu____21474} -> begin
(FStar_Syntax_DsEnv.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals2 = (

let uu____21488 = (FStar_All.pipe_right lets1 (FStar_Util.for_some (fun uu____21519 -> (match (uu____21519) with
| (uu____21532, (uu____21533, t)) -> begin
(Prims.op_Equality t.FStar_Parser_AST.level FStar_Parser_AST.Formula)
end))))
in (match (uu____21488) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals1
end
| uu____21549 -> begin
quals1
end))
in (

let lbs1 = (

let uu____21551 = (FStar_All.pipe_right quals2 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____21551) with
| true -> begin
(

let uu____21554 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu___137_21568 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let uu___138_21570 = fv
in {FStar_Syntax_Syntax.fv_name = uu___138_21570.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = uu___138_21570.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = uu___137_21568.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___137_21568.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___137_21568.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___137_21568.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___137_21568.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___137_21568.FStar_Syntax_Syntax.lbpos})))))
in (((FStar_Pervasives_Native.fst lbs)), (uu____21554)))
end
| uu____21575 -> begin
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
| uu____21597 -> begin
(failwith "Desugaring a let did not produce a let")
end));
)
end))))
end
| uu____21602 -> begin
(

let uu____21603 = (match (lets) with
| ((pat, body))::[] -> begin
((pat), (body))
end
| uu____21622 -> begin
(failwith "expand_toplevel_pattern should only allow single definition lets")
end)
in (match (uu____21603) with
| (pat, body) -> begin
(

let fresh_toplevel_name = (FStar_Ident.gen FStar_Range.dummyRange)
in (

let fresh_pat = (

let var_pat = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((fresh_toplevel_name), (FStar_Pervasives_Native.None)))) FStar_Range.dummyRange)
in (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat1, ty) -> begin
(

let uu___139_21658 = pat1
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed (((var_pat), (ty))); FStar_Parser_AST.prange = uu___139_21658.FStar_Parser_AST.prange})
end
| uu____21665 -> begin
var_pat
end))
in (

let main_let = (desugar_decl env (

let uu___140_21672 = d
in {FStar_Parser_AST.d = FStar_Parser_AST.TopLevelLet (((isrec), ((((fresh_pat), (body)))::[]))); FStar_Parser_AST.drange = uu___140_21672.FStar_Parser_AST.drange; FStar_Parser_AST.doc = uu___140_21672.FStar_Parser_AST.doc; FStar_Parser_AST.quals = (FStar_Parser_AST.Private)::d.FStar_Parser_AST.quals; FStar_Parser_AST.attrs = uu___140_21672.FStar_Parser_AST.attrs}))
in (

let build_projection = (fun uu____21708 id1 -> (match (uu____21708) with
| (env1, ses) -> begin
(

let main = (

let uu____21729 = (

let uu____21730 = (FStar_Ident.lid_of_ids ((fresh_toplevel_name)::[]))
in FStar_Parser_AST.Var (uu____21730))
in (FStar_Parser_AST.mk_term uu____21729 FStar_Range.dummyRange FStar_Parser_AST.Expr))
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

let uu____21780 = (desugar_decl env1 id_decl)
in (match (uu____21780) with
| (env2, ses') -> begin
((env2), ((FStar_List.append ses ses')))
end))))))))
end))
in (

let bvs = (

let uu____21798 = (gather_pattern_bound_vars pat)
in (FStar_All.pipe_right uu____21798 FStar_Util.set_elements))
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

let uu____21823 = (close_fun env t)
in (desugar_term env uu____21823))
in (

let quals1 = (

let uu____21827 = ((FStar_Syntax_DsEnv.iface env) && (FStar_Syntax_DsEnv.admitted_iface env))
in (match (uu____21827) with
| true -> begin
(FStar_Parser_AST.Assumption)::quals
end
| uu____21830 -> begin
quals
end))
in (

let lid = (FStar_Syntax_DsEnv.qualify env id1)
in (

let se = (

let uu____21833 = (FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals1)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), ([]), (t1))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = uu____21833; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se)
in (

let env2 = (FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc)
in ((env2), ((se)::[])))))))))
end
| FStar_Parser_AST.Exception (id1, FStar_Pervasives_Native.None) -> begin
(

let uu____21841 = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_lid env) FStar_Parser_Const.exn_lid)
in (match (uu____21841) with
| (t, uu____21855) -> begin
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

let uu____21885 = (

let uu____21892 = (FStar_Syntax_Syntax.null_binder t)
in (uu____21892)::[])
in (

let uu____21905 = (

let uu____21908 = (

let uu____21909 = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_lid env) FStar_Parser_Const.exn_lid)
in (FStar_Pervasives_Native.fst uu____21909))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____21908))
in (FStar_Syntax_Util.arrow uu____21885 uu____21905)))
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

let uu____21970 = (FStar_Syntax_DsEnv.try_lookup_effect_name env l1)
in (match (uu____21970) with
| FStar_Pervasives_Native.None -> begin
(

let uu____21973 = (

let uu____21978 = (

let uu____21979 = (

let uu____21980 = (FStar_Syntax_Print.lid_to_string l1)
in (Prims.strcat uu____21980 " not found"))
in (Prims.strcat "Effect name " uu____21979))
in ((FStar_Errors.Fatal_EffectNotFound), (uu____21978)))
in (FStar_Errors.raise_error uu____21973 d.FStar_Parser_AST.drange))
end
| FStar_Pervasives_Native.Some (l2) -> begin
l2
end)))
in (

let src = (lookup1 l.FStar_Parser_AST.msource)
in (

let dst = (lookup1 l.FStar_Parser_AST.mdest)
in (

let uu____21984 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(

let uu____22026 = (

let uu____22035 = (

let uu____22042 = (desugar_term env t)
in (([]), (uu____22042)))
in FStar_Pervasives_Native.Some (uu____22035))
in ((uu____22026), (FStar_Pervasives_Native.None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(

let uu____22075 = (

let uu____22084 = (

let uu____22091 = (desugar_term env wp)
in (([]), (uu____22091)))
in FStar_Pervasives_Native.Some (uu____22084))
in (

let uu____22100 = (

let uu____22109 = (

let uu____22116 = (desugar_term env t)
in (([]), (uu____22116)))
in FStar_Pervasives_Native.Some (uu____22109))
in ((uu____22075), (uu____22100))))
end
| FStar_Parser_AST.LiftForFree (t) -> begin
(

let uu____22142 = (

let uu____22151 = (

let uu____22158 = (desugar_term env t)
in (([]), (uu____22158)))
in FStar_Pervasives_Native.Some (uu____22151))
in ((FStar_Pervasives_Native.None), (uu____22142)))
end)
in (match (uu____21984) with
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

let uu____22236 = (

let uu____22237 = (

let uu____22244 = (FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids)
in ((uu____22244), (t1)))
in FStar_Syntax_Syntax.Sig_splice (uu____22237))
in {FStar_Syntax_Syntax.sigel = uu____22236; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se)
in ((env1), ((se)::[])))))
end)))


let desugar_decls : env_t  ->  FStar_Parser_AST.decl Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env decls -> (

let uu____22270 = (FStar_List.fold_left (fun uu____22290 d -> (match (uu____22290) with
| (env1, sigelts) -> begin
(

let uu____22310 = (desugar_decl env1 d)
in (match (uu____22310) with
| (env2, se) -> begin
((env2), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls)
in (match (uu____22270) with
| (env1, sigelts) -> begin
(

let rec forward = (fun acc uu___112_22355 -> (match (uu___112_22355) with
| (se1)::(se2)::sigelts1 -> begin
(match (((se1.FStar_Syntax_Syntax.sigel), (se2.FStar_Syntax_Syntax.sigel))) with
| (FStar_Syntax_Syntax.Sig_declare_typ (uu____22369), FStar_Syntax_Syntax.Sig_let (uu____22370)) -> begin
(

let uu____22383 = (

let uu____22386 = (

let uu___141_22387 = se2
in (

let uu____22388 = (

let uu____22391 = (FStar_List.filter (fun uu___111_22405 -> (match (uu___111_22405) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____22409; FStar_Syntax_Syntax.vars = uu____22410}, uu____22411); FStar_Syntax_Syntax.pos = uu____22412; FStar_Syntax_Syntax.vars = uu____22413} when (

let uu____22436 = (

let uu____22437 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____22437))
in (Prims.op_Equality uu____22436 "FStar.Pervasives.Comment")) -> begin
true
end
| uu____22438 -> begin
false
end)) se1.FStar_Syntax_Syntax.sigattrs)
in (FStar_List.append uu____22391 se2.FStar_Syntax_Syntax.sigattrs))
in {FStar_Syntax_Syntax.sigel = uu___141_22387.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___141_22387.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___141_22387.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___141_22387.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu____22388}))
in (uu____22386)::(se1)::acc)
in (forward uu____22383 sigelts1))
end
| uu____22443 -> begin
(forward ((se1)::acc) ((se2)::sigelts1))
end)
end
| sigelts1 -> begin
(FStar_List.rev_append acc sigelts1)
end))
in (

let uu____22451 = (forward [] sigelts)
in ((env1), (uu____22451))))
end)))


let open_prims_all : (FStar_Parser_AST.decoration Prims.list  ->  FStar_Parser_AST.decl) Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Parser_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Parser_Const.all_lid)) FStar_Range.dummyRange))::[]


let generalize_annotated_univs : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun s -> (

let bs_univnames = (fun bs -> (

let uu____22493 = (

let uu____22506 = (FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name)
in (FStar_List.fold_left (fun uvs uu____22523 -> (match (uu____22523) with
| ({FStar_Syntax_Syntax.ppname = uu____22532; FStar_Syntax_Syntax.index = uu____22533; FStar_Syntax_Syntax.sort = t}, uu____22535) -> begin
(

let uu____22538 = (FStar_Syntax_Free.univnames t)
in (FStar_Util.set_union uvs uu____22538))
end)) uu____22506))
in (FStar_All.pipe_right bs uu____22493)))
in (

let empty_set = (FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name)
in (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____22552) -> begin
(failwith "Impossible: collect_annotated_universes: bare data/type constructor")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____22569) -> begin
(failwith "Impossible: collect_annotated_universes: bare data/type constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (sigs, lids) -> begin
(

let uvs = (

let uu____22595 = (FStar_All.pipe_right sigs (FStar_List.fold_left (fun uvs se -> (

let se_univs = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____22616, uu____22617, bs, t, uu____22620, uu____22621) -> begin
(

let uu____22630 = (bs_univnames bs)
in (

let uu____22633 = (FStar_Syntax_Free.univnames t)
in (FStar_Util.set_union uu____22630 uu____22633)))
end
| FStar_Syntax_Syntax.Sig_datacon (uu____22636, uu____22637, t, uu____22639, uu____22640, uu____22641) -> begin
(FStar_Syntax_Free.univnames t)
end
| uu____22646 -> begin
(failwith "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt")
end)
in (FStar_Util.set_union uvs se_univs))) empty_set))
in (FStar_All.pipe_right uu____22595 FStar_Util.set_elements))
in (

let usubst = (FStar_Syntax_Subst.univ_var_closing uvs)
in (

let uu___142_22654 = s
in (

let uu____22655 = (

let uu____22656 = (

let uu____22665 = (FStar_All.pipe_right sigs (FStar_List.map (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____22683, bs, t, lids1, lids2) -> begin
(

let uu___143_22696 = se
in (

let uu____22697 = (

let uu____22698 = (

let uu____22715 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let uu____22716 = (

let uu____22717 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst uu____22717 t))
in ((lid), (uvs), (uu____22715), (uu____22716), (lids1), (lids2))))
in FStar_Syntax_Syntax.Sig_inductive_typ (uu____22698))
in {FStar_Syntax_Syntax.sigel = uu____22697; FStar_Syntax_Syntax.sigrng = uu___143_22696.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___143_22696.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___143_22696.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___143_22696.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____22729, t, tlid, n1, lids1) -> begin
(

let uu___144_22738 = se
in (

let uu____22739 = (

let uu____22740 = (

let uu____22755 = (FStar_Syntax_Subst.subst usubst t)
in ((lid), (uvs), (uu____22755), (tlid), (n1), (lids1)))
in FStar_Syntax_Syntax.Sig_datacon (uu____22740))
in {FStar_Syntax_Syntax.sigel = uu____22739; FStar_Syntax_Syntax.sigrng = uu___144_22738.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___144_22738.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___144_22738.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___144_22738.FStar_Syntax_Syntax.sigattrs}))
end
| uu____22758 -> begin
(failwith "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt")
end))))
in ((uu____22665), (lids)))
in FStar_Syntax_Syntax.Sig_bundle (uu____22656))
in {FStar_Syntax_Syntax.sigel = uu____22655; FStar_Syntax_Syntax.sigrng = uu___142_22654.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___142_22654.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___142_22654.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___142_22654.FStar_Syntax_Syntax.sigattrs}))))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____22764, t) -> begin
(

let uvs = (

let uu____22767 = (FStar_Syntax_Free.univnames t)
in (FStar_All.pipe_right uu____22767 FStar_Util.set_elements))
in (

let uu___145_22772 = s
in (

let uu____22773 = (

let uu____22774 = (

let uu____22781 = (FStar_Syntax_Subst.close_univ_vars uvs t)
in ((lid), (uvs), (uu____22781)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____22774))
in {FStar_Syntax_Syntax.sigel = uu____22773; FStar_Syntax_Syntax.sigrng = uu___145_22772.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___145_22772.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___145_22772.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___145_22772.FStar_Syntax_Syntax.sigattrs})))
end
| FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) -> begin
(

let lb_univnames = (fun lb -> (

let uu____22803 = (FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____22806 = (match (lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, e, uu____22813) -> begin
(

let uvs1 = (bs_univnames bs)
in (

let uvs2 = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (uu____22842, (FStar_Util.Inl (t), uu____22844), uu____22845) -> begin
(FStar_Syntax_Free.univnames t)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____22892, (FStar_Util.Inr (c), uu____22894), uu____22895) -> begin
(FStar_Syntax_Free.univnames_comp c)
end
| uu____22942 -> begin
empty_set
end)
in (FStar_Util.set_union uvs1 uvs2)))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____22943, (FStar_Util.Inl (t), uu____22945), uu____22946) -> begin
(FStar_Syntax_Free.univnames t)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____22993, (FStar_Util.Inr (c), uu____22995), uu____22996) -> begin
(FStar_Syntax_Free.univnames_comp c)
end
| uu____23043 -> begin
empty_set
end)
in (FStar_Util.set_union uu____22803 uu____22806))))
in (

let all_lb_univs = (

let uu____23047 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun uvs lb -> (

let uu____23063 = (lb_univnames lb)
in (FStar_Util.set_union uvs uu____23063))) empty_set))
in (FStar_All.pipe_right uu____23047 FStar_Util.set_elements))
in (

let usubst = (FStar_Syntax_Subst.univ_var_closing all_lb_univs)
in (

let uu___146_23073 = s
in (

let uu____23074 = (

let uu____23075 = (

let uu____23082 = (

let uu____23083 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu___147_23095 = lb
in (

let uu____23096 = (FStar_Syntax_Subst.subst usubst lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____23099 = (FStar_Syntax_Subst.subst usubst lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___147_23095.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = all_lb_univs; FStar_Syntax_Syntax.lbtyp = uu____23096; FStar_Syntax_Syntax.lbeff = uu___147_23095.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____23099; FStar_Syntax_Syntax.lbattrs = uu___147_23095.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___147_23095.FStar_Syntax_Syntax.lbpos}))))))
in ((b), (uu____23083)))
in ((uu____23082), (lids)))
in FStar_Syntax_Syntax.Sig_let (uu____23075))
in {FStar_Syntax_Syntax.sigel = uu____23074; FStar_Syntax_Syntax.sigrng = uu___146_23073.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___146_23073.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___146_23073.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___146_23073.FStar_Syntax_Syntax.sigattrs})))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____23107, fml) -> begin
(

let uvs = (

let uu____23110 = (FStar_Syntax_Free.univnames fml)
in (FStar_All.pipe_right uu____23110 FStar_Util.set_elements))
in (

let uu___148_23115 = s
in (

let uu____23116 = (

let uu____23117 = (

let uu____23124 = (FStar_Syntax_Subst.close_univ_vars uvs fml)
in ((lid), (uvs), (uu____23124)))
in FStar_Syntax_Syntax.Sig_assume (uu____23117))
in {FStar_Syntax_Syntax.sigel = uu____23116; FStar_Syntax_Syntax.sigrng = uu___148_23115.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___148_23115.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___148_23115.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___148_23115.FStar_Syntax_Syntax.sigattrs})))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uu____23126, bs, c, flags1) -> begin
(

let uvs = (

let uu____23135 = (

let uu____23138 = (bs_univnames bs)
in (

let uu____23141 = (FStar_Syntax_Free.univnames_comp c)
in (FStar_Util.set_union uu____23138 uu____23141)))
in (FStar_All.pipe_right uu____23135 FStar_Util.set_elements))
in (

let usubst = (FStar_Syntax_Subst.univ_var_closing uvs)
in (

let uu___149_23149 = s
in (

let uu____23150 = (

let uu____23151 = (

let uu____23164 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let uu____23165 = (FStar_Syntax_Subst.subst_comp usubst c)
in ((lid), (uvs), (uu____23164), (uu____23165), (flags1))))
in FStar_Syntax_Syntax.Sig_effect_abbrev (uu____23151))
in {FStar_Syntax_Syntax.sigel = uu____23150; FStar_Syntax_Syntax.sigrng = uu___149_23149.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___149_23149.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___149_23149.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___149_23149.FStar_Syntax_Syntax.sigattrs}))))
end
| uu____23168 -> begin
s
end))))


let desugar_modul_common : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let env1 = (match (((curmod), (m))) with
| (FStar_Pervasives_Native.None, uu____23203) -> begin
env
end
| (FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.name = prev_lid; FStar_Syntax_Syntax.declarations = uu____23207; FStar_Syntax_Syntax.exports = uu____23208; FStar_Syntax_Syntax.is_interface = uu____23209}), FStar_Parser_AST.Module (current_lid, uu____23211)) when ((FStar_Ident.lid_equals prev_lid current_lid) && (FStar_Options.interactive ())) -> begin
env
end
| (FStar_Pervasives_Native.Some (prev_mod), uu____23219) -> begin
(

let uu____23222 = (FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod)
in (FStar_Pervasives_Native.fst uu____23222))
end)
in (

let uu____23227 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(

let uu____23263 = (FStar_Syntax_DsEnv.prepare_module_or_interface true admitted env1 mname FStar_Syntax_DsEnv.default_mii)
in ((uu____23263), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(

let uu____23280 = (FStar_Syntax_DsEnv.prepare_module_or_interface false false env1 mname FStar_Syntax_DsEnv.default_mii)
in ((uu____23280), (mname), (decls), (false)))
end)
in (match (uu____23227) with
| ((env2, pop_when_done), mname, decls, intf) -> begin
(

let uu____23310 = (desugar_decls env2 decls)
in (match (uu____23310) with
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

let uu____23375 = ((FStar_Options.interactive ()) && (

let uu____23377 = (

let uu____23378 = (

let uu____23379 = (FStar_Options.file_list ())
in (FStar_List.hd uu____23379))
in (FStar_Util.get_file_extension uu____23378))
in (FStar_List.mem uu____23377 (("fsti")::("fsi")::[]))))
in (match (uu____23375) with
| true -> begin
(as_interface m)
end
| uu____23382 -> begin
m
end))
in (

let uu____23383 = (desugar_modul_common curmod env m1)
in (match (uu____23383) with
| (x, y, pop_when_done) -> begin
((match (pop_when_done) with
| true -> begin
(

let uu____23398 = (FStar_Syntax_DsEnv.pop ())
in ())
end
| uu____23399 -> begin
()
end);
((x), (y));
)
end))))


let desugar_modul : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (

let uu____23418 = (desugar_modul_common FStar_Pervasives_Native.None env m)
in (match (uu____23418) with
| (env1, modul, pop_when_done) -> begin
(

let uu____23432 = (FStar_Syntax_DsEnv.finish_module_or_interface env1 modul)
in (match (uu____23432) with
| (env2, modul1) -> begin
((

let uu____23444 = (FStar_Options.dump_module modul1.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____23444) with
| true -> begin
(

let uu____23445 = (FStar_Syntax_Print.modul_to_string modul1)
in (FStar_Util.print1 "Module after desugaring:\n%s\n" uu____23445))
end
| uu____23446 -> begin
()
end));
(

let uu____23447 = (match (pop_when_done) with
| true -> begin
(FStar_Syntax_DsEnv.export_interface modul1.FStar_Syntax_Syntax.name env2)
end
| uu____23448 -> begin
env2
end)
in ((uu____23447), (modul1)));
)
end))
end)))


let ast_modul_to_modul : FStar_Parser_AST.modul  ->  FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv = (fun modul env -> (

let uu____23465 = (desugar_modul env modul)
in (match (uu____23465) with
| (env1, modul1) -> begin
((modul1), (env1))
end)))


let decls_to_sigelts : FStar_Parser_AST.decl Prims.list  ->  FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv = (fun decls env -> (

let uu____23496 = (desugar_decls env decls)
in (match (uu____23496) with
| (env1, sigelts) -> begin
((sigelts), (env1))
end)))


let partial_ast_modul_to_modul : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Parser_AST.modul  ->  FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv = (fun modul a_modul env -> (

let uu____23538 = (desugar_partial_modul modul env a_modul)
in (match (uu____23538) with
| (env1, modul1) -> begin
((modul1), (env1))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Syntax_DsEnv.module_inclusion_info  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  unit FStar_Syntax_DsEnv.withenv = (fun m mii erase_univs en -> (

let erase_univs_ed = (fun ed -> (

let erase_binders = (fun bs -> (match (bs) with
| [] -> begin
[]
end
| uu____23624 -> begin
(

let t = (

let uu____23632 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (FStar_Syntax_Syntax.t_unit), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (erase_univs uu____23632))
in (

let uu____23643 = (

let uu____23644 = (FStar_Syntax_Subst.compress t)
in uu____23644.FStar_Syntax_Syntax.n)
in (match (uu____23643) with
| FStar_Syntax_Syntax.Tm_abs (bs1, uu____23654, uu____23655) -> begin
bs1
end
| uu____23676 -> begin
(failwith "Impossible")
end)))
end))
in (

let uu____23683 = (

let uu____23690 = (erase_binders ed.FStar_Syntax_Syntax.binders)
in (FStar_Syntax_Subst.open_term' uu____23690 FStar_Syntax_Syntax.t_unit))
in (match (uu____23683) with
| (binders, uu____23692, binders_opening) -> begin
(

let erase_term = (fun t -> (

let uu____23700 = (

let uu____23701 = (FStar_Syntax_Subst.subst binders_opening t)
in (erase_univs uu____23701))
in (FStar_Syntax_Subst.close binders uu____23700)))
in (

let erase_tscheme = (fun uu____23719 -> (match (uu____23719) with
| (us, t) -> begin
(

let t1 = (

let uu____23739 = (FStar_Syntax_Subst.shift_subst (FStar_List.length us) binders_opening)
in (FStar_Syntax_Subst.subst uu____23739 t))
in (

let uu____23742 = (

let uu____23743 = (erase_univs t1)
in (FStar_Syntax_Subst.close binders uu____23743))
in (([]), (uu____23742))))
end))
in (

let erase_action = (fun action -> (

let opening = (FStar_Syntax_Subst.shift_subst (FStar_List.length action.FStar_Syntax_Syntax.action_univs) binders_opening)
in (

let erased_action_params = (match (action.FStar_Syntax_Syntax.action_params) with
| [] -> begin
[]
end
| uu____23762 -> begin
(

let bs = (

let uu____23770 = (FStar_Syntax_Subst.subst_binders opening action.FStar_Syntax_Syntax.action_params)
in (FStar_All.pipe_left erase_binders uu____23770))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (FStar_Syntax_Syntax.t_unit), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____23802 = (

let uu____23803 = (

let uu____23806 = (FStar_Syntax_Subst.close binders t)
in (FStar_Syntax_Subst.compress uu____23806))
in uu____23803.FStar_Syntax_Syntax.n)
in (match (uu____23802) with
| FStar_Syntax_Syntax.Tm_abs (bs1, uu____23808, uu____23809) -> begin
bs1
end
| uu____23830 -> begin
(failwith "Impossible")
end))))
end)
in (

let erase_term1 = (fun t -> (

let uu____23837 = (

let uu____23838 = (FStar_Syntax_Subst.subst opening t)
in (erase_univs uu____23838))
in (FStar_Syntax_Subst.close binders uu____23837)))
in (

let uu___150_23839 = action
in (

let uu____23840 = (erase_term1 action.FStar_Syntax_Syntax.action_defn)
in (

let uu____23841 = (erase_term1 action.FStar_Syntax_Syntax.action_typ)
in {FStar_Syntax_Syntax.action_name = uu___150_23839.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___150_23839.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = erased_action_params; FStar_Syntax_Syntax.action_defn = uu____23840; FStar_Syntax_Syntax.action_typ = uu____23841})))))))
in (

let uu___151_23842 = ed
in (

let uu____23843 = (FStar_Syntax_Subst.close_binders binders)
in (

let uu____23844 = (erase_term ed.FStar_Syntax_Syntax.signature)
in (

let uu____23845 = (erase_tscheme ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____23846 = (erase_tscheme ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____23847 = (erase_tscheme ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____23848 = (erase_tscheme ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____23849 = (erase_tscheme ed.FStar_Syntax_Syntax.stronger)
in (

let uu____23850 = (erase_tscheme ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____23851 = (erase_tscheme ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____23852 = (erase_tscheme ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____23853 = (erase_tscheme ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____23854 = (erase_tscheme ed.FStar_Syntax_Syntax.trivial)
in (

let uu____23855 = (erase_term ed.FStar_Syntax_Syntax.repr)
in (

let uu____23856 = (erase_tscheme ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____23857 = (erase_tscheme ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____23858 = (FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = uu___151_23842.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___151_23842.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = uu____23843; FStar_Syntax_Syntax.signature = uu____23844; FStar_Syntax_Syntax.ret_wp = uu____23845; FStar_Syntax_Syntax.bind_wp = uu____23846; FStar_Syntax_Syntax.if_then_else = uu____23847; FStar_Syntax_Syntax.ite_wp = uu____23848; FStar_Syntax_Syntax.stronger = uu____23849; FStar_Syntax_Syntax.close_wp = uu____23850; FStar_Syntax_Syntax.assert_p = uu____23851; FStar_Syntax_Syntax.assume_p = uu____23852; FStar_Syntax_Syntax.null_wp = uu____23853; FStar_Syntax_Syntax.trivial = uu____23854; FStar_Syntax_Syntax.repr = uu____23855; FStar_Syntax_Syntax.return_repr = uu____23856; FStar_Syntax_Syntax.bind_repr = uu____23857; FStar_Syntax_Syntax.actions = uu____23858; FStar_Syntax_Syntax.eff_attrs = uu___151_23842.FStar_Syntax_Syntax.eff_attrs}))))))))))))))))))))
end))))
in (

let push_sigelt1 = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let se' = (

let uu___152_23874 = se
in (

let uu____23875 = (

let uu____23876 = (erase_univs_ed ed)
in FStar_Syntax_Syntax.Sig_new_effect (uu____23876))
in {FStar_Syntax_Syntax.sigel = uu____23875; FStar_Syntax_Syntax.sigrng = uu___152_23874.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___152_23874.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___152_23874.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___152_23874.FStar_Syntax_Syntax.sigattrs}))
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se')
in (push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng)))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed) -> begin
(

let se' = (

let uu___153_23880 = se
in (

let uu____23881 = (

let uu____23882 = (erase_univs_ed ed)
in FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____23882))
in {FStar_Syntax_Syntax.sigel = uu____23881; FStar_Syntax_Syntax.sigrng = uu___153_23880.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___153_23880.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___153_23880.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___153_23880.FStar_Syntax_Syntax.sigattrs}))
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se')
in (push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng)))
end
| uu____23884 -> begin
(FStar_Syntax_DsEnv.push_sigelt env se)
end))
in (

let uu____23885 = (FStar_Syntax_DsEnv.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name mii)
in (match (uu____23885) with
| (en1, pop_when_done) -> begin
(

let en2 = (

let uu____23897 = (FStar_Syntax_DsEnv.set_current_module en1 m.FStar_Syntax_Syntax.name)
in (FStar_List.fold_left push_sigelt1 uu____23897 m.FStar_Syntax_Syntax.exports))
in (

let env = (FStar_Syntax_DsEnv.finish en2 m)
in (

let uu____23899 = (match (pop_when_done) with
| true -> begin
(FStar_Syntax_DsEnv.export_interface m.FStar_Syntax_Syntax.name env)
end
| uu____23900 -> begin
env
end)
in ((()), (uu____23899)))))
end)))))




