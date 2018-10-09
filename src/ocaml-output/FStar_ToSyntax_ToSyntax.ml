
open Prims
open FStar_Pervasives

type annotated_pat =
(FStar_Syntax_Syntax.pat * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.typ) Prims.list)


let desugar_disjunctive_pattern : (FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) Prims.list) Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list = (fun annotated_pats when_opt branch1 -> (FStar_All.pipe_right annotated_pats (FStar_List.map (fun uu____104 -> (match (uu____104) with
| (pat, annots) -> begin
(

let branch2 = (FStar_List.fold_left (fun br uu____159 -> (match (uu____159) with
| (bv, ty) -> begin
(

let lb = (

let uu____177 = (FStar_Syntax_Syntax.bv_to_name bv)
in (FStar_Syntax_Util.mk_letbinding (FStar_Util.Inl (bv)) [] ty FStar_Parser_Const.effect_Tot_lid uu____177 [] br.FStar_Syntax_Syntax.pos))
in (

let branch2 = (

let uu____183 = (

let uu____184 = (FStar_Syntax_Syntax.mk_binder bv)
in (uu____184)::[])
in (FStar_Syntax_Subst.close uu____183 branch1))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_let (((((false), ((lb)::[]))), (branch2)))) FStar_Pervasives_Native.None br.FStar_Syntax_Syntax.pos)))
end)) branch1 annots)
in (FStar_Syntax_Util.branch ((pat), (when_opt), (branch2))))
end)))))


let trans_qual : FStar_Range.range  ->  FStar_Ident.lident FStar_Pervasives_Native.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun r maybe_effect_id uu___247_237 -> (match (uu___247_237) with
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


let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun uu___248_246 -> (match (uu___248_246) with
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
| FStar_Parser_AST.LightOff -> begin
FStar_Syntax_Syntax.LightOff
end))


let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option = (fun uu___249_260 -> (match (uu___249_260) with
| FStar_Parser_AST.Hash -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)
end
| uu____263 -> begin
FStar_Pervasives_Native.None
end))


let arg_withimp_e : 'Auu____270 . FStar_Parser_AST.imp  ->  'Auu____270  ->  ('Auu____270 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) = (fun imp t -> ((t), ((as_imp imp))))


let arg_withimp_t : 'Auu____295 . FStar_Parser_AST.imp  ->  'Auu____295  ->  ('Auu____295 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
((t), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end
| uu____314 -> begin
((t), (FStar_Pervasives_Native.None))
end))


let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (uu____331) -> begin
true
end
| uu____336 -> begin
false
end)))))


let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t1) -> begin
(unparen t1)
end
| uu____343 -> begin
t
end))


let tm_type_z : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (

let uu____349 = (

let uu____350 = (FStar_Ident.lid_of_path (("Type0")::[]) r)
in FStar_Parser_AST.Name (uu____350))
in (FStar_Parser_AST.mk_term uu____349 r FStar_Parser_AST.Kind)))


let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (

let uu____356 = (

let uu____357 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (uu____357))
in (FStar_Parser_AST.mk_term uu____356 r FStar_Parser_AST.Kind)))


let rec is_comp_type : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> (

let uu____368 = (

let uu____369 = (unparen t)
in uu____369.FStar_Parser_AST.tm)
in (match (uu____368) with
| FStar_Parser_AST.Name (l) -> begin
(

let uu____371 = (FStar_Syntax_DsEnv.try_lookup_effect_name env l)
in (FStar_All.pipe_right uu____371 FStar_Option.isSome))
end
| FStar_Parser_AST.Construct (l, uu____377) -> begin
(

let uu____390 = (FStar_Syntax_DsEnv.try_lookup_effect_name env l)
in (FStar_All.pipe_right uu____390 FStar_Option.isSome))
end
| FStar_Parser_AST.App (head1, uu____396, uu____397) -> begin
(is_comp_type env head1)
end
| FStar_Parser_AST.Paren (t1) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.Ascribed (t1, uu____400, uu____401) -> begin
(is_comp_type env t1)
end
| FStar_Parser_AST.LetOpen (uu____406, t1) -> begin
(is_comp_type env t1)
end
| uu____408 -> begin
false
end)))


let unit_ty : FStar_Parser_AST.term = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.unit_lid)) FStar_Range.dummyRange FStar_Parser_AST.Type_level)


let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n1 s r -> (

let uu____424 = (

let uu____427 = (

let uu____428 = (

let uu____433 = (FStar_Parser_AST.compile_op n1 s r)
in ((uu____433), (r)))
in (FStar_Ident.mk_ident uu____428))
in (uu____427)::[])
in (FStar_All.pipe_right uu____424 FStar_Ident.lid_of_ids)))


let op_as_term : 'Auu____446 . FStar_Syntax_DsEnv.env  ->  Prims.int  ->  'Auu____446  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env arity rng op -> (

let r = (fun l dd -> (

let uu____482 = (

let uu____483 = (

let uu____484 = (FStar_Ident.set_lid_range l op.FStar_Ident.idRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____484 dd FStar_Pervasives_Native.None))
in (FStar_All.pipe_right uu____483 FStar_Syntax_Syntax.fv_to_tm))
in FStar_Pervasives_Native.Some (uu____482)))
in (

let fallback = (fun uu____492 -> (

let uu____493 = (FStar_Ident.text_of_id op)
in (match (uu____493) with
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

let uu____496 = (FStar_Options.ml_ish ())
in (match (uu____496) with
| true -> begin
(r FStar_Parser_Const.list_append_lid (FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "2"))))
end
| uu____499 -> begin
(r FStar_Parser_Const.list_tot_append_lid (FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "2"))))
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
| uu____500 -> begin
FStar_Pervasives_Native.None
end)))
in (

let uu____501 = (

let uu____504 = (compile_op_lid arity op.FStar_Ident.idText op.FStar_Ident.idRange)
in (FStar_Syntax_DsEnv.try_lookup_lid env uu____504))
in (match (uu____501) with
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____508 -> begin
(fallback ())
end)))))


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (

let uu____522 = (FStar_Util.remove_dups (fun x y -> (Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) uu____522)))


let rec free_type_vars_b : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Syntax_DsEnv.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (uu____569) -> begin
((env), ([]))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____573 = (FStar_Syntax_DsEnv.push_bv env x)
in (match (uu____573) with
| (env1, uu____585) -> begin
((env1), ((x)::[]))
end))
end
| FStar_Parser_AST.Annotated (uu____588, term) -> begin
(

let uu____590 = (free_type_vars env term)
in ((env), (uu____590)))
end
| FStar_Parser_AST.TAnnotated (id1, uu____596) -> begin
(

let uu____597 = (FStar_Syntax_DsEnv.push_bv env id1)
in (match (uu____597) with
| (env1, uu____609) -> begin
((env1), ([]))
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____613 = (free_type_vars env t)
in ((env), (uu____613)))
end))
and free_type_vars : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (

let uu____620 = (

let uu____621 = (unparen t)
in uu____621.FStar_Parser_AST.tm)
in (match (uu____620) with
| FStar_Parser_AST.Labeled (uu____624) -> begin
(failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____634 = (FStar_Syntax_DsEnv.try_lookup_id env a)
in (match (uu____634) with
| FStar_Pervasives_Native.None -> begin
(a)::[]
end
| uu____639 -> begin
[]
end))
end
| FStar_Parser_AST.Wild -> begin
[]
end
| FStar_Parser_AST.Const (uu____642) -> begin
[]
end
| FStar_Parser_AST.Uvar (uu____643) -> begin
[]
end
| FStar_Parser_AST.Var (uu____644) -> begin
[]
end
| FStar_Parser_AST.Projector (uu____645) -> begin
[]
end
| FStar_Parser_AST.Discrim (uu____650) -> begin
[]
end
| FStar_Parser_AST.Name (uu____651) -> begin
[]
end
| FStar_Parser_AST.Requires (t1, uu____653) -> begin
(free_type_vars env t1)
end
| FStar_Parser_AST.Ensures (t1, uu____659) -> begin
(free_type_vars env t1)
end
| FStar_Parser_AST.NamedTyp (uu____664, t1) -> begin
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
| FStar_Parser_AST.Construct (uu____682, ts) -> begin
(FStar_List.collect (fun uu____703 -> (match (uu____703) with
| (t1, uu____711) -> begin
(free_type_vars env t1)
end)) ts)
end
| FStar_Parser_AST.Op (uu____712, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, uu____720) -> begin
(

let uu____721 = (free_type_vars env t1)
in (

let uu____724 = (free_type_vars env t2)
in (FStar_List.append uu____721 uu____724)))
end
| FStar_Parser_AST.Refine (b, t1) -> begin
(

let uu____729 = (free_type_vars_b env b)
in (match (uu____729) with
| (env1, f) -> begin
(

let uu____744 = (free_type_vars env1 t1)
in (FStar_List.append f uu____744))
end))
end
| FStar_Parser_AST.Sum (binders, body) -> begin
(

let uu____761 = (FStar_List.fold_left (fun uu____785 bt -> (match (uu____785) with
| (env1, free) -> begin
(

let uu____809 = (match (bt) with
| FStar_Util.Inl (binder) -> begin
(free_type_vars_b env1 binder)
end
| FStar_Util.Inr (t1) -> begin
(

let uu____824 = (free_type_vars env1 body)
in ((env1), (uu____824)))
end)
in (match (uu____809) with
| (env2, f) -> begin
((env2), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (uu____761) with
| (env1, free) -> begin
(

let uu____853 = (free_type_vars env1 body)
in (FStar_List.append free uu____853))
end))
end
| FStar_Parser_AST.Product (binders, body) -> begin
(

let uu____862 = (FStar_List.fold_left (fun uu____882 binder -> (match (uu____882) with
| (env1, free) -> begin
(

let uu____902 = (free_type_vars_b env1 binder)
in (match (uu____902) with
| (env2, f) -> begin
((env2), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (uu____862) with
| (env1, free) -> begin
(

let uu____933 = (free_type_vars env1 body)
in (FStar_List.append free uu____933))
end))
end
| FStar_Parser_AST.Project (t1, uu____937) -> begin
(free_type_vars env t1)
end
| FStar_Parser_AST.Attributes (cattributes) -> begin
(FStar_List.collect (free_type_vars env) cattributes)
end
| FStar_Parser_AST.Abs (uu____941) -> begin
[]
end
| FStar_Parser_AST.Let (uu____948) -> begin
[]
end
| FStar_Parser_AST.LetOpen (uu____969) -> begin
[]
end
| FStar_Parser_AST.If (uu____974) -> begin
[]
end
| FStar_Parser_AST.QForall (uu____981) -> begin
[]
end
| FStar_Parser_AST.QExists (uu____994) -> begin
[]
end
| FStar_Parser_AST.Record (uu____1007) -> begin
[]
end
| FStar_Parser_AST.Match (uu____1020) -> begin
[]
end
| FStar_Parser_AST.TryWith (uu____1035) -> begin
[]
end
| FStar_Parser_AST.Bind (uu____1050) -> begin
[]
end
| FStar_Parser_AST.Quote (uu____1057) -> begin
[]
end
| FStar_Parser_AST.VQuote (uu____1062) -> begin
[]
end
| FStar_Parser_AST.Antiquote (uu____1063) -> begin
[]
end
| FStar_Parser_AST.Seq (uu____1064) -> begin
[]
end)))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (

let rec aux = (fun args t1 -> (

let uu____1117 = (

let uu____1118 = (unparen t1)
in uu____1118.FStar_Parser_AST.tm)
in (match (uu____1117) with
| FStar_Parser_AST.App (t2, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t2)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t1.FStar_Parser_AST.range; FStar_Parser_AST.level = t1.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| uu____1160 -> begin
((t1), (args))
end)))
in (aux [] t)))


let close : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (

let uu____1184 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv uu____1184))
in (match ((Prims.op_Equality (FStar_List.length ftv) (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____1191 -> begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (

let uu____1202 = (

let uu____1203 = (

let uu____1208 = (tm_type x.FStar_Ident.idRange)
in ((x), (uu____1208)))
in FStar_Parser_AST.TAnnotated (uu____1203))
in (FStar_Parser_AST.mk_binder uu____1202 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end)))


let close_fun : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (

let uu____1225 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv uu____1225))
in (match ((Prims.op_Equality (FStar_List.length ftv) (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____1232 -> begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (

let uu____1243 = (

let uu____1244 = (

let uu____1249 = (tm_type x.FStar_Ident.idRange)
in ((x), (uu____1249)))
in FStar_Parser_AST.TAnnotated (uu____1244))
in (FStar_Parser_AST.mk_binder uu____1243 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))))))
in (

let t1 = (

let uu____1251 = (

let uu____1252 = (unparen t)
in uu____1252.FStar_Parser_AST.tm)
in (match (uu____1251) with
| FStar_Parser_AST.Product (uu____1253) -> begin
t
end
| uu____1260 -> begin
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
| uu____1296 -> begin
((bs), (t))
end))


let rec is_var_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatWild (uu____1304) -> begin
true
end
| FStar_Parser_AST.PatTvar (uu____1307, uu____1308) -> begin
true
end
| FStar_Parser_AST.PatVar (uu____1313, uu____1314) -> begin
true
end
| FStar_Parser_AST.PatAscribed (p1, uu____1320) -> begin
(is_var_pattern p1)
end
| uu____1333 -> begin
false
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p1, uu____1340) -> begin
(is_app_pattern p1)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____1353); FStar_Parser_AST.prange = uu____1354}, uu____1355) -> begin
true
end
| uu____1366 -> begin
false
end))


let replace_unit_pattern : FStar_Parser_AST.pattern  ->  FStar_Parser_AST.pattern = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatConst (FStar_Const.Const_unit) -> begin
(FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatAscribed ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatWild (FStar_Pervasives_Native.None)) p.FStar_Parser_AST.prange)), (((unit_ty), (FStar_Pervasives_Native.None)))))) p.FStar_Parser_AST.prange)
end
| uu____1380 -> begin
p
end))


let rec destruct_app_pattern : FStar_Syntax_DsEnv.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * (FStar_Parser_AST.term * FStar_Parser_AST.term FStar_Pervasives_Native.option) FStar_Pervasives_Native.option) = (fun env is_top_level1 p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p1, t) -> begin
(

let uu____1450 = (destruct_app_pattern env is_top_level1 p1)
in (match (uu____1450) with
| (name, args, uu____1493) -> begin
((name), (args), (FStar_Pervasives_Native.Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id1, uu____1543); FStar_Parser_AST.prange = uu____1544}, args) when is_top_level1 -> begin
(

let uu____1554 = (

let uu____1559 = (FStar_Syntax_DsEnv.qualify env id1)
in FStar_Util.Inr (uu____1559))
in ((uu____1554), (args), (FStar_Pervasives_Native.None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id1, uu____1581); FStar_Parser_AST.prange = uu____1582}, args) -> begin
((FStar_Util.Inl (id1)), (args), (FStar_Pervasives_Native.None))
end
| uu____1612 -> begin
(failwith "Not an app pattern")
end))


let rec gather_pattern_bound_vars_maybe_top : Prims.bool  ->  FStar_Ident.ident FStar_Util.set  ->  FStar_Parser_AST.pattern  ->  FStar_Ident.ident FStar_Util.set = (fun fail_on_patconst acc p -> (

let gather_pattern_bound_vars_from_list = (FStar_List.fold_left (gather_pattern_bound_vars_maybe_top fail_on_patconst) acc)
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatWild (uu____1667) -> begin
acc
end
| FStar_Parser_AST.PatName (uu____1670) -> begin
acc
end
| FStar_Parser_AST.PatOp (uu____1671) -> begin
acc
end
| FStar_Parser_AST.PatConst (uu____1672) -> begin
(match (fail_on_patconst) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Error_CannotRedefineConst), ("Constants cannot be redefined")) p.FStar_Parser_AST.prange)
end
| uu____1677 -> begin
acc
end)
end
| FStar_Parser_AST.PatApp (phead, pats) -> begin
(gather_pattern_bound_vars_from_list ((phead)::pats))
end
| FStar_Parser_AST.PatTvar (x, uu____1685) -> begin
(FStar_Util.set_add x acc)
end
| FStar_Parser_AST.PatVar (x, uu____1691) -> begin
(FStar_Util.set_add x acc)
end
| FStar_Parser_AST.PatList (pats) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatTuple (pats, uu____1700) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatOr (pats) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatRecord (guarded_pats) -> begin
(

let uu____1715 = (FStar_List.map FStar_Pervasives_Native.snd guarded_pats)
in (gather_pattern_bound_vars_from_list uu____1715))
end
| FStar_Parser_AST.PatAscribed (pat, uu____1723) -> begin
(gather_pattern_bound_vars_maybe_top fail_on_patconst acc pat)
end)))


let gather_pattern_bound_vars : Prims.bool  ->  FStar_Parser_AST.pattern  ->  FStar_Ident.ident FStar_Util.set = (fun fail_on_patconst p -> (

let acc = (FStar_Util.new_set (fun id1 id2 -> (match ((Prims.op_Equality id1.FStar_Ident.idText id2.FStar_Ident.idText)) with
| true -> begin
(Prims.parse_int "0")
end
| uu____1757 -> begin
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
| uu____1792 -> begin
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
| uu____1828 -> begin
false
end))


let __proj__LetBinder__item___0 : bnd  ->  (FStar_Ident.lident * (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)) = (fun projectee -> (match (projectee) with
| LetBinder (_0) -> begin
_0
end))


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun uu___250_1874 -> (match (uu___250_1874) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| uu____1881 -> begin
(failwith "Impossible")
end))


type env_t =
FStar_Syntax_DsEnv.env


type lenv_t =
FStar_Syntax_Syntax.bv Prims.list


let mk_lb : (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax Prims.list * (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Range.range)  ->  FStar_Syntax_Syntax.letbinding = (fun uu____1914 -> (match (uu____1914) with
| (attrs, n1, t, e, pos) -> begin
{FStar_Syntax_Syntax.lbname = n1; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e; FStar_Syntax_Syntax.lbattrs = attrs; FStar_Syntax_Syntax.lbpos = pos}
end))


let no_annot_abs : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun bs t -> (FStar_Syntax_Util.abs bs t FStar_Pervasives_Native.None))


let mk_ref_read : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun tm -> (

let tm' = (

let uu____1994 = (

let uu____2011 = (

let uu____2014 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____2014))
in (

let uu____2015 = (

let uu____2026 = (

let uu____2035 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (uu____2035)))
in (uu____2026)::[])
in ((uu____2011), (uu____2015))))
in FStar_Syntax_Syntax.Tm_app (uu____1994))
in (FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_alloc : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun tm -> (

let tm' = (

let uu____2082 = (

let uu____2099 = (

let uu____2102 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____2102))
in (

let uu____2103 = (

let uu____2114 = (

let uu____2123 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (uu____2123)))
in (uu____2114)::[])
in ((uu____2099), (uu____2103))))
in FStar_Syntax_Syntax.Tm_app (uu____2082))
in (FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_assign : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t1 t2 pos -> (

let tm = (

let uu____2184 = (

let uu____2201 = (

let uu____2204 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____2204))
in (

let uu____2205 = (

let uu____2216 = (

let uu____2225 = (FStar_Syntax_Syntax.as_implicit false)
in ((t1), (uu____2225)))
in (

let uu____2232 = (

let uu____2243 = (

let uu____2252 = (FStar_Syntax_Syntax.as_implicit false)
in ((t2), (uu____2252)))
in (uu____2243)::[])
in (uu____2216)::uu____2232))
in ((uu____2201), (uu____2205))))
in FStar_Syntax_Syntax.Tm_app (uu____2184))
in (FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos)))


let generalize_annotated_univs : FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt = (fun s -> (

let bs_univnames = (fun bs -> (

let uu____2310 = (

let uu____2325 = (FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name)
in (FStar_List.fold_left (fun uvs uu____2344 -> (match (uu____2344) with
| ({FStar_Syntax_Syntax.ppname = uu____2355; FStar_Syntax_Syntax.index = uu____2356; FStar_Syntax_Syntax.sort = t}, uu____2358) -> begin
(

let uu____2365 = (FStar_Syntax_Free.univnames t)
in (FStar_Util.set_union uvs uu____2365))
end)) uu____2325))
in (FStar_All.pipe_right bs uu____2310)))
in (

let empty_set = (FStar_Util.new_set FStar_Syntax_Syntax.order_univ_name)
in (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____2381) -> begin
(failwith "Impossible: collect_annotated_universes: bare data/type constructor")
end
| FStar_Syntax_Syntax.Sig_datacon (uu____2398) -> begin
(failwith "Impossible: collect_annotated_universes: bare data/type constructor")
end
| FStar_Syntax_Syntax.Sig_bundle (sigs, lids) -> begin
(

let uvs = (

let uu____2424 = (FStar_All.pipe_right sigs (FStar_List.fold_left (fun uvs se -> (

let se_univs = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____2445, uu____2446, bs, t, uu____2449, uu____2450) -> begin
(

let uu____2459 = (bs_univnames bs)
in (

let uu____2462 = (FStar_Syntax_Free.univnames t)
in (FStar_Util.set_union uu____2459 uu____2462)))
end
| FStar_Syntax_Syntax.Sig_datacon (uu____2465, uu____2466, t, uu____2468, uu____2469, uu____2470) -> begin
(FStar_Syntax_Free.univnames t)
end
| uu____2475 -> begin
(failwith "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt")
end)
in (FStar_Util.set_union uvs se_univs))) empty_set))
in (FStar_All.pipe_right uu____2424 FStar_Util.set_elements))
in (

let usubst = (FStar_Syntax_Subst.univ_var_closing uvs)
in (

let uu___278_2483 = s
in (

let uu____2484 = (

let uu____2485 = (

let uu____2494 = (FStar_All.pipe_right sigs (FStar_List.map (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____2512, bs, t, lids1, lids2) -> begin
(

let uu___279_2525 = se
in (

let uu____2526 = (

let uu____2527 = (

let uu____2544 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let uu____2545 = (

let uu____2546 = (FStar_Syntax_Subst.shift_subst (FStar_List.length bs) usubst)
in (FStar_Syntax_Subst.subst uu____2546 t))
in ((lid), (uvs), (uu____2544), (uu____2545), (lids1), (lids2))))
in FStar_Syntax_Syntax.Sig_inductive_typ (uu____2527))
in {FStar_Syntax_Syntax.sigel = uu____2526; FStar_Syntax_Syntax.sigrng = uu___279_2525.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___279_2525.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___279_2525.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___279_2525.FStar_Syntax_Syntax.sigattrs}))
end
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____2560, t, tlid, n1, lids1) -> begin
(

let uu___280_2569 = se
in (

let uu____2570 = (

let uu____2571 = (

let uu____2586 = (FStar_Syntax_Subst.subst usubst t)
in ((lid), (uvs), (uu____2586), (tlid), (n1), (lids1)))
in FStar_Syntax_Syntax.Sig_datacon (uu____2571))
in {FStar_Syntax_Syntax.sigel = uu____2570; FStar_Syntax_Syntax.sigrng = uu___280_2569.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___280_2569.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___280_2569.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___280_2569.FStar_Syntax_Syntax.sigattrs}))
end
| uu____2589 -> begin
(failwith "Impossible: collect_annotated_universes: Sig_bundle should not have a non data/type sigelt")
end))))
in ((uu____2494), (lids)))
in FStar_Syntax_Syntax.Sig_bundle (uu____2485))
in {FStar_Syntax_Syntax.sigel = uu____2484; FStar_Syntax_Syntax.sigrng = uu___278_2483.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___278_2483.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___278_2483.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___278_2483.FStar_Syntax_Syntax.sigattrs}))))
end
| FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____2595, t) -> begin
(

let uvs = (

let uu____2598 = (FStar_Syntax_Free.univnames t)
in (FStar_All.pipe_right uu____2598 FStar_Util.set_elements))
in (

let uu___281_2603 = s
in (

let uu____2604 = (

let uu____2605 = (

let uu____2612 = (FStar_Syntax_Subst.close_univ_vars uvs t)
in ((lid), (uvs), (uu____2612)))
in FStar_Syntax_Syntax.Sig_declare_typ (uu____2605))
in {FStar_Syntax_Syntax.sigel = uu____2604; FStar_Syntax_Syntax.sigrng = uu___281_2603.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___281_2603.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___281_2603.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___281_2603.FStar_Syntax_Syntax.sigattrs})))
end
| FStar_Syntax_Syntax.Sig_let ((b, lbs), lids) -> begin
(

let lb_univnames = (fun lb -> (

let uu____2634 = (FStar_Syntax_Free.univnames lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____2637 = (match (lb.FStar_Syntax_Syntax.lbdef.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (bs, e, uu____2644) -> begin
(

let uvs1 = (bs_univnames bs)
in (

let uvs2 = (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_ascribed (uu____2677, (FStar_Util.Inl (t), uu____2679), uu____2680) -> begin
(FStar_Syntax_Free.univnames t)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____2727, (FStar_Util.Inr (c), uu____2729), uu____2730) -> begin
(FStar_Syntax_Free.univnames_comp c)
end
| uu____2777 -> begin
empty_set
end)
in (FStar_Util.set_union uvs1 uvs2)))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____2778, (FStar_Util.Inl (t), uu____2780), uu____2781) -> begin
(FStar_Syntax_Free.univnames t)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____2828, (FStar_Util.Inr (c), uu____2830), uu____2831) -> begin
(FStar_Syntax_Free.univnames_comp c)
end
| uu____2878 -> begin
empty_set
end)
in (FStar_Util.set_union uu____2634 uu____2637))))
in (

let all_lb_univs = (

let uu____2882 = (FStar_All.pipe_right lbs (FStar_List.fold_left (fun uvs lb -> (

let uu____2898 = (lb_univnames lb)
in (FStar_Util.set_union uvs uu____2898))) empty_set))
in (FStar_All.pipe_right uu____2882 FStar_Util.set_elements))
in (

let usubst = (FStar_Syntax_Subst.univ_var_closing all_lb_univs)
in (

let uu___282_2908 = s
in (

let uu____2909 = (

let uu____2910 = (

let uu____2917 = (

let uu____2918 = (FStar_All.pipe_right lbs (FStar_List.map (fun lb -> (

let uu___283_2930 = lb
in (

let uu____2931 = (FStar_Syntax_Subst.subst usubst lb.FStar_Syntax_Syntax.lbtyp)
in (

let uu____2934 = (FStar_Syntax_Subst.subst usubst lb.FStar_Syntax_Syntax.lbdef)
in {FStar_Syntax_Syntax.lbname = uu___283_2930.FStar_Syntax_Syntax.lbname; FStar_Syntax_Syntax.lbunivs = all_lb_univs; FStar_Syntax_Syntax.lbtyp = uu____2931; FStar_Syntax_Syntax.lbeff = uu___283_2930.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu____2934; FStar_Syntax_Syntax.lbattrs = uu___283_2930.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___283_2930.FStar_Syntax_Syntax.lbpos}))))))
in ((b), (uu____2918)))
in ((uu____2917), (lids)))
in FStar_Syntax_Syntax.Sig_let (uu____2910))
in {FStar_Syntax_Syntax.sigel = uu____2909; FStar_Syntax_Syntax.sigrng = uu___282_2908.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___282_2908.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___282_2908.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___282_2908.FStar_Syntax_Syntax.sigattrs})))))
end
| FStar_Syntax_Syntax.Sig_assume (lid, uu____2942, fml) -> begin
(

let uvs = (

let uu____2945 = (FStar_Syntax_Free.univnames fml)
in (FStar_All.pipe_right uu____2945 FStar_Util.set_elements))
in (

let uu___284_2950 = s
in (

let uu____2951 = (

let uu____2952 = (

let uu____2959 = (FStar_Syntax_Subst.close_univ_vars uvs fml)
in ((lid), (uvs), (uu____2959)))
in FStar_Syntax_Syntax.Sig_assume (uu____2952))
in {FStar_Syntax_Syntax.sigel = uu____2951; FStar_Syntax_Syntax.sigrng = uu___284_2950.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___284_2950.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___284_2950.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___284_2950.FStar_Syntax_Syntax.sigattrs})))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, uu____2961, bs, c, flags1) -> begin
(

let uvs = (

let uu____2970 = (

let uu____2973 = (bs_univnames bs)
in (

let uu____2976 = (FStar_Syntax_Free.univnames_comp c)
in (FStar_Util.set_union uu____2973 uu____2976)))
in (FStar_All.pipe_right uu____2970 FStar_Util.set_elements))
in (

let usubst = (FStar_Syntax_Subst.univ_var_closing uvs)
in (

let uu___285_2984 = s
in (

let uu____2985 = (

let uu____2986 = (

let uu____2999 = (FStar_Syntax_Subst.subst_binders usubst bs)
in (

let uu____3000 = (FStar_Syntax_Subst.subst_comp usubst c)
in ((lid), (uvs), (uu____2999), (uu____3000), (flags1))))
in FStar_Syntax_Syntax.Sig_effect_abbrev (uu____2986))
in {FStar_Syntax_Syntax.sigel = uu____2985; FStar_Syntax_Syntax.sigrng = uu___285_2984.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___285_2984.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___285_2984.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___285_2984.FStar_Syntax_Syntax.sigattrs}))))
end
| uu____3003 -> begin
s
end))))


let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun uu___251_3008 -> (match (uu___251_3008) with
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
| "null_wp" -> begin
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
| uu____3009 -> begin
false
end))


let rec sum_to_universe : FStar_Syntax_Syntax.universe  ->  Prims.int  ->  FStar_Syntax_Syntax.universe = (fun u n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
u
end
| uu____3020 -> begin
(

let uu____3021 = (sum_to_universe u (n1 - (Prims.parse_int "1")))
in FStar_Syntax_Syntax.U_succ (uu____3021))
end))


let int_to_universe : Prims.int  ->  FStar_Syntax_Syntax.universe = (fun n1 -> (sum_to_universe FStar_Syntax_Syntax.U_zero n1))


let rec desugar_maybe_non_constant_universe : FStar_Parser_AST.term  ->  (Prims.int, FStar_Syntax_Syntax.universe) FStar_Util.either = (fun t -> (

let uu____3040 = (

let uu____3041 = (unparen t)
in uu____3041.FStar_Parser_AST.tm)
in (match (uu____3040) with
| FStar_Parser_AST.Wild -> begin
(

let uu____3046 = (

let uu____3047 = (FStar_Syntax_Unionfind.univ_fresh ())
in FStar_Syntax_Syntax.U_unif (uu____3047))
in FStar_Util.Inr (uu____3046))
end
| FStar_Parser_AST.Uvar (u) -> begin
FStar_Util.Inr (FStar_Syntax_Syntax.U_name (u))
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (repr, uu____3058)) -> begin
(

let n1 = (FStar_Util.int_of_string repr)
in ((match ((n1 < (Prims.parse_int "0"))) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_NegativeUniverseConstFatal_NotSupported), ((Prims.strcat "Negative universe constant  are not supported : " repr))) t.FStar_Parser_AST.range)
end
| uu____3073 -> begin
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

let uu____3123 = (sum_to_universe u n1)
in FStar_Util.Inr (uu____3123))
end
| (FStar_Util.Inr (u), FStar_Util.Inl (n1)) -> begin
(

let uu____3134 = (sum_to_universe u n1)
in FStar_Util.Inr (uu____3134))
end
| (FStar_Util.Inr (u11), FStar_Util.Inr (u21)) -> begin
(

let uu____3145 = (

let uu____3150 = (

let uu____3151 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "This universe might contain a sum of two universe variables " uu____3151))
in ((FStar_Errors.Fatal_UniverseMightContainSumOfTwoUnivVars), (uu____3150)))
in (FStar_Errors.raise_error uu____3145 t.FStar_Parser_AST.range))
end)))
end
| FStar_Parser_AST.App (uu____3156) -> begin
(

let rec aux = (fun t1 univargs -> (

let uu____3190 = (

let uu____3191 = (unparen t1)
in uu____3191.FStar_Parser_AST.tm)
in (match (uu____3190) with
| FStar_Parser_AST.App (t2, targ, uu____3198) -> begin
(

let uarg = (desugar_maybe_non_constant_universe targ)
in (aux t2 ((uarg)::univargs)))
end
| FStar_Parser_AST.Var (max_lid1) -> begin
(match ((FStar_List.existsb (fun uu___252_3221 -> (match (uu___252_3221) with
| FStar_Util.Inr (uu____3226) -> begin
true
end
| uu____3227 -> begin
false
end)) univargs)) with
| true -> begin
(

let uu____3232 = (

let uu____3233 = (FStar_List.map (fun uu___253_3242 -> (match (uu___253_3242) with
| FStar_Util.Inl (n1) -> begin
(int_to_universe n1)
end
| FStar_Util.Inr (u) -> begin
u
end)) univargs)
in FStar_Syntax_Syntax.U_max (uu____3233))
in FStar_Util.Inr (uu____3232))
end
| uu____3249 -> begin
(

let nargs = (FStar_List.map (fun uu___254_3259 -> (match (uu___254_3259) with
| FStar_Util.Inl (n1) -> begin
n1
end
| FStar_Util.Inr (uu____3265) -> begin
(failwith "impossible")
end)) univargs)
in (

let uu____3266 = (FStar_List.fold_left (fun m n1 -> (match ((m > n1)) with
| true -> begin
m
end
| uu____3271 -> begin
n1
end)) (Prims.parse_int "0") nargs)
in FStar_Util.Inl (uu____3266)))
end)
end
| uu____3272 -> begin
(

let uu____3273 = (

let uu____3278 = (

let uu____3279 = (

let uu____3280 = (FStar_Parser_AST.term_to_string t1)
in (Prims.strcat uu____3280 " in universe context"))
in (Prims.strcat "Unexpected term " uu____3279))
in ((FStar_Errors.Fatal_UnexpectedTermInUniverse), (uu____3278)))
in (FStar_Errors.raise_error uu____3273 t1.FStar_Parser_AST.range))
end)))
in (aux t []))
end
| uu____3289 -> begin
(

let uu____3290 = (

let uu____3295 = (

let uu____3296 = (

let uu____3297 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat uu____3297 " in universe context"))
in (Prims.strcat "Unexpected term " uu____3296))
in ((FStar_Errors.Fatal_UnexpectedTermInUniverse), (uu____3295)))
in (FStar_Errors.raise_error uu____3290 t.FStar_Parser_AST.range))
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
| ((bv, {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_quoted (e, {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = uu____3327}); FStar_Syntax_Syntax.pos = uu____3328; FStar_Syntax_Syntax.vars = uu____3329}))::uu____3330 -> begin
(

let uu____3361 = (

let uu____3366 = (

let uu____3367 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Unexpected antiquotation: `@(%s)" uu____3367))
in ((FStar_Errors.Fatal_UnexpectedAntiquotation), (uu____3366)))
in (FStar_Errors.raise_error uu____3361 e.FStar_Syntax_Syntax.pos))
end
| ((bv, e))::uu____3370 -> begin
(

let uu____3389 = (

let uu____3394 = (

let uu____3395 = (FStar_Syntax_Print.term_to_string e)
in (FStar_Util.format1 "Unexpected antiquotation: `#(%s)" uu____3395))
in ((FStar_Errors.Fatal_UnexpectedAntiquotation), (uu____3394)))
in (FStar_Errors.raise_error uu____3389 e.FStar_Syntax_Syntax.pos))
end))


let check_fields : 'Auu____3404 . FStar_Syntax_DsEnv.env  ->  (FStar_Ident.lident * 'Auu____3404) Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_DsEnv.record_or_dc = (fun env fields rg -> (

let uu____3432 = (FStar_List.hd fields)
in (match (uu____3432) with
| (f, uu____3442) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f);
(

let record = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_record_by_field_name env) f)
in (

let check_field = (fun uu____3454 -> (match (uu____3454) with
| (f', uu____3460) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f');
(

let uu____3462 = (FStar_Syntax_DsEnv.belongs_to_record env f' record)
in (match (uu____3462) with
| true -> begin
()
end
| uu____3463 -> begin
(

let msg = (FStar_Util.format3 "Field %s belongs to record type %s, whereas field %s does not" f.FStar_Ident.str record.FStar_Syntax_DsEnv.typename.FStar_Ident.str f'.FStar_Ident.str)
in (FStar_Errors.raise_error ((FStar_Errors.Fatal_FieldsNotBelongToSameRecordType), (msg)) rg))
end));
)
end))
in ((

let uu____3466 = (FStar_List.tl fields)
in (FStar_List.iter check_field uu____3466));
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
| FStar_Syntax_Syntax.Pat_dot_term (uu____3850) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_wild (uu____3857) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_constant (uu____3858) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (uu____3860, pats1) -> begin
(

let aux = (fun out uu____3898 -> (match (uu____3898) with
| (p2, uu____3910) -> begin
(

let intersection = (

let uu____3918 = (pat_vars p2)
in (FStar_Util.set_intersect uu____3918 out))
in (

let uu____3921 = (FStar_Util.set_is_empty intersection)
in (match (uu____3921) with
| true -> begin
(

let uu____3924 = (pat_vars p2)
in (FStar_Util.set_union out uu____3924))
end
| uu____3927 -> begin
(

let duplicate_bv = (

let uu____3929 = (FStar_Util.set_elements intersection)
in (FStar_List.hd uu____3929))
in (

let uu____3932 = (

let uu____3937 = (FStar_Util.format1 "Non-linear patterns are not permitted: `%s` appears more than once in this pattern." duplicate_bv.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in ((FStar_Errors.Fatal_NonLinearPatternNotPermitted), (uu____3937)))
in (FStar_Errors.raise_error uu____3932 r)))
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

let uu____3957 = (pat_vars p1)
in (FStar_All.pipe_right uu____3957 (fun a1 -> ())))
end
| (p1)::ps -> begin
(

let pvars = (pat_vars p1)
in (

let aux = (fun p2 -> (

let uu____3985 = (

let uu____3986 = (pat_vars p2)
in (FStar_Util.set_eq pvars uu____3986))
in (match (uu____3985) with
| true -> begin
()
end
| uu____3989 -> begin
(

let nonlinear_vars = (

let uu____3993 = (pat_vars p2)
in (FStar_Util.set_symmetric_difference pvars uu____3993))
in (

let first_nonlinear_var = (

let uu____3997 = (FStar_Util.set_elements nonlinear_vars)
in (FStar_List.hd uu____3997))
in (

let uu____4000 = (

let uu____4005 = (FStar_Util.format1 "Patterns in this match are incoherent, variable %s is bound in some but not all patterns." first_nonlinear_var.FStar_Syntax_Syntax.ppname.FStar_Ident.idText)
in ((FStar_Errors.Fatal_IncoherentPatterns), (uu____4005)))
in (FStar_Errors.raise_error uu____4000 r))))
end)))
in (FStar_List.iter aux ps)))
end)))
in (

let resolvex = (fun l e x -> (

let uu____4030 = (FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (Prims.op_Equality y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText x.FStar_Ident.idText))))
in (match (uu____4030) with
| FStar_Pervasives_Native.Some (y) -> begin
((l), (e), (y))
end
| uu____4046 -> begin
(

let uu____4049 = (FStar_Syntax_DsEnv.push_bv e x)
in (match (uu____4049) with
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
| FStar_Parser_AST.PatOr (uu____4194) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.PatOp (op) -> begin
(

let uu____4216 = (

let uu____4217 = (

let uu____4218 = (

let uu____4225 = (

let uu____4226 = (

let uu____4231 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") op.FStar_Ident.idText op.FStar_Ident.idRange)
in ((uu____4231), (op.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____4226))
in ((uu____4225), (FStar_Pervasives_Native.None)))
in FStar_Parser_AST.PatVar (uu____4218))
in {FStar_Parser_AST.pat = uu____4217; FStar_Parser_AST.prange = p1.FStar_Parser_AST.prange})
in (aux loc env1 uu____4216))
end
| FStar_Parser_AST.PatAscribed (p2, (t, tacopt)) -> begin
((match (tacopt) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (uu____4248) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly), ("Type ascriptions within patterns cannot be associated with a tactic")) orig.FStar_Parser_AST.prange)
end);
(

let uu____4249 = (aux loc env1 p2)
in (match (uu____4249) with
| (loc1, env', binder, p3, annots, imp) -> begin
(

let annot_pat_var = (fun p4 t1 -> (match (p4.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu___286_4334 = p4
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var ((

let uu___287_4339 = x
in {FStar_Syntax_Syntax.ppname = uu___287_4339.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___287_4339.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})); FStar_Syntax_Syntax.p = uu___286_4334.FStar_Syntax_Syntax.p})
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu___288_4341 = p4
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild ((

let uu___289_4346 = x
in {FStar_Syntax_Syntax.ppname = uu___289_4346.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___289_4346.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})); FStar_Syntax_Syntax.p = uu___288_4341.FStar_Syntax_Syntax.p})
end
| uu____4347 when top -> begin
p4
end
| uu____4348 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_TypeWithinPatternsAllowedOnVariablesOnly), ("Type ascriptions within patterns are only allowed on variables")) orig.FStar_Parser_AST.prange)
end))
in (

let uu____4351 = (match (binder) with
| LetBinder (uu____4372) -> begin
(failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t1 = (

let uu____4396 = (close_fun env1 t)
in (desugar_term env1 uu____4396))
in (

let x1 = (

let uu___290_4398 = x
in {FStar_Syntax_Syntax.ppname = uu___290_4398.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___290_4398.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (((((x1), (t1)))::[]), (LocalBinder (((x1), (aq)))))))
end)
in (match (uu____4351) with
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

let uu____4463 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env1), (LocalBinder (((x), (aq1)))), (uu____4463), ([]), (imp))))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____4476 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____4476), ([]), (false))))
end
| FStar_Parser_AST.PatTvar (x, aq) -> begin
(

let imp = (Prims.op_Equality aq (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))
in (

let aq1 = (trans_aqual env1 aq)
in (

let uu____4497 = (resolvex loc env1 x)
in (match (uu____4497) with
| (loc1, env2, xbv) -> begin
(

let uu____4525 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc1), (env2), (LocalBinder (((xbv), (aq1)))), (uu____4525), ([]), (imp)))
end))))
end
| FStar_Parser_AST.PatVar (x, aq) -> begin
(

let imp = (Prims.op_Equality aq (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))
in (

let aq1 = (trans_aqual env1 aq)
in (

let uu____4546 = (resolvex loc env1 x)
in (match (uu____4546) with
| (loc1, env2, xbv) -> begin
(

let uu____4574 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc1), (env2), (LocalBinder (((xbv), (aq1)))), (uu____4574), ([]), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l1 = (FStar_Syntax_DsEnv.fail_or env1 (FStar_Syntax_DsEnv.try_lookup_datacon env1) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____4588 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), ([])))))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____4588), ([]), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = uu____4614}, args) -> begin
(

let uu____4620 = (FStar_List.fold_right (fun arg uu____4679 -> (match (uu____4679) with
| (loc1, env2, annots, args1) -> begin
(

let uu____4756 = (aux loc1 env2 arg)
in (match (uu____4756) with
| (loc2, env3, uu____4801, arg1, ans, imp) -> begin
((loc2), (env3), ((FStar_List.append ans annots)), ((((arg1), (imp)))::args1))
end))
end)) args ((loc), (env1), ([]), ([])))
in (match (uu____4620) with
| (loc1, env2, annots, args1) -> begin
(

let l1 = (FStar_Syntax_DsEnv.fail_or env2 (FStar_Syntax_DsEnv.try_lookup_datacon env2) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____4923 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args1)))))
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____4923), (annots), (false)))))
end))
end
| FStar_Parser_AST.PatApp (uu____4938) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedPattern), ("Unexpected pattern")) p1.FStar_Parser_AST.prange)
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____4966 = (FStar_List.fold_right (fun pat uu____5017 -> (match (uu____5017) with
| (loc1, env2, annots, pats1) -> begin
(

let uu____5078 = (aux loc1 env2 pat)
in (match (uu____5078) with
| (loc2, env3, uu____5119, pat1, ans, uu____5122) -> begin
((loc2), (env3), ((FStar_List.append ans annots)), ((pat1)::pats1))
end))
end)) pats ((loc), (env1), ([]), ([])))
in (match (uu____4966) with
| (loc1, env2, annots, pats1) -> begin
(

let pat = (

let uu____5216 = (

let uu____5219 = (

let uu____5226 = (FStar_Range.end_range p1.FStar_Parser_AST.prange)
in (pos_r uu____5226))
in (

let uu____5227 = (

let uu____5228 = (

let uu____5241 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.nil_lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____5241), ([])))
in FStar_Syntax_Syntax.Pat_cons (uu____5228))
in (FStar_All.pipe_left uu____5219 uu____5227)))
in (FStar_List.fold_right (fun hd1 tl1 -> (

let r = (FStar_Range.union_ranges hd1.FStar_Syntax_Syntax.p tl1.FStar_Syntax_Syntax.p)
in (

let uu____5273 = (

let uu____5274 = (

let uu____5287 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.cons_lid FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____5287), ((((hd1), (false)))::(((tl1), (false)))::[])))
in FStar_Syntax_Syntax.Pat_cons (uu____5274))
in (FStar_All.pipe_left (pos_r r) uu____5273)))) pats1 uu____5216))
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (pat), (annots), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep1) -> begin
(

let uu____5333 = (FStar_List.fold_left (fun uu____5391 p2 -> (match (uu____5391) with
| (loc1, env2, annots, pats) -> begin
(

let uu____5469 = (aux loc1 env2 p2)
in (match (uu____5469) with
| (loc2, env3, uu____5514, pat, ans, uu____5517) -> begin
((loc2), (env3), ((FStar_List.append ans annots)), ((((pat), (false)))::pats))
end))
end)) ((loc), (env1), ([]), ([])) args)
in (match (uu____5333) with
| (loc1, env2, annots, args1) -> begin
(

let args2 = (FStar_List.rev args1)
in (

let l = (match (dep1) with
| true -> begin
(FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end
| uu____5656 -> begin
(FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end)
in (

let constr = (FStar_Syntax_DsEnv.fail_or env2 (FStar_Syntax_DsEnv.try_lookup_lid env2) l)
in (

let l1 = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____5666 -> begin
(failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____5668 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args2)))))
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____5668), (annots), (false))))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedPattern), ("Unexpected pattern")) p1.FStar_Parser_AST.prange)
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(

let record = (check_fields env1 fields p1.FStar_Parser_AST.prange)
in (

let fields1 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____5743 -> (match (uu____5743) with
| (f, p2) -> begin
((f.FStar_Ident.ident), (p2))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map (fun uu____5773 -> (match (uu____5773) with
| (f, uu____5779) -> begin
(

let uu____5780 = (FStar_All.pipe_right fields1 (FStar_List.tryFind (fun uu____5806 -> (match (uu____5806) with
| (g, uu____5812) -> begin
(Prims.op_Equality f.FStar_Ident.idText g.FStar_Ident.idText)
end))))
in (match (uu____5780) with
| FStar_Pervasives_Native.None -> begin
(FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatWild (FStar_Pervasives_Native.None)) p1.FStar_Parser_AST.prange)
end
| FStar_Pervasives_Native.Some (uu____5817, p2) -> begin
p2
end))
end))))
in (

let app = (

let uu____5824 = (

let uu____5825 = (

let uu____5832 = (

let uu____5833 = (

let uu____5834 = (FStar_Ident.lid_of_ids (FStar_List.append record.FStar_Syntax_DsEnv.typename.FStar_Ident.ns ((record.FStar_Syntax_DsEnv.constrname)::[])))
in FStar_Parser_AST.PatName (uu____5834))
in (FStar_Parser_AST.mk_pattern uu____5833 p1.FStar_Parser_AST.prange))
in ((uu____5832), (args)))
in FStar_Parser_AST.PatApp (uu____5825))
in (FStar_Parser_AST.mk_pattern uu____5824 p1.FStar_Parser_AST.prange))
in (

let uu____5837 = (aux loc env1 app)
in (match (uu____5837) with
| (env2, e, b, p2, annots, uu____5881) -> begin
(

let p3 = (match (p2.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args1) -> begin
(

let uu____5917 = (

let uu____5918 = (

let uu____5931 = (

let uu___291_5932 = fv
in (

let uu____5933 = (

let uu____5936 = (

let uu____5937 = (

let uu____5944 = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map FStar_Pervasives_Native.fst))
in ((record.FStar_Syntax_DsEnv.typename), (uu____5944)))
in FStar_Syntax_Syntax.Record_ctor (uu____5937))
in FStar_Pervasives_Native.Some (uu____5936))
in {FStar_Syntax_Syntax.fv_name = uu___291_5932.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = uu___291_5932.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu____5933}))
in ((uu____5931), (args1)))
in FStar_Syntax_Syntax.Pat_cons (uu____5918))
in (FStar_All.pipe_left pos uu____5917))
end
| uu____5969 -> begin
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

let uu____6051 = (aux' true loc env1 p2)
in (match (uu____6051) with
| (loc1, env2, var, p3, ans, uu____6093) -> begin
(

let uu____6106 = (FStar_List.fold_left (fun uu____6155 p4 -> (match (uu____6155) with
| (loc2, env3, ps1) -> begin
(

let uu____6220 = (aux' true loc2 env3 p4)
in (match (uu____6220) with
| (loc3, env4, uu____6259, p5, ans1, uu____6262) -> begin
((loc3), (env4), ((((p5), (ans1)))::ps1))
end))
end)) ((loc1), (env2), ([])) ps)
in (match (uu____6106) with
| (loc2, env3, ps1) -> begin
(

let pats = (((p3), (ans)))::(FStar_List.rev ps1)
in ((env3), (var), (pats)))
end))
end))
end
| uu____6421 -> begin
(

let uu____6422 = (aux' true loc env1 p1)
in (match (uu____6422) with
| (loc1, env2, vars, pat, ans, b) -> begin
((env2), (vars), ((((pat), (ans)))::[]))
end))
end)))
in (

let uu____6515 = (aux_maybe_or env p)
in (match (uu____6515) with
| (env1, b, pats) -> begin
((

let uu____6570 = (FStar_List.map FStar_Pervasives_Native.fst pats)
in (check_linear_pattern_variables uu____6570 p.FStar_Parser_AST.prange));
((env1), (b), (pats));
)
end)))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * annotated_pat Prims.list) = (fun top env p -> (

let mklet = (fun x ty tacopt -> (

let uu____6642 = (

let uu____6643 = (

let uu____6654 = (FStar_Syntax_DsEnv.qualify env x)
in ((uu____6654), (((ty), (tacopt)))))
in LetBinder (uu____6643))
in ((env), (uu____6642), ([]))))
in (

let op_to_ident = (fun x -> (

let uu____6671 = (

let uu____6676 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") x.FStar_Ident.idText x.FStar_Ident.idRange)
in ((uu____6676), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____6671)))
in (match (top) with
| true -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(

let uu____6694 = (op_to_ident x)
in (mklet uu____6694 FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None))
end
| FStar_Parser_AST.PatVar (x, uu____6696) -> begin
(mklet x FStar_Syntax_Syntax.tun FStar_Pervasives_Native.None)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatOp (x); FStar_Parser_AST.prange = uu____6702}, (t, tacopt)) -> begin
(

let tacopt1 = (FStar_Util.map_opt tacopt (desugar_term env))
in (

let uu____6718 = (op_to_ident x)
in (

let uu____6719 = (desugar_term env t)
in (mklet uu____6718 uu____6719 tacopt1))))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____6721); FStar_Parser_AST.prange = uu____6722}, (t, tacopt)) -> begin
(

let tacopt1 = (FStar_Util.map_opt tacopt (desugar_term env))
in (

let uu____6742 = (desugar_term env t)
in (mklet x uu____6742 tacopt1)))
end
| uu____6743 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedPattern), ("Unexpected pattern at the top-level")) p.FStar_Parser_AST.prange)
end)
end
| uu____6752 -> begin
(

let uu____6753 = (desugar_data_pat env p)
in (match (uu____6753) with
| (env1, binder, p1) -> begin
(

let p2 = (match (p1) with
| (({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (uu____6782); FStar_Syntax_Syntax.p = uu____6783}, uu____6784))::[] -> begin
[]
end
| (({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (uu____6797); FStar_Syntax_Syntax.p = uu____6798}, uu____6799))::[] -> begin
[]
end
| uu____6812 -> begin
p1
end)
in ((env1), (binder), (p2)))
end))
end))))
and desugar_binding_pat : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * annotated_pat Prims.list) = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * annotated_pat Prims.list) = (fun uu____6819 env pat -> (

let uu____6822 = (desugar_data_pat env pat)
in (match (uu____6822) with
| (env1, uu____6838, pat1) -> begin
((env1), (pat1))
end)))
and desugar_match_pat : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * annotated_pat Prims.list) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term_aq : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations) = (fun env e -> (

let env1 = (FStar_Syntax_DsEnv.set_expect_typ env false)
in (desugar_term_maybe_top false env1 e)))
and desugar_term : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let uu____6857 = (desugar_term_aq env e)
in (match (uu____6857) with
| (t, aq) -> begin
((check_no_aq aq);
t;
)
end)))
and desugar_typ_aq : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.antiquotations) = (fun env e -> (

let env1 = (FStar_Syntax_DsEnv.set_expect_typ env true)
in (desugar_term_maybe_top false env1 e)))
and desugar_typ : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let uu____6874 = (desugar_typ_aq env e)
in (match (uu____6874) with
| (t, aq) -> begin
((check_no_aq aq);
t;
)
end)))
and desugar_machine_integer : FStar_Syntax_DsEnv.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun env repr uu____6884 range -> (match (uu____6884) with
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

let uu____6894 = (

let uu____6895 = (FStar_Const.within_bounds repr signedness width)
in (not (uu____6895)))
in (match (uu____6894) with
| true -> begin
(

let uu____6896 = (

let uu____6901 = (FStar_Util.format2 "%s is not in the expected range for %s" repr tnm)
in ((FStar_Errors.Error_OutOfRange), (uu____6901)))
in (FStar_Errors.log_issue range uu____6896))
end
| uu____6902 -> begin
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

let uu____6906 = (FStar_Ident.path_of_text intro_nm)
in (FStar_Ident.lid_of_path uu____6906 range))
in (

let lid1 = (

let uu____6910 = (FStar_Syntax_DsEnv.try_lookup_lid env lid)
in (match (uu____6910) with
| FStar_Pervasives_Native.Some (intro_term) -> begin
(match (intro_term.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let private_lid = (

let uu____6920 = (FStar_Ident.path_of_text private_intro_nm)
in (FStar_Ident.lid_of_path uu____6920 range))
in (

let private_fv = (

let uu____6922 = (FStar_Syntax_Util.incr_delta_depth fv.FStar_Syntax_Syntax.fv_delta)
in (FStar_Syntax_Syntax.lid_as_fv private_lid uu____6922 fv.FStar_Syntax_Syntax.fv_qual))
in (

let uu___292_6923 = intro_term
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (private_fv); FStar_Syntax_Syntax.pos = uu___292_6923.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___292_6923.FStar_Syntax_Syntax.vars})))
end
| uu____6924 -> begin
(failwith (Prims.strcat "Unexpected non-fvar for " intro_nm))
end)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____6927 = (

let uu____6932 = (FStar_Util.format1 "Unexpected numeric literal.  Restart F* to load %s." tnm)
in ((FStar_Errors.Fatal_UnexpectedNumericLiteral), (uu____6932)))
in (FStar_Errors.raise_error uu____6927 range))
end))
in (

let repr1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (FStar_Pervasives_Native.None))))) FStar_Pervasives_Native.None range)
in (

let uu____6948 = (

let uu____6955 = (

let uu____6956 = (

let uu____6973 = (

let uu____6984 = (

let uu____6993 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr1), (uu____6993)))
in (uu____6984)::[])
in ((lid1), (uu____6973)))
in FStar_Syntax_Syntax.Tm_app (uu____6956))
in (FStar_Syntax_Syntax.mk uu____6955))
in (uu____6948 FStar_Pervasives_Native.None range)))))));
))
end))
and desugar_name : (FStar_Syntax_Syntax.term'  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  env_t  ->  Prims.bool  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.term = (fun mk1 setpos env resolve l -> (

let uu____7042 = (

let uu____7049 = ((match (resolve) with
| true -> begin
FStar_Syntax_DsEnv.try_lookup_lid_with_attributes
end
| uu____7062 -> begin
FStar_Syntax_DsEnv.try_lookup_lid_with_attributes_no_resolve
end) env)
in (FStar_Syntax_DsEnv.fail_or env uu____7049 l))
in (match (uu____7042) with
| (tm, attrs) -> begin
(

let warn_if_deprecated = (fun attrs1 -> (FStar_List.iter (fun a -> (match (a.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____7099; FStar_Syntax_Syntax.vars = uu____7100}, args) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v FStar_Parser_Const.deprecated_attr) -> begin
(

let msg = (

let uu____7127 = (FStar_Syntax_Print.term_to_string tm)
in (Prims.strcat uu____7127 " is deprecated"))
in (

let msg1 = (match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____7137 = (

let uu____7138 = (

let uu____7141 = (FStar_List.hd args)
in (FStar_Pervasives_Native.fst uu____7141))
in uu____7138.FStar_Syntax_Syntax.n)
in (match (uu____7137) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____7163)) when (not ((Prims.op_Equality (FStar_Util.trim_string s) ""))) -> begin
(Prims.strcat msg (Prims.strcat ", use " (Prims.strcat s " instead")))
end
| uu____7164 -> begin
msg
end))
end
| uu____7165 -> begin
msg
end)
in (

let uu____7166 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.log_issue uu____7166 ((FStar_Errors.Warning_DeprecatedDefinition), (msg1))))))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v FStar_Parser_Const.deprecated_attr) -> begin
(

let msg = (

let uu____7169 = (FStar_Syntax_Print.term_to_string tm)
in (Prims.strcat uu____7169 " is deprecated"))
in (

let uu____7170 = (FStar_Ident.range_of_lid l)
in (FStar_Errors.log_issue uu____7170 ((FStar_Errors.Warning_DeprecatedDefinition), (msg)))))
end
| uu____7171 -> begin
()
end)) attrs1))
in ((warn_if_deprecated attrs);
(

let tm1 = (setpos tm)
in tm1);
))
end)))
and desugar_attributes : env_t  ->  FStar_Parser_AST.term Prims.list  ->  FStar_Syntax_Syntax.cflag Prims.list = (fun env cattributes -> (

let desugar_attribute = (fun t -> (

let uu____7186 = (

let uu____7187 = (unparen t)
in uu____7187.FStar_Parser_AST.tm)
in (match (uu____7186) with
| FStar_Parser_AST.Var ({FStar_Ident.ns = uu____7188; FStar_Ident.ident = uu____7189; FStar_Ident.nsstr = uu____7190; FStar_Ident.str = "cps"}) -> begin
FStar_Syntax_Syntax.CPS
end
| uu____7193 -> begin
(

let uu____7194 = (

let uu____7199 = (

let uu____7200 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "Unknown attribute " uu____7200))
in ((FStar_Errors.Fatal_UnknownAttribute), (uu____7199)))
in (FStar_Errors.raise_error uu____7194 t.FStar_Parser_AST.range))
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

let uu___293_7283 = e
in {FStar_Syntax_Syntax.n = uu___293_7283.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___293_7283.FStar_Syntax_Syntax.vars}))
in (

let uu____7286 = (

let uu____7287 = (unparen top)
in uu____7287.FStar_Parser_AST.tm)
in (match (uu____7286) with
| FStar_Parser_AST.Wild -> begin
(((setpos FStar_Syntax_Syntax.tun)), (noaqs))
end
| FStar_Parser_AST.Labeled (uu____7292) -> begin
(

let uu____7299 = (desugar_formula env top)
in ((uu____7299), (noaqs)))
end
| FStar_Parser_AST.Requires (t, lopt) -> begin
(

let uu____7306 = (desugar_formula env t)
in ((uu____7306), (noaqs)))
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(

let uu____7313 = (desugar_formula env t)
in ((uu____7313), (noaqs)))
end
| FStar_Parser_AST.Attributes (ts) -> begin
(failwith "Attributes should not be desugared by desugar_term_maybe_top")
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (i, FStar_Pervasives_Native.Some (size))) -> begin
(

let uu____7337 = (desugar_machine_integer env i size top.FStar_Parser_AST.range)
in ((uu____7337), (noaqs)))
end
| FStar_Parser_AST.Const (c) -> begin
(

let uu____7339 = (mk1 (FStar_Syntax_Syntax.Tm_constant (c)))
in ((uu____7339), (noaqs)))
end
| FStar_Parser_AST.Op ({FStar_Ident.idText = "=!="; FStar_Ident.idRange = r}, args) -> begin
(

let e = (

let uu____7347 = (

let uu____7348 = (

let uu____7355 = (FStar_Ident.mk_ident (("=="), (r)))
in ((uu____7355), (args)))
in FStar_Parser_AST.Op (uu____7348))
in (FStar_Parser_AST.mk_term uu____7347 top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
in (

let uu____7358 = (

let uu____7359 = (

let uu____7360 = (

let uu____7367 = (FStar_Ident.mk_ident (("~"), (r)))
in ((uu____7367), ((e)::[])))
in FStar_Parser_AST.Op (uu____7360))
in (FStar_Parser_AST.mk_term uu____7359 top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
in (desugar_term_aq env uu____7358)))
end
| FStar_Parser_AST.Op (op_star, (lhs)::(rhs)::[]) when ((

let uu____7377 = (FStar_Ident.text_of_id op_star)
in (Prims.op_Equality uu____7377 "*")) && (

let uu____7379 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range op_star)
in (FStar_All.pipe_right uu____7379 FStar_Option.isNone))) -> begin
(

let rec flatten1 = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____7394}, (t1)::(t2)::[]) when (

let uu____7399 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range op_star)
in (FStar_All.pipe_right uu____7399 FStar_Option.isNone)) -> begin
(

let uu____7404 = (flatten1 t1)
in (FStar_List.append uu____7404 ((t2)::[])))
end
| uu____7407 -> begin
(t)::[]
end))
in (

let terms = (flatten1 lhs)
in (

let t = (

let uu___294_7412 = top
in (

let uu____7413 = (

let uu____7414 = (

let uu____7425 = (FStar_List.map (fun _0_1 -> FStar_Util.Inr (_0_1)) terms)
in ((uu____7425), (rhs)))
in FStar_Parser_AST.Sum (uu____7414))
in {FStar_Parser_AST.tm = uu____7413; FStar_Parser_AST.range = uu___294_7412.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___294_7412.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env t))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____7443 = (

let uu____7444 = (FStar_Syntax_DsEnv.fail_or2 (FStar_Syntax_DsEnv.try_lookup_id env) a)
in (FStar_All.pipe_left setpos uu____7444))
in ((uu____7443), (noaqs)))
end
| FStar_Parser_AST.Uvar (u) -> begin
(

let uu____7450 = (

let uu____7455 = (

let uu____7456 = (

let uu____7457 = (FStar_Ident.text_of_id u)
in (Prims.strcat uu____7457 " in non-universe context"))
in (Prims.strcat "Unexpected universe variable " uu____7456))
in ((FStar_Errors.Fatal_UnexpectedUniverseVariable), (uu____7455)))
in (FStar_Errors.raise_error uu____7450 top.FStar_Parser_AST.range))
end
| FStar_Parser_AST.Op (s, args) -> begin
(

let uu____7468 = (op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)
in (match (uu____7468) with
| FStar_Pervasives_Native.None -> begin
(

let uu____7475 = (

let uu____7480 = (

let uu____7481 = (FStar_Ident.text_of_id s)
in (Prims.strcat "Unexpected or unbound operator: " uu____7481))
in ((FStar_Errors.Fatal_UnepxectedOrUnboundOperator), (uu____7480)))
in (FStar_Errors.raise_error uu____7475 top.FStar_Parser_AST.range))
end
| FStar_Pervasives_Native.Some (op) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let uu____7491 = (

let uu____7516 = (FStar_All.pipe_right args (FStar_List.map (fun t -> (

let uu____7578 = (desugar_term_aq env t)
in (match (uu____7578) with
| (t', s1) -> begin
((((t'), (FStar_Pervasives_Native.None))), (s1))
end)))))
in (FStar_All.pipe_right uu____7516 FStar_List.unzip))
in (match (uu____7491) with
| (args1, aqs) -> begin
(

let uu____7711 = (mk1 (FStar_Syntax_Syntax.Tm_app (((op), (args1)))))
in ((uu____7711), ((join_aqs aqs))))
end))
end
| uu____7724 -> begin
((op), (noaqs))
end)
end))
end
| FStar_Parser_AST.Construct (n1, ((a, uu____7727))::[]) when (Prims.op_Equality n1.FStar_Ident.str "SMTPat") -> begin
(

let uu____7742 = (

let uu___295_7743 = top
in (

let uu____7744 = (

let uu____7745 = (

let uu____7752 = (

let uu___296_7753 = top
in (

let uu____7754 = (

let uu____7755 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____7755))
in {FStar_Parser_AST.tm = uu____7754; FStar_Parser_AST.range = uu___296_7753.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___296_7753.FStar_Parser_AST.level}))
in ((uu____7752), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____7745))
in {FStar_Parser_AST.tm = uu____7744; FStar_Parser_AST.range = uu___295_7743.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___295_7743.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____7742))
end
| FStar_Parser_AST.Construct (n1, ((a, uu____7758))::[]) when (Prims.op_Equality n1.FStar_Ident.str "SMTPatT") -> begin
((FStar_Errors.log_issue top.FStar_Parser_AST.range ((FStar_Errors.Warning_SMTPatTDeprecated), ("SMTPatT is deprecated; please just use SMTPat")));
(

let uu____7774 = (

let uu___297_7775 = top
in (

let uu____7776 = (

let uu____7777 = (

let uu____7784 = (

let uu___298_7785 = top
in (

let uu____7786 = (

let uu____7787 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____7787))
in {FStar_Parser_AST.tm = uu____7786; FStar_Parser_AST.range = uu___298_7785.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___298_7785.FStar_Parser_AST.level}))
in ((uu____7784), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____7777))
in {FStar_Parser_AST.tm = uu____7776; FStar_Parser_AST.range = uu___297_7775.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___297_7775.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____7774));
)
end
| FStar_Parser_AST.Construct (n1, ((a, uu____7790))::[]) when (Prims.op_Equality n1.FStar_Ident.str "SMTPatOr") -> begin
(

let uu____7805 = (

let uu___299_7806 = top
in (

let uu____7807 = (

let uu____7808 = (

let uu____7815 = (

let uu___300_7816 = top
in (

let uu____7817 = (

let uu____7818 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat_or")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____7818))
in {FStar_Parser_AST.tm = uu____7817; FStar_Parser_AST.range = uu___300_7816.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___300_7816.FStar_Parser_AST.level}))
in ((uu____7815), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____7808))
in {FStar_Parser_AST.tm = uu____7807; FStar_Parser_AST.range = uu___299_7806.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___299_7806.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____7805))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____7819; FStar_Ident.ident = uu____7820; FStar_Ident.nsstr = uu____7821; FStar_Ident.str = "Type0"}) -> begin
(

let uu____7824 = (mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
in ((uu____7824), (noaqs)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____7825; FStar_Ident.ident = uu____7826; FStar_Ident.nsstr = uu____7827; FStar_Ident.str = "Type"}) -> begin
(

let uu____7830 = (mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
in ((uu____7830), (noaqs)))
end
| FStar_Parser_AST.Construct ({FStar_Ident.ns = uu____7831; FStar_Ident.ident = uu____7832; FStar_Ident.nsstr = uu____7833; FStar_Ident.str = "Type"}, ((t, FStar_Parser_AST.UnivApp))::[]) -> begin
(

let uu____7851 = (

let uu____7852 = (

let uu____7853 = (desugar_universe t)
in FStar_Syntax_Syntax.Tm_type (uu____7853))
in (mk1 uu____7852))
in ((uu____7851), (noaqs)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____7854; FStar_Ident.ident = uu____7855; FStar_Ident.nsstr = uu____7856; FStar_Ident.str = "Effect"}) -> begin
(

let uu____7859 = (mk1 (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
in ((uu____7859), (noaqs)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____7860; FStar_Ident.ident = uu____7861; FStar_Ident.nsstr = uu____7862; FStar_Ident.str = "True"}) -> begin
(

let uu____7865 = (

let uu____7866 = (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar uu____7866 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))
in ((uu____7865), (noaqs)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____7867; FStar_Ident.ident = uu____7868; FStar_Ident.nsstr = uu____7869; FStar_Ident.str = "False"}) -> begin
(

let uu____7872 = (

let uu____7873 = (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar uu____7873 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))
in ((uu____7872), (noaqs)))
end
| FStar_Parser_AST.Projector (eff_name, {FStar_Ident.idText = txt; FStar_Ident.idRange = uu____7876}) when ((is_special_effect_combinator txt) && (FStar_Syntax_DsEnv.is_effect_name env eff_name)) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env eff_name);
(

let uu____7878 = (FStar_Syntax_DsEnv.try_lookup_effect_defn env eff_name)
in (match (uu____7878) with
| FStar_Pervasives_Native.Some (ed) -> begin
(

let lid = (FStar_Syntax_Util.dm4f_lid ed txt)
in (

let uu____7887 = (FStar_Syntax_Syntax.fvar lid (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in ((uu____7887), (noaqs))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____7888 = (

let uu____7889 = (FStar_Ident.text_of_lid eff_name)
in (FStar_Util.format2 "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)" uu____7889 txt))
in (failwith uu____7888))
end));
)
end
| FStar_Parser_AST.Var (l) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l);
(

let uu____7896 = (desugar_name mk1 setpos env true l)
in ((uu____7896), (noaqs)));
)
end
| FStar_Parser_AST.Name (l) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l);
(

let uu____7899 = (desugar_name mk1 setpos env true l)
in ((uu____7899), (noaqs)));
)
end
| FStar_Parser_AST.Projector (l, i) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l);
(

let name = (

let uu____7910 = (FStar_Syntax_DsEnv.try_lookup_datacon env l)
in (match (uu____7910) with
| FStar_Pervasives_Native.Some (uu____7919) -> begin
FStar_Pervasives_Native.Some (((true), (l)))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____7924 = (FStar_Syntax_DsEnv.try_lookup_root_effect_name env l)
in (match (uu____7924) with
| FStar_Pervasives_Native.Some (new_name) -> begin
FStar_Pervasives_Native.Some (((false), (new_name)))
end
| uu____7938 -> begin
FStar_Pervasives_Native.None
end))
end))
in (match (name) with
| FStar_Pervasives_Native.Some (resolve, new_name) -> begin
(

let uu____7955 = (

let uu____7956 = (FStar_Syntax_Util.mk_field_projector_name_from_ident new_name i)
in (desugar_name mk1 setpos env resolve uu____7956))
in ((uu____7955), (noaqs)))
end
| uu____7957 -> begin
(

let uu____7964 = (

let uu____7969 = (FStar_Util.format1 "Data constructor or effect %s not found" l.FStar_Ident.str)
in ((FStar_Errors.Fatal_EffectNotFound), (uu____7969)))
in (FStar_Errors.raise_error uu____7964 top.FStar_Parser_AST.range))
end));
)
end
| FStar_Parser_AST.Discrim (lid) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env lid);
(

let uu____7976 = (FStar_Syntax_DsEnv.try_lookup_datacon env lid)
in (match (uu____7976) with
| FStar_Pervasives_Native.None -> begin
(

let uu____7983 = (

let uu____7988 = (FStar_Util.format1 "Data constructor %s not found" lid.FStar_Ident.str)
in ((FStar_Errors.Fatal_DataContructorNotFound), (uu____7988)))
in (FStar_Errors.raise_error uu____7983 top.FStar_Parser_AST.range))
end
| uu____7993 -> begin
(

let lid' = (FStar_Syntax_Util.mk_discriminator lid)
in (

let uu____7997 = (desugar_name mk1 setpos env true lid')
in ((uu____7997), (noaqs))))
end));
)
end
| FStar_Parser_AST.Construct (l, args) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env l);
(

let uu____8013 = (FStar_Syntax_DsEnv.try_lookup_datacon env l)
in (match (uu____8013) with
| FStar_Pervasives_Native.Some (head1) -> begin
(

let head2 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (head1)))
in (match (args) with
| [] -> begin
((head2), (noaqs))
end
| uu____8032 -> begin
(

let uu____8039 = (FStar_Util.take (fun uu____8063 -> (match (uu____8063) with
| (uu____8068, imp) -> begin
(Prims.op_Equality imp FStar_Parser_AST.UnivApp)
end)) args)
in (match (uu____8039) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun x -> (desugar_universe (FStar_Pervasives_Native.fst x))) universes)
in (

let uu____8113 = (

let uu____8138 = (FStar_List.map (fun uu____8181 -> (match (uu____8181) with
| (t, imp) -> begin
(

let uu____8198 = (desugar_term_aq env t)
in (match (uu____8198) with
| (te, aq) -> begin
(((arg_withimp_e imp te)), (aq))
end))
end)) args1)
in (FStar_All.pipe_right uu____8138 FStar_List.unzip))
in (match (uu____8113) with
| (args2, aqs) -> begin
(

let head3 = (match ((Prims.op_Equality universes1 [])) with
| true -> begin
head2
end
| uu____8336 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_uinst (((head2), (universes1)))))
end)
in (

let uu____8339 = (mk1 (FStar_Syntax_Syntax.Tm_app (((head3), (args2)))))
in ((uu____8339), ((join_aqs aqs)))))
end)))
end))
end))
end
| FStar_Pervasives_Native.None -> begin
(

let err = (

let uu____8357 = (FStar_Syntax_DsEnv.try_lookup_effect_name env l)
in (match (uu____8357) with
| FStar_Pervasives_Native.None -> begin
((FStar_Errors.Fatal_ConstructorNotFound), ((Prims.strcat "Constructor " (Prims.strcat l.FStar_Ident.str " not found"))))
end
| FStar_Pervasives_Native.Some (uu____8364) -> begin
((FStar_Errors.Fatal_UnexpectedEffect), ((Prims.strcat "Effect " (Prims.strcat l.FStar_Ident.str " used at an unexpected position"))))
end))
in (FStar_Errors.raise_error err top.FStar_Parser_AST.range))
end));
)
end
| FStar_Parser_AST.Sum (binders, t) when (FStar_Util.for_all (fun uu___255_8389 -> (match (uu___255_8389) with
| FStar_Util.Inr (uu____8394) -> begin
true
end
| uu____8395 -> begin
false
end)) binders) -> begin
(

let terms = (

let uu____8403 = (FStar_All.pipe_right binders (FStar_List.map (fun uu___256_8420 -> (match (uu___256_8420) with
| FStar_Util.Inr (x) -> begin
x
end
| FStar_Util.Inl (uu____8426) -> begin
(failwith "Impossible")
end))))
in (FStar_List.append uu____8403 ((t)::[])))
in (

let uu____8427 = (

let uu____8452 = (FStar_All.pipe_right terms (FStar_List.map (fun t1 -> (

let uu____8509 = (desugar_typ_aq env t1)
in (match (uu____8509) with
| (t', aq) -> begin
(

let uu____8520 = (FStar_Syntax_Syntax.as_arg t')
in ((uu____8520), (aq)))
end)))))
in (FStar_All.pipe_right uu____8452 FStar_List.unzip))
in (match (uu____8427) with
| (targs, aqs) -> begin
(

let tup = (

let uu____8630 = (FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_lid env) uu____8630))
in (

let uu____8639 = (mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
in ((uu____8639), ((join_aqs aqs)))))
end)))
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let uu____8666 = (

let uu____8683 = (

let uu____8690 = (

let uu____8697 = (FStar_All.pipe_left (fun _0_2 -> FStar_Util.Inl (_0_2)) (FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type_level FStar_Pervasives_Native.None))
in (uu____8697)::[])
in (FStar_List.append binders uu____8690))
in (FStar_List.fold_left (fun uu____8750 b -> (match (uu____8750) with
| (env1, tparams, typs) -> begin
(

let uu____8811 = (match (b) with
| FStar_Util.Inl (b1) -> begin
(desugar_binder env1 b1)
end
| FStar_Util.Inr (t1) -> begin
(

let uu____8826 = (desugar_typ env1 t1)
in ((FStar_Pervasives_Native.None), (uu____8826)))
end)
in (match (uu____8811) with
| (xopt, t1) -> begin
(

let uu____8851 = (match (xopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8860 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env1), (uu____8860)))
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_Syntax_DsEnv.push_bv env1 x)
end)
in (match (uu____8851) with
| (env2, x) -> begin
(

let uu____8880 = (

let uu____8883 = (

let uu____8886 = (

let uu____8887 = (no_annot_abs tparams t1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____8887))
in (uu____8886)::[])
in (FStar_List.append typs uu____8883))
in ((env2), ((FStar_List.append tparams (((((

let uu___301_8913 = x
in {FStar_Syntax_Syntax.ppname = uu___301_8913.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___301_8913.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})), (FStar_Pervasives_Native.None)))::[]))), (uu____8880)))
end))
end))
end)) ((env), ([]), ([])) uu____8683))
in (match (uu____8666) with
| (env1, uu____8941, targs) -> begin
(

let tup = (

let uu____8964 = (FStar_Parser_Const.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Syntax_DsEnv.fail_or env1 (FStar_Syntax_DsEnv.try_lookup_lid env1) uu____8964))
in (

let uu____8965 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
in ((uu____8965), (noaqs))))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let uu____8984 = (uncurry binders t)
in (match (uu____8984) with
| (bs, t1) -> begin
(

let rec aux = (fun env1 bs1 uu___257_9028 -> (match (uu___257_9028) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range true env1 t1)
in (

let uu____9044 = (FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod)
in (FStar_All.pipe_left setpos uu____9044)))
end
| (hd1)::tl1 -> begin
(

let bb = (desugar_binder env1 hd1)
in (

let uu____9068 = (as_binder env1 hd1.FStar_Parser_AST.aqual bb)
in (match (uu____9068) with
| (b, env2) -> begin
(aux env2 ((b)::bs1) tl1)
end)))
end))
in (

let uu____9101 = (aux env [] bs)
in ((uu____9101), (noaqs))))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(

let uu____9110 = (desugar_binder env b)
in (match (uu____9110) with
| (FStar_Pervasives_Native.None, uu____9121) -> begin
(failwith "Missing binder in refinement")
end
| b1 -> begin
(

let uu____9135 = (as_binder env FStar_Pervasives_Native.None b1)
in (match (uu____9135) with
| ((x, uu____9151), env1) -> begin
(

let f1 = (desugar_formula env1 f)
in (

let uu____9164 = (

let uu____9165 = (FStar_Syntax_Util.refine x f1)
in (FStar_All.pipe_left setpos uu____9165))
in ((uu____9164), (noaqs))))
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

let uu____9243 = (FStar_Util.set_is_empty i)
in (match (uu____9243) with
| true -> begin
(

let uu____9246 = (FStar_Util.set_union acc set1)
in (aux uu____9246 sets2))
end
| uu____9249 -> begin
(

let uu____9250 = (

let uu____9251 = (FStar_Util.set_elements i)
in (FStar_List.hd uu____9251))
in FStar_Pervasives_Native.Some (uu____9250))
end)))
end))
in (

let uu____9254 = (FStar_Syntax_Syntax.new_id_set ())
in (aux uu____9254 sets))))
in ((

let uu____9258 = (check_disjoint bvss)
in (match (uu____9258) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (id1) -> begin
(

let uu____9262 = (

let uu____9267 = (FStar_Util.format1 "Non-linear patterns are not permitted: `%s` appears more than once in this function definition." id1.FStar_Ident.idText)
in ((FStar_Errors.Fatal_NonLinearPatternNotPermitted), (uu____9267)))
in (

let uu____9268 = (FStar_Ident.range_of_id id1)
in (FStar_Errors.raise_error uu____9262 uu____9268)))
end));
(

let binders1 = (FStar_All.pipe_right binders (FStar_List.map replace_unit_pattern))
in (

let uu____9276 = (FStar_List.fold_left (fun uu____9296 pat -> (match (uu____9296) with
| (env1, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (uu____9322, (t, FStar_Pervasives_Native.None)) -> begin
(

let uu____9332 = (

let uu____9335 = (free_type_vars env1 t)
in (FStar_List.append uu____9335 ftvs))
in ((env1), (uu____9332)))
end
| FStar_Parser_AST.PatAscribed (uu____9340, (t, FStar_Pervasives_Native.Some (tac))) -> begin
(

let uu____9351 = (

let uu____9354 = (free_type_vars env1 t)
in (

let uu____9357 = (

let uu____9360 = (free_type_vars env1 tac)
in (FStar_List.append uu____9360 ftvs))
in (FStar_List.append uu____9354 uu____9357)))
in ((env1), (uu____9351)))
end
| uu____9365 -> begin
((env1), (ftvs))
end)
end)) ((env), ([])) binders1)
in (match (uu____9276) with
| (uu____9374, ftv) -> begin
(

let ftv1 = (sort_ftv ftv)
in (

let binders2 = (

let uu____9386 = (FStar_All.pipe_right ftv1 (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append uu____9386 binders1))
in (

let rec aux = (fun env1 bs sc_pat_opt uu___258_9443 -> (match (uu___258_9443) with
| [] -> begin
(

let uu____9470 = (desugar_term_aq env1 body)
in (match (uu____9470) with
| (body1, aq) -> begin
(

let body2 = (match (sc_pat_opt) with
| FStar_Pervasives_Native.Some (sc, pat) -> begin
(

let body2 = (

let uu____9507 = (

let uu____9508 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right uu____9508 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close uu____9507 body1))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (FStar_Pervasives_Native.None), (body2)))::[])))) FStar_Pervasives_Native.None body2.FStar_Syntax_Syntax.pos))
end
| FStar_Pervasives_Native.None -> begin
body1
end)
in (

let uu____9577 = (

let uu____9580 = (no_annot_abs (FStar_List.rev bs) body2)
in (setpos uu____9580))
in ((uu____9577), (aq))))
end))
end
| (p)::rest -> begin
(

let uu____9595 = (desugar_binding_pat env1 p)
in (match (uu____9595) with
| (env2, b, pat) -> begin
(

let pat1 = (match (pat) with
| [] -> begin
FStar_Pervasives_Native.None
end
| ((p1, uu____9629))::[] -> begin
FStar_Pervasives_Native.Some (p1)
end
| uu____9644 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnsupportedDisjuctivePatterns), ("Disjunctive patterns are not supported in abstractions")) p.FStar_Parser_AST.prange)
end)
in (

let uu____9651 = (match (b) with
| LetBinder (uu____9692) -> begin
(failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt1 = (match (((pat1), (sc_pat_opt))) with
| (FStar_Pervasives_Native.None, uu____9760) -> begin
sc_pat_opt
end
| (FStar_Pervasives_Native.Some (p1), FStar_Pervasives_Native.None) -> begin
(

let uu____9814 = (

let uu____9823 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____9823), (p1)))
in FStar_Pervasives_Native.Some (uu____9814))
end
| (FStar_Pervasives_Native.Some (p1), FStar_Pervasives_Native.Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (uu____9885), uu____9886) -> begin
(

let tup2 = (

let uu____9888 = (FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____9888 FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____9892 = (

let uu____9899 = (

let uu____9900 = (

let uu____9917 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (

let uu____9920 = (

let uu____9931 = (FStar_Syntax_Syntax.as_arg sc)
in (

let uu____9940 = (

let uu____9951 = (

let uu____9960 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____9960))
in (uu____9951)::[])
in (uu____9931)::uu____9940))
in ((uu____9917), (uu____9920))))
in FStar_Syntax_Syntax.Tm_app (uu____9900))
in (FStar_Syntax_Syntax.mk uu____9899))
in (uu____9892 FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
in (

let p2 = (

let uu____10011 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p1), (false)))::[])))) uu____10011))
in FStar_Pervasives_Native.Some (((sc1), (p2))))))
end
| (FStar_Syntax_Syntax.Tm_app (uu____10054, args), FStar_Syntax_Syntax.Pat_cons (uu____10056, pats)) -> begin
(

let tupn = (

let uu____10099 = (FStar_Parser_Const.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____10099 FStar_Syntax_Syntax.delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____10111 = (

let uu____10112 = (

let uu____10129 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (

let uu____10132 = (

let uu____10143 = (

let uu____10154 = (

let uu____10163 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____10163))
in (uu____10154)::[])
in (FStar_List.append args uu____10143))
in ((uu____10129), (uu____10132))))
in FStar_Syntax_Syntax.Tm_app (uu____10112))
in (mk1 uu____10111))
in (

let p2 = (

let uu____10211 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p1), (false)))::[])))))) uu____10211))
in FStar_Pervasives_Native.Some (((sc1), (p2))))))
end
| uu____10252 -> begin
(failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt1)))
end)
in (match (uu____9651) with
| (b1, sc_pat_opt1) -> begin
(aux env2 ((b1)::bs) sc_pat_opt1 rest)
end)))
end))
end))
in (aux env [] FStar_Pervasives_Native.None binders2))))
end)));
)))
end
| FStar_Parser_AST.App (uu____10345, uu____10346, FStar_Parser_AST.UnivApp) -> begin
(

let rec aux = (fun universes e -> (

let uu____10368 = (

let uu____10369 = (unparen e)
in uu____10369.FStar_Parser_AST.tm)
in (match (uu____10368) with
| FStar_Parser_AST.App (e1, t, FStar_Parser_AST.UnivApp) -> begin
(

let univ_arg = (desugar_universe t)
in (aux ((univ_arg)::universes) e1))
end
| uu____10379 -> begin
(

let uu____10380 = (desugar_term_aq env e)
in (match (uu____10380) with
| (head1, aq) -> begin
(

let uu____10393 = (mk1 (FStar_Syntax_Syntax.Tm_uinst (((head1), (universes)))))
in ((uu____10393), (aq)))
end))
end)))
in (aux [] top))
end
| FStar_Parser_AST.App (uu____10400) -> begin
(

let rec aux = (fun args aqs e -> (

let uu____10477 = (

let uu____10478 = (unparen e)
in uu____10478.FStar_Parser_AST.tm)
in (match (uu____10477) with
| FStar_Parser_AST.App (e1, t, imp) when (Prims.op_disEquality imp FStar_Parser_AST.UnivApp) -> begin
(

let uu____10496 = (desugar_term_aq env t)
in (match (uu____10496) with
| (t1, aq) -> begin
(

let arg = (arg_withimp_e imp t1)
in (aux ((arg)::args) ((aq)::aqs) e1))
end))
end
| uu____10544 -> begin
(

let uu____10545 = (desugar_term_aq env e)
in (match (uu____10545) with
| (head1, aq) -> begin
(

let uu____10566 = (mk1 (FStar_Syntax_Syntax.Tm_app (((head1), (args)))))
in ((uu____10566), ((join_aqs ((aq)::aqs)))))
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

let uu____10626 = (FStar_Parser_AST.mkExplicitApp bind1 ((t1)::(k)::[]) top.FStar_Parser_AST.range)
in (desugar_term_aq env uu____10626))))))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(

let t = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), ((((FStar_Pervasives_Native.None), ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatWild (FStar_Pervasives_Native.None)) t1.FStar_Parser_AST.range)), (t1)))))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr)
in (

let uu____10678 = (desugar_term_aq env t)
in (match (uu____10678) with
| (tm, s) -> begin
(

let uu____10689 = (mk1 (FStar_Syntax_Syntax.Tm_meta (((tm), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))))
in ((uu____10689), (s)))
end)))
end
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(

let env1 = (FStar_Syntax_DsEnv.push_namespace env lid)
in (

let uu____10695 = (

let uu____10708 = (FStar_Syntax_DsEnv.expect_typ env1)
in (match (uu____10708) with
| true -> begin
desugar_typ_aq
end
| uu____10719 -> begin
desugar_term_aq
end))
in (uu____10695 env1 e)))
end
| FStar_Parser_AST.Let (qual, lbs, body) -> begin
(

let is_rec = (Prims.op_Equality qual FStar_Parser_AST.Rec)
in (

let ds_let_rec_or_app = (fun uu____10763 -> (

let bindings = lbs
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun uu____10906 -> (match (uu____10906) with
| (attr_opt, (p, def)) -> begin
(

let uu____10964 = (is_app_pattern p)
in (match (uu____10964) with
| true -> begin
(

let uu____10995 = (destruct_app_pattern env top_level p)
in ((attr_opt), (uu____10995), (def)))
end
| uu____11040 -> begin
(match ((FStar_Parser_AST.un_function p def)) with
| FStar_Pervasives_Native.Some (p1, def1) -> begin
(

let uu____11077 = (destruct_app_pattern env top_level p1)
in ((attr_opt), (uu____11077), (def1)))
end
| uu____11122 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id1, uu____11160); FStar_Parser_AST.prange = uu____11161}, t) -> begin
(match (top_level) with
| true -> begin
(

let uu____11209 = (

let uu____11230 = (

let uu____11235 = (FStar_Syntax_DsEnv.qualify env id1)
in FStar_Util.Inr (uu____11235))
in ((uu____11230), ([]), (FStar_Pervasives_Native.Some (t))))
in ((attr_opt), (uu____11209), (def)))
end
| uu____11280 -> begin
((attr_opt), (((FStar_Util.Inl (id1)), ([]), (FStar_Pervasives_Native.Some (t)))), (def))
end)
end
| FStar_Parser_AST.PatVar (id1, uu____11326) -> begin
(match (top_level) with
| true -> begin
(

let uu____11361 = (

let uu____11382 = (

let uu____11387 = (FStar_Syntax_DsEnv.qualify env id1)
in FStar_Util.Inr (uu____11387))
in ((uu____11382), ([]), (FStar_Pervasives_Native.None)))
in ((attr_opt), (uu____11361), (def)))
end
| uu____11432 -> begin
((attr_opt), (((FStar_Util.Inl (id1)), ([]), (FStar_Pervasives_Native.None))), (def))
end)
end
| uu____11477 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedLetBinding), ("Unexpected let binding")) p.FStar_Parser_AST.prange)
end)
end)
end))
end))))
in (

let uu____11508 = (FStar_List.fold_left (fun uu____11581 uu____11582 -> (match (((uu____11581), (uu____11582))) with
| ((env1, fnames, rec_bindings), (_attr_opt, (f, uu____11690, uu____11691), uu____11692)) -> begin
(

let uu____11809 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let uu____11835 = (FStar_Syntax_DsEnv.push_bv env1 x)
in (match (uu____11835) with
| (env2, xx) -> begin
(

let uu____11854 = (

let uu____11857 = (FStar_Syntax_Syntax.mk_binder xx)
in (uu____11857)::rec_bindings)
in ((env2), (FStar_Util.Inl (xx)), (uu____11854)))
end))
end
| FStar_Util.Inr (l) -> begin
(

let uu____11865 = (FStar_Syntax_DsEnv.push_top_level_rec_binding env1 l.FStar_Ident.ident FStar_Syntax_Syntax.delta_equational)
in ((uu____11865), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (uu____11809) with
| (env2, lbname, rec_bindings1) -> begin
((env2), ((lbname)::fnames), (rec_bindings1))
end))
end)) ((env), ([]), ([])) funs)
in (match (uu____11508) with
| (env', fnames, rec_bindings) -> begin
(

let fnames1 = (FStar_List.rev fnames)
in (

let rec_bindings1 = (FStar_List.rev rec_bindings)
in (

let desugar_one_def = (fun env1 lbname uu____12013 -> (match (uu____12013) with
| (attrs_opt, (uu____12049, args, result_t), def) -> begin
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

let uu____12137 = (is_comp_type env1 t)
in (match (uu____12137) with
| true -> begin
((

let uu____12139 = (FStar_All.pipe_right args1 (FStar_List.tryFind (fun x -> (

let uu____12149 = (is_var_pattern x)
in (not (uu____12149))))))
in (match (uu____12139) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (p) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ComputationTypeNotAllowed), ("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable")) p.FStar_Parser_AST.prange)
end));
t;
)
end
| uu____12151 -> begin
(

let uu____12152 = (((FStar_Options.ml_ish ()) && (

let uu____12154 = (FStar_Syntax_DsEnv.try_lookup_effect_name env1 FStar_Parser_Const.effect_ML_lid)
in (FStar_Option.isSome uu____12154))) && ((not (is_rec)) || (Prims.op_disEquality (FStar_List.length args1) (Prims.parse_int "0"))))
in (match (uu____12152) with
| true -> begin
(FStar_Parser_AST.ml_comp t)
end
| uu____12157 -> begin
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
| uu____12161 -> begin
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

let uu____12176 = (

let uu____12177 = (FStar_Syntax_Util.incr_delta_qualifier body1)
in (FStar_Syntax_Syntax.lid_as_fv l uu____12177 FStar_Pervasives_Native.None))
in FStar_Util.Inr (uu____12176))
end)
in (

let body2 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.close rec_bindings1 body1)
end
| uu____12183 -> begin
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
| uu____12253 -> begin
env
end)) fnames1 funs)
in (

let uu____12254 = (desugar_term_aq env' body)
in (match (uu____12254) with
| (body1, aq) -> begin
(

let uu____12267 = (

let uu____12270 = (

let uu____12271 = (

let uu____12284 = (FStar_Syntax_Subst.close rec_bindings1 body1)
in ((((is_rec), (lbs1))), (uu____12284)))
in FStar_Syntax_Syntax.Tm_let (uu____12271))
in (FStar_All.pipe_left mk1 uu____12270))
in ((uu____12267), (aq)))
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

let uu____12357 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (uu____12357) with
| (env1, binder, pat1) -> begin
(

let uu____12379 = (match (binder) with
| LetBinder (l, (t, _tacopt)) -> begin
(

let uu____12405 = (desugar_term_aq env1 t2)
in (match (uu____12405) with
| (body1, aq) -> begin
(

let fv = (

let uu____12419 = (FStar_Syntax_Util.incr_delta_qualifier t11)
in (FStar_Syntax_Syntax.lid_as_fv l uu____12419 FStar_Pervasives_Native.None))
in (

let uu____12420 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_let (((((false), (((mk_lb ((attrs), (FStar_Util.Inr (fv)), (t), (t11), (t11.FStar_Syntax_Syntax.pos))))::[]))), (body1)))))
in ((uu____12420), (aq))))
end))
end
| LocalBinder (x, uu____12450) -> begin
(

let uu____12451 = (desugar_term_aq env1 t2)
in (match (uu____12451) with
| (body1, aq) -> begin
(

let body2 = (match (pat1) with
| [] -> begin
body1
end
| (({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (uu____12465); FStar_Syntax_Syntax.p = uu____12466}, uu____12467))::[] -> begin
body1
end
| uu____12480 -> begin
(

let uu____12483 = (

let uu____12490 = (

let uu____12491 = (

let uu____12514 = (FStar_Syntax_Syntax.bv_to_name x)
in (

let uu____12517 = (desugar_disjunctive_pattern pat1 FStar_Pervasives_Native.None body1)
in ((uu____12514), (uu____12517))))
in FStar_Syntax_Syntax.Tm_match (uu____12491))
in (FStar_Syntax_Syntax.mk uu____12490))
in (uu____12483 FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
end)
in (

let uu____12557 = (

let uu____12560 = (

let uu____12561 = (

let uu____12574 = (

let uu____12577 = (

let uu____12578 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____12578)::[])
in (FStar_Syntax_Subst.close uu____12577 body2))
in ((((false), (((mk_lb ((attrs), (FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t11), (t11.FStar_Syntax_Syntax.pos))))::[]))), (uu____12574)))
in FStar_Syntax_Syntax.Tm_let (uu____12561))
in (FStar_All.pipe_left mk1 uu____12560))
in ((uu____12557), (aq))))
end))
end)
in (match (uu____12379) with
| (tm, aq) -> begin
((tm), (aq))
end))
end)))))
in (

let uu____12637 = (FStar_List.hd lbs)
in (match (uu____12637) with
| (attrs, (head_pat, defn)) -> begin
(

let uu____12681 = (is_rec || (is_app_pattern head_pat))
in (match (uu____12681) with
| true -> begin
(ds_let_rec_or_app ())
end
| uu____12686 -> begin
(ds_non_rec attrs head_pat defn body)
end))
end)))))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (

let t_bool1 = (

let uu____12694 = (

let uu____12695 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in FStar_Syntax_Syntax.Tm_fvar (uu____12695))
in (mk1 uu____12694))
in (

let uu____12696 = (desugar_term_aq env t1)
in (match (uu____12696) with
| (t1', aq1) -> begin
(

let uu____12707 = (desugar_term_aq env t2)
in (match (uu____12707) with
| (t2', aq2) -> begin
(

let uu____12718 = (desugar_term_aq env t3)
in (match (uu____12718) with
| (t3', aq3) -> begin
(

let uu____12729 = (

let uu____12730 = (

let uu____12731 = (

let uu____12754 = (

let uu____12771 = (

let uu____12786 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) t2.FStar_Parser_AST.range)
in ((uu____12786), (FStar_Pervasives_Native.None), (t2')))
in (

let uu____12799 = (

let uu____12816 = (

let uu____12831 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) t3.FStar_Parser_AST.range)
in ((uu____12831), (FStar_Pervasives_Native.None), (t3')))
in (uu____12816)::[])
in (uu____12771)::uu____12799))
in ((t1'), (uu____12754)))
in FStar_Syntax_Syntax.Tm_match (uu____12731))
in (mk1 uu____12730))
in ((uu____12729), ((join_aqs ((aq1)::(aq2)::(aq3)::[])))))
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

let desugar_branch = (fun uu____13024 -> (match (uu____13024) with
| (pat, wopt, b) -> begin
(

let uu____13046 = (desugar_match_pat env pat)
in (match (uu____13046) with
| (env1, pat1) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (e1) -> begin
(

let uu____13077 = (desugar_term env1 e1)
in FStar_Pervasives_Native.Some (uu____13077))
end)
in (

let uu____13082 = (desugar_term_aq env1 b)
in (match (uu____13082) with
| (b1, aq) -> begin
(

let uu____13095 = (desugar_disjunctive_pattern pat1 wopt1 b1)
in ((uu____13095), (aq)))
end)))
end))
end))
in (

let uu____13100 = (desugar_term_aq env e)
in (match (uu____13100) with
| (e1, aq) -> begin
(

let uu____13111 = (

let uu____13142 = (

let uu____13175 = (FStar_List.map desugar_branch branches)
in (FStar_All.pipe_right uu____13175 FStar_List.unzip))
in (FStar_All.pipe_right uu____13142 (fun uu____13305 -> (match (uu____13305) with
| (x, y) -> begin
(((FStar_List.flatten x)), (y))
end))))
in (match (uu____13111) with
| (brs, aqs) -> begin
(

let uu____13524 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_match (((e1), (brs)))))
in ((uu____13524), ((join_aqs ((aq)::aqs)))))
end))
end)))
end
| FStar_Parser_AST.Ascribed (e, t, tac_opt) -> begin
(

let uu____13558 = (

let uu____13579 = (is_comp_type env t)
in (match (uu____13579) with
| true -> begin
(

let comp = (desugar_comp t.FStar_Parser_AST.range true env t)
in ((FStar_Util.Inr (comp)), ([])))
end
| uu____13629 -> begin
(

let uu____13630 = (desugar_term_aq env t)
in (match (uu____13630) with
| (tm, aq) -> begin
((FStar_Util.Inl (tm)), (aq))
end))
end))
in (match (uu____13558) with
| (annot, aq0) -> begin
(

let tac_opt1 = (FStar_Util.map_opt tac_opt (desugar_term env))
in (

let uu____13722 = (desugar_term_aq env e)
in (match (uu____13722) with
| (e1, aq) -> begin
(

let uu____13733 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_ascribed (((e1), (((annot), (tac_opt1))), (FStar_Pervasives_Native.None)))))
in ((uu____13733), ((FStar_List.append aq0 aq))))
end)))
end))
end
| FStar_Parser_AST.Record (uu____13772, []) -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedEmptyRecord), ("Unexpected empty record")) top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let record = (check_fields env fields top.FStar_Parser_AST.range)
in (

let user_ns = (

let uu____13813 = (FStar_List.hd fields)
in (match (uu____13813) with
| (f, uu____13825) -> begin
f.FStar_Ident.ns
end))
in (

let get_field = (fun xopt f -> (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun uu____13871 -> (match (uu____13871) with
| (g, uu____13877) -> begin
(Prims.op_Equality f.FStar_Ident.idText g.FStar_Ident.ident.FStar_Ident.idText)
end))))
in (

let fn = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((f)::[])))
in (match (found) with
| FStar_Pervasives_Native.Some (uu____13883, e) -> begin
((fn), (e))
end
| FStar_Pervasives_Native.None -> begin
(match (xopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____13897 = (

let uu____13902 = (FStar_Util.format2 "Field %s of record type %s is missing" f.FStar_Ident.idText record.FStar_Syntax_DsEnv.typename.FStar_Ident.str)
in ((FStar_Errors.Fatal_MissingFieldInRecord), (uu____13902)))
in (FStar_Errors.raise_error uu____13897 top.FStar_Parser_AST.range))
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

let uu____13910 = (

let uu____13921 = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map (fun uu____13952 -> (match (uu____13952) with
| (f, uu____13962) -> begin
(

let uu____13963 = (

let uu____13964 = (get_field FStar_Pervasives_Native.None f)
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____13964))
in ((uu____13963), (FStar_Parser_AST.Nothing)))
end))))
in ((user_constrname), (uu____13921)))
in FStar_Parser_AST.Construct (uu____13910))
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (

let uu____13982 = (

let uu____13983 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____13983))
in (FStar_Parser_AST.mk_term uu____13982 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record1 = (

let uu____13985 = (

let uu____13998 = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map (fun uu____14028 -> (match (uu____14028) with
| (f, uu____14038) -> begin
(get_field (FStar_Pervasives_Native.Some (xterm)) f)
end))))
in ((FStar_Pervasives_Native.None), (uu____13998)))
in FStar_Parser_AST.Record (uu____13985))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), ((((FStar_Pervasives_Native.None), ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (FStar_Pervasives_Native.None)))) x.FStar_Ident.idRange)), (e)))))::[]), ((FStar_Parser_AST.mk_term record1 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm1 = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let uu____14098 = (desugar_term_aq env recterm1)
in (match (uu____14098) with
| (e, s) -> begin
(match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____14114; FStar_Syntax_Syntax.vars = uu____14115}, args) -> begin
(

let uu____14141 = (

let uu____14142 = (

let uu____14143 = (

let uu____14160 = (

let uu____14163 = (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos)
in (

let uu____14164 = (

let uu____14167 = (

let uu____14168 = (

let uu____14175 = (FStar_All.pipe_right record.FStar_Syntax_DsEnv.fields (FStar_List.map FStar_Pervasives_Native.fst))
in ((record.FStar_Syntax_DsEnv.typename), (uu____14175)))
in FStar_Syntax_Syntax.Record_ctor (uu____14168))
in FStar_Pervasives_Native.Some (uu____14167))
in (FStar_Syntax_Syntax.fvar uu____14163 FStar_Syntax_Syntax.delta_constant uu____14164)))
in ((uu____14160), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____14143))
in (FStar_All.pipe_left mk1 uu____14142))
in ((uu____14141), (s)))
end
| uu____14204 -> begin
((e), (s))
end)
end))))))))
end
| FStar_Parser_AST.Project (e, f) -> begin
((FStar_Syntax_DsEnv.fail_if_qualified_by_curmodule env f);
(

let uu____14208 = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_dc_by_field_name env) f)
in (match (uu____14208) with
| (constrname, is_rec) -> begin
(

let uu____14223 = (desugar_term_aq env e)
in (match (uu____14223) with
| (e1, s) -> begin
(

let projname = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname f.FStar_Ident.ident)
in (

let qual = (match (is_rec) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (((constrname), (f.FStar_Ident.ident))))
end
| uu____14240 -> begin
FStar_Pervasives_Native.None
end)
in (

let uu____14241 = (

let uu____14242 = (

let uu____14243 = (

let uu____14260 = (

let uu____14263 = (

let uu____14264 = (FStar_Ident.range_of_lid f)
in (FStar_Ident.set_lid_range projname uu____14264))
in (FStar_Syntax_Syntax.fvar uu____14263 (FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "1"))) qual))
in (

let uu____14265 = (

let uu____14276 = (FStar_Syntax_Syntax.as_arg e1)
in (uu____14276)::[])
in ((uu____14260), (uu____14265))))
in FStar_Syntax_Syntax.Tm_app (uu____14243))
in (FStar_All.pipe_left mk1 uu____14242))
in ((uu____14241), (s)))))
end))
end));
)
end
| FStar_Parser_AST.NamedTyp (uu____14313, e) -> begin
(desugar_term_aq env e)
end
| FStar_Parser_AST.Paren (e) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.VQuote (e) -> begin
(

let tm = (desugar_term env e)
in (

let uu____14322 = (

let uu____14323 = (FStar_Syntax_Subst.compress tm)
in uu____14323.FStar_Syntax_Syntax.n)
in (match (uu____14322) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____14331 = (

let uu___302_14332 = (

let uu____14333 = (

let uu____14334 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____14334))
in (FStar_Syntax_Util.exp_string uu____14333))
in {FStar_Syntax_Syntax.n = uu___302_14332.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = e.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___302_14332.FStar_Syntax_Syntax.vars})
in ((uu____14331), (noaqs)))
end
| uu____14335 -> begin
(

let uu____14336 = (

let uu____14341 = (

let uu____14342 = (FStar_Syntax_Print.term_to_string tm)
in (Prims.strcat "VQuote, expected an fvar, got: " uu____14342))
in ((FStar_Errors.Fatal_UnexpectedTermVQuote), (uu____14341)))
in (FStar_Errors.raise_error uu____14336 top.FStar_Parser_AST.range))
end)))
end
| FStar_Parser_AST.Quote (e, FStar_Parser_AST.Static) -> begin
(

let uu____14348 = (desugar_term_aq env e)
in (match (uu____14348) with
| (tm, vts) -> begin
(

let qi = {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static; FStar_Syntax_Syntax.antiquotes = vts}
in (

let uu____14360 = (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_quoted (((tm), (qi)))))
in ((uu____14360), (noaqs))))
end))
end
| FStar_Parser_AST.Antiquote (e) -> begin
(

let bv = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (e.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (

let uu____14365 = (FStar_Syntax_Syntax.bv_to_name bv)
in (

let uu____14366 = (

let uu____14367 = (

let uu____14374 = (desugar_term env e)
in ((bv), (uu____14374)))
in (uu____14367)::[])
in ((uu____14365), (uu____14366)))))
end
| FStar_Parser_AST.Quote (e, FStar_Parser_AST.Dynamic) -> begin
(

let qi = {FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic; FStar_Syntax_Syntax.antiquotes = []}
in (

let uu____14399 = (

let uu____14400 = (

let uu____14401 = (

let uu____14408 = (desugar_term env e)
in ((uu____14408), (qi)))
in FStar_Syntax_Syntax.Tm_quoted (uu____14401))
in (FStar_All.pipe_left mk1 uu____14400))
in ((uu____14399), (noaqs))))
end
| uu____14413 when (Prims.op_Equality top.FStar_Parser_AST.level FStar_Parser_AST.Formula) -> begin
(

let uu____14414 = (desugar_formula env top)
in ((uu____14414), (noaqs)))
end
| uu____14415 -> begin
(

let uu____14416 = (

let uu____14421 = (

let uu____14422 = (FStar_Parser_AST.term_to_string top)
in (Prims.strcat "Unexpected term: " uu____14422))
in ((FStar_Errors.Fatal_UnexpectedTerm), (uu____14421)))
in (FStar_Errors.raise_error uu____14416 top.FStar_Parser_AST.range))
end)))))))
and not_ascribed : FStar_Parser_AST.term  ->  Prims.bool = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Ascribed (uu____14428) -> begin
false
end
| uu____14437 -> begin
true
end))
and desugar_args : FStar_Syntax_DsEnv.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____14474 -> (match (uu____14474) with
| (a, imp) -> begin
(

let uu____14487 = (desugar_term env a)
in (arg_withimp_e imp uu____14487))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun r allow_type_promotion env t -> (

let fail1 = (fun err -> (FStar_Errors.raise_error err r))
in (

let is_requires = (fun uu____14520 -> (match (uu____14520) with
| (t1, uu____14526) -> begin
(

let uu____14527 = (

let uu____14528 = (unparen t1)
in uu____14528.FStar_Parser_AST.tm)
in (match (uu____14527) with
| FStar_Parser_AST.Requires (uu____14529) -> begin
true
end
| uu____14536 -> begin
false
end))
end))
in (

let is_ensures = (fun uu____14546 -> (match (uu____14546) with
| (t1, uu____14552) -> begin
(

let uu____14553 = (

let uu____14554 = (unparen t1)
in uu____14554.FStar_Parser_AST.tm)
in (match (uu____14553) with
| FStar_Parser_AST.Ensures (uu____14555) -> begin
true
end
| uu____14562 -> begin
false
end))
end))
in (

let is_app = (fun head1 uu____14577 -> (match (uu____14577) with
| (t1, uu____14583) -> begin
(

let uu____14584 = (

let uu____14585 = (unparen t1)
in uu____14585.FStar_Parser_AST.tm)
in (match (uu____14584) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = uu____14587; FStar_Parser_AST.level = uu____14588}, uu____14589, uu____14590) -> begin
(Prims.op_Equality d.FStar_Ident.ident.FStar_Ident.idText head1)
end
| uu____14591 -> begin
false
end))
end))
in (

let is_smt_pat = (fun uu____14601 -> (match (uu____14601) with
| (t1, uu____14607) -> begin
(

let uu____14608 = (

let uu____14609 = (unparen t1)
in uu____14609.FStar_Parser_AST.tm)
in (match (uu____14608) with
| FStar_Parser_AST.Construct (cons1, (({FStar_Parser_AST.tm = FStar_Parser_AST.Construct (smtpat, uu____14612); FStar_Parser_AST.range = uu____14613; FStar_Parser_AST.level = uu____14614}, uu____14615))::(uu____14616)::[]) -> begin
((FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid) && (FStar_Util.for_some (fun s -> (Prims.op_Equality smtpat.FStar_Ident.str s)) (("SMTPat")::("SMTPatT")::("SMTPatOr")::[])))
end
| FStar_Parser_AST.Construct (cons1, (({FStar_Parser_AST.tm = FStar_Parser_AST.Var (smtpat); FStar_Parser_AST.range = uu____14655; FStar_Parser_AST.level = uu____14656}, uu____14657))::(uu____14658)::[]) -> begin
((FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid) && (FStar_Util.for_some (fun s -> (Prims.op_Equality smtpat.FStar_Ident.str s)) (("smt_pat")::("smt_pat_or")::[])))
end
| uu____14683 -> begin
false
end))
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t1 -> (

let uu____14715 = (head_and_args t1)
in (match (uu____14715) with
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

let wildpat = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatWild (FStar_Pervasives_Native.None)) ens.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ((((wildpat)::[]), (ens)))) ens.FStar_Parser_AST.range FStar_Parser_AST.Expr)))
in (

let thunk_ens = (fun uu____14813 -> (match (uu____14813) with
| (e, i) -> begin
(

let uu____14824 = (thunk_ens_ e)
in ((uu____14824), (i)))
end))
in (

let fail_lemma = (fun uu____14836 -> (

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

let uu____14916 = (

let uu____14923 = (

let uu____14930 = (thunk_ens ens)
in (uu____14930)::(nil_pat)::[])
in (req_true)::uu____14923)
in (unit_tm)::uu____14916)
end
| (req)::(ens)::[] when ((is_requires req) && (is_ensures ens)) -> begin
(

let uu____14977 = (

let uu____14984 = (

let uu____14991 = (thunk_ens ens)
in (uu____14991)::(nil_pat)::[])
in (req)::uu____14984)
in (unit_tm)::uu____14977)
end
| (ens)::(smtpat)::[] when ((((

let uu____15040 = (is_requires ens)
in (not (uu____15040))) && (

let uu____15042 = (is_smt_pat ens)
in (not (uu____15042)))) && (

let uu____15044 = (is_decreases ens)
in (not (uu____15044)))) && (is_smt_pat smtpat)) -> begin
(

let uu____15045 = (

let uu____15052 = (

let uu____15059 = (thunk_ens ens)
in (uu____15059)::(smtpat)::[])
in (req_true)::uu____15052)
in (unit_tm)::uu____15045)
end
| (ens)::(dec)::[] when ((is_ensures ens) && (is_decreases dec)) -> begin
(

let uu____15106 = (

let uu____15113 = (

let uu____15120 = (thunk_ens ens)
in (uu____15120)::(nil_pat)::(dec)::[])
in (req_true)::uu____15113)
in (unit_tm)::uu____15106)
end
| (ens)::(dec)::(smtpat)::[] when (((is_ensures ens) && (is_decreases dec)) && (is_smt_pat smtpat)) -> begin
(

let uu____15180 = (

let uu____15187 = (

let uu____15194 = (thunk_ens ens)
in (uu____15194)::(smtpat)::(dec)::[])
in (req_true)::uu____15187)
in (unit_tm)::uu____15180)
end
| (req)::(ens)::(dec)::[] when (((is_requires req) && (is_ensures ens)) && (is_decreases dec)) -> begin
(

let uu____15254 = (

let uu____15261 = (

let uu____15268 = (thunk_ens ens)
in (uu____15268)::(nil_pat)::(dec)::[])
in (req)::uu____15261)
in (unit_tm)::uu____15254)
end
| (req)::(ens)::(smtpat)::[] when (((is_requires req) && (is_ensures ens)) && (is_smt_pat smtpat)) -> begin
(

let uu____15328 = (

let uu____15335 = (

let uu____15342 = (thunk_ens ens)
in (uu____15342)::(smtpat)::[])
in (req)::uu____15335)
in (unit_tm)::uu____15328)
end
| (req)::(ens)::(dec)::(smtpat)::[] when ((((is_requires req) && (is_ensures ens)) && (is_smt_pat smtpat)) && (is_decreases dec)) -> begin
(

let uu____15407 = (

let uu____15414 = (

let uu____15421 = (thunk_ens ens)
in (uu____15421)::(dec)::(smtpat)::[])
in (req)::uu____15414)
in (unit_tm)::uu____15407)
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

let uu____15483 = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_effect_name_and_attributes env) l)
in ((uu____15483), (args)))
end
| FStar_Parser_AST.Name (l) when ((

let uu____15511 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Ident.lid_equals uu____15511 FStar_Parser_Const.prims_lid)) && (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Tot")) -> begin
(

let uu____15512 = (

let uu____15519 = (FStar_Ident.set_lid_range FStar_Parser_Const.effect_Tot_lid head1.FStar_Parser_AST.range)
in ((uu____15519), ([])))
in ((uu____15512), (args)))
end
| FStar_Parser_AST.Name (l) when ((

let uu____15537 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Ident.lid_equals uu____15537 FStar_Parser_Const.prims_lid)) && (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "GTot")) -> begin
(

let uu____15538 = (

let uu____15545 = (FStar_Ident.set_lid_range FStar_Parser_Const.effect_GTot_lid head1.FStar_Parser_AST.range)
in ((uu____15545), ([])))
in ((uu____15538), (args)))
end
| FStar_Parser_AST.Name (l) when (((Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Type") || (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Type0")) || (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Effect")) -> begin
(

let uu____15561 = (

let uu____15568 = (FStar_Ident.set_lid_range FStar_Parser_Const.effect_Tot_lid head1.FStar_Parser_AST.range)
in ((uu____15568), ([])))
in ((uu____15561), ((((t1), (FStar_Parser_AST.Nothing)))::[])))
end
| uu____15591 when allow_type_promotion -> begin
(

let default_effect = (

let uu____15593 = (FStar_Options.ml_ish ())
in (match (uu____15593) with
| true -> begin
FStar_Parser_Const.effect_ML_lid
end
| uu____15594 -> begin
((

let uu____15596 = (FStar_Options.warn_default_effects ())
in (match (uu____15596) with
| true -> begin
(FStar_Errors.log_issue head1.FStar_Parser_AST.range ((FStar_Errors.Warning_UseDefaultEffect), ("Using default effect Tot")))
end
| uu____15597 -> begin
()
end));
FStar_Parser_Const.effect_Tot_lid;
)
end))
in (

let uu____15598 = (

let uu____15605 = (FStar_Ident.set_lid_range default_effect head1.FStar_Parser_AST.range)
in ((uu____15605), ([])))
in ((uu____15598), ((((t1), (FStar_Parser_AST.Nothing)))::[]))))
end
| uu____15628 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_EffectNotFound), ("Expected an effect constructor")) t1.FStar_Parser_AST.range)
end)
end)))
in (

let uu____15645 = (pre_process_comp_typ t)
in (match (uu____15645) with
| ((eff, cattributes), args) -> begin
((match ((Prims.op_Equality (FStar_List.length args) (Prims.parse_int "0"))) with
| true -> begin
(

let uu____15694 = (

let uu____15699 = (

let uu____15700 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" uu____15700))
in ((FStar_Errors.Fatal_NotEnoughArgsToEffect), (uu____15699)))
in (fail1 uu____15694))
end
| uu____15701 -> begin
()
end);
(

let is_universe = (fun uu____15711 -> (match (uu____15711) with
| (uu____15716, imp) -> begin
(Prims.op_Equality imp FStar_Parser_AST.UnivApp)
end))
in (

let uu____15718 = (FStar_Util.take is_universe args)
in (match (uu____15718) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun uu____15777 -> (match (uu____15777) with
| (u, imp) -> begin
(desugar_universe u)
end)) universes)
in (

let uu____15784 = (

let uu____15799 = (FStar_List.hd args1)
in (

let uu____15808 = (FStar_List.tl args1)
in ((uu____15799), (uu____15808))))
in (match (uu____15784) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (FStar_Pervasives_Native.fst result_arg))
in (

let rest1 = (desugar_args env rest)
in (

let uu____15863 = (

let is_decrease = (fun uu____15901 -> (match (uu____15901) with
| (t1, uu____15911) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____15921; FStar_Syntax_Syntax.vars = uu____15922}, (uu____15923)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.decreases_lid)
end
| uu____15962 -> begin
false
end)
end))
in (FStar_All.pipe_right rest1 (FStar_List.partition is_decrease)))
in (match (uu____15863) with
| (dec, rest2) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun uu____16078 -> (match (uu____16078) with
| (t1, uu____16088) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____16097, ((arg, uu____16099))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| uu____16138 -> begin
(failwith "impos")
end)
end))))
in (

let no_additional_args = (

let is_empty = (fun l -> (match (l) with
| [] -> begin
true
end
| uu____16155 -> begin
false
end))
in ((((is_empty decreases_clause) && (is_empty rest2)) && (is_empty cattributes)) && (is_empty universes1)))
in (

let uu____16166 = (no_additional_args && (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid))
in (match (uu____16166) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end
| uu____16169 -> begin
(

let uu____16170 = (no_additional_args && (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid))
in (match (uu____16170) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end
| uu____16173 -> begin
(

let flags1 = (

let uu____16177 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Lemma_lid)
in (match (uu____16177) with
| true -> begin
(FStar_Syntax_Syntax.LEMMA)::[]
end
| uu____16180 -> begin
(

let uu____16181 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid)
in (match (uu____16181) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____16184 -> begin
(

let uu____16185 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_ML_lid)
in (match (uu____16185) with
| true -> begin
(FStar_Syntax_Syntax.MLEFFECT)::[]
end
| uu____16188 -> begin
(

let uu____16189 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid)
in (match (uu____16189) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____16192 -> begin
[]
end))
end))
end))
end))
in (

let flags2 = (FStar_List.append flags1 cattributes)
in (

let rest3 = (

let uu____16207 = (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Lemma_lid)
in (match (uu____16207) with
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

let uu____16296 = (FStar_Ident.set_lid_range FStar_Parser_Const.pattern_lid pat.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar uu____16296 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.mk_Tm_app nil ((((pattern), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag))))::[]) FStar_Pervasives_Native.None pat.FStar_Syntax_Syntax.pos)))
end
| uu____16317 -> begin
pat
end)
in (

let uu____16318 = (

let uu____16329 = (

let uu____16340 = (

let uu____16349 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat1), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) FStar_Pervasives_Native.None pat1.FStar_Syntax_Syntax.pos)
in ((uu____16349), (aq)))
in (uu____16340)::[])
in (ens)::uu____16329)
in (req)::uu____16318))
end
| uu____16390 -> begin
rest2
end)
end
| uu____16401 -> begin
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
| uu____16414 -> begin
FStar_Pervasives_Native.None
end))
in (

let mk1 = (fun t -> (FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let uu___303_16435 = t
in {FStar_Syntax_Syntax.n = uu___303_16435.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___303_16435.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let uu___304_16477 = b
in {FStar_Parser_AST.b = uu___304_16477.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___304_16477.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___304_16477.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env1 pats1 -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (

let uu____16540 = (desugar_term env1 e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) uu____16540)))))) pats1))
in (match (tk) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____16553 = (FStar_Syntax_DsEnv.push_bv env a)
in (match (uu____16553) with
| (env1, a1) -> begin
(

let a2 = (

let uu___305_16563 = a1
in {FStar_Syntax_Syntax.ppname = uu___305_16563.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___305_16563.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats1 = (desugar_pats env1 pats)
in (

let body1 = (desugar_formula env1 body)
in (

let body2 = (match (pats1) with
| [] -> begin
body1
end
| uu____16589 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_meta (((body1), (FStar_Syntax_Syntax.Meta_pattern (pats1))))))
end)
in (

let body3 = (

let uu____16603 = (

let uu____16606 = (

let uu____16607 = (FStar_Syntax_Syntax.mk_binder a2)
in (uu____16607)::[])
in (no_annot_abs uu____16606 body2))
in (FStar_All.pipe_left setpos uu____16603))
in (

let uu____16628 = (

let uu____16629 = (

let uu____16646 = (

let uu____16649 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Syntax_Syntax.fvar uu____16649 (FStar_Syntax_Syntax.Delta_constant_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None))
in (

let uu____16650 = (

let uu____16661 = (FStar_Syntax_Syntax.as_arg body3)
in (uu____16661)::[])
in ((uu____16646), (uu____16650))))
in FStar_Syntax_Syntax.Tm_app (uu____16629))
in (FStar_All.pipe_left mk1 uu____16628)))))))
end))
end
| uu____16700 -> begin
(failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body1 = (

let uu____16780 = (q ((rest), (pats), (body)))
in (

let uu____16787 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term uu____16780 uu____16787 FStar_Parser_AST.Formula)))
in (

let uu____16788 = (q (((b)::[]), ([]), (body1)))
in (FStar_Parser_AST.mk_term uu____16788 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| uu____16797 -> begin
(failwith "impossible")
end))
in (

let uu____16800 = (

let uu____16801 = (unparen f)
in uu____16801.FStar_Parser_AST.tm)
in (match (uu____16800) with
| FStar_Parser_AST.Labeled (f1, l, p) -> begin
(

let f2 = (desugar_formula env f1)
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((f2), (FStar_Syntax_Syntax.Meta_labeled (((l), (f2.FStar_Syntax_Syntax.pos), (p)))))))))
end
| FStar_Parser_AST.QForall ([], uu____16808, uu____16809) -> begin
(failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QExists ([], uu____16820, uu____16821) -> begin
(failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____16852 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env uu____16852)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____16888 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env uu____16888)))
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
| uu____16931 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Syntax_DsEnv.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list) = (fun env bs -> (

let uu____16936 = (FStar_List.fold_left (fun uu____16969 b -> (match (uu____16969) with
| (env1, out) -> begin
(

let tk = (desugar_binder env1 (

let uu___306_17013 = b
in {FStar_Parser_AST.b = uu___306_17013.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___306_17013.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___306_17013.FStar_Parser_AST.aqual}))
in (match (tk) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____17028 = (FStar_Syntax_DsEnv.push_bv env1 a)
in (match (uu____17028) with
| (env2, a1) -> begin
(

let a2 = (

let uu___307_17046 = a1
in {FStar_Syntax_Syntax.ppname = uu___307_17046.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___307_17046.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let uu____17047 = (

let uu____17054 = (

let uu____17059 = (trans_aqual env2 b.FStar_Parser_AST.aqual)
in ((a2), (uu____17059)))
in (uu____17054)::out)
in ((env2), (uu____17047))))
end))
end
| uu____17070 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_UnexpectedBinder), ("Unexpected binder")) b.FStar_Parser_AST.brange)
end))
end)) ((env), ([])) bs)
in (match (uu____16936) with
| (env1, tpars) -> begin
((env1), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.TAnnotated (x, t) -> begin
(

let uu____17141 = (desugar_typ env t)
in ((FStar_Pervasives_Native.Some (x)), (uu____17141)))
end
| FStar_Parser_AST.Annotated (x, t) -> begin
(

let uu____17146 = (desugar_typ env t)
in ((FStar_Pervasives_Native.Some (x)), (uu____17146)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____17150 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) FStar_Pervasives_Native.None x.FStar_Ident.idRange)
in ((FStar_Pervasives_Native.Some (x)), (uu____17150)))
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____17154 = (desugar_typ env t)
in ((FStar_Pervasives_Native.None), (uu____17154)))
end
| FStar_Parser_AST.Variable (x) -> begin
((FStar_Pervasives_Native.Some (x)), (FStar_Syntax_Syntax.tun))
end))
and as_binder : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  (FStar_Ident.ident FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term)  ->  ((FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) * FStar_Syntax_DsEnv.env) = (fun env imp uu___259_17162 -> (match (uu___259_17162) with
| (FStar_Pervasives_Native.None, k) -> begin
(

let uu____17184 = (FStar_Syntax_Syntax.null_binder k)
in ((uu____17184), (env)))
end
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____17201 = (FStar_Syntax_DsEnv.push_bv env a)
in (match (uu____17201) with
| (env1, a1) -> begin
(

let uu____17218 = (

let uu____17225 = (trans_aqual env1 imp)
in (((

let uu___308_17231 = a1
in {FStar_Syntax_Syntax.ppname = uu___308_17231.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___308_17231.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), (uu____17225)))
in ((uu____17218), (env1)))
end))
end))
and trans_aqual : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.aqual = (fun env uu___260_17239 -> (match (uu___260_17239) with
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)
end
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality)
end
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Meta (t)) -> begin
(

let uu____17243 = (

let uu____17244 = (desugar_term env t)
in FStar_Syntax_Syntax.Meta (uu____17244))
in FStar_Pervasives_Native.Some (uu____17243))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))


let binder_ident : FStar_Parser_AST.binder  ->  FStar_Ident.ident FStar_Pervasives_Native.option = (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.TAnnotated (x, uu____17259) -> begin
FStar_Pervasives_Native.Some (x)
end
| FStar_Parser_AST.Annotated (x, uu____17261) -> begin
FStar_Pervasives_Native.Some (x)
end
| FStar_Parser_AST.TVariable (x) -> begin
FStar_Pervasives_Native.Some (x)
end
| FStar_Parser_AST.Variable (x) -> begin
FStar_Pervasives_Native.Some (x)
end
| FStar_Parser_AST.NoName (uu____17264) -> begin
FStar_Pervasives_Native.None
end))


let binder_idents : FStar_Parser_AST.binder Prims.list  ->  FStar_Ident.ident Prims.list = (fun bs -> (FStar_List.collect (fun b -> (

let uu____17281 = (binder_ident b)
in (FStar_Common.list_of_option uu____17281))) bs))


let mk_data_discriminators : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_DsEnv.env  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun quals env datas -> (

let quals1 = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___261_17317 -> (match (uu___261_17317) with
| FStar_Syntax_Syntax.NoExtract -> begin
true
end
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____17318 -> begin
false
end))))
in (

let quals2 = (fun q -> (

let uu____17331 = ((

let uu____17334 = (FStar_Syntax_DsEnv.iface env)
in (not (uu____17334))) || (FStar_Syntax_DsEnv.admitted_iface env))
in (match (uu____17331) with
| true -> begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals1)
end
| uu____17337 -> begin
(FStar_List.append q quals1)
end)))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (

let uu____17348 = (FStar_Ident.range_of_lid disc_name)
in (

let uu____17349 = (quals2 ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((disc_name), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = uu____17348; FStar_Syntax_Syntax.sigquals = uu____17349; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))))))))


let mk_indexed_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  FStar_Syntax_DsEnv.env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq env lid fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let uu____17388 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____17426 -> (match (uu____17426) with
| (x, uu____17436) -> begin
(

let uu____17441 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____17441) with
| (field_name, uu____17449) -> begin
(

let only_decl = (((

let uu____17453 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____17453)) || (Prims.op_disEquality fvq FStar_Syntax_Syntax.Data_ctor)) || (

let uu____17455 = (

let uu____17456 = (FStar_Syntax_DsEnv.current_module env)
in uu____17456.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____17455)))
in (

let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____17472 = (FStar_List.filter (fun uu___262_17476 -> (match (uu___262_17476) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____17477 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____17472)
end
| uu____17478 -> begin
q
end))
in (

let quals1 = (

let iquals1 = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___263_17490 -> (match (uu___263_17490) with
| FStar_Syntax_Syntax.NoExtract -> begin
true
end
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____17491 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals1)))
in (

let decl = (

let uu____17493 = (FStar_Ident.range_of_lid field_name)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = uu____17493; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____17496 -> begin
(

let dd = (

let uu____17498 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____17498) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "1")))
end
| uu____17501 -> begin
FStar_Syntax_Syntax.Delta_equational_at_level ((Prims.parse_int "1"))
end))
in (

let lb = (

let uu____17503 = (

let uu____17508 = (FStar_Syntax_Syntax.lid_as_fv field_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____17508))
in {FStar_Syntax_Syntax.lbname = uu____17503; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbattrs = []; FStar_Syntax_Syntax.lbpos = FStar_Range.dummyRange})
in (

let impl = (

let uu____17512 = (

let uu____17513 = (

let uu____17520 = (

let uu____17523 = (

let uu____17524 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____17524 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____17523)::[])
in ((((false), ((lb)::[]))), (uu____17520)))
in FStar_Syntax_Syntax.Sig_let (uu____17513))
in {FStar_Syntax_Syntax.sigel = uu____17512; FStar_Syntax_Syntax.sigrng = p; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____17537 -> begin
(decl)::(impl)::[]
end))))
end))))))
end))
end))))
in (FStar_All.pipe_right uu____17388 FStar_List.flatten))))


let mk_data_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____17568, t, uu____17570, n1, uu____17572) when (

let uu____17577 = (FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid)
in (not (uu____17577))) -> begin
(

let uu____17578 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____17578) with
| (formals, uu____17596) -> begin
(match (formals) with
| [] -> begin
[]
end
| uu____17625 -> begin
(

let filter_records = (fun uu___264_17641 -> (match (uu___264_17641) with
| FStar_Syntax_Syntax.RecordConstructor (uu____17644, fns) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| uu____17656 -> begin
FStar_Pervasives_Native.None
end))
in (

let fv_qual = (

let uu____17658 = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals filter_records)
in (match (uu____17658) with
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
| uu____17667 -> begin
iquals
end)
in (

let uu____17668 = (FStar_Util.first_N n1 formals)
in (match (uu____17668) with
| (uu____17697, rest) -> begin
(mk_indexed_projector_names iquals1 fv_qual env lid rest)
end)))))
end)
end))
end
| uu____17731 -> begin
[]
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars kopt t lids quals rng -> (

let dd = (

let uu____17809 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____17809) with
| true -> begin
(

let uu____17812 = (FStar_Syntax_Util.incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (uu____17812))
end
| uu____17813 -> begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end))
in (

let lb = (

let uu____17815 = (

let uu____17820 = (FStar_Syntax_Syntax.lid_as_fv lid dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____17820))
in (

let uu____17821 = (match ((FStar_Util.is_some kopt)) with
| true -> begin
(

let uu____17826 = (

let uu____17829 = (FStar_All.pipe_right kopt FStar_Util.must)
in (FStar_Syntax_Syntax.mk_Total uu____17829))
in (FStar_Syntax_Util.arrow typars uu____17826))
end
| uu____17832 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let uu____17833 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = uu____17815; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____17821; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____17833; FStar_Syntax_Syntax.lbattrs = []; FStar_Syntax_Syntax.lbpos = rng})))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (lids))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))


let rec desugar_tycon : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.decl  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d quals tcs -> (

let rng = d.FStar_Parser_AST.drange
in (

let tycon_id = (fun uu___265_17884 -> (match (uu___265_17884) with
| FStar_Parser_AST.TyconAbstract (id1, uu____17886, uu____17887) -> begin
id1
end
| FStar_Parser_AST.TyconAbbrev (id1, uu____17897, uu____17898, uu____17899) -> begin
id1
end
| FStar_Parser_AST.TyconRecord (id1, uu____17909, uu____17910, uu____17911) -> begin
id1
end
| FStar_Parser_AST.TyconVariant (id1, uu____17941, uu____17942, uu____17943) -> begin
id1
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (x, uu____17987) -> begin
(

let uu____17988 = (

let uu____17989 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____17989))
in (FStar_Parser_AST.mk_term uu____17988 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| FStar_Parser_AST.Variable (x) -> begin
(

let uu____17991 = (

let uu____17992 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____17992))
in (FStar_Parser_AST.mk_term uu____17991 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| FStar_Parser_AST.TAnnotated (a, uu____17994) -> begin
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
| uu____18025 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (

let uu____18033 = (

let uu____18034 = (

let uu____18041 = (binder_to_term b)
in ((out), (uu____18041), ((imp_of_aqual b))))
in FStar_Parser_AST.App (uu____18034))
in (FStar_Parser_AST.mk_term uu____18033 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun uu___266_18053 -> (match (uu___266_18053) with
| FStar_Parser_AST.TyconRecord (id1, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id1.FStar_Ident.idText)), (id1.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun uu____18108 -> (match (uu____18108) with
| (x, t, uu____18119) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated (((x), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr FStar_Pervasives_Native.None)
end)) fields)
in (

let result = (

let uu____18125 = (

let uu____18126 = (

let uu____18127 = (FStar_Ident.lid_of_ids ((id1)::[]))
in FStar_Parser_AST.Var (uu____18127))
in (FStar_Parser_AST.mk_term uu____18126 id1.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____18125 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id1.FStar_Ident.idRange FStar_Parser_AST.Type_level)
in (

let names1 = (

let uu____18134 = (binder_idents parms)
in (id1)::uu____18134)
in ((FStar_List.iter (fun uu____18152 -> (match (uu____18152) with
| (f, uu____18162, uu____18163) -> begin
(

let uu____18168 = (FStar_Util.for_some (fun i -> (FStar_Ident.ident_equals f i)) names1)
in (match (uu____18168) with
| true -> begin
(

let uu____18171 = (

let uu____18176 = (

let uu____18177 = (FStar_Ident.string_of_ident f)
in (FStar_Util.format1 "Field %s shadows the record\'s name or a parameter of it, please rename it" uu____18177))
in ((FStar_Errors.Error_FieldShadow), (uu____18176)))
in (FStar_Errors.raise_error uu____18171 f.FStar_Ident.idRange))
end
| uu____18178 -> begin
()
end))
end)) fields);
(

let uu____18179 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____18206 -> (match (uu____18206) with
| (x, uu____18216, uu____18217) -> begin
x
end))))
in ((FStar_Parser_AST.TyconVariant (((id1), (parms), (kopt), ((((constrName), (FStar_Pervasives_Native.Some (constrTyp)), (FStar_Pervasives_Native.None), (false)))::[])))), (uu____18179)));
))))))
end
| uu____18270 -> begin
(failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals1 _env mutuals uu___267_18309 -> (match (uu___267_18309) with
| FStar_Parser_AST.TyconAbstract (id1, binders, kopt) -> begin
(

let uu____18333 = (typars_of_binders _env binders)
in (match (uu____18333) with
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

let uu____18369 = (

let uu____18370 = (

let uu____18371 = (FStar_Ident.lid_of_ids ((id1)::[]))
in FStar_Parser_AST.Var (uu____18371))
in (FStar_Parser_AST.mk_term uu____18370 id1.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____18369 binders))
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
| uu____18382 -> begin
(failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env1 bs -> (

let uu____18424 = (FStar_List.fold_left (fun uu____18458 uu____18459 -> (match (((uu____18458), (uu____18459))) with
| ((env2, tps), (x, imp)) -> begin
(

let uu____18528 = (FStar_Syntax_DsEnv.push_bv env2 x.FStar_Syntax_Syntax.ppname)
in (match (uu____18528) with
| (env3, y) -> begin
((env3), ((((y), (imp)))::tps))
end))
end)) ((env1), ([])) bs)
in (match (uu____18424) with
| (env2, bs1) -> begin
((env2), ((FStar_List.rev bs1)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id1, bs, kopt))::[] -> begin
(

let kopt1 = (match (kopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____18619 = (tm_type_z id1.FStar_Ident.idRange)
in FStar_Pervasives_Native.Some (uu____18619))
end
| uu____18620 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id1), (bs), (kopt1)))
in (

let uu____18628 = (desugar_abstract_tc quals env [] tc)
in (match (uu____18628) with
| (uu____18641, uu____18642, se, uu____18644) -> begin
(

let se1 = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, uu____18647, typars, k, [], []) -> begin
(

let quals1 = se.FStar_Syntax_Syntax.sigquals
in (

let quals2 = (match ((FStar_List.contains FStar_Syntax_Syntax.Assumption quals1)) with
| true -> begin
quals1
end
| uu____18662 -> begin
((

let uu____18664 = (

let uu____18665 = (FStar_Options.ml_ish ())
in (not (uu____18665)))
in (match (uu____18664) with
| true -> begin
(

let uu____18666 = (

let uu____18671 = (

let uu____18672 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Adding an implicit \'assume new\' qualifier on %s" uu____18672))
in ((FStar_Errors.Warning_AddImplicitAssumeNewQualifier), (uu____18671)))
in (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng uu____18666))
end
| uu____18673 -> begin
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
| uu____18681 -> begin
(

let uu____18682 = (

let uu____18689 = (

let uu____18690 = (

let uu____18705 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (uu____18705)))
in FStar_Syntax_Syntax.Tm_arrow (uu____18690))
in (FStar_Syntax_Syntax.mk uu____18689))
in (uu____18682 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
end)
in (

let uu___309_18721 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t))); FStar_Syntax_Syntax.sigrng = uu___309_18721.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = uu___309_18721.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___309_18721.FStar_Syntax_Syntax.sigattrs}))))
end
| uu____18722 -> begin
(failwith "Impossible")
end)
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se1)
in (

let env2 = (

let uu____18725 = (FStar_Syntax_DsEnv.qualify env1 id1)
in (FStar_Syntax_DsEnv.push_doc env1 uu____18725 d.FStar_Parser_AST.doc))
in ((env2), ((se1)::[])))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id1, binders, kopt, t))::[] -> begin
(

let uu____18738 = (typars_of_binders env binders)
in (match (uu____18738) with
| (env', typars) -> begin
(

let kopt1 = (match (kopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____18772 = (FStar_Util.for_some (fun uu___268_18774 -> (match (uu___268_18774) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| uu____18775 -> begin
false
end)) quals)
in (match (uu____18772) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.teff)
end
| uu____18778 -> begin
FStar_Pervasives_Native.None
end))
end
| FStar_Pervasives_Native.Some (k) -> begin
(

let uu____18780 = (desugar_term env' k)
in FStar_Pervasives_Native.Some (uu____18780))
end)
in (

let t0 = t
in (

let quals1 = (

let uu____18785 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___269_18789 -> (match (uu___269_18789) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| uu____18790 -> begin
false
end))))
in (match (uu____18785) with
| true -> begin
quals
end
| uu____18793 -> begin
(match ((Prims.op_Equality t0.FStar_Parser_AST.level FStar_Parser_AST.Formula)) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals
end
| uu____18796 -> begin
quals
end)
end))
in (

let qlid = (FStar_Syntax_DsEnv.qualify env id1)
in (

let se = (

let uu____18799 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Effect))
in (match (uu____18799) with
| true -> begin
(

let uu____18802 = (

let uu____18809 = (

let uu____18810 = (unparen t)
in uu____18810.FStar_Parser_AST.tm)
in (match (uu____18809) with
| FStar_Parser_AST.Construct (head1, args) -> begin
(

let uu____18831 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____18861))::args_rev -> begin
(

let uu____18873 = (

let uu____18874 = (unparen last_arg)
in uu____18874.FStar_Parser_AST.tm)
in (match (uu____18873) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____18902 -> begin
(([]), (args))
end))
end
| uu____18911 -> begin
(([]), (args))
end)
in (match (uu____18831) with
| (cattributes, args1) -> begin
(

let uu____18950 = (desugar_attributes env cattributes)
in (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((head1), (args1)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (uu____18950)))
end))
end
| uu____18961 -> begin
((t), ([]))
end))
in (match (uu____18802) with
| (t1, cattributes) -> begin
(

let c = (desugar_comp t1.FStar_Parser_AST.range false env' t1)
in (

let typars1 = (FStar_Syntax_Subst.close_binders typars)
in (

let c1 = (FStar_Syntax_Subst.close_comp typars1 c)
in (

let quals2 = (FStar_All.pipe_right quals1 (FStar_List.filter (fun uu___270_18983 -> (match (uu___270_18983) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| uu____18984 -> begin
true
end))))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((qlid), ([]), (typars1), (c1), ((FStar_List.append cattributes (FStar_Syntax_Util.comp_flags c1))))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))))
end))
end
| uu____18987 -> begin
(

let t1 = (desugar_typ env' t)
in (mk_typ_abbrev qlid [] typars kopt1 t1 ((qlid)::[]) quals1 rng))
end))
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se)
in (

let env2 = (FStar_Syntax_DsEnv.push_doc env1 qlid d.FStar_Parser_AST.doc)
in ((env2), ((se)::[])))))))))
end))
end
| (FStar_Parser_AST.TyconRecord (uu____18991))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let uu____19015 = (tycon_record_as_variant trec)
in (match (uu____19015) with
| (t, fs) -> begin
(

let uu____19032 = (

let uu____19035 = (

let uu____19036 = (

let uu____19045 = (

let uu____19048 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Ident.ids_of_lid uu____19048))
in ((uu____19045), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____19036))
in (uu____19035)::quals)
in (desugar_tycon env d uu____19032 ((t)::[])))
end)))
end
| (uu____19053)::uu____19054 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Syntax_DsEnv.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals1 et tc -> (

let uu____19221 = et
in (match (uu____19221) with
| (env1, tcs1) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (uu____19446) -> begin
(

let trec = tc
in (

let uu____19470 = (tycon_record_as_variant trec)
in (match (uu____19470) with
| (t, fs) -> begin
(

let uu____19529 = (

let uu____19532 = (

let uu____19533 = (

let uu____19542 = (

let uu____19545 = (FStar_Syntax_DsEnv.current_module env1)
in (FStar_Ident.ids_of_lid uu____19545))
in ((uu____19542), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____19533))
in (uu____19532)::quals1)
in (collect_tcs uu____19529 ((env1), (tcs1)) t))
end)))
end
| FStar_Parser_AST.TyconVariant (id1, binders, kopt, constructors) -> begin
(

let uu____19632 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id1), (binders), (kopt)))))
in (match (uu____19632) with
| (env2, uu____19692, se, tconstr) -> begin
((env2), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals1))))::tcs1))
end))
end
| FStar_Parser_AST.TyconAbbrev (id1, binders, kopt, t) -> begin
(

let uu____19841 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id1), (binders), (kopt)))))
in (match (uu____19841) with
| (env2, uu____19901, se, tconstr) -> begin
((env2), ((FStar_Util.Inr (((se), (binders), (t), (quals1))))::tcs1))
end))
end
| uu____20026 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_NonInductiveInMutuallyDefinedType), ("Mutually defined type contains a non-inductive element")) rng)
end)
end)))
in (

let uu____20073 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (uu____20073) with
| (env1, tcs1) -> begin
(

let tcs2 = (FStar_List.rev tcs1)
in (

let docs_tps_sigelts = (FStar_All.pipe_right tcs2 (FStar_List.collect (fun uu___272_20578 -> (match (uu___272_20578) with
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (id1, uvs, tpars, k, uu____20643, uu____20644); FStar_Syntax_Syntax.sigrng = uu____20645; FStar_Syntax_Syntax.sigquals = uu____20646; FStar_Syntax_Syntax.sigmeta = uu____20647; FStar_Syntax_Syntax.sigattrs = uu____20648}, binders, t, quals1) -> begin
(

let t1 = (

let uu____20711 = (typars_of_binders env1 binders)
in (match (uu____20711) with
| (env2, tpars1) -> begin
(

let uu____20738 = (push_tparams env2 tpars1)
in (match (uu____20738) with
| (env_tps, tpars2) -> begin
(

let t1 = (desugar_typ env_tps t)
in (

let tpars3 = (FStar_Syntax_Subst.close_binders tpars2)
in (FStar_Syntax_Subst.close tpars3 t1)))
end))
end))
in (

let uu____20767 = (

let uu____20786 = (mk_typ_abbrev id1 uvs tpars (FStar_Pervasives_Native.Some (k)) t1 ((id1)::[]) quals1 rng)
in ((((id1), (d.FStar_Parser_AST.doc))), ([]), (uu____20786)))
in (uu____20767)::[]))
end
| FStar_Util.Inl ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs1, tpars, k, mutuals1, uu____20846); FStar_Syntax_Syntax.sigrng = uu____20847; FStar_Syntax_Syntax.sigquals = tname_quals; FStar_Syntax_Syntax.sigmeta = uu____20849; FStar_Syntax_Syntax.sigattrs = uu____20850}, constrs, tconstr, quals1) -> begin
(

let mk_tot = (fun t -> (

let tot1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((tot1), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)))
in (

let tycon = ((tname), (tpars), (k))
in (

let uu____20948 = (push_tparams env1 tpars)
in (match (uu____20948) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun uu____21015 -> (match (uu____21015) with
| (x, uu____21027) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let tot_tconstr = (mk_tot tconstr)
in (

let uu____21031 = (

let uu____21058 = (FStar_All.pipe_right constrs (FStar_List.map (fun uu____21166 -> (match (uu____21166) with
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
| uu____21217 -> begin
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

let uu____21220 = (close env_tps t)
in (desugar_term env_tps uu____21220))
in (

let name = (FStar_Syntax_DsEnv.qualify env1 id1)
in (

let quals2 = (FStar_All.pipe_right tname_quals (FStar_List.collect (fun uu___271_21231 -> (match (uu___271_21231) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| uu____21243 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (

let uu____21251 = (

let uu____21270 = (

let uu____21271 = (

let uu____21272 = (

let uu____21287 = (

let uu____21288 = (

let uu____21291 = (FStar_All.pipe_right t1 FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total uu____21291))
in (FStar_Syntax_Util.arrow data_tpars uu____21288))
in ((name), (univs1), (uu____21287), (tname), (ntps), (mutuals1)))
in FStar_Syntax_Syntax.Sig_datacon (uu____21272))
in {FStar_Syntax_Syntax.sigel = uu____21271; FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in ((((name), (doc1))), (tps), (uu____21270)))
in ((name), (uu____21251))))))))
end))))
in (FStar_All.pipe_left FStar_List.split uu____21058))
in (match (uu____21031) with
| (constrNames, constrs1) -> begin
(((((tname), (d.FStar_Parser_AST.doc))), ([]), ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs1), (tpars), (k), (mutuals1), (constrNames))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = tname_quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))::constrs1
end))))
end))))
end
| uu____21506 -> begin
(failwith "impossible")
end))))
in (

let name_docs = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.map (fun uu____21632 -> (match (uu____21632) with
| (name_doc, uu____21658, uu____21659) -> begin
name_doc
end))))
in (

let sigelts = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.map (fun uu____21731 -> (match (uu____21731) with
| (uu____21750, uu____21751, se) -> begin
se
end))))
in (

let uu____21777 = (

let uu____21784 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle sigelts quals uu____21784 rng))
in (match (uu____21777) with
| (bundle, abbrevs) -> begin
(

let env2 = (FStar_Syntax_DsEnv.push_sigelt env0 bundle)
in (

let env3 = (FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env2 abbrevs)
in (

let data_ops = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.collect (fun uu____21846 -> (match (uu____21846) with
| (uu____21867, tps, se) -> begin
(mk_data_projector_names quals env3 se)
end))))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, uu____21914, tps, k, uu____21917, constrs) when ((FStar_List.length constrs) > (Prims.parse_int "1")) -> begin
(

let quals1 = se.FStar_Syntax_Syntax.sigquals
in (

let quals2 = (match (((FStar_List.contains FStar_Syntax_Syntax.Abstract quals1) && (not ((FStar_List.contains FStar_Syntax_Syntax.Private quals1))))) with
| true -> begin
(FStar_Syntax_Syntax.Private)::quals1
end
| uu____21935 -> begin
quals1
end)
in (mk_data_discriminators quals2 env3 constrs)))
end
| uu____21936 -> begin
[]
end))))
in (

let ops = (FStar_List.append discs data_ops)
in (

let env4 = (FStar_List.fold_left FStar_Syntax_DsEnv.push_sigelt env3 ops)
in (

let env5 = (FStar_List.fold_left (fun acc uu____21953 -> (match (uu____21953) with
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

let uu____21996 = (FStar_List.fold_left (fun uu____22031 b -> (match (uu____22031) with
| (env1, binders1) -> begin
(

let uu____22075 = (desugar_binder env1 b)
in (match (uu____22075) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____22098 = (as_binder env1 b.FStar_Parser_AST.aqual ((FStar_Pervasives_Native.Some (a)), (k)))
in (match (uu____22098) with
| (binder, env2) -> begin
((env2), ((binder)::binders1))
end))
end
| uu____22151 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_MissingNameInBinder), ("Missing name in binder")) b.FStar_Parser_AST.brange)
end))
end)) ((env), ([])) binders)
in (match (uu____21996) with
| (env1, binders1) -> begin
((env1), ((FStar_List.rev binders1)))
end)))


let push_reflect_effect : FStar_Syntax_DsEnv.env  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Ident.lid  ->  FStar_Range.range  ->  FStar_Syntax_DsEnv.env = (fun env quals effect_name range -> (

let uu____22252 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___273_22257 -> (match (uu___273_22257) with
| FStar_Syntax_Syntax.Reflectable (uu____22258) -> begin
true
end
| uu____22259 -> begin
false
end))))
in (match (uu____22252) with
| true -> begin
(

let monad_env = (FStar_Syntax_DsEnv.enter_monad_scope env effect_name.FStar_Ident.ident)
in (

let reflect_lid = (

let uu____22262 = (FStar_Ident.id_of_text "reflect")
in (FStar_All.pipe_right uu____22262 (FStar_Syntax_DsEnv.qualify monad_env)))
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (effect_name))::[]
in (

let refl_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = range; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (FStar_Syntax_DsEnv.push_sigelt env refl_decl)))))
end
| uu____22267 -> begin
env
end)))


let get_fail_attr : Prims.bool  ->  FStar_Syntax_Syntax.term  ->  (Prims.int Prims.list * Prims.bool) FStar_Pervasives_Native.option = (fun warn at1 -> (

let uu____22294 = (FStar_Syntax_Util.head_and_args at1)
in (match (uu____22294) with
| (hd1, args) -> begin
(

let uu____22345 = (

let uu____22360 = (

let uu____22361 = (FStar_Syntax_Subst.compress hd1)
in uu____22361.FStar_Syntax_Syntax.n)
in ((uu____22360), (args)))
in (match (uu____22345) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((a1, uu____22384))::[]) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_lax_attr)) -> begin
(

let uu____22419 = (

let uu____22424 = (

let uu____22433 = (FStar_Syntax_Embeddings.e_list FStar_Syntax_Embeddings.e_int)
in (FStar_Syntax_Embeddings.unembed uu____22433 a1))
in (uu____22424 true FStar_Syntax_Embeddings.id_norm_cb))
in (match (uu____22419) with
| FStar_Pervasives_Native.Some (es) when ((FStar_List.length es) > (Prims.parse_int "0")) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_lax_attr)
in (

let uu____22458 = (

let uu____22465 = (FStar_List.map FStar_BigInt.to_int_fs es)
in ((uu____22465), (b)))
in FStar_Pervasives_Native.Some (uu____22458)))
end
| uu____22476 -> begin
((match (warn) with
| true -> begin
(FStar_Errors.log_issue at1.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_UnappliedFail), ("Found ill-applied \'expect_failure\', argument should be a non-empty list of integer literals")))
end
| uu____22482 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), []) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_lax_attr)) -> begin
(

let b = (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_lax_attr)
in FStar_Pervasives_Native.Some ((([]), (b))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____22518) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_attr) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.fail_lax_attr)) -> begin
((match (warn) with
| true -> begin
(FStar_Errors.log_issue at1.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_UnappliedFail), ("Found ill-applied \'expect_failure\', argument should be a non-empty list of integer literals")))
end
| uu____22540 -> begin
()
end);
FStar_Pervasives_Native.None;
)
end
| uu____22547 -> begin
FStar_Pervasives_Native.None
end))
end)))


let rec desugar_effect : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.term Prims.list  ->  (FStar_Syntax_DsEnv.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_typ eff_decls attrs -> (

let env0 = env
in (

let monad_env = (FStar_Syntax_DsEnv.enter_monad_scope env eff_name)
in (

let uu____22716 = (desugar_binders monad_env eff_binders)
in (match (uu____22716) with
| (env1, binders) -> begin
(

let eff_t = (desugar_term env1 eff_typ)
in (

let for_free = (

let uu____22755 = (

let uu____22756 = (

let uu____22765 = (FStar_Syntax_Util.arrow_formals eff_t)
in (FStar_Pervasives_Native.fst uu____22765))
in (FStar_List.length uu____22756))
in (Prims.op_Equality uu____22755 (Prims.parse_int "1")))
in (

let mandatory_members = (

let rr_members = ("repr")::("return")::("bind")::[]
in (match (for_free) with
| true -> begin
rr_members
end
| uu____22804 -> begin
(FStar_List.append rr_members (("return_wp")::("bind_wp")::("if_then_else")::("ite_wp")::("stronger")::("close_wp")::("assert_p")::("assume_p")::("null_wp")::("trivial")::[]))
end))
in (

let name_of_eff_decl = (fun decl -> (match (decl.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____22811, uu____22812, ((FStar_Parser_AST.TyconAbbrev (name, uu____22814, uu____22815, uu____22816), uu____22817))::[]) -> begin
(FStar_Ident.text_of_id name)
end
| uu____22850 -> begin
(failwith "Malformed effect member declaration.")
end))
in (

let uu____22851 = (FStar_List.partition (fun decl -> (

let uu____22863 = (name_of_eff_decl decl)
in (FStar_List.mem uu____22863 mandatory_members))) eff_decls)
in (match (uu____22851) with
| (mandatory_members_decls, actions) -> begin
(

let uu____22880 = (FStar_All.pipe_right mandatory_members_decls (FStar_List.fold_left (fun uu____22909 decl -> (match (uu____22909) with
| (env2, out) -> begin
(

let uu____22929 = (desugar_decl env2 decl)
in (match (uu____22929) with
| (env3, ses) -> begin
(

let uu____22942 = (

let uu____22945 = (FStar_List.hd ses)
in (uu____22945)::out)
in ((env3), (uu____22942)))
end))
end)) ((env1), ([]))))
in (match (uu____22880) with
| (env2, decls) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (

let actions_docs = (FStar_All.pipe_right actions (FStar_List.map (fun d1 -> (match (d1.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____23014, uu____23015, ((FStar_Parser_AST.TyconAbbrev (name, action_params, uu____23018, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (uu____23019, ((def, uu____23021))::((cps_type, uu____23023))::[]); FStar_Parser_AST.range = uu____23024; FStar_Parser_AST.level = uu____23025}), doc1))::[]) when (not (for_free)) -> begin
(

let uu____23077 = (desugar_binders env2 action_params)
in (match (uu____23077) with
| (env3, action_params1) -> begin
(

let action_params2 = (FStar_Syntax_Subst.close_binders action_params1)
in (

let uu____23115 = (

let uu____23116 = (FStar_Syntax_DsEnv.qualify env3 name)
in (

let uu____23117 = (

let uu____23118 = (desugar_term env3 def)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____23118))
in (

let uu____23125 = (

let uu____23126 = (desugar_typ env3 cps_type)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____23126))
in {FStar_Syntax_Syntax.action_name = uu____23116; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = action_params2; FStar_Syntax_Syntax.action_defn = uu____23117; FStar_Syntax_Syntax.action_typ = uu____23125})))
in ((uu____23115), (doc1))))
end))
end
| FStar_Parser_AST.Tycon (uu____23135, uu____23136, ((FStar_Parser_AST.TyconAbbrev (name, action_params, uu____23139, defn), doc1))::[]) when for_free -> begin
(

let uu____23174 = (desugar_binders env2 action_params)
in (match (uu____23174) with
| (env3, action_params1) -> begin
(

let action_params2 = (FStar_Syntax_Subst.close_binders action_params1)
in (

let uu____23212 = (

let uu____23213 = (FStar_Syntax_DsEnv.qualify env3 name)
in (

let uu____23214 = (

let uu____23215 = (desugar_term env3 defn)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____23215))
in {FStar_Syntax_Syntax.action_name = uu____23213; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = action_params2; FStar_Syntax_Syntax.action_defn = uu____23214; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
in ((uu____23212), (doc1))))
end))
end
| uu____23224 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_MalformedActionDeclaration), ("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples).")) d1.FStar_Parser_AST.drange)
end))))
in (

let actions1 = (FStar_List.map FStar_Pervasives_Native.fst actions_docs)
in (

let eff_t1 = (FStar_Syntax_Subst.close binders1 eff_t)
in (

let lookup1 = (fun s -> (

let l = (

let uu____23256 = (FStar_Ident.mk_ident ((s), (d.FStar_Parser_AST.drange)))
in (FStar_Syntax_DsEnv.qualify env2 uu____23256))
in (

let uu____23257 = (

let uu____23258 = (FStar_Syntax_DsEnv.fail_or env2 (FStar_Syntax_DsEnv.try_lookup_definition env2) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders1) uu____23258))
in (([]), (uu____23257)))))
in (

let mname = (FStar_Syntax_DsEnv.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange (FStar_Pervasives_Native.Some (mname))) quals)
in (

let se = (match (for_free) with
| true -> begin
(

let dummy_tscheme = (

let uu____23275 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (([]), (uu____23275)))
in (

let uu____23282 = (

let uu____23283 = (

let uu____23284 = (

let uu____23285 = (lookup1 "repr")
in (FStar_Pervasives_Native.snd uu____23285))
in (

let uu____23294 = (lookup1 "return")
in (

let uu____23295 = (lookup1 "bind")
in (

let uu____23296 = (FStar_List.map (desugar_term env2) attrs)
in {FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = eff_t1; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = uu____23284; FStar_Syntax_Syntax.return_repr = uu____23294; FStar_Syntax_Syntax.bind_repr = uu____23295; FStar_Syntax_Syntax.actions = actions1; FStar_Syntax_Syntax.eff_attrs = uu____23296}))))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____23283))
in {FStar_Syntax_Syntax.sigel = uu____23282; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qualifiers; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))
end
| uu____23299 -> begin
(

let rr = (FStar_Util.for_some (fun uu___274_23302 -> (match (uu___274_23302) with
| FStar_Syntax_Syntax.Reifiable -> begin
true
end
| FStar_Syntax_Syntax.Reflectable (uu____23303) -> begin
true
end
| uu____23304 -> begin
false
end)) qualifiers)
in (

let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in (

let uu____23318 = (

let uu____23319 = (

let uu____23320 = (lookup1 "return_wp")
in (

let uu____23321 = (lookup1 "bind_wp")
in (

let uu____23322 = (lookup1 "if_then_else")
in (

let uu____23323 = (lookup1 "ite_wp")
in (

let uu____23324 = (lookup1 "stronger")
in (

let uu____23325 = (lookup1 "close_wp")
in (

let uu____23326 = (lookup1 "assert_p")
in (

let uu____23327 = (lookup1 "assume_p")
in (

let uu____23328 = (lookup1 "null_wp")
in (

let uu____23329 = (lookup1 "trivial")
in (

let uu____23330 = (match (rr) with
| true -> begin
(

let uu____23331 = (lookup1 "repr")
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____23331))
end
| uu____23346 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let uu____23347 = (match (rr) with
| true -> begin
(lookup1 "return")
end
| uu____23348 -> begin
un_ts
end)
in (

let uu____23349 = (match (rr) with
| true -> begin
(lookup1 "bind")
end
| uu____23350 -> begin
un_ts
end)
in (

let uu____23351 = (FStar_List.map (desugar_term env2) attrs)
in {FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = eff_t1; FStar_Syntax_Syntax.ret_wp = uu____23320; FStar_Syntax_Syntax.bind_wp = uu____23321; FStar_Syntax_Syntax.if_then_else = uu____23322; FStar_Syntax_Syntax.ite_wp = uu____23323; FStar_Syntax_Syntax.stronger = uu____23324; FStar_Syntax_Syntax.close_wp = uu____23325; FStar_Syntax_Syntax.assert_p = uu____23326; FStar_Syntax_Syntax.assume_p = uu____23327; FStar_Syntax_Syntax.null_wp = uu____23328; FStar_Syntax_Syntax.trivial = uu____23329; FStar_Syntax_Syntax.repr = uu____23330; FStar_Syntax_Syntax.return_repr = uu____23347; FStar_Syntax_Syntax.bind_repr = uu____23349; FStar_Syntax_Syntax.actions = actions1; FStar_Syntax_Syntax.eff_attrs = uu____23351}))))))))))))))
in FStar_Syntax_Syntax.Sig_new_effect (uu____23319))
in {FStar_Syntax_Syntax.sigel = uu____23318; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qualifiers; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))
end)
in (

let env3 = (FStar_Syntax_DsEnv.push_sigelt env0 se)
in (

let env4 = (FStar_Syntax_DsEnv.push_doc env3 mname d.FStar_Parser_AST.doc)
in (

let env5 = (FStar_All.pipe_right actions_docs (FStar_List.fold_left (fun env5 uu____23377 -> (match (uu____23377) with
| (a, doc1) -> begin
(

let env6 = (

let uu____23391 = (FStar_Syntax_Util.action_as_lb mname a a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_DsEnv.push_sigelt env5 uu____23391))
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

let uu____23415 = (desugar_binders env1 eff_binders)
in (match (uu____23415) with
| (env2, binders) -> begin
(

let uu____23452 = (

let uu____23463 = (head_and_args defn)
in (match (uu____23463) with
| (head1, args) -> begin
(

let lid = (match (head1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
l
end
| uu____23500 -> begin
(

let uu____23501 = (

let uu____23506 = (

let uu____23507 = (

let uu____23508 = (FStar_Parser_AST.term_to_string head1)
in (Prims.strcat uu____23508 " not found"))
in (Prims.strcat "Effect " uu____23507))
in ((FStar_Errors.Fatal_EffectNotFound), (uu____23506)))
in (FStar_Errors.raise_error uu____23501 d.FStar_Parser_AST.drange))
end)
in (

let ed = (FStar_Syntax_DsEnv.fail_or env2 (FStar_Syntax_DsEnv.try_lookup_effect_defn env2) lid)
in (

let uu____23510 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____23540))::args_rev -> begin
(

let uu____23552 = (

let uu____23553 = (unparen last_arg)
in uu____23553.FStar_Parser_AST.tm)
in (match (uu____23552) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____23581 -> begin
(([]), (args))
end))
end
| uu____23590 -> begin
(([]), (args))
end)
in (match (uu____23510) with
| (cattributes, args1) -> begin
(

let uu____23633 = (desugar_args env2 args1)
in (

let uu____23634 = (desugar_attributes env2 cattributes)
in ((lid), (ed), (uu____23633), (uu____23634))))
end))))
end))
in (match (uu____23452) with
| (ed_lid, ed, args, cattributes) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in ((match ((Prims.op_disEquality (FStar_List.length args) (FStar_List.length ed.FStar_Syntax_Syntax.binders))) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_ArgumentLengthMismatch), ("Unexpected number of arguments to effect constructor")) defn.FStar_Parser_AST.range)
end
| uu____23669 -> begin
()
end);
(

let uu____23670 = (FStar_Syntax_Subst.open_term' ed.FStar_Syntax_Syntax.binders FStar_Syntax_Syntax.t_unit)
in (match (uu____23670) with
| (ed_binders, uu____23684, ed_binders_opening) -> begin
(

let sub1 = (fun uu____23697 -> (match (uu____23697) with
| (us, x) -> begin
(

let x1 = (

let uu____23711 = (FStar_Syntax_Subst.shift_subst (FStar_List.length us) ed_binders_opening)
in (FStar_Syntax_Subst.subst uu____23711 x))
in (

let s = (FStar_Syntax_Util.subst_of_list ed_binders args)
in (

let uu____23715 = (

let uu____23716 = (FStar_Syntax_Subst.subst s x1)
in ((us), (uu____23716)))
in (FStar_Syntax_Subst.close_tscheme binders1 uu____23715))))
end))
in (

let mname = (FStar_Syntax_DsEnv.qualify env0 eff_name)
in (

let ed1 = (

let uu____23725 = (

let uu____23726 = (sub1 (([]), (ed.FStar_Syntax_Syntax.signature)))
in (FStar_Pervasives_Native.snd uu____23726))
in (

let uu____23741 = (sub1 ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____23742 = (sub1 ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____23743 = (sub1 ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____23744 = (sub1 ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____23745 = (sub1 ed.FStar_Syntax_Syntax.stronger)
in (

let uu____23746 = (sub1 ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____23747 = (sub1 ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____23748 = (sub1 ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____23749 = (sub1 ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____23750 = (sub1 ed.FStar_Syntax_Syntax.trivial)
in (

let uu____23751 = (

let uu____23752 = (sub1 (([]), (ed.FStar_Syntax_Syntax.repr)))
in (FStar_Pervasives_Native.snd uu____23752))
in (

let uu____23767 = (sub1 ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____23768 = (sub1 ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____23769 = (FStar_List.map (fun action -> (

let uu____23777 = (FStar_Syntax_DsEnv.qualify env2 action.FStar_Syntax_Syntax.action_unqualified_name)
in (

let uu____23778 = (

let uu____23779 = (sub1 (([]), (action.FStar_Syntax_Syntax.action_defn)))
in (FStar_Pervasives_Native.snd uu____23779))
in (

let uu____23794 = (

let uu____23795 = (sub1 (([]), (action.FStar_Syntax_Syntax.action_typ)))
in (FStar_Pervasives_Native.snd uu____23795))
in {FStar_Syntax_Syntax.action_name = uu____23777; FStar_Syntax_Syntax.action_unqualified_name = action.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = action.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = uu____23778; FStar_Syntax_Syntax.action_typ = uu____23794})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = cattributes; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = ed.FStar_Syntax_Syntax.univs; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = uu____23725; FStar_Syntax_Syntax.ret_wp = uu____23741; FStar_Syntax_Syntax.bind_wp = uu____23742; FStar_Syntax_Syntax.if_then_else = uu____23743; FStar_Syntax_Syntax.ite_wp = uu____23744; FStar_Syntax_Syntax.stronger = uu____23745; FStar_Syntax_Syntax.close_wp = uu____23746; FStar_Syntax_Syntax.assert_p = uu____23747; FStar_Syntax_Syntax.assume_p = uu____23748; FStar_Syntax_Syntax.null_wp = uu____23749; FStar_Syntax_Syntax.trivial = uu____23750; FStar_Syntax_Syntax.repr = uu____23751; FStar_Syntax_Syntax.return_repr = uu____23767; FStar_Syntax_Syntax.bind_repr = uu____23768; FStar_Syntax_Syntax.actions = uu____23769; FStar_Syntax_Syntax.eff_attrs = ed.FStar_Syntax_Syntax.eff_attrs})))))))))))))))
in (

let se = (

let for_free = (

let uu____23812 = (

let uu____23813 = (

let uu____23822 = (FStar_Syntax_Util.arrow_formals ed1.FStar_Syntax_Syntax.signature)
in (FStar_Pervasives_Native.fst uu____23822))
in (FStar_List.length uu____23813))
in (Prims.op_Equality uu____23812 (Prims.parse_int "1")))
in (

let uu____23853 = (

let uu____23856 = (trans_qual1 (FStar_Pervasives_Native.Some (mname)))
in (FStar_List.map uu____23856 quals))
in {FStar_Syntax_Syntax.sigel = (match (for_free) with
| true -> begin
FStar_Syntax_Syntax.Sig_new_effect_for_free (ed1)
end
| uu____23861 -> begin
FStar_Syntax_Syntax.Sig_new_effect (ed1)
end); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = uu____23853; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))
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

let uu____23878 = (FStar_Syntax_Util.action_as_lb mname a a.FStar_Syntax_Syntax.action_defn.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_DsEnv.push_sigelt env5 uu____23878))
in (FStar_Syntax_DsEnv.push_doc env6 a.FStar_Syntax_Syntax.action_name doc1)))) env4))
in (

let env6 = (

let uu____23880 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____23880) with
| true -> begin
(

let reflect_lid = (

let uu____23884 = (FStar_Ident.id_of_text "reflect")
in (FStar_All.pipe_right uu____23884 (FStar_Syntax_DsEnv.qualify monad_env)))
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]
in (

let refl_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (FStar_Syntax_DsEnv.push_sigelt env5 refl_decl))))
end
| uu____23889 -> begin
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

let uu____23894 = (match (d.FStar_Parser_AST.doc) with
| FStar_Pervasives_Native.None -> begin
((""), ([]))
end
| FStar_Pervasives_Native.Some (fsdoc) -> begin
fsdoc
end)
in (match (uu____23894) with
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
| FStar_Pervasives_Native.Some (uu____23945) -> begin
(

let uu____23946 = (

let uu____23947 = (FStar_Parser_ToDocument.signature_to_document d)
in (FStar_Pprint.pretty_string 0.950000 (Prims.parse_int "80") uu____23947))
in (Prims.strcat "\n  " uu____23946))
end
| uu____23948 -> begin
""
end)
in (

let other = (FStar_List.filter_map (fun uu____23961 -> (match (uu____23961) with
| (k, v1) -> begin
(match (((Prims.op_disEquality k "summary") && (Prims.op_disEquality k "type"))) with
| true -> begin
FStar_Pervasives_Native.Some ((Prims.strcat k (Prims.strcat ": " v1)))
end
| uu____23972 -> begin
FStar_Pervasives_Native.None
end)
end)) kv)
in (

let other1 = (match ((Prims.op_disEquality other [])) with
| true -> begin
(Prims.strcat (FStar_String.concat "\n" other) "\n")
end
| uu____23976 -> begin
""
end)
in (

let str = (Prims.strcat summary (Prims.strcat pp (Prims.strcat other1 text)))
in (

let fv = (

let uu____23979 = (FStar_Ident.lid_of_str "FStar.Pervasives.Comment")
in (FStar_Syntax_Syntax.fvar uu____23979 FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None))
in (

let arg = (FStar_Syntax_Util.exp_string str)
in (

let uu____23981 = (

let uu____23992 = (FStar_Syntax_Syntax.as_arg arg)
in (uu____23992)::[])
in (FStar_Syntax_Util.mk_app fv uu____23981)))))))))
end)))
and desugar_decl_aux : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (

let uu____24023 = (desugar_decl_noattrs env d)
in (match (uu____24023) with
| (env1, sigelts) -> begin
(

let attrs = d.FStar_Parser_AST.attrs
in (

let attrs1 = (FStar_List.map (desugar_term env1) attrs)
in (

let attrs2 = (

let uu____24041 = (mk_comment_attr d)
in (uu____24041)::attrs1)
in (

let uu____24042 = (FStar_List.mapi (fun i sigelt -> (match ((Prims.op_Equality i (Prims.parse_int "0"))) with
| true -> begin
(

let uu___310_24048 = sigelt
in {FStar_Syntax_Syntax.sigel = uu___310_24048.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___310_24048.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___310_24048.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___310_24048.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = attrs2})
end
| uu____24049 -> begin
(

let uu___311_24050 = sigelt
in (

let uu____24051 = (FStar_List.filter (fun at1 -> (

let uu____24057 = (get_fail_attr false at1)
in (FStar_Option.isNone uu____24057))) attrs2)
in {FStar_Syntax_Syntax.sigel = uu___311_24050.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___311_24050.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___311_24050.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___311_24050.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu____24051}))
end)) sigelts)
in ((env1), (uu____24042))))))
end)))
and desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (

let uu____24078 = (desugar_decl_aux env d)
in (match (uu____24078) with
| (env1, ses) -> begin
(

let uu____24089 = (FStar_All.pipe_right ses (FStar_List.map generalize_annotated_univs))
in ((env1), (uu____24089)))
end)))
and desugar_decl_noattrs : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (

let trans_qual1 = (trans_qual d.FStar_Parser_AST.drange)
in (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(

let p1 = (trans_pragma p)
in ((FStar_Syntax_Util.process_pragma p1 d.FStar_Parser_AST.drange);
(

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_pragma (p1); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in ((env), ((se)::[])));
))
end
| FStar_Parser_AST.Fsdoc (uu____24117) -> begin
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

let uu____24122 = (FStar_Syntax_DsEnv.iface env)
in (match (uu____24122) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_FriendInterface), ("\'friend\' declarations are not allowed in interfaces")) d.FStar_Parser_AST.drange)
end
| uu____24131 -> begin
(

let uu____24132 = (

let uu____24133 = (

let uu____24134 = (FStar_Syntax_DsEnv.dep_graph env)
in (

let uu____24135 = (FStar_Syntax_DsEnv.current_module env)
in (FStar_Parser_Dep.module_has_interface uu____24134 uu____24135)))
in (not (uu____24133)))
in (match (uu____24132) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_FriendInterface), ("\'friend\' declarations are not allowed in modules that lack interfaces")) d.FStar_Parser_AST.drange)
end
| uu____24144 -> begin
(

let uu____24145 = (

let uu____24146 = (

let uu____24147 = (FStar_Syntax_DsEnv.dep_graph env)
in (FStar_Parser_Dep.module_has_interface uu____24147 lid))
in (not (uu____24146)))
in (match (uu____24145) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_FriendInterface), ("\'friend\' declarations cannot refer to modules that lack interfaces")) d.FStar_Parser_AST.drange)
end
| uu____24156 -> begin
(

let uu____24157 = (

let uu____24158 = (

let uu____24159 = (FStar_Syntax_DsEnv.dep_graph env)
in (FStar_Parser_Dep.deps_has_implementation uu____24159 lid))
in (not (uu____24158)))
in (match (uu____24157) with
| true -> begin
(FStar_Errors.raise_error ((FStar_Errors.Fatal_FriendInterface), ("\'friend\' module has not been loaded; recompute dependences (C-c C-r) if in interactive mode")) d.FStar_Parser_AST.drange)
end
| uu____24168 -> begin
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

let uu____24173 = (FStar_Syntax_DsEnv.push_module_abbrev env x l)
in ((uu____24173), ([])))
end
| FStar_Parser_AST.Tycon (is_effect, typeclass, tcs) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let quals1 = (match (is_effect) with
| true -> begin
(FStar_Parser_AST.Effect_qual)::quals
end
| uu____24199 -> begin
quals
end)
in (

let quals2 = (match (typeclass) with
| true -> begin
(match (tcs) with
| ((FStar_Parser_AST.TyconRecord (uu____24207), uu____24208))::[] -> begin
(FStar_Parser_AST.Noeq)::quals1
end
| uu____24247 -> begin
(FStar_Errors.raise_error ((FStar_Errors.Error_BadClassDecl), ("Ill-formed `class` declaration: definition must be a record type")) d.FStar_Parser_AST.drange)
end)
end
| uu____24258 -> begin
quals1
end)
in (

let tcs1 = (FStar_List.map (fun uu____24271 -> (match (uu____24271) with
| (x, uu____24279) -> begin
x
end)) tcs)
in (

let uu____24284 = (

let uu____24289 = (FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals2)
in (desugar_tycon env d uu____24289 tcs1))
in (match (uu____24284) with
| (env1, ses) -> begin
(

let mkclass = (fun lid -> (

let uu____24306 = (

let uu____24307 = (

let uu____24314 = (FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None FStar_Syntax_Syntax.tun)
in (FStar_Syntax_Syntax.mk_binder uu____24314))
in (uu____24307)::[])
in (

let uu____24327 = (

let uu____24330 = (FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.mk_class_lid)
in (

let uu____24333 = (

let uu____24344 = (

let uu____24353 = (

let uu____24354 = (FStar_Ident.string_of_lid lid)
in (FStar_Syntax_Util.exp_string uu____24354))
in (FStar_Syntax_Syntax.as_arg uu____24353))
in (uu____24344)::[])
in (FStar_Syntax_Util.mk_app uu____24330 uu____24333)))
in (FStar_Syntax_Util.abs uu____24306 uu____24327 FStar_Pervasives_Native.None))))
in (

let get_meths = (fun se -> (

let rec get_fname = (fun quals3 -> (match (quals3) with
| (FStar_Syntax_Syntax.Projector (uu____24393, id1))::uu____24395 -> begin
FStar_Pervasives_Native.Some (id1)
end
| (uu____24398)::quals4 -> begin
(get_fname quals4)
end
| [] -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____24402 = (get_fname se.FStar_Syntax_Syntax.sigquals)
in (match (uu____24402) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (id1) -> begin
(

let uu____24408 = (FStar_Syntax_DsEnv.qualify env1 id1)
in (uu____24408)::[])
end))))
in (

let rec splice_decl = (fun meths se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses1, uu____24429) -> begin
(FStar_List.concatMap (splice_decl meths) ses1)
end
| FStar_Syntax_Syntax.Sig_inductive_typ (lid, uu____24439, uu____24440, uu____24441, uu____24442, uu____24443) -> begin
(

let uu____24452 = (

let uu____24453 = (

let uu____24454 = (

let uu____24461 = (mkclass lid)
in ((meths), (uu____24461)))
in FStar_Syntax_Syntax.Sig_splice (uu____24454))
in {FStar_Syntax_Syntax.sigel = uu____24453; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (uu____24452)::[])
end
| uu____24464 -> begin
[]
end))
in (

let extra = (match (typeclass) with
| true -> begin
(

let meths = (FStar_List.concatMap get_meths ses)
in (FStar_List.concatMap (splice_decl meths) ses))
end
| uu____24473 -> begin
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
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatOp (uu____24494); FStar_Parser_AST.prange = uu____24495}, uu____24496))::[] -> begin
false
end
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____24505); FStar_Parser_AST.prange = uu____24506}, uu____24507))::[] -> begin
false
end
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatOp (uu____24522); FStar_Parser_AST.prange = uu____24523}, uu____24524); FStar_Parser_AST.prange = uu____24525}, uu____24526))::[] -> begin
false
end
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____24547); FStar_Parser_AST.prange = uu____24548}, uu____24549); FStar_Parser_AST.prange = uu____24550}, uu____24551))::[] -> begin
false
end
| ((p, uu____24579))::[] -> begin
(

let uu____24588 = (is_app_pattern p)
in (not (uu____24588)))
end
| uu____24589 -> begin
false
end))
in (match ((not (expand_toplevel_pattern))) with
| true -> begin
(

let lets1 = (FStar_List.map (fun x -> ((FStar_Pervasives_Native.None), (x))) lets)
in (

let as_inner_let = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets1), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)
in (

let uu____24662 = (desugar_term_maybe_top true env as_inner_let)
in (match (uu____24662) with
| (ds_lets, aq) -> begin
((check_no_aq aq);
(

let uu____24674 = (

let uu____24675 = (FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets)
in uu____24675.FStar_Syntax_Syntax.n)
in (match (uu____24674) with
| FStar_Syntax_Syntax.Tm_let (lbs, uu____24685) -> begin
(

let fvs = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals1 = (match (quals) with
| (uu____24718)::uu____24719 -> begin
(FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals)
end
| uu____24722 -> begin
(FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.collect (fun uu___275_24737 -> (match (uu___275_24737) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (uu____24740); FStar_Syntax_Syntax.lbunivs = uu____24741; FStar_Syntax_Syntax.lbtyp = uu____24742; FStar_Syntax_Syntax.lbeff = uu____24743; FStar_Syntax_Syntax.lbdef = uu____24744; FStar_Syntax_Syntax.lbattrs = uu____24745; FStar_Syntax_Syntax.lbpos = uu____24746} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____24758; FStar_Syntax_Syntax.lbtyp = uu____24759; FStar_Syntax_Syntax.lbeff = uu____24760; FStar_Syntax_Syntax.lbdef = uu____24761; FStar_Syntax_Syntax.lbattrs = uu____24762; FStar_Syntax_Syntax.lbpos = uu____24763} -> begin
(FStar_Syntax_DsEnv.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals2 = (

let uu____24777 = (FStar_All.pipe_right lets1 (FStar_Util.for_some (fun uu____24808 -> (match (uu____24808) with
| (uu____24821, (uu____24822, t)) -> begin
(Prims.op_Equality t.FStar_Parser_AST.level FStar_Parser_AST.Formula)
end))))
in (match (uu____24777) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals1
end
| uu____24838 -> begin
quals1
end))
in (

let lbs1 = (

let uu____24840 = (FStar_All.pipe_right quals2 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____24840) with
| true -> begin
(

let uu____24843 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu___312_24857 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let uu___313_24859 = fv
in {FStar_Syntax_Syntax.fv_name = uu___313_24859.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = uu___313_24859.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = uu___312_24857.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___312_24857.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___312_24857.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___312_24857.FStar_Syntax_Syntax.lbdef; FStar_Syntax_Syntax.lbattrs = uu___312_24857.FStar_Syntax_Syntax.lbattrs; FStar_Syntax_Syntax.lbpos = uu___312_24857.FStar_Syntax_Syntax.lbpos})))))
in (((FStar_Pervasives_Native.fst lbs)), (uu____24843)))
end
| uu____24864 -> begin
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
| uu____24886 -> begin
(failwith "Desugaring a let did not produce a let")
end));
)
end))))
end
| uu____24891 -> begin
(

let uu____24892 = (match (lets) with
| ((pat, body))::[] -> begin
((pat), (body))
end
| uu____24911 -> begin
(failwith "expand_toplevel_pattern should only allow single definition lets")
end)
in (match (uu____24892) with
| (pat, body) -> begin
(

let fresh_toplevel_name = (FStar_Ident.gen FStar_Range.dummyRange)
in (

let fresh_pat = (

let var_pat = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((fresh_toplevel_name), (FStar_Pervasives_Native.None)))) FStar_Range.dummyRange)
in (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat1, ty) -> begin
(

let uu___314_24947 = pat1
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed (((var_pat), (ty))); FStar_Parser_AST.prange = uu___314_24947.FStar_Parser_AST.prange})
end
| uu____24954 -> begin
var_pat
end))
in (

let main_let = (desugar_decl env (

let uu___315_24961 = d
in {FStar_Parser_AST.d = FStar_Parser_AST.TopLevelLet (((isrec), ((((fresh_pat), (body)))::[]))); FStar_Parser_AST.drange = uu___315_24961.FStar_Parser_AST.drange; FStar_Parser_AST.doc = uu___315_24961.FStar_Parser_AST.doc; FStar_Parser_AST.quals = (FStar_Parser_AST.Private)::d.FStar_Parser_AST.quals; FStar_Parser_AST.attrs = uu___315_24961.FStar_Parser_AST.attrs}))
in (

let build_projection = (fun uu____24997 id1 -> (match (uu____24997) with
| (env1, ses) -> begin
(

let main = (

let uu____25018 = (

let uu____25019 = (FStar_Ident.lid_of_ids ((fresh_toplevel_name)::[]))
in FStar_Parser_AST.Var (uu____25019))
in (FStar_Parser_AST.mk_term uu____25018 FStar_Range.dummyRange FStar_Parser_AST.Expr))
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

let uu____25069 = (desugar_decl env1 id_decl)
in (match (uu____25069) with
| (env2, ses') -> begin
((env2), ((FStar_List.append ses ses')))
end))))))))
end))
in (

let bvs = (

let uu____25087 = (gather_pattern_bound_vars true pat)
in (FStar_All.pipe_right uu____25087 FStar_Util.set_elements))
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

let uu____25110 = (close_fun env t)
in (desugar_term env uu____25110))
in (

let quals1 = (

let uu____25114 = ((FStar_Syntax_DsEnv.iface env) && (FStar_Syntax_DsEnv.admitted_iface env))
in (match (uu____25114) with
| true -> begin
(FStar_Parser_AST.Assumption)::quals
end
| uu____25117 -> begin
quals
end))
in (

let lid = (FStar_Syntax_DsEnv.qualify env id1)
in (

let se = (

let uu____25120 = (FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals1)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), ([]), (t1))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = uu____25120; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se)
in (

let env2 = (FStar_Syntax_DsEnv.push_doc env1 lid d.FStar_Parser_AST.doc)
in ((env2), ((se)::[])))))))))
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

let uu____25134 = (

let uu____25143 = (FStar_Syntax_Syntax.null_binder t)
in (uu____25143)::[])
in (

let uu____25162 = (

let uu____25165 = (FStar_Syntax_DsEnv.fail_or env (FStar_Syntax_DsEnv.try_lookup_lid env) FStar_Parser_Const.exn_lid)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____25165))
in (FStar_Syntax_Util.arrow uu____25134 uu____25162))))
end)
in (

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
in (desugar_effect env d quals eff_name eff_binders eff_typ eff_decls attrs)))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(

let lookup1 = (fun l1 -> (

let uu____25218 = (FStar_Syntax_DsEnv.try_lookup_effect_name env l1)
in (match (uu____25218) with
| FStar_Pervasives_Native.None -> begin
(

let uu____25221 = (

let uu____25226 = (

let uu____25227 = (

let uu____25228 = (FStar_Syntax_Print.lid_to_string l1)
in (Prims.strcat uu____25228 " not found"))
in (Prims.strcat "Effect name " uu____25227))
in ((FStar_Errors.Fatal_EffectNotFound), (uu____25226)))
in (FStar_Errors.raise_error uu____25221 d.FStar_Parser_AST.drange))
end
| FStar_Pervasives_Native.Some (l2) -> begin
l2
end)))
in (

let src = (lookup1 l.FStar_Parser_AST.msource)
in (

let dst = (lookup1 l.FStar_Parser_AST.mdest)
in (

let uu____25232 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(

let uu____25250 = (

let uu____25253 = (

let uu____25254 = (desugar_term env t)
in (([]), (uu____25254)))
in FStar_Pervasives_Native.Some (uu____25253))
in ((uu____25250), (FStar_Pervasives_Native.None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(

let uu____25267 = (

let uu____25270 = (

let uu____25271 = (desugar_term env wp)
in (([]), (uu____25271)))
in FStar_Pervasives_Native.Some (uu____25270))
in (

let uu____25278 = (

let uu____25281 = (

let uu____25282 = (desugar_term env t)
in (([]), (uu____25282)))
in FStar_Pervasives_Native.Some (uu____25281))
in ((uu____25267), (uu____25278))))
end
| FStar_Parser_AST.LiftForFree (t) -> begin
(

let uu____25294 = (

let uu____25297 = (

let uu____25298 = (desugar_term env t)
in (([]), (uu____25298)))
in FStar_Pervasives_Native.Some (uu____25297))
in ((FStar_Pervasives_Native.None), (uu____25294)))
end)
in (match (uu____25232) with
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

let uu____25332 = (

let uu____25333 = (

let uu____25340 = (FStar_List.map (FStar_Syntax_DsEnv.qualify env) ids)
in ((uu____25340), (t1)))
in FStar_Syntax_Syntax.Sig_splice (uu____25333))
in {FStar_Syntax_Syntax.sigel = uu____25332; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se)
in ((env1), ((se)::[])))))
end)))


let desugar_decls : env_t  ->  FStar_Parser_AST.decl Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env decls -> (

let uu____25366 = (FStar_List.fold_left (fun uu____25386 d -> (match (uu____25386) with
| (env1, sigelts) -> begin
(

let uu____25406 = (desugar_decl env1 d)
in (match (uu____25406) with
| (env2, se) -> begin
((env2), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls)
in (match (uu____25366) with
| (env1, sigelts) -> begin
(

let rec forward = (fun acc uu___277_25451 -> (match (uu___277_25451) with
| (se1)::(se2)::sigelts1 -> begin
(match (((se1.FStar_Syntax_Syntax.sigel), (se2.FStar_Syntax_Syntax.sigel))) with
| (FStar_Syntax_Syntax.Sig_declare_typ (uu____25465), FStar_Syntax_Syntax.Sig_let (uu____25466)) -> begin
(

let uu____25479 = (

let uu____25482 = (

let uu___316_25483 = se2
in (

let uu____25484 = (

let uu____25487 = (FStar_List.filter (fun uu___276_25501 -> (match (uu___276_25501) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____25505; FStar_Syntax_Syntax.vars = uu____25506}, uu____25507); FStar_Syntax_Syntax.pos = uu____25508; FStar_Syntax_Syntax.vars = uu____25509} when (

let uu____25536 = (

let uu____25537 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____25537))
in (Prims.op_Equality uu____25536 "FStar.Pervasives.Comment")) -> begin
true
end
| uu____25538 -> begin
false
end)) se1.FStar_Syntax_Syntax.sigattrs)
in (FStar_List.append uu____25487 se2.FStar_Syntax_Syntax.sigattrs))
in {FStar_Syntax_Syntax.sigel = uu___316_25483.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___316_25483.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___316_25483.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___316_25483.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu____25484}))
in (uu____25482)::(se1)::acc)
in (forward uu____25479 sigelts1))
end
| uu____25543 -> begin
(forward ((se1)::acc) ((se2)::sigelts1))
end)
end
| sigelts1 -> begin
(FStar_List.rev_append acc sigelts1)
end))
in (

let uu____25551 = (forward [] sigelts)
in ((env1), (uu____25551))))
end)))


let open_prims_all : (FStar_Parser_AST.decoration Prims.list  ->  FStar_Parser_AST.decl) Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Parser_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Parser_Const.all_lid)) FStar_Range.dummyRange))::[]


let desugar_modul_common : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let env1 = (match (((curmod), (m))) with
| (FStar_Pervasives_Native.None, uu____25612) -> begin
env
end
| (FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.name = prev_lid; FStar_Syntax_Syntax.declarations = uu____25616; FStar_Syntax_Syntax.exports = uu____25617; FStar_Syntax_Syntax.is_interface = uu____25618}), FStar_Parser_AST.Module (current_lid, uu____25620)) when ((FStar_Ident.lid_equals prev_lid current_lid) && (FStar_Options.interactive ())) -> begin
env
end
| (FStar_Pervasives_Native.Some (prev_mod), uu____25628) -> begin
(

let uu____25631 = (FStar_Syntax_DsEnv.finish_module_or_interface env prev_mod)
in (FStar_Pervasives_Native.fst uu____25631))
end)
in (

let uu____25636 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(

let uu____25672 = (FStar_Syntax_DsEnv.prepare_module_or_interface true admitted env1 mname FStar_Syntax_DsEnv.default_mii)
in ((uu____25672), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(

let uu____25689 = (FStar_Syntax_DsEnv.prepare_module_or_interface false false env1 mname FStar_Syntax_DsEnv.default_mii)
in ((uu____25689), (mname), (decls), (false)))
end)
in (match (uu____25636) with
| ((env2, pop_when_done), mname, decls, intf) -> begin
(

let uu____25719 = (desugar_decls env2 decls)
in (match (uu____25719) with
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

let uu____25781 = ((FStar_Options.interactive ()) && (

let uu____25783 = (

let uu____25784 = (

let uu____25785 = (FStar_Options.file_list ())
in (FStar_List.hd uu____25785))
in (FStar_Util.get_file_extension uu____25784))
in (FStar_List.mem uu____25783 (("fsti")::("fsi")::[]))))
in (match (uu____25781) with
| true -> begin
(as_interface m)
end
| uu____25788 -> begin
m
end))
in (

let uu____25789 = (desugar_modul_common curmod env m1)
in (match (uu____25789) with
| (env1, modul, pop_when_done) -> begin
(match (pop_when_done) with
| true -> begin
(

let uu____25807 = (FStar_Syntax_DsEnv.pop ())
in ((uu____25807), (modul)))
end
| uu____25808 -> begin
((env1), (modul))
end)
end))))


let desugar_modul : FStar_Syntax_DsEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (

let uu____25827 = (desugar_modul_common FStar_Pervasives_Native.None env m)
in (match (uu____25827) with
| (env1, modul, pop_when_done) -> begin
(

let uu____25841 = (FStar_Syntax_DsEnv.finish_module_or_interface env1 modul)
in (match (uu____25841) with
| (env2, modul1) -> begin
((

let uu____25853 = (FStar_Options.dump_module modul1.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____25853) with
| true -> begin
(

let uu____25854 = (FStar_Syntax_Print.modul_to_string modul1)
in (FStar_Util.print1 "Module after desugaring:\n%s\n" uu____25854))
end
| uu____25855 -> begin
()
end));
(

let uu____25856 = (match (pop_when_done) with
| true -> begin
(FStar_Syntax_DsEnv.export_interface modul1.FStar_Syntax_Syntax.name env2)
end
| uu____25857 -> begin
env2
end)
in ((uu____25856), (modul1)));
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
| uu____25878 -> begin
()
end);
res;
)));
))


let ast_modul_to_modul : FStar_Parser_AST.modul  ->  FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv = (fun modul env -> (with_options (fun uu____25903 -> (

let uu____25904 = (desugar_modul env modul)
in (match (uu____25904) with
| (e, m) -> begin
((m), (e))
end)))))


let decls_to_sigelts : FStar_Parser_AST.decl Prims.list  ->  FStar_Syntax_Syntax.sigelts FStar_Syntax_DsEnv.withenv = (fun decls env -> (with_options (fun uu____25945 -> (

let uu____25946 = (desugar_decls env decls)
in (match (uu____25946) with
| (env1, sigelts) -> begin
((sigelts), (env1))
end)))))


let partial_ast_modul_to_modul : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Parser_AST.modul  ->  FStar_Syntax_Syntax.modul FStar_Syntax_DsEnv.withenv = (fun modul a_modul env -> (with_options (fun uu____26000 -> (

let uu____26001 = (desugar_partial_modul modul env a_modul)
in (match (uu____26001) with
| (env1, modul1) -> begin
((modul1), (env1))
end)))))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Syntax_DsEnv.module_inclusion_info  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term)  ->  unit FStar_Syntax_DsEnv.withenv = (fun m mii erase_univs en -> (

let erase_univs_ed = (fun ed -> (

let erase_binders = (fun bs -> (match (bs) with
| [] -> begin
[]
end
| uu____26099 -> begin
(

let t = (

let uu____26109 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (FStar_Syntax_Syntax.t_unit), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (erase_univs uu____26109))
in (

let uu____26122 = (

let uu____26123 = (FStar_Syntax_Subst.compress t)
in uu____26123.FStar_Syntax_Syntax.n)
in (match (uu____26122) with
| FStar_Syntax_Syntax.Tm_abs (bs1, uu____26135, uu____26136) -> begin
bs1
end
| uu____26161 -> begin
(failwith "Impossible")
end)))
end))
in (

let uu____26170 = (

let uu____26177 = (erase_binders ed.FStar_Syntax_Syntax.binders)
in (FStar_Syntax_Subst.open_term' uu____26177 FStar_Syntax_Syntax.t_unit))
in (match (uu____26170) with
| (binders, uu____26179, binders_opening) -> begin
(

let erase_term = (fun t -> (

let uu____26187 = (

let uu____26188 = (FStar_Syntax_Subst.subst binders_opening t)
in (erase_univs uu____26188))
in (FStar_Syntax_Subst.close binders uu____26187)))
in (

let erase_tscheme = (fun uu____26206 -> (match (uu____26206) with
| (us, t) -> begin
(

let t1 = (

let uu____26226 = (FStar_Syntax_Subst.shift_subst (FStar_List.length us) binders_opening)
in (FStar_Syntax_Subst.subst uu____26226 t))
in (

let uu____26229 = (

let uu____26230 = (erase_univs t1)
in (FStar_Syntax_Subst.close binders uu____26230))
in (([]), (uu____26229))))
end))
in (

let erase_action = (fun action -> (

let opening = (FStar_Syntax_Subst.shift_subst (FStar_List.length action.FStar_Syntax_Syntax.action_univs) binders_opening)
in (

let erased_action_params = (match (action.FStar_Syntax_Syntax.action_params) with
| [] -> begin
[]
end
| uu____26253 -> begin
(

let bs = (

let uu____26263 = (FStar_Syntax_Subst.subst_binders opening action.FStar_Syntax_Syntax.action_params)
in (FStar_All.pipe_left erase_binders uu____26263))
in (

let t = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs (((bs), (FStar_Syntax_Syntax.t_unit), (FStar_Pervasives_Native.None)))) FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (

let uu____26303 = (

let uu____26304 = (

let uu____26307 = (FStar_Syntax_Subst.close binders t)
in (FStar_Syntax_Subst.compress uu____26307))
in uu____26304.FStar_Syntax_Syntax.n)
in (match (uu____26303) with
| FStar_Syntax_Syntax.Tm_abs (bs1, uu____26309, uu____26310) -> begin
bs1
end
| uu____26335 -> begin
(failwith "Impossible")
end))))
end)
in (

let erase_term1 = (fun t -> (

let uu____26342 = (

let uu____26343 = (FStar_Syntax_Subst.subst opening t)
in (erase_univs uu____26343))
in (FStar_Syntax_Subst.close binders uu____26342)))
in (

let uu___317_26344 = action
in (

let uu____26345 = (erase_term1 action.FStar_Syntax_Syntax.action_defn)
in (

let uu____26346 = (erase_term1 action.FStar_Syntax_Syntax.action_typ)
in {FStar_Syntax_Syntax.action_name = uu___317_26344.FStar_Syntax_Syntax.action_name; FStar_Syntax_Syntax.action_unqualified_name = uu___317_26344.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = erased_action_params; FStar_Syntax_Syntax.action_defn = uu____26345; FStar_Syntax_Syntax.action_typ = uu____26346})))))))
in (

let uu___318_26347 = ed
in (

let uu____26348 = (FStar_Syntax_Subst.close_binders binders)
in (

let uu____26349 = (erase_term ed.FStar_Syntax_Syntax.signature)
in (

let uu____26350 = (erase_tscheme ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____26351 = (erase_tscheme ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____26352 = (erase_tscheme ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____26353 = (erase_tscheme ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____26354 = (erase_tscheme ed.FStar_Syntax_Syntax.stronger)
in (

let uu____26355 = (erase_tscheme ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____26356 = (erase_tscheme ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____26357 = (erase_tscheme ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____26358 = (erase_tscheme ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____26359 = (erase_tscheme ed.FStar_Syntax_Syntax.trivial)
in (

let uu____26360 = (erase_term ed.FStar_Syntax_Syntax.repr)
in (

let uu____26361 = (erase_tscheme ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____26362 = (erase_tscheme ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____26363 = (FStar_List.map erase_action ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = uu___318_26347.FStar_Syntax_Syntax.cattributes; FStar_Syntax_Syntax.mname = uu___318_26347.FStar_Syntax_Syntax.mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = uu____26348; FStar_Syntax_Syntax.signature = uu____26349; FStar_Syntax_Syntax.ret_wp = uu____26350; FStar_Syntax_Syntax.bind_wp = uu____26351; FStar_Syntax_Syntax.if_then_else = uu____26352; FStar_Syntax_Syntax.ite_wp = uu____26353; FStar_Syntax_Syntax.stronger = uu____26354; FStar_Syntax_Syntax.close_wp = uu____26355; FStar_Syntax_Syntax.assert_p = uu____26356; FStar_Syntax_Syntax.assume_p = uu____26357; FStar_Syntax_Syntax.null_wp = uu____26358; FStar_Syntax_Syntax.trivial = uu____26359; FStar_Syntax_Syntax.repr = uu____26360; FStar_Syntax_Syntax.return_repr = uu____26361; FStar_Syntax_Syntax.bind_repr = uu____26362; FStar_Syntax_Syntax.actions = uu____26363; FStar_Syntax_Syntax.eff_attrs = uu___318_26347.FStar_Syntax_Syntax.eff_attrs}))))))))))))))))))))
end))))
in (

let push_sigelt1 = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ed) -> begin
(

let se' = (

let uu___319_26379 = se
in (

let uu____26380 = (

let uu____26381 = (erase_univs_ed ed)
in FStar_Syntax_Syntax.Sig_new_effect (uu____26381))
in {FStar_Syntax_Syntax.sigel = uu____26380; FStar_Syntax_Syntax.sigrng = uu___319_26379.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___319_26379.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___319_26379.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___319_26379.FStar_Syntax_Syntax.sigattrs}))
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se')
in (push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng)))
end
| FStar_Syntax_Syntax.Sig_new_effect_for_free (ed) -> begin
(

let se' = (

let uu___320_26385 = se
in (

let uu____26386 = (

let uu____26387 = (erase_univs_ed ed)
in FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____26387))
in {FStar_Syntax_Syntax.sigel = uu____26386; FStar_Syntax_Syntax.sigrng = uu___320_26385.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___320_26385.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___320_26385.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___320_26385.FStar_Syntax_Syntax.sigattrs}))
in (

let env1 = (FStar_Syntax_DsEnv.push_sigelt env se')
in (push_reflect_effect env1 se.FStar_Syntax_Syntax.sigquals ed.FStar_Syntax_Syntax.mname se.FStar_Syntax_Syntax.sigrng)))
end
| uu____26389 -> begin
(FStar_Syntax_DsEnv.push_sigelt env se)
end))
in (

let uu____26390 = (FStar_Syntax_DsEnv.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name mii)
in (match (uu____26390) with
| (en1, pop_when_done) -> begin
(

let en2 = (

let uu____26402 = (FStar_Syntax_DsEnv.set_current_module en1 m.FStar_Syntax_Syntax.name)
in (FStar_List.fold_left push_sigelt1 uu____26402 m.FStar_Syntax_Syntax.exports))
in (

let env = (FStar_Syntax_DsEnv.finish en2 m)
in (

let uu____26404 = (match (pop_when_done) with
| true -> begin
(FStar_Syntax_DsEnv.export_interface m.FStar_Syntax_Syntax.name env)
end
| uu____26405 -> begin
env
end)
in ((()), (uu____26404)))))
end)))))




