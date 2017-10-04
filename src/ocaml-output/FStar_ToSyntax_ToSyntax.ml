
open Prims
open FStar_Pervasives

let desugar_disjunctive_pattern : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.branch Prims.list = (fun pats when_opt branch1 -> (FStar_All.pipe_right pats (FStar_List.map (fun pat -> (FStar_Syntax_Util.branch ((pat), (when_opt), (branch1)))))))


let trans_aqual : FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option = (fun uu___209_62 -> (match (uu___209_62) with
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)
end
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality)
end
| uu____67 -> begin
FStar_Pervasives_Native.None
end))


let trans_qual : FStar_Range.range  ->  FStar_Ident.lident FStar_Pervasives_Native.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun r maybe_effect_id uu___210_83 -> (match (uu___210_83) with
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
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Qualifier reflect only supported on effects"), (r)))))
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
(FStar_Exn.raise (FStar_Errors.Error ((("The \'default\' qualifier on effects is no longer supported"), (r)))))
end
| FStar_Parser_AST.Inline -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unsupported qualifier"), (r)))))
end
| FStar_Parser_AST.Visible -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unsupported qualifier"), (r)))))
end))


let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun uu___211_91 -> (match (uu___211_91) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end
| FStar_Parser_AST.LightOff -> begin
FStar_Syntax_Syntax.LightOff
end))


let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option = (fun uu___212_101 -> (match (uu___212_101) with
| FStar_Parser_AST.Hash -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)
end
| uu____104 -> begin
FStar_Pervasives_Native.None
end))


let arg_withimp_e : 'Auu____111 . FStar_Parser_AST.imp  ->  'Auu____111  ->  ('Auu____111 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) = (fun imp t -> ((t), ((as_imp imp))))


let arg_withimp_t : 'Auu____134 . FStar_Parser_AST.imp  ->  'Auu____134  ->  ('Auu____134 * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
((t), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)))
end
| uu____151 -> begin
((t), (FStar_Pervasives_Native.None))
end))


let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (uu____167) -> begin
true
end
| uu____172 -> begin
false
end)))))


let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t1) -> begin
(unparen t1)
end
| uu____178 -> begin
t
end))


let tm_type_z : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (

let uu____183 = (

let uu____184 = (FStar_Ident.lid_of_path (("Type0")::[]) r)
in FStar_Parser_AST.Name (uu____184))
in (FStar_Parser_AST.mk_term uu____183 r FStar_Parser_AST.Kind)))


let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (

let uu____189 = (

let uu____190 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (uu____190))
in (FStar_Parser_AST.mk_term uu____189 r FStar_Parser_AST.Kind)))


let rec is_comp_type : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(

let uu____200 = (FStar_ToSyntax_Env.try_lookup_effect_name env l)
in (FStar_All.pipe_right uu____200 FStar_Option.isSome))
end
| FStar_Parser_AST.Construct (l, uu____206) -> begin
(

let uu____219 = (FStar_ToSyntax_Env.try_lookup_effect_name env l)
in (FStar_All.pipe_right uu____219 FStar_Option.isSome))
end
| FStar_Parser_AST.App (head1, uu____225, uu____226) -> begin
(is_comp_type env head1)
end
| FStar_Parser_AST.Paren (t1) -> begin
(is_comp_type env t1)
end
| FStar_Parser_AST.Ascribed (t1, uu____229, uu____230) -> begin
(is_comp_type env t1)
end
| FStar_Parser_AST.LetOpen (uu____235, t1) -> begin
(is_comp_type env t1)
end
| uu____237 -> begin
false
end))


let unit_ty : FStar_Parser_AST.term = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.unit_lid)) FStar_Range.dummyRange FStar_Parser_AST.Type_level)


let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n1 s r -> (

let uu____250 = (

let uu____253 = (

let uu____254 = (

let uu____259 = (FStar_Parser_AST.compile_op n1 s r)
in ((uu____259), (r)))
in (FStar_Ident.mk_ident uu____254))
in (uu____253)::[])
in (FStar_All.pipe_right uu____250 FStar_Ident.lid_of_ids)))


let op_as_term : 'Auu____272 . FStar_ToSyntax_Env.env  ->  Prims.int  ->  'Auu____272  ->  FStar_Ident.ident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env arity rng op -> (

let r = (fun l dd -> (

let uu____300 = (

let uu____301 = (FStar_Syntax_Syntax.lid_as_fv (FStar_Ident.set_lid_range l op.FStar_Ident.idRange) dd FStar_Pervasives_Native.None)
in (FStar_All.pipe_right uu____301 FStar_Syntax_Syntax.fv_to_tm))
in FStar_Pervasives_Native.Some (uu____300)))
in (

let fallback = (fun uu____307 -> (match ((FStar_Ident.text_of_id op)) with
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

let uu____310 = (FStar_Options.ml_ish ())
in (match (uu____310) with
| true -> begin
(r FStar_Parser_Const.list_append_lid FStar_Syntax_Syntax.Delta_equational)
end
| uu____313 -> begin
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
| uu____314 -> begin
FStar_Pervasives_Native.None
end))
in (

let uu____315 = (

let uu____322 = (compile_op_lid arity op.FStar_Ident.idText op.FStar_Ident.idRange)
in (FStar_ToSyntax_Env.try_lookup_lid env uu____322))
in (match (uu____315) with
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some ((FStar_Pervasives_Native.fst t))
end
| uu____334 -> begin
(fallback ())
end)))))


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (

let uu____351 = (FStar_Util.remove_dups (fun x y -> (Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) uu____351)))


let rec free_type_vars_b : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_ToSyntax_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (uu____390) -> begin
((env), ([]))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____394 = (FStar_ToSyntax_Env.push_bv env x)
in (match (uu____394) with
| (env1, uu____406) -> begin
((env1), ((x)::[]))
end))
end
| FStar_Parser_AST.Annotated (uu____409, term) -> begin
(

let uu____411 = (free_type_vars env term)
in ((env), (uu____411)))
end
| FStar_Parser_AST.TAnnotated (id, uu____417) -> begin
(

let uu____418 = (FStar_ToSyntax_Env.push_bv env id)
in (match (uu____418) with
| (env1, uu____430) -> begin
((env1), ([]))
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____434 = (free_type_vars env t)
in ((env), (uu____434)))
end))
and free_type_vars : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (

let uu____441 = (

let uu____442 = (unparen t)
in uu____442.FStar_Parser_AST.tm)
in (match (uu____441) with
| FStar_Parser_AST.Labeled (uu____445) -> begin
(failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____455 = (FStar_ToSyntax_Env.try_lookup_id env a)
in (match (uu____455) with
| FStar_Pervasives_Native.None -> begin
(a)::[]
end
| uu____468 -> begin
[]
end))
end
| FStar_Parser_AST.Wild -> begin
[]
end
| FStar_Parser_AST.Const (uu____475) -> begin
[]
end
| FStar_Parser_AST.Uvar (uu____476) -> begin
[]
end
| FStar_Parser_AST.Var (uu____477) -> begin
[]
end
| FStar_Parser_AST.Projector (uu____478) -> begin
[]
end
| FStar_Parser_AST.Discrim (uu____483) -> begin
[]
end
| FStar_Parser_AST.Name (uu____484) -> begin
[]
end
| FStar_Parser_AST.Assign (uu____485, t1) -> begin
(free_type_vars env t1)
end
| FStar_Parser_AST.Requires (t1, uu____488) -> begin
(free_type_vars env t1)
end
| FStar_Parser_AST.Ensures (t1, uu____494) -> begin
(free_type_vars env t1)
end
| FStar_Parser_AST.NamedTyp (uu____499, t1) -> begin
(free_type_vars env t1)
end
| FStar_Parser_AST.Paren (t1) -> begin
(free_type_vars env t1)
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
| FStar_Parser_AST.Construct (uu____515, ts) -> begin
(FStar_List.collect (fun uu____536 -> (match (uu____536) with
| (t1, uu____544) -> begin
(free_type_vars env t1)
end)) ts)
end
| FStar_Parser_AST.Op (uu____545, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, uu____553) -> begin
(

let uu____554 = (free_type_vars env t1)
in (

let uu____557 = (free_type_vars env t2)
in (FStar_List.append uu____554 uu____557)))
end
| FStar_Parser_AST.Refine (b, t1) -> begin
(

let uu____562 = (free_type_vars_b env b)
in (match (uu____562) with
| (env1, f) -> begin
(

let uu____577 = (free_type_vars env1 t1)
in (FStar_List.append f uu____577))
end))
end
| FStar_Parser_AST.Product (binders, body) -> begin
(

let uu____586 = (FStar_List.fold_left (fun uu____606 binder -> (match (uu____606) with
| (env1, free) -> begin
(

let uu____626 = (free_type_vars_b env1 binder)
in (match (uu____626) with
| (env2, f) -> begin
((env2), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (uu____586) with
| (env1, free) -> begin
(

let uu____657 = (free_type_vars env1 body)
in (FStar_List.append free uu____657))
end))
end
| FStar_Parser_AST.Sum (binders, body) -> begin
(

let uu____666 = (FStar_List.fold_left (fun uu____686 binder -> (match (uu____686) with
| (env1, free) -> begin
(

let uu____706 = (free_type_vars_b env1 binder)
in (match (uu____706) with
| (env2, f) -> begin
((env2), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (uu____666) with
| (env1, free) -> begin
(

let uu____737 = (free_type_vars env1 body)
in (FStar_List.append free uu____737))
end))
end
| FStar_Parser_AST.Project (t1, uu____741) -> begin
(free_type_vars env t1)
end
| FStar_Parser_AST.Attributes (cattributes) -> begin
(FStar_List.collect (free_type_vars env) cattributes)
end
| FStar_Parser_AST.Abs (uu____745) -> begin
[]
end
| FStar_Parser_AST.Let (uu____752) -> begin
[]
end
| FStar_Parser_AST.LetOpen (uu____765) -> begin
[]
end
| FStar_Parser_AST.If (uu____770) -> begin
[]
end
| FStar_Parser_AST.QForall (uu____777) -> begin
[]
end
| FStar_Parser_AST.QExists (uu____790) -> begin
[]
end
| FStar_Parser_AST.Record (uu____803) -> begin
[]
end
| FStar_Parser_AST.Match (uu____816) -> begin
[]
end
| FStar_Parser_AST.TryWith (uu____831) -> begin
[]
end
| FStar_Parser_AST.Bind (uu____846) -> begin
[]
end
| FStar_Parser_AST.Seq (uu____853) -> begin
[]
end)))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (

let rec aux = (fun args t1 -> (

let uu____901 = (

let uu____902 = (unparen t1)
in uu____902.FStar_Parser_AST.tm)
in (match (uu____901) with
| FStar_Parser_AST.App (t2, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t2)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t1.FStar_Parser_AST.range; FStar_Parser_AST.level = t1.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| uu____944 -> begin
((t1), (args))
end)))
in (aux [] t)))


let close : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (

let uu____966 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv uu____966))
in (match ((Prims.op_Equality (FStar_List.length ftv) (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____973 -> begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (

let uu____984 = (

let uu____985 = (

let uu____990 = (tm_type x.FStar_Ident.idRange)
in ((x), (uu____990)))
in FStar_Parser_AST.TAnnotated (uu____985))
in (FStar_Parser_AST.mk_binder uu____984 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end)))


let close_fun : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (

let uu____1005 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv uu____1005))
in (match ((Prims.op_Equality (FStar_List.length ftv) (Prims.parse_int "0"))) with
| true -> begin
t
end
| uu____1012 -> begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (

let uu____1023 = (

let uu____1024 = (

let uu____1029 = (tm_type x.FStar_Ident.idRange)
in ((x), (uu____1029)))
in FStar_Parser_AST.TAnnotated (uu____1024))
in (FStar_Parser_AST.mk_binder uu____1023 x.FStar_Ident.idRange FStar_Parser_AST.Type_level (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))))))
in (

let t1 = (

let uu____1031 = (

let uu____1032 = (unparen t)
in uu____1032.FStar_Parser_AST.tm)
in (match (uu____1031) with
| FStar_Parser_AST.Product (uu____1033) -> begin
t
end
| uu____1040 -> begin
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
| uu____1074 -> begin
((bs), (t))
end))


let rec is_var_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatWild -> begin
true
end
| FStar_Parser_AST.PatTvar (uu____1081, uu____1082) -> begin
true
end
| FStar_Parser_AST.PatVar (uu____1087, uu____1088) -> begin
true
end
| FStar_Parser_AST.PatAscribed (p1, uu____1094) -> begin
(is_var_pattern p1)
end
| uu____1095 -> begin
false
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p1, uu____1101) -> begin
(is_app_pattern p1)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____1102); FStar_Parser_AST.prange = uu____1103}, uu____1104) -> begin
true
end
| uu____1115 -> begin
false
end))


let replace_unit_pattern : FStar_Parser_AST.pattern  ->  FStar_Parser_AST.pattern = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatConst (FStar_Const.Const_unit) -> begin
(FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatAscribed ((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)), (unit_ty)))) p.FStar_Parser_AST.prange)
end
| uu____1120 -> begin
p
end))


let rec destruct_app_pattern : FStar_ToSyntax_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term FStar_Pervasives_Native.option) = (fun env is_top_level1 p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p1, t) -> begin
(

let uu____1163 = (destruct_app_pattern env is_top_level1 p1)
in (match (uu____1163) with
| (name, args, uu____1194) -> begin
((name), (args), (FStar_Pervasives_Native.Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, uu____1220); FStar_Parser_AST.prange = uu____1221}, args) when is_top_level1 -> begin
(

let uu____1231 = (

let uu____1236 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (uu____1236))
in ((uu____1231), (args), (FStar_Pervasives_Native.None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, uu____1246); FStar_Parser_AST.prange = uu____1247}, args) -> begin
((FStar_Util.Inl (id)), (args), (FStar_Pervasives_Native.None))
end
| uu____1265 -> begin
(failwith "Not an app pattern")
end))


let rec gather_pattern_bound_vars_maybe_top : FStar_Ident.ident FStar_Util.set  ->  FStar_Parser_AST.pattern  ->  FStar_Ident.ident FStar_Util.set = (fun acc p -> (

let gather_pattern_bound_vars_from_list = (FStar_List.fold_left gather_pattern_bound_vars_maybe_top acc)
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatWild -> begin
acc
end
| FStar_Parser_AST.PatConst (uu____1305) -> begin
acc
end
| FStar_Parser_AST.PatVar (uu____1306, FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)) -> begin
acc
end
| FStar_Parser_AST.PatName (uu____1309) -> begin
acc
end
| FStar_Parser_AST.PatTvar (uu____1310) -> begin
acc
end
| FStar_Parser_AST.PatOp (uu____1317) -> begin
acc
end
| FStar_Parser_AST.PatApp (phead, pats) -> begin
(gather_pattern_bound_vars_from_list ((phead)::pats))
end
| FStar_Parser_AST.PatVar (x, uu____1325) -> begin
(FStar_Util.set_add x acc)
end
| FStar_Parser_AST.PatList (pats) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatTuple (pats, uu____1334) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatOr (pats) -> begin
(gather_pattern_bound_vars_from_list pats)
end
| FStar_Parser_AST.PatRecord (guarded_pats) -> begin
(

let uu____1349 = (FStar_List.map FStar_Pervasives_Native.snd guarded_pats)
in (gather_pattern_bound_vars_from_list uu____1349))
end
| FStar_Parser_AST.PatAscribed (pat, uu____1357) -> begin
(gather_pattern_bound_vars_maybe_top acc pat)
end)))


let gather_pattern_bound_vars : FStar_Parser_AST.pattern  ->  FStar_Ident.ident FStar_Util.set = (

let acc = (FStar_Util.new_set (fun id1 id2 -> (match ((Prims.op_Equality id1.FStar_Ident.idText id2.FStar_Ident.idText)) with
| true -> begin
(Prims.parse_int "0")
end
| uu____1370 -> begin
(Prims.parse_int "1")
end)))
in (fun p -> (gather_pattern_bound_vars_maybe_top acc p)))

type bnd =
| LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * FStar_Syntax_Syntax.term)


let uu___is_LocalBinder : bnd  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LocalBinder (_0) -> begin
true
end
| uu____1397 -> begin
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
| uu____1427 -> begin
false
end))


let __proj__LetBinder__item___0 : bnd  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| LetBinder (_0) -> begin
_0
end))


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun uu___213_1455 -> (match (uu___213_1455) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| uu____1462 -> begin
(failwith "Impossible")
end))


let as_binder : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  (FStar_Ident.ident FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_ToSyntax_Env.env) = (fun env imp uu___214_1490 -> (match (uu___214_1490) with
| (FStar_Pervasives_Native.None, k) -> begin
(

let uu____1506 = (FStar_Syntax_Syntax.null_binder k)
in ((uu____1506), (env)))
end
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____1511 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____1511) with
| (env1, a1) -> begin
(((((

let uu___237_1531 = a1
in {FStar_Syntax_Syntax.ppname = uu___237_1531.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___237_1531.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), ((trans_aqual imp)))), (env1))
end))
end))


type env_t =
FStar_ToSyntax_Env.env


type lenv_t =
FStar_Syntax_Syntax.bv Prims.list


let mk_lb : ((FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  FStar_Syntax_Syntax.letbinding = (fun uu____1551 -> (match (uu____1551) with
| (n1, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n1; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))


let no_annot_abs : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t FStar_Pervasives_Native.None))


let mk_ref_read : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun tm -> (

let tm' = (

let uu____1604 = (

let uu____1619 = (

let uu____1620 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____1620))
in (

let uu____1621 = (

let uu____1630 = (

let uu____1637 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (uu____1637)))
in (uu____1630)::[])
in ((uu____1619), (uu____1621))))
in FStar_Syntax_Syntax.Tm_app (uu____1604))
in (FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_alloc : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun tm -> (

let tm' = (

let uu____1671 = (

let uu____1686 = (

let uu____1687 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____1687))
in (

let uu____1688 = (

let uu____1697 = (

let uu____1704 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (uu____1704)))
in (uu____1697)::[])
in ((uu____1686), (uu____1688))))
in FStar_Syntax_Syntax.Tm_app (uu____1671))
in (FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_assign : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t1 t2 pos -> (

let tm = (

let uu____1750 = (

let uu____1765 = (

let uu____1766 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____1766))
in (

let uu____1767 = (

let uu____1776 = (

let uu____1783 = (FStar_Syntax_Syntax.as_implicit false)
in ((t1), (uu____1783)))
in (

let uu____1786 = (

let uu____1795 = (

let uu____1802 = (FStar_Syntax_Syntax.as_implicit false)
in ((t2), (uu____1802)))
in (uu____1795)::[])
in (uu____1776)::uu____1786))
in ((uu____1765), (uu____1767))))
in FStar_Syntax_Syntax.Tm_app (uu____1750))
in (FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos)))


let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun uu___215_1834 -> (match (uu___215_1834) with
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
| uu____1835 -> begin
false
end))


let rec sum_to_universe : FStar_Syntax_Syntax.universe  ->  Prims.int  ->  FStar_Syntax_Syntax.universe = (fun u n1 -> (match ((Prims.op_Equality n1 (Prims.parse_int "0"))) with
| true -> begin
u
end
| uu____1844 -> begin
(

let uu____1845 = (sum_to_universe u (n1 - (Prims.parse_int "1")))
in FStar_Syntax_Syntax.U_succ (uu____1845))
end))


let int_to_universe : Prims.int  ->  FStar_Syntax_Syntax.universe = (fun n1 -> (sum_to_universe FStar_Syntax_Syntax.U_zero n1))


let rec desugar_maybe_non_constant_universe : FStar_Parser_AST.term  ->  (Prims.int, FStar_Syntax_Syntax.universe) FStar_Util.either = (fun t -> (

let uu____1862 = (

let uu____1863 = (unparen t)
in uu____1863.FStar_Parser_AST.tm)
in (match (uu____1862) with
| FStar_Parser_AST.Wild -> begin
(

let uu____1868 = (

let uu____1869 = (FStar_Syntax_Unionfind.univ_fresh ())
in FStar_Syntax_Syntax.U_unif (uu____1869))
in FStar_Util.Inr (uu____1868))
end
| FStar_Parser_AST.Uvar (u) -> begin
FStar_Util.Inr (FStar_Syntax_Syntax.U_name (u))
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (repr, uu____1880)) -> begin
(

let n1 = (FStar_Util.int_of_string repr)
in ((match ((n1 < (Prims.parse_int "0"))) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Error ((((Prims.strcat "Negative universe constant  are not supported : " repr)), (t.FStar_Parser_AST.range)))))
end
| uu____1895 -> begin
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

let uu____1946 = (sum_to_universe u n1)
in FStar_Util.Inr (uu____1946))
end
| (FStar_Util.Inr (u), FStar_Util.Inl (n1)) -> begin
(

let uu____1957 = (sum_to_universe u n1)
in FStar_Util.Inr (uu____1957))
end
| (FStar_Util.Inr (u11), FStar_Util.Inr (u21)) -> begin
(

let uu____1968 = (

let uu____1969 = (

let uu____1974 = (

let uu____1975 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "This universe might contain a sum of two universe variables " uu____1975))
in ((uu____1974), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____1969))
in (FStar_Exn.raise uu____1968))
end)))
end
| FStar_Parser_AST.App (uu____1980) -> begin
(

let rec aux = (fun t1 univargs -> (

let uu____2010 = (

let uu____2011 = (unparen t1)
in uu____2011.FStar_Parser_AST.tm)
in (match (uu____2010) with
| FStar_Parser_AST.App (t2, targ, uu____2018) -> begin
(

let uarg = (desugar_maybe_non_constant_universe targ)
in (aux t2 ((uarg)::univargs)))
end
| FStar_Parser_AST.Var (max_lid1) -> begin
(match ((FStar_List.existsb (fun uu___216_2042 -> (match (uu___216_2042) with
| FStar_Util.Inr (uu____2047) -> begin
true
end
| uu____2048 -> begin
false
end)) univargs)) with
| true -> begin
(

let uu____2053 = (

let uu____2054 = (FStar_List.map (fun uu___217_2063 -> (match (uu___217_2063) with
| FStar_Util.Inl (n1) -> begin
(int_to_universe n1)
end
| FStar_Util.Inr (u) -> begin
u
end)) univargs)
in FStar_Syntax_Syntax.U_max (uu____2054))
in FStar_Util.Inr (uu____2053))
end
| uu____2070 -> begin
(

let nargs = (FStar_List.map (fun uu___218_2080 -> (match (uu___218_2080) with
| FStar_Util.Inl (n1) -> begin
n1
end
| FStar_Util.Inr (uu____2086) -> begin
(failwith "impossible")
end)) univargs)
in (

let uu____2087 = (FStar_List.fold_left (fun m n1 -> (match ((m > n1)) with
| true -> begin
m
end
| uu____2092 -> begin
n1
end)) (Prims.parse_int "0") nargs)
in FStar_Util.Inl (uu____2087)))
end)
end
| uu____2093 -> begin
(

let uu____2094 = (

let uu____2095 = (

let uu____2100 = (

let uu____2101 = (

let uu____2102 = (FStar_Parser_AST.term_to_string t1)
in (Prims.strcat uu____2102 " in universe context"))
in (Prims.strcat "Unexpected term " uu____2101))
in ((uu____2100), (t1.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____2095))
in (FStar_Exn.raise uu____2094))
end)))
in (aux t []))
end
| uu____2111 -> begin
(

let uu____2112 = (

let uu____2113 = (

let uu____2118 = (

let uu____2119 = (

let uu____2120 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat uu____2120 " in universe context"))
in (Prims.strcat "Unexpected term " uu____2119))
in ((uu____2118), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____2113))
in (FStar_Exn.raise uu____2112))
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


let check_fields : 'Auu____2144 . FStar_ToSyntax_Env.env  ->  (FStar_Ident.lident * 'Auu____2144) Prims.list  ->  FStar_Range.range  ->  FStar_ToSyntax_Env.record_or_dc = (fun env fields rg -> (

let uu____2169 = (FStar_List.hd fields)
in (match (uu____2169) with
| (f, uu____2179) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f);
(

let record = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f)
in (

let check_field = (fun uu____2189 -> (match (uu____2189) with
| (f', uu____2195) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f');
(

let uu____2197 = (FStar_ToSyntax_Env.belongs_to_record env f' record)
in (match (uu____2197) with
| true -> begin
()
end
| uu____2198 -> begin
(

let msg = (FStar_Util.format3 "Field %s belongs to record type %s, whereas field %s does not" f.FStar_Ident.str record.FStar_ToSyntax_Env.typename.FStar_Ident.str f'.FStar_Ident.str)
in (FStar_Exn.raise (FStar_Errors.Error (((msg), (rg))))))
end));
)
end))
in ((

let uu____2201 = (FStar_List.tl fields)
in (FStar_List.iter check_field uu____2201));
(match (()) with
| () -> begin
record
end);
)));
)
end)))


let rec desugar_data_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.list) = (fun env p is_mut -> (

let check_linear_pattern_variables = (fun p1 -> (

let rec pat_vars = (fun p2 -> (match (p2.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____2415) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_wild (uu____2422) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_constant (uu____2423) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (uu____2425, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out uu____2465 -> (match (uu____2465) with
| (p3, uu____2475) -> begin
(

let uu____2476 = (pat_vars p3)
in (FStar_Util.set_union out uu____2476))
end)) FStar_Syntax_Syntax.no_names))
end))
in (pat_vars p1)))
in ((match (((is_mut), (p.FStar_Parser_AST.pat))) with
| (false, uu____2480) -> begin
()
end
| (true, FStar_Parser_AST.PatVar (uu____2481)) -> begin
()
end
| (true, uu____2488) -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("let-mutable is for variables only"), (p.FStar_Parser_AST.prange)))))
end);
(

let push_bv_maybe_mut = (match (is_mut) with
| true -> begin
FStar_ToSyntax_Env.push_bv_mutable
end
| uu____2506 -> begin
FStar_ToSyntax_Env.push_bv
end)
in (

let resolvex = (fun l e x -> (

let uu____2523 = (FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (Prims.op_Equality y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText x.FStar_Ident.idText))))
in (match (uu____2523) with
| FStar_Pervasives_Native.Some (y) -> begin
((l), (e), (y))
end
| uu____2537 -> begin
(

let uu____2540 = (push_bv_maybe_mut e x)
in (match (uu____2540) with
| (e1, x1) -> begin
(((x1)::l), (e1), (x1))
end))
end)))
in (

let rec aux = (fun loc env1 p1 -> (

let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q p1.FStar_Parser_AST.prange))
in (

let pos_r = (fun r q -> (FStar_Syntax_Syntax.withinfo q r))
in (match (p1.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr (uu____2604) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.PatOp (op) -> begin
(

let uu____2620 = (

let uu____2621 = (

let uu____2622 = (

let uu____2629 = (

let uu____2630 = (

let uu____2635 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") op.FStar_Ident.idText op.FStar_Ident.idRange)
in ((uu____2635), (op.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____2630))
in ((uu____2629), (FStar_Pervasives_Native.None)))
in FStar_Parser_AST.PatVar (uu____2622))
in {FStar_Parser_AST.pat = uu____2621; FStar_Parser_AST.prange = p1.FStar_Parser_AST.prange})
in (aux loc env1 uu____2620))
end
| FStar_Parser_AST.PatAscribed (p2, t) -> begin
(

let uu____2640 = (aux loc env1 p2)
in (match (uu____2640) with
| (loc1, env', binder, p3, imp) -> begin
(

let binder1 = (match (binder) with
| LetBinder (uu____2675) -> begin
(failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t1 = (

let uu____2683 = (close_fun env1 t)
in (desugar_term env1 uu____2683))
in ((match ((match (x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
false
end
| uu____2685 -> begin
true
end)) with
| true -> begin
(

let uu____2686 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____2687 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____2688 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3_warning "Multiple ascriptions for %s in pattern, type %s was shadowed by %s" uu____2686 uu____2687 uu____2688))))
end
| uu____2689 -> begin
()
end);
LocalBinder ((((

let uu___238_2691 = x
in {FStar_Syntax_Syntax.ppname = uu___238_2691.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___238_2691.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})), (aq)));
))
end)
in ((loc1), (env'), (binder1), (p3), (imp)))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____2695 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____2695), (false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____2706 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____2706), (false))))
end
| FStar_Parser_AST.PatTvar (x, aq) -> begin
(

let imp = (Prims.op_Equality aq (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))
in (

let aq1 = (trans_aqual aq)
in (

let uu____2727 = (resolvex loc env1 x)
in (match (uu____2727) with
| (loc1, env2, xbv) -> begin
(

let uu____2749 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc1), (env2), (LocalBinder (((xbv), (aq1)))), (uu____2749), (imp)))
end))))
end
| FStar_Parser_AST.PatVar (x, aq) -> begin
(

let imp = (Prims.op_Equality aq (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))
in (

let aq1 = (trans_aqual aq)
in (

let uu____2770 = (resolvex loc env1 x)
in (match (uu____2770) with
| (loc1, env2, xbv) -> begin
(

let uu____2792 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc1), (env2), (LocalBinder (((xbv), (aq1)))), (uu____2792), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l1 = (FStar_ToSyntax_Env.fail_or env1 (FStar_ToSyntax_Env.try_lookup_datacon env1) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____2804 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), ([])))))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____2804), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = uu____2828}, args) -> begin
(

let uu____2834 = (FStar_List.fold_right (fun arg uu____2875 -> (match (uu____2875) with
| (loc1, env2, args1) -> begin
(

let uu____2923 = (aux loc1 env2 arg)
in (match (uu____2923) with
| (loc2, env3, uu____2952, arg1, imp) -> begin
((loc2), (env3), ((((arg1), (imp)))::args1))
end))
end)) args ((loc), (env1), ([])))
in (match (uu____2834) with
| (loc1, env2, args1) -> begin
(

let l1 = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_datacon env2) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____3022 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args1)))))
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3022), (false)))))
end))
end
| FStar_Parser_AST.PatApp (uu____3039) -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected pattern"), (p1.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____3061 = (FStar_List.fold_right (fun pat uu____3094 -> (match (uu____3094) with
| (loc1, env2, pats1) -> begin
(

let uu____3126 = (aux loc1 env2 pat)
in (match (uu____3126) with
| (loc2, env3, uu____3151, pat1, uu____3153) -> begin
((loc2), (env3), ((pat1)::pats1))
end))
end)) pats ((loc), (env1), ([])))
in (match (uu____3061) with
| (loc1, env2, pats1) -> begin
(

let pat = (

let uu____3196 = (

let uu____3199 = (

let uu____3204 = (FStar_Range.end_range p1.FStar_Parser_AST.prange)
in (pos_r uu____3204))
in (

let uu____3205 = (

let uu____3206 = (

let uu____3219 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____3219), ([])))
in FStar_Syntax_Syntax.Pat_cons (uu____3206))
in (FStar_All.pipe_left uu____3199 uu____3205)))
in (FStar_List.fold_right (fun hd1 tl1 -> (

let r = (FStar_Range.union_ranges hd1.FStar_Syntax_Syntax.p tl1.FStar_Syntax_Syntax.p)
in (

let uu____3251 = (

let uu____3252 = (

let uu____3265 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____3265), ((((hd1), (false)))::(((tl1), (false)))::[])))
in FStar_Syntax_Syntax.Pat_cons (uu____3252))
in (FStar_All.pipe_left (pos_r r) uu____3251)))) pats1 uu____3196))
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep1) -> begin
(

let uu____3309 = (FStar_List.fold_left (fun uu____3349 p2 -> (match (uu____3349) with
| (loc1, env2, pats) -> begin
(

let uu____3398 = (aux loc1 env2 p2)
in (match (uu____3398) with
| (loc2, env3, uu____3427, pat, uu____3429) -> begin
((loc2), (env3), ((((pat), (false)))::pats))
end))
end)) ((loc), (env1), ([])) args)
in (match (uu____3309) with
| (loc1, env2, args1) -> begin
(

let args2 = (FStar_List.rev args1)
in (

let l = (match (dep1) with
| true -> begin
(FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end
| uu____3517 -> begin
(FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end)
in (

let uu____3524 = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_lid env2) l)
in (match (uu____3524) with
| (constr, uu____3546) -> begin
(

let l1 = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____3549 -> begin
(failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____3551 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args2)))))
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3551), (false)))))
end))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected pattern"), (p1.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(

let record = (check_fields env1 fields p1.FStar_Parser_AST.prange)
in (

let fields1 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____3622 -> (match (uu____3622) with
| (f, p2) -> begin
((f.FStar_Ident.ident), (p2))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____3652 -> (match (uu____3652) with
| (f, uu____3658) -> begin
(

let uu____3659 = (FStar_All.pipe_right fields1 (FStar_List.tryFind (fun uu____3685 -> (match (uu____3685) with
| (g, uu____3691) -> begin
(Prims.op_Equality f.FStar_Ident.idText g.FStar_Ident.idText)
end))))
in (match (uu____3659) with
| FStar_Pervasives_Native.None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p1.FStar_Parser_AST.prange)
end
| FStar_Pervasives_Native.Some (uu____3696, p2) -> begin
p2
end))
end))))
in (

let app = (

let uu____3703 = (

let uu____3704 = (

let uu____3711 = (

let uu____3712 = (

let uu____3713 = (FStar_Ident.lid_of_ids (FStar_List.append record.FStar_ToSyntax_Env.typename.FStar_Ident.ns ((record.FStar_ToSyntax_Env.constrname)::[])))
in FStar_Parser_AST.PatName (uu____3713))
in (FStar_Parser_AST.mk_pattern uu____3712 p1.FStar_Parser_AST.prange))
in ((uu____3711), (args)))
in FStar_Parser_AST.PatApp (uu____3704))
in (FStar_Parser_AST.mk_pattern uu____3703 p1.FStar_Parser_AST.prange))
in (

let uu____3716 = (aux loc env1 app)
in (match (uu____3716) with
| (env2, e, b, p2, uu____3745) -> begin
(

let p3 = (match (p2.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args1) -> begin
(

let uu____3773 = (

let uu____3774 = (

let uu____3787 = (

let uu___239_3788 = fv
in (

let uu____3789 = (

let uu____3792 = (

let uu____3793 = (

let uu____3800 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map FStar_Pervasives_Native.fst))
in ((record.FStar_ToSyntax_Env.typename), (uu____3800)))
in FStar_Syntax_Syntax.Record_ctor (uu____3793))
in FStar_Pervasives_Native.Some (uu____3792))
in {FStar_Syntax_Syntax.fv_name = uu___239_3788.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = uu___239_3788.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu____3789}))
in ((uu____3787), (args1)))
in FStar_Syntax_Syntax.Pat_cons (uu____3774))
in (FStar_All.pipe_left pos uu____3773))
end
| uu____3827 -> begin
p2
end)
in ((env2), (e), (b), (p3), (false)))
end))))))
end))))
in (

let aux_maybe_or = (fun env1 p1 -> (

let loc = []
in (match (p1.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr ([]) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.PatOr ((p2)::ps) -> begin
(

let uu____3874 = (aux loc env1 p2)
in (match (uu____3874) with
| (loc1, env2, var, p3, uu____3901) -> begin
(

let uu____3906 = (FStar_List.fold_left (fun uu____3938 p4 -> (match (uu____3938) with
| (loc2, env3, ps1) -> begin
(

let uu____3971 = (aux loc2 env3 p4)
in (match (uu____3971) with
| (loc3, env4, uu____3996, p5, uu____3998) -> begin
((loc3), (env4), ((p5)::ps1))
end))
end)) ((loc1), (env2), ([])) ps)
in (match (uu____3906) with
| (loc2, env3, ps1) -> begin
(

let pats = (p3)::(FStar_List.rev ps1)
in ((env3), (var), (pats)))
end))
end))
end
| uu____4049 -> begin
(

let uu____4050 = (aux loc env1 p1)
in (match (uu____4050) with
| (loc1, env2, vars, pat, b) -> begin
((env2), (vars), ((pat)::[]))
end))
end)))
in (

let uu____4090 = (aux_maybe_or env p)
in (match (uu____4090) with
| (env1, b, pats) -> begin
((

let uu____4121 = (FStar_List.map check_linear_pattern_variables pats)
in (FStar_All.pipe_left FStar_Pervasives.ignore uu____4121));
((env1), (b), (pats));
)
end))))));
)))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.list) = (fun top env p is_mut -> (

let mklet = (fun x -> (

let uu____4156 = (

let uu____4157 = (

let uu____4162 = (FStar_ToSyntax_Env.qualify env x)
in ((uu____4162), (FStar_Syntax_Syntax.tun)))
in LetBinder (uu____4157))
in ((env), (uu____4156), ([]))))
in (match (top) with
| true -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(

let uu____4182 = (

let uu____4183 = (

let uu____4188 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") x.FStar_Ident.idText x.FStar_Ident.idRange)
in ((uu____4188), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____4183))
in (mklet uu____4182))
end
| FStar_Parser_AST.PatVar (x, uu____4190) -> begin
(mklet x)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____4196); FStar_Parser_AST.prange = uu____4197}, t) -> begin
(

let uu____4203 = (

let uu____4204 = (

let uu____4209 = (FStar_ToSyntax_Env.qualify env x)
in (

let uu____4210 = (desugar_term env t)
in ((uu____4209), (uu____4210))))
in LetBinder (uu____4204))
in ((env), (uu____4203), ([])))
end
| uu____4213 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end
| uu____4222 -> begin
(

let uu____4223 = (desugar_data_pat env p is_mut)
in (match (uu____4223) with
| (env1, binder, p1) -> begin
(

let p2 = (match (p1) with
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (uu____4252); FStar_Syntax_Syntax.p = uu____4253})::[] -> begin
[]
end
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (uu____4258); FStar_Syntax_Syntax.p = uu____4259})::[] -> begin
[]
end
| uu____4264 -> begin
p1
end)
in ((env1), (binder), (p2)))
end))
end)))
and desugar_binding_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.list) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat Prims.list) = (fun uu____4271 env pat -> (

let uu____4274 = (desugar_data_pat env pat false)
in (match (uu____4274) with
| (env1, uu____4290, pat1) -> begin
((env1), (pat1))
end)))
and desugar_match_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat Prims.list) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env1 = (FStar_ToSyntax_Env.set_expect_typ env false)
in (desugar_term_maybe_top false env1 e)))
and desugar_typ : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env1 = (FStar_ToSyntax_Env.set_expect_typ env true)
in (desugar_term_maybe_top false env1 e)))
and desugar_machine_integer : FStar_ToSyntax_Env.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun env repr uu____4308 range -> (match (uu____4308) with
| (signedness, width) -> begin
(

let uu____4316 = (FStar_Const.bounds signedness width)
in (match (uu____4316) with
| (lower, upper) -> begin
(

let value = (

let uu____4324 = (FStar_Util.ensure_decimal repr)
in (FStar_Util.int_of_string uu____4324))
in (

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
in ((match ((not (((lower <= value) && (value <= upper))))) with
| true -> begin
(

let uu____4327 = (

let uu____4328 = (

let uu____4333 = (FStar_Util.format2 "%s is not in the expected range for %s" repr tnm)
in ((uu____4333), (range)))
in FStar_Errors.Error (uu____4328))
in (FStar_Exn.raise uu____4327))
end
| uu____4334 -> begin
()
end);
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

let uu____4341 = (FStar_ToSyntax_Env.try_lookup_lid env lid)
in (match (uu____4341) with
| FStar_Pervasives_Native.Some (intro_term, uu____4351) -> begin
(match (intro_term.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let private_lid = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text private_intro_nm) range)
in (

let private_fv = (

let uu____4361 = (FStar_Syntax_Util.incr_delta_depth fv.FStar_Syntax_Syntax.fv_delta)
in (FStar_Syntax_Syntax.lid_as_fv private_lid uu____4361 fv.FStar_Syntax_Syntax.fv_qual))
in (

let uu___240_4362 = intro_term
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (private_fv); FStar_Syntax_Syntax.pos = uu___240_4362.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___240_4362.FStar_Syntax_Syntax.vars})))
end
| uu____4363 -> begin
(failwith (Prims.strcat "Unexpected non-fvar for " intro_nm))
end)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4370 = (

let uu____4371 = (

let uu____4376 = (FStar_Util.format1 "Unexpected numeric literal.  Restart F* to load %s." tnm)
in ((uu____4376), (range)))
in FStar_Errors.Error (uu____4371))
in (FStar_Exn.raise uu____4370))
end))
in (

let repr1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (FStar_Pervasives_Native.None))))) FStar_Pervasives_Native.None range)
in (

let uu____4392 = (

let uu____4395 = (

let uu____4396 = (

let uu____4411 = (

let uu____4420 = (

let uu____4427 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr1), (uu____4427)))
in (uu____4420)::[])
in ((lid1), (uu____4411)))
in FStar_Syntax_Syntax.Tm_app (uu____4396))
in (FStar_Syntax_Syntax.mk uu____4395))
in (uu____4392 FStar_Pervasives_Native.None range)))))));
)))
end))
end))
and desugar_name : (FStar_Syntax_Syntax.term'  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  env_t  ->  Prims.bool  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.term = (fun mk1 setpos env resolve l -> (

let uu____4466 = (FStar_ToSyntax_Env.fail_or env ((match (resolve) with
| true -> begin
FStar_ToSyntax_Env.try_lookup_lid
end
| uu____4475 -> begin
FStar_ToSyntax_Env.try_lookup_lid_no_resolve
end) env) l)
in (match (uu____4466) with
| (tm, mut) -> begin
(

let tm1 = (setpos tm)
in (match (mut) with
| true -> begin
(

let uu____4481 = (

let uu____4482 = (

let uu____4489 = (mk_ref_read tm1)
in ((uu____4489), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval))))
in FStar_Syntax_Syntax.Tm_meta (uu____4482))
in (FStar_All.pipe_left mk1 uu____4481))
end
| uu____4494 -> begin
tm1
end))
end)))
and desugar_attributes : env_t  ->  FStar_Parser_AST.term Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun env cattributes -> (

let desugar_attribute = (fun t -> (

let uu____4505 = (

let uu____4506 = (unparen t)
in uu____4506.FStar_Parser_AST.tm)
in (match (uu____4505) with
| FStar_Parser_AST.Var ({FStar_Ident.ns = uu____4507; FStar_Ident.ident = uu____4508; FStar_Ident.nsstr = uu____4509; FStar_Ident.str = "cps"}) -> begin
FStar_Syntax_Syntax.CPS
end
| uu____4512 -> begin
(

let uu____4513 = (

let uu____4514 = (

let uu____4519 = (

let uu____4520 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "Unknown attribute " uu____4520))
in ((uu____4519), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____4514))
in (FStar_Exn.raise uu____4513))
end)))
in (FStar_List.map desugar_attribute cattributes)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (

let mk1 = (fun e -> (FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let uu___241_4540 = e
in {FStar_Syntax_Syntax.n = uu___241_4540.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___241_4540.FStar_Syntax_Syntax.vars}))
in (

let uu____4543 = (

let uu____4544 = (unparen top)
in uu____4544.FStar_Parser_AST.tm)
in (match (uu____4543) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (uu____4545) -> begin
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
| FStar_Parser_AST.Const (FStar_Const.Const_int (i, FStar_Pervasives_Native.Some (size))) -> begin
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
| FStar_Parser_AST.Op (op_star, (uu____4596)::(uu____4597)::[]) when ((Prims.op_Equality (FStar_Ident.text_of_id op_star) "*") && (

let uu____4601 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range op_star)
in (FStar_All.pipe_right uu____4601 FStar_Option.isNone))) -> begin
(

let rec flatten1 = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4614}, (t1)::(t2)::[]) -> begin
(

let uu____4619 = (flatten1 t1)
in (FStar_List.append uu____4619 ((t2)::[])))
end
| uu____4622 -> begin
(t)::[]
end))
in (

let targs = (

let uu____4626 = (

let uu____4629 = (unparen top)
in (flatten1 uu____4629))
in (FStar_All.pipe_right uu____4626 (FStar_List.map (fun t -> (

let uu____4637 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg uu____4637))))))
in (

let uu____4638 = (

let uu____4643 = (FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) uu____4643))
in (match (uu____4638) with
| (tup, uu____4649) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____4653 = (

let uu____4656 = (FStar_ToSyntax_Env.fail_or2 (FStar_ToSyntax_Env.try_lookup_id env) a)
in (FStar_Pervasives_Native.fst uu____4656))
in (FStar_All.pipe_left setpos uu____4653))
end
| FStar_Parser_AST.Uvar (u) -> begin
(FStar_Exn.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected universe variable " (Prims.strcat (FStar_Ident.text_of_id u) " in non-universe context"))), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(

let uu____4676 = (op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)
in (match (uu____4676) with
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected or unbound operator: " (FStar_Ident.text_of_id s))), (top.FStar_Parser_AST.range)))))
end
| FStar_Pervasives_Native.Some (op) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let args1 = (FStar_All.pipe_right args (FStar_List.map (fun t -> (

let uu____4708 = (desugar_term env t)
in ((uu____4708), (FStar_Pervasives_Native.None))))))
in (mk1 (FStar_Syntax_Syntax.Tm_app (((op), (args1))))))
end
| uu____4719 -> begin
op
end)
end))
end
| FStar_Parser_AST.Construct (n1, ((a, uu____4722))::[]) when (Prims.op_Equality n1.FStar_Ident.str "SMTPat") -> begin
(

let uu____4737 = (

let uu___242_4738 = top
in (

let uu____4739 = (

let uu____4740 = (

let uu____4747 = (

let uu___243_4748 = top
in (

let uu____4749 = (

let uu____4750 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____4750))
in {FStar_Parser_AST.tm = uu____4749; FStar_Parser_AST.range = uu___243_4748.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___243_4748.FStar_Parser_AST.level}))
in ((uu____4747), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____4740))
in {FStar_Parser_AST.tm = uu____4739; FStar_Parser_AST.range = uu___242_4738.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___242_4738.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____4737))
end
| FStar_Parser_AST.Construct (n1, ((a, uu____4753))::[]) when (Prims.op_Equality n1.FStar_Ident.str "SMTPatT") -> begin
(

let uu____4768 = (

let uu___244_4769 = top
in (

let uu____4770 = (

let uu____4771 = (

let uu____4778 = (

let uu___245_4779 = top
in (

let uu____4780 = (

let uu____4781 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____4781))
in {FStar_Parser_AST.tm = uu____4780; FStar_Parser_AST.range = uu___245_4779.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___245_4779.FStar_Parser_AST.level}))
in ((uu____4778), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____4771))
in {FStar_Parser_AST.tm = uu____4770; FStar_Parser_AST.range = uu___244_4769.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___244_4769.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____4768))
end
| FStar_Parser_AST.Construct (n1, ((a, uu____4784))::[]) when (Prims.op_Equality n1.FStar_Ident.str "SMTPatOr") -> begin
(

let uu____4799 = (

let uu___246_4800 = top
in (

let uu____4801 = (

let uu____4802 = (

let uu____4809 = (

let uu___247_4810 = top
in (

let uu____4811 = (

let uu____4812 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat_or")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____4812))
in {FStar_Parser_AST.tm = uu____4811; FStar_Parser_AST.range = uu___247_4810.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___247_4810.FStar_Parser_AST.level}))
in ((uu____4809), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____4802))
in {FStar_Parser_AST.tm = uu____4801; FStar_Parser_AST.range = uu___246_4800.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___246_4800.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____4799))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____4813; FStar_Ident.ident = uu____4814; FStar_Ident.nsstr = uu____4815; FStar_Ident.str = "Type0"}) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____4818; FStar_Ident.ident = uu____4819; FStar_Ident.nsstr = uu____4820; FStar_Ident.str = "Type"}) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Construct ({FStar_Ident.ns = uu____4823; FStar_Ident.ident = uu____4824; FStar_Ident.nsstr = uu____4825; FStar_Ident.str = "Type"}, ((t, FStar_Parser_AST.UnivApp))::[]) -> begin
(

let uu____4843 = (

let uu____4844 = (desugar_universe t)
in FStar_Syntax_Syntax.Tm_type (uu____4844))
in (mk1 uu____4843))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____4845; FStar_Ident.ident = uu____4846; FStar_Ident.nsstr = uu____4847; FStar_Ident.str = "Effect"}) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____4850; FStar_Ident.ident = uu____4851; FStar_Ident.nsstr = uu____4852; FStar_Ident.str = "True"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____4855; FStar_Ident.ident = uu____4856; FStar_Ident.nsstr = uu____4857; FStar_Ident.str = "False"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
end
| FStar_Parser_AST.Projector (eff_name, {FStar_Ident.idText = txt; FStar_Ident.idRange = uu____4862}) when ((is_special_effect_combinator txt) && (FStar_ToSyntax_Env.is_effect_name env eff_name)) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name);
(

let uu____4864 = (FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name)
in (match (uu____4864) with
| FStar_Pervasives_Native.Some (ed) -> begin
(

let lid = (FStar_Syntax_Util.dm4f_lid ed txt)
in (FStar_Syntax_Syntax.fvar lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4869 = (FStar_Util.format2 "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)" (FStar_Ident.text_of_lid eff_name) txt)
in (failwith uu____4869))
end));
)
end
| FStar_Parser_AST.Assign (ident, t2) -> begin
(

let t21 = (desugar_term env t2)
in (

let uu____4873 = (FStar_ToSyntax_Env.fail_or2 (FStar_ToSyntax_Env.try_lookup_id env) ident)
in (match (uu____4873) with
| (t1, mut) -> begin
((match ((not (mut))) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Can only assign to mutable values"), (top.FStar_Parser_AST.range)))))
end
| uu____4885 -> begin
()
end);
(mk_ref_assign t1 t21 top.FStar_Parser_AST.range);
)
end)))
end
| FStar_Parser_AST.Var (l) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l);
(desugar_name mk1 setpos env true l);
)
end
| FStar_Parser_AST.Name (l) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l);
(desugar_name mk1 setpos env true l);
)
end
| FStar_Parser_AST.Projector (l, i) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l);
(

let name = (

let uu____4900 = (FStar_ToSyntax_Env.try_lookup_datacon env l)
in (match (uu____4900) with
| FStar_Pervasives_Native.Some (uu____4909) -> begin
FStar_Pervasives_Native.Some (((true), (l)))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4914 = (FStar_ToSyntax_Env.try_lookup_root_effect_name env l)
in (match (uu____4914) with
| FStar_Pervasives_Native.Some (new_name) -> begin
FStar_Pervasives_Native.Some (((false), (new_name)))
end
| uu____4928 -> begin
FStar_Pervasives_Native.None
end))
end))
in (match (name) with
| FStar_Pervasives_Native.Some (resolve, new_name) -> begin
(

let uu____4941 = (FStar_Syntax_Util.mk_field_projector_name_from_ident new_name i)
in (desugar_name mk1 setpos env resolve uu____4941))
end
| uu____4942 -> begin
(

let uu____4949 = (

let uu____4950 = (

let uu____4955 = (FStar_Util.format1 "Data constructor or effect %s not found" l.FStar_Ident.str)
in ((uu____4955), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____4950))
in (FStar_Exn.raise uu____4949))
end));
)
end
| FStar_Parser_AST.Discrim (lid) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid);
(

let uu____4958 = (FStar_ToSyntax_Env.try_lookup_datacon env lid)
in (match (uu____4958) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4961 = (

let uu____4962 = (

let uu____4967 = (FStar_Util.format1 "Data constructor %s not found" lid.FStar_Ident.str)
in ((uu____4967), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____4962))
in (FStar_Exn.raise uu____4961))
end
| uu____4968 -> begin
(

let lid' = (FStar_Syntax_Util.mk_discriminator lid)
in (desugar_name mk1 setpos env true lid'))
end));
)
end
| FStar_Parser_AST.Construct (l, args) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l);
(

let uu____4987 = (FStar_ToSyntax_Env.try_lookup_datacon env l)
in (match (uu____4987) with
| FStar_Pervasives_Native.Some (head1) -> begin
(

let uu____4991 = (

let uu____4998 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (head1)))
in ((uu____4998), (true)))
in (match (uu____4991) with
| (head2, is_data) -> begin
(match (args) with
| [] -> begin
head2
end
| uu____5013 -> begin
(

let uu____5020 = (FStar_Util.take (fun uu____5044 -> (match (uu____5044) with
| (uu____5049, imp) -> begin
(Prims.op_Equality imp FStar_Parser_AST.UnivApp)
end)) args)
in (match (uu____5020) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun x -> (desugar_universe (FStar_Pervasives_Native.fst x))) universes)
in (

let args2 = (FStar_List.map (fun uu____5113 -> (match (uu____5113) with
| (t, imp) -> begin
(

let te = (desugar_term env t)
in (arg_withimp_e imp te))
end)) args1)
in (

let head3 = (match ((Prims.op_Equality universes1 [])) with
| true -> begin
head2
end
| uu____5134 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_uinst (((head2), (universes1)))))
end)
in (

let app = (mk1 (FStar_Syntax_Syntax.Tm_app (((head3), (args2)))))
in (match (is_data) with
| true -> begin
(mk1 (FStar_Syntax_Syntax.Tm_meta (((app), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end
| uu____5154 -> begin
app
end)))))
end))
end)
end))
end
| FStar_Pervasives_Native.None -> begin
(

let error_msg = (

let uu____5156 = (FStar_ToSyntax_Env.try_lookup_effect_name env l)
in (match (uu____5156) with
| FStar_Pervasives_Native.None -> begin
(Prims.strcat "Constructor " (Prims.strcat l.FStar_Ident.str " not found"))
end
| FStar_Pervasives_Native.Some (uu____5159) -> begin
(Prims.strcat "Effect " (Prims.strcat l.FStar_Ident.str " used at an unexpected position"))
end))
in (FStar_Exn.raise (FStar_Errors.Error (((error_msg), (top.FStar_Parser_AST.range))))))
end));
)
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let uu____5166 = (FStar_List.fold_left (fun uu____5211 b -> (match (uu____5211) with
| (env1, tparams, typs) -> begin
(

let uu____5268 = (desugar_binder env1 b)
in (match (uu____5268) with
| (xopt, t1) -> begin
(

let uu____5297 = (match (xopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5306 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env1), (uu____5306)))
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_ToSyntax_Env.push_bv env1 x)
end)
in (match (uu____5297) with
| (env2, x) -> begin
(

let uu____5326 = (

let uu____5329 = (

let uu____5332 = (

let uu____5333 = (no_annot_abs tparams t1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____5333))
in (uu____5332)::[])
in (FStar_List.append typs uu____5329))
in ((env2), ((FStar_List.append tparams (((((

let uu___248_5359 = x
in {FStar_Syntax_Syntax.ppname = uu___248_5359.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___248_5359.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})), (FStar_Pervasives_Native.None)))::[]))), (uu____5326)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type_level FStar_Pervasives_Native.None))::[])))
in (match (uu____5166) with
| (env1, uu____5383, targs) -> begin
(

let uu____5405 = (

let uu____5410 = (FStar_Parser_Const.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_ToSyntax_Env.fail_or env1 (FStar_ToSyntax_Env.try_lookup_lid env1) uu____5410))
in (match (uu____5405) with
| (tup, uu____5416) -> begin
(FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let uu____5427 = (uncurry binders t)
in (match (uu____5427) with
| (bs, t1) -> begin
(

let rec aux = (fun env1 bs1 uu___219_5459 -> (match (uu___219_5459) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range env1 t1)
in (

let uu____5473 = (FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod)
in (FStar_All.pipe_left setpos uu____5473)))
end
| (hd1)::tl1 -> begin
(

let bb = (desugar_binder env1 hd1)
in (

let uu____5495 = (as_binder env1 hd1.FStar_Parser_AST.aqual bb)
in (match (uu____5495) with
| (b, env2) -> begin
(aux env2 ((b)::bs1) tl1)
end)))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(

let uu____5510 = (desugar_binder env b)
in (match (uu____5510) with
| (FStar_Pervasives_Native.None, uu____5517) -> begin
(failwith "Missing binder in refinement")
end
| b1 -> begin
(

let uu____5527 = (as_binder env FStar_Pervasives_Native.None b1)
in (match (uu____5527) with
| ((x, uu____5533), env1) -> begin
(

let f1 = (desugar_formula env1 f)
in (

let uu____5540 = (FStar_Syntax_Util.refine x f1)
in (FStar_All.pipe_left setpos uu____5540)))
end))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let binders1 = (FStar_All.pipe_right binders (FStar_List.map replace_unit_pattern))
in (

let uu____5560 = (FStar_List.fold_left (fun uu____5580 pat -> (match (uu____5580) with
| (env1, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (uu____5606, t) -> begin
(

let uu____5608 = (

let uu____5611 = (free_type_vars env1 t)
in (FStar_List.append uu____5611 ftvs))
in ((env1), (uu____5608)))
end
| uu____5616 -> begin
((env1), (ftvs))
end)
end)) ((env), ([])) binders1)
in (match (uu____5560) with
| (uu____5621, ftv) -> begin
(

let ftv1 = (sort_ftv ftv)
in (

let binders2 = (

let uu____5633 = (FStar_All.pipe_right ftv1 (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append uu____5633 binders1))
in (

let rec aux = (fun env1 bs sc_pat_opt uu___220_5674 -> (match (uu___220_5674) with
| [] -> begin
(

let body1 = (desugar_term env1 body)
in (

let body2 = (match (sc_pat_opt) with
| FStar_Pervasives_Native.Some (sc, pat) -> begin
(

let body2 = (

let uu____5712 = (

let uu____5713 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right uu____5713 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close uu____5712 body1))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (FStar_Pervasives_Native.None), (body2)))::[])))) FStar_Pervasives_Native.None body2.FStar_Syntax_Syntax.pos))
end
| FStar_Pervasives_Native.None -> begin
body1
end)
in (

let uu____5766 = (no_annot_abs (FStar_List.rev bs) body2)
in (setpos uu____5766))))
end
| (p)::rest -> begin
(

let uu____5777 = (desugar_binding_pat env1 p)
in (match (uu____5777) with
| (env2, b, pat) -> begin
(

let pat1 = (match (pat) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (p1)::[] -> begin
FStar_Pervasives_Native.Some (p1)
end
| uu____5801 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Disjunctive patterns are not supported in abstractions"), (p.FStar_Parser_AST.prange)))))
end)
in (

let uu____5806 = (match (b) with
| LetBinder (uu____5839) -> begin
(failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt1 = (match (((pat1), (sc_pat_opt))) with
| (FStar_Pervasives_Native.None, uu____5889) -> begin
sc_pat_opt
end
| (FStar_Pervasives_Native.Some (p1), FStar_Pervasives_Native.None) -> begin
(

let uu____5925 = (

let uu____5930 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____5930), (p1)))
in FStar_Pervasives_Native.Some (uu____5925))
end
| (FStar_Pervasives_Native.Some (p1), FStar_Pervasives_Native.Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (uu____5966), uu____5967) -> begin
(

let tup2 = (

let uu____5969 = (FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____5969 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____5973 = (

let uu____5976 = (

let uu____5977 = (

let uu____5992 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (

let uu____5995 = (

let uu____5998 = (FStar_Syntax_Syntax.as_arg sc)
in (

let uu____5999 = (

let uu____6002 = (

let uu____6003 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____6003))
in (uu____6002)::[])
in (uu____5998)::uu____5999))
in ((uu____5992), (uu____5995))))
in FStar_Syntax_Syntax.Tm_app (uu____5977))
in (FStar_Syntax_Syntax.mk uu____5976))
in (uu____5973 FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
in (

let p2 = (

let uu____6014 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p1), (false)))::[])))) uu____6014))
in FStar_Pervasives_Native.Some (((sc1), (p2))))))
end
| (FStar_Syntax_Syntax.Tm_app (uu____6045, args), FStar_Syntax_Syntax.Pat_cons (uu____6047, pats)) -> begin
(

let tupn = (

let uu____6086 = (FStar_Parser_Const.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____6086 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____6096 = (

let uu____6097 = (

let uu____6112 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (

let uu____6115 = (

let uu____6124 = (

let uu____6133 = (

let uu____6134 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____6134))
in (uu____6133)::[])
in (FStar_List.append args uu____6124))
in ((uu____6112), (uu____6115))))
in FStar_Syntax_Syntax.Tm_app (uu____6097))
in (mk1 uu____6096))
in (

let p2 = (

let uu____6154 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p1), (false)))::[])))))) uu____6154))
in FStar_Pervasives_Native.Some (((sc1), (p2))))))
end
| uu____6189 -> begin
(failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt1)))
end)
in (match (uu____5806) with
| (b1, sc_pat_opt1) -> begin
(aux env2 ((b1)::bs) sc_pat_opt1 rest)
end)))
end))
end))
in (aux env [] FStar_Pervasives_Native.None binders2))))
end)))
end
| FStar_Parser_AST.App (uu____6256, uu____6257, FStar_Parser_AST.UnivApp) -> begin
(

let rec aux = (fun universes e -> (

let uu____6271 = (

let uu____6272 = (unparen e)
in uu____6272.FStar_Parser_AST.tm)
in (match (uu____6271) with
| FStar_Parser_AST.App (e1, t, FStar_Parser_AST.UnivApp) -> begin
(

let univ_arg = (desugar_universe t)
in (aux ((univ_arg)::universes) e1))
end
| uu____6278 -> begin
(

let head1 = (desugar_term env e)
in (mk1 (FStar_Syntax_Syntax.Tm_uinst (((head1), (universes))))))
end)))
in (aux [] top))
end
| FStar_Parser_AST.App (uu____6282) -> begin
(

let rec aux = (fun args e -> (

let uu____6314 = (

let uu____6315 = (unparen e)
in uu____6315.FStar_Parser_AST.tm)
in (match (uu____6314) with
| FStar_Parser_AST.App (e1, t, imp) when (Prims.op_disEquality imp FStar_Parser_AST.UnivApp) -> begin
(

let arg = (

let uu____6328 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) uu____6328))
in (aux ((arg)::args) e1))
end
| uu____6341 -> begin
(

let head1 = (desugar_term env e)
in (mk1 (FStar_Syntax_Syntax.Tm_app (((head1), (args))))))
end)))
in (aux [] top))
end
| FStar_Parser_AST.Bind (x, t1, t2) -> begin
(

let xpat = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (FStar_Pervasives_Native.None)))) x.FStar_Ident.idRange)
in (

let k = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs ((((xpat)::[]), (t2)))) t2.FStar_Parser_AST.range t2.FStar_Parser_AST.level)
in (

let bind1 = (

let uu____6367 = (

let uu____6368 = (FStar_Ident.lid_of_path (("bind")::[]) x.FStar_Ident.idRange)
in FStar_Parser_AST.Var (uu____6368))
in (FStar_Parser_AST.mk_term uu____6367 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let uu____6369 = (FStar_Parser_AST.mkExplicitApp bind1 ((t1)::(k)::[]) top.FStar_Parser_AST.range)
in (desugar_term env uu____6369)))))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(

let uu____6372 = (

let uu____6373 = (

let uu____6380 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((uu____6380), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))
in FStar_Syntax_Syntax.Tm_meta (uu____6373))
in (mk1 uu____6372))
end
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(

let env1 = (FStar_ToSyntax_Env.push_namespace env lid)
in (

let uu____6398 = (

let uu____6403 = (FStar_ToSyntax_Env.expect_typ env1)
in (match (uu____6403) with
| true -> begin
desugar_typ
end
| uu____6408 -> begin
desugar_term
end))
in (uu____6398 env1 e)))
end
| FStar_Parser_AST.Let (qual1, ((pat, _snd))::_tl, body) -> begin
(

let is_rec = (Prims.op_Equality qual1 FStar_Parser_AST.Rec)
in (

let ds_let_rec_or_app = (fun uu____6436 -> (

let bindings = (((pat), (_snd)))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun uu____6522 -> (match (uu____6522) with
| (p, def) -> begin
(

let uu____6547 = (is_app_pattern p)
in (match (uu____6547) with
| true -> begin
(

let uu____6566 = (destruct_app_pattern env top_level p)
in ((uu____6566), (def)))
end
| uu____6595 -> begin
(match ((FStar_Parser_AST.un_function p def)) with
| FStar_Pervasives_Native.Some (p1, def1) -> begin
(

let uu____6620 = (destruct_app_pattern env top_level p1)
in ((uu____6620), (def1)))
end
| uu____6649 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, uu____6675); FStar_Parser_AST.prange = uu____6676}, t) -> begin
(match (top_level) with
| true -> begin
(

let uu____6700 = (

let uu____6715 = (

let uu____6720 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (uu____6720))
in ((uu____6715), ([]), (FStar_Pervasives_Native.Some (t))))
in ((uu____6700), (def)))
end
| uu____6743 -> begin
((((FStar_Util.Inl (id)), ([]), (FStar_Pervasives_Native.Some (t)))), (def))
end)
end
| FStar_Parser_AST.PatVar (id, uu____6767) -> begin
(match (top_level) with
| true -> begin
(

let uu____6790 = (

let uu____6805 = (

let uu____6810 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (uu____6810))
in ((uu____6805), ([]), (FStar_Pervasives_Native.None)))
in ((uu____6790), (def)))
end
| uu____6833 -> begin
((((FStar_Util.Inl (id)), ([]), (FStar_Pervasives_Native.None))), (def))
end)
end
| uu____6856 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end))
end))))
in (

let uu____6875 = (FStar_List.fold_left (fun uu____6935 uu____6936 -> (match (((uu____6935), (uu____6936))) with
| ((env1, fnames, rec_bindings), ((f, uu____7019, uu____7020), uu____7021)) -> begin
(

let uu____7100 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let uu____7126 = (FStar_ToSyntax_Env.push_bv env1 x)
in (match (uu____7126) with
| (env2, xx) -> begin
(

let uu____7145 = (

let uu____7148 = (FStar_Syntax_Syntax.mk_binder xx)
in (uu____7148)::rec_bindings)
in ((env2), (FStar_Util.Inl (xx)), (uu____7145)))
end))
end
| FStar_Util.Inr (l) -> begin
(

let uu____7156 = (FStar_ToSyntax_Env.push_top_level_rec_binding env1 l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in ((uu____7156), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (uu____7100) with
| (env2, lbname, rec_bindings1) -> begin
((env2), ((lbname)::fnames), (rec_bindings1))
end))
end)) ((env), ([]), ([])) funs)
in (match (uu____6875) with
| (env', fnames, rec_bindings) -> begin
(

let fnames1 = (FStar_List.rev fnames)
in (

let rec_bindings1 = (FStar_List.rev rec_bindings)
in (

let desugar_one_def = (fun env1 lbname uu____7282 -> (match (uu____7282) with
| ((uu____7305, args, result_t), def) -> begin
(

let args1 = (FStar_All.pipe_right args (FStar_List.map replace_unit_pattern))
in (

let def1 = (match (result_t) with
| FStar_Pervasives_Native.None -> begin
def
end
| FStar_Pervasives_Native.Some (t) -> begin
(

let t1 = (

let uu____7349 = (is_comp_type env1 t)
in (match (uu____7349) with
| true -> begin
((

let uu____7351 = (FStar_All.pipe_right args1 (FStar_List.tryFind (fun x -> (

let uu____7361 = (is_var_pattern x)
in (not (uu____7361))))))
in (match (uu____7351) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (p) -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable"), (p.FStar_Parser_AST.prange)))))
end));
t;
)
end
| uu____7363 -> begin
(

let uu____7364 = (((FStar_Options.ml_ish ()) && (

let uu____7366 = (FStar_ToSyntax_Env.try_lookup_effect_name env1 FStar_Parser_Const.effect_ML_lid)
in (FStar_Option.isSome uu____7366))) && ((not (is_rec)) || (Prims.op_disEquality (FStar_List.length args1) (Prims.parse_int "0"))))
in (match (uu____7364) with
| true -> begin
(FStar_Parser_AST.ml_comp t)
end
| uu____7369 -> begin
(FStar_Parser_AST.tot_comp t)
end))
end))
in (

let uu____7370 = (FStar_Range.union_ranges t1.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t1), (FStar_Pervasives_Native.None)))) uu____7370 FStar_Parser_AST.Expr)))
end)
in (

let def2 = (match (args1) with
| [] -> begin
def1
end
| uu____7374 -> begin
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

let uu____7389 = (

let uu____7390 = (FStar_Syntax_Util.incr_delta_qualifier body1)
in (FStar_Syntax_Syntax.lid_as_fv l uu____7390 FStar_Pervasives_Native.None))
in FStar_Util.Inr (uu____7389))
end)
in (

let body2 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.close rec_bindings1 body1)
end
| uu____7392 -> begin
body1
end)
in (mk_lb ((lbname1), (FStar_Syntax_Syntax.tun), (body2)))))))))
end))
in (

let lbs = (FStar_List.map2 (desugar_one_def (match (is_rec) with
| true -> begin
env'
end
| uu____7422 -> begin
env
end)) fnames1 funs)
in (

let body1 = (desugar_term env' body)
in (

let uu____7424 = (

let uu____7425 = (

let uu____7438 = (FStar_Syntax_Subst.close rec_bindings1 body1)
in ((((is_rec), (lbs))), (uu____7438)))
in FStar_Syntax_Syntax.Tm_let (uu____7425))
in (FStar_All.pipe_left mk1 uu____7424)))))))
end)))))
in (

let ds_non_rec = (fun pat1 t1 t2 -> (

let t11 = (desugar_term env t1)
in (

let is_mutable = (Prims.op_Equality qual1 FStar_Parser_AST.Mutable)
in (

let t12 = (match (is_mutable) with
| true -> begin
(mk_ref_alloc t11)
end
| uu____7468 -> begin
t11
end)
in (

let uu____7469 = (desugar_binding_pat_maybe_top top_level env pat1 is_mutable)
in (match (uu____7469) with
| (env1, binder, pat2) -> begin
(

let tm = (match (binder) with
| LetBinder (l, t) -> begin
(

let body1 = (desugar_term env1 t2)
in (

let fv = (

let uu____7496 = (FStar_Syntax_Util.incr_delta_qualifier t12)
in (FStar_Syntax_Syntax.lid_as_fv l uu____7496 FStar_Pervasives_Native.None))
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_let (((((false), (({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t12})::[]))), (body1)))))))
end
| LocalBinder (x, uu____7508) -> begin
(

let body1 = (desugar_term env1 t2)
in (

let body2 = (match (pat2) with
| [] -> begin
body1
end
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (uu____7511); FStar_Syntax_Syntax.p = uu____7512})::[] -> begin
body1
end
| uu____7517 -> begin
(

let uu____7520 = (

let uu____7523 = (

let uu____7524 = (

let uu____7547 = (FStar_Syntax_Syntax.bv_to_name x)
in (

let uu____7548 = (desugar_disjunctive_pattern pat2 FStar_Pervasives_Native.None body1)
in ((uu____7547), (uu____7548))))
in FStar_Syntax_Syntax.Tm_match (uu____7524))
in (FStar_Syntax_Syntax.mk uu____7523))
in (uu____7520 FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
end)
in (

let uu____7558 = (

let uu____7559 = (

let uu____7572 = (

let uu____7573 = (

let uu____7574 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____7574)::[])
in (FStar_Syntax_Subst.close uu____7573 body2))
in ((((false), (((mk_lb ((FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t12))))::[]))), (uu____7572)))
in FStar_Syntax_Syntax.Tm_let (uu____7559))
in (FStar_All.pipe_left mk1 uu____7558))))
end)
in (match (is_mutable) with
| true -> begin
(FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((tm), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc))))))
end
| uu____7599 -> begin
tm
end))
end))))))
in (

let uu____7600 = (is_rec || (is_app_pattern pat))
in (match (uu____7600) with
| true -> begin
(ds_let_rec_or_app ())
end
| uu____7601 -> begin
(ds_non_rec pat _snd body)
end)))))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (

let t_bool1 = (

let uu____7609 = (

let uu____7610 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Syntax_Syntax.Tm_fvar (uu____7610))
in (mk1 uu____7609))
in (

let uu____7611 = (

let uu____7612 = (

let uu____7635 = (

let uu____7638 = (desugar_term env t1)
in (FStar_Syntax_Util.ascribe uu____7638 ((FStar_Util.Inl (t_bool1)), (FStar_Pervasives_Native.None))))
in (

let uu____7659 = (

let uu____7674 = (

let uu____7687 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) t2.FStar_Parser_AST.range)
in (

let uu____7690 = (desugar_term env t2)
in ((uu____7687), (FStar_Pervasives_Native.None), (uu____7690))))
in (

let uu____7699 = (

let uu____7714 = (

let uu____7727 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) t3.FStar_Parser_AST.range)
in (

let uu____7730 = (desugar_term env t3)
in ((uu____7727), (FStar_Pervasives_Native.None), (uu____7730))))
in (uu____7714)::[])
in (uu____7674)::uu____7699))
in ((uu____7635), (uu____7659))))
in FStar_Syntax_Syntax.Tm_match (uu____7612))
in (mk1 uu____7611))))
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
in (desugar_term env a2))))))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(

let desugar_branch = (fun uu____7871 -> (match (uu____7871) with
| (pat, wopt, b) -> begin
(

let uu____7889 = (desugar_match_pat env pat)
in (match (uu____7889) with
| (env1, pat1) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (e1) -> begin
(

let uu____7910 = (desugar_term env1 e1)
in FStar_Pervasives_Native.Some (uu____7910))
end)
in (

let b1 = (desugar_term env1 b)
in (desugar_disjunctive_pattern pat1 wopt1 b1)))
end))
end))
in (

let uu____7912 = (

let uu____7913 = (

let uu____7936 = (desugar_term env e)
in (

let uu____7937 = (FStar_List.collect desugar_branch branches)
in ((uu____7936), (uu____7937))))
in FStar_Syntax_Syntax.Tm_match (uu____7913))
in (FStar_All.pipe_left mk1 uu____7912)))
end
| FStar_Parser_AST.Ascribed (e, t, tac_opt) -> begin
(

let annot = (

let uu____7966 = (is_comp_type env t)
in (match (uu____7966) with
| true -> begin
(

let uu____7973 = (desugar_comp t.FStar_Parser_AST.range env t)
in FStar_Util.Inr (uu____7973))
end
| uu____7978 -> begin
(

let uu____7979 = (desugar_term env t)
in FStar_Util.Inl (uu____7979))
end))
in (

let tac_opt1 = (FStar_Util.map_opt tac_opt (desugar_term env))
in (

let uu____7985 = (

let uu____7986 = (

let uu____8013 = (desugar_term env e)
in ((uu____8013), (((annot), (tac_opt1))), (FStar_Pervasives_Native.None)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____7986))
in (FStar_All.pipe_left mk1 uu____7985))))
end
| FStar_Parser_AST.Record (uu____8038, []) -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let record = (check_fields env fields top.FStar_Parser_AST.range)
in (

let user_ns = (

let uu____8075 = (FStar_List.hd fields)
in (match (uu____8075) with
| (f, uu____8087) -> begin
f.FStar_Ident.ns
end))
in (

let get_field = (fun xopt f -> (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun uu____8129 -> (match (uu____8129) with
| (g, uu____8135) -> begin
(Prims.op_Equality f.FStar_Ident.idText g.FStar_Ident.ident.FStar_Ident.idText)
end))))
in (

let fn = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((f)::[])))
in (match (found) with
| FStar_Pervasives_Native.Some (uu____8141, e) -> begin
((fn), (e))
end
| FStar_Pervasives_Native.None -> begin
(match (xopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8155 = (

let uu____8156 = (

let uu____8161 = (FStar_Util.format2 "Field %s of record type %s is missing" f.FStar_Ident.idText record.FStar_ToSyntax_Env.typename.FStar_Ident.str)
in ((uu____8161), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____8156))
in (FStar_Exn.raise uu____8155))
end
| FStar_Pervasives_Native.Some (x) -> begin
((fn), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Project (((x), (fn)))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end))))
in (

let user_constrname = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((record.FStar_ToSyntax_Env.constrname)::[])))
in (

let recterm = (match (eopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8169 = (

let uu____8180 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____8211 -> (match (uu____8211) with
| (f, uu____8221) -> begin
(

let uu____8222 = (

let uu____8223 = (get_field FStar_Pervasives_Native.None f)
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____8223))
in ((uu____8222), (FStar_Parser_AST.Nothing)))
end))))
in ((user_constrname), (uu____8180)))
in FStar_Parser_AST.Construct (uu____8169))
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (

let uu____8241 = (

let uu____8242 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____8242))
in (FStar_Parser_AST.mk_term uu____8241 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record1 = (

let uu____8244 = (

let uu____8257 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____8287 -> (match (uu____8287) with
| (f, uu____8297) -> begin
(get_field (FStar_Pervasives_Native.Some (xterm)) f)
end))))
in ((FStar_Pervasives_Native.None), (uu____8257)))
in FStar_Parser_AST.Record (uu____8244))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (FStar_Pervasives_Native.None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record1 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm1 = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_term env recterm1)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____8325; FStar_Syntax_Syntax.vars = uu____8326}, args); FStar_Syntax_Syntax.pos = uu____8328; FStar_Syntax_Syntax.vars = uu____8329}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(

let e1 = (

let uu____8357 = (

let uu____8358 = (

let uu____8373 = (

let uu____8374 = (

let uu____8377 = (

let uu____8378 = (

let uu____8385 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map FStar_Pervasives_Native.fst))
in ((record.FStar_ToSyntax_Env.typename), (uu____8385)))
in FStar_Syntax_Syntax.Record_ctor (uu____8378))
in FStar_Pervasives_Native.Some (uu____8377))
in (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant uu____8374))
in ((uu____8373), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____8358))
in (FStar_All.pipe_left mk1 uu____8357))
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((e1), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))))))
end
| uu____8416 -> begin
e
end))))))))
end
| FStar_Parser_AST.Project (e, f) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f);
(

let uu____8420 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f)
in (match (uu____8420) with
| (constrname, is_rec) -> begin
(

let e1 = (desugar_term env e)
in (

let projname = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname f.FStar_Ident.ident)
in (

let qual1 = (match (is_rec) with
| true -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_projector (((constrname), (f.FStar_Ident.ident))))
end
| uu____8438 -> begin
FStar_Pervasives_Native.None
end)
in (

let uu____8439 = (

let uu____8440 = (

let uu____8455 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projname (FStar_Ident.range_of_lid f)) FStar_Syntax_Syntax.Delta_equational qual1)
in (

let uu____8456 = (

let uu____8459 = (FStar_Syntax_Syntax.as_arg e1)
in (uu____8459)::[])
in ((uu____8455), (uu____8456))))
in FStar_Syntax_Syntax.Tm_app (uu____8440))
in (FStar_All.pipe_left mk1 uu____8439)))))
end));
)
end
| FStar_Parser_AST.NamedTyp (uu____8464, e) -> begin
(desugar_term env e)
end
| FStar_Parser_AST.Paren (e) -> begin
(desugar_term env e)
end
| uu____8467 when (Prims.op_Equality top.FStar_Parser_AST.level FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| uu____8468 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Let (uu____8469, uu____8470, uu____8471) -> begin
(failwith "Not implemented yet")
end
| FStar_Parser_AST.QForall (uu____8484, uu____8485, uu____8486) -> begin
(failwith "Not implemented yet")
end
| FStar_Parser_AST.QExists (uu____8499, uu____8500, uu____8501) -> begin
(failwith "Not implemented yet")
end)))))
and not_ascribed : FStar_Parser_AST.term  ->  Prims.bool = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Ascribed (uu____8515) -> begin
false
end
| uu____8524 -> begin
true
end))
and is_synth_by_tactic : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun e t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (l, r, FStar_Parser_AST.Hash) -> begin
(is_synth_by_tactic e l)
end
| FStar_Parser_AST.Var (lid) -> begin
(

let uu____8530 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name e lid)
in (match (uu____8530) with
| FStar_Pervasives_Native.Some (lid1) -> begin
(FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid)
end
| FStar_Pervasives_Native.None -> begin
false
end))
end
| uu____8534 -> begin
false
end))
and desugar_args : FStar_ToSyntax_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____8571 -> (match (uu____8571) with
| (a, imp) -> begin
(

let uu____8584 = (desugar_term env a)
in (arg_withimp_e imp uu____8584))
end)))))
and desugar_comp : FStar_Range.range  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun r env t -> (

let fail = (fun msg -> (FStar_Exn.raise (FStar_Errors.Error (((msg), (r))))))
in (

let is_requires = (fun uu____8603 -> (match (uu____8603) with
| (t1, uu____8609) -> begin
(

let uu____8610 = (

let uu____8611 = (unparen t1)
in uu____8611.FStar_Parser_AST.tm)
in (match (uu____8610) with
| FStar_Parser_AST.Requires (uu____8612) -> begin
true
end
| uu____8619 -> begin
false
end))
end))
in (

let is_ensures = (fun uu____8627 -> (match (uu____8627) with
| (t1, uu____8633) -> begin
(

let uu____8634 = (

let uu____8635 = (unparen t1)
in uu____8635.FStar_Parser_AST.tm)
in (match (uu____8634) with
| FStar_Parser_AST.Ensures (uu____8636) -> begin
true
end
| uu____8643 -> begin
false
end))
end))
in (

let is_app = (fun head1 uu____8654 -> (match (uu____8654) with
| (t1, uu____8660) -> begin
(

let uu____8661 = (

let uu____8662 = (unparen t1)
in uu____8662.FStar_Parser_AST.tm)
in (match (uu____8661) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = uu____8664; FStar_Parser_AST.level = uu____8665}, uu____8666, uu____8667) -> begin
(Prims.op_Equality d.FStar_Ident.ident.FStar_Ident.idText head1)
end
| uu____8668 -> begin
false
end))
end))
in (

let is_smt_pat = (fun uu____8676 -> (match (uu____8676) with
| (t1, uu____8682) -> begin
(

let uu____8683 = (

let uu____8684 = (unparen t1)
in uu____8684.FStar_Parser_AST.tm)
in (match (uu____8683) with
| FStar_Parser_AST.Construct (cons1, (({FStar_Parser_AST.tm = FStar_Parser_AST.Construct (smtpat, uu____8687); FStar_Parser_AST.range = uu____8688; FStar_Parser_AST.level = uu____8689}, uu____8690))::(uu____8691)::[]) -> begin
((FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid) && (FStar_Util.for_some (fun s -> (Prims.op_Equality smtpat.FStar_Ident.str s)) (("SMTPat")::("SMTPatT")::("SMTPatOr")::[])))
end
| FStar_Parser_AST.Construct (cons1, (({FStar_Parser_AST.tm = FStar_Parser_AST.Var (smtpat); FStar_Parser_AST.range = uu____8730; FStar_Parser_AST.level = uu____8731}, uu____8732))::(uu____8733)::[]) -> begin
((FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid) && (FStar_Util.for_some (fun s -> (Prims.op_Equality smtpat.FStar_Ident.str s)) (("smt_pat")::("smt_pat_or")::[])))
end
| uu____8758 -> begin
false
end))
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t1 -> (

let uu____8786 = (head_and_args t1)
in (match (uu____8786) with
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

let ens_true = (

let ens = FStar_Parser_AST.Ensures ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.true_lid)) t1.FStar_Parser_AST.range FStar_Parser_AST.Formula)), (FStar_Pervasives_Native.None)))
in (((FStar_Parser_AST.mk_term ens t1.FStar_Parser_AST.range FStar_Parser_AST.Type_level)), (FStar_Parser_AST.Nothing)))
in (

let fail_lemma = (fun uu____8879 -> (

let expected_one_of = ("Lemma post")::("Lemma (ensures post)")::("Lemma (requires pre) (ensures post)")::("Lemma post [SMTPat ...]")::("Lemma (ensures post) [SMTPat ...]")::("Lemma (ensures post) (decreases d)")::("Lemma (ensures post) (decreases d) [SMTPat ...]")::("Lemma (requires pre) (ensures post) (decreases d)")::("Lemma (requires pre) (ensures post) [SMTPat ...]")::("Lemma (requires pre) (ensures post) (decreases d) [SMTPat ...]")::[]
in (

let msg = (FStar_String.concat "\n\t" expected_one_of)
in (FStar_Exn.raise (FStar_Errors.Error ((((Prims.strcat "Invalid arguments to \'Lemma\'; expected one of the following:\n\t" msg)), (t1.FStar_Parser_AST.range))))))))
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
(unit_tm)::(req_true)::(ens)::(nil_pat)::[]
end
| (req)::(ens)::[] when ((is_requires req) && (is_ensures ens)) -> begin
(unit_tm)::(req)::(ens)::(nil_pat)::[]
end
| (ens)::(smtpat)::[] when ((((

let uu____9045 = (is_requires ens)
in (not (uu____9045))) && (

let uu____9047 = (is_smt_pat ens)
in (not (uu____9047)))) && (

let uu____9049 = (is_decreases ens)
in (not (uu____9049)))) && (is_smt_pat smtpat)) -> begin
(unit_tm)::(req_true)::(ens)::(smtpat)::[]
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
| (req)::(ens)::(smtpat)::[] when (((is_requires req) && (is_ensures ens)) && (is_smt_pat smtpat)) -> begin
(unit_tm)::args
end
| (req)::(ens)::(dec)::(smtpat)::[] when ((((is_requires req) && (is_ensures ens)) && (is_smt_pat smtpat)) && (is_decreases dec)) -> begin
(unit_tm)::args
end
| _other -> begin
(fail_lemma ())
end)
in (

let head_and_attributes = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes env) lemma)
in ((head_and_attributes), (args1)))))))))
end
| FStar_Parser_AST.Name (l) when (FStar_ToSyntax_Env.is_effect_name env l) -> begin
(

let uu____9338 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes env) l)
in ((uu____9338), (args)))
end
| FStar_Parser_AST.Name (l) when ((

let uu____9366 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals uu____9366 FStar_Parser_Const.prims_lid)) && (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Tot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Parser_Const.effect_Tot_lid head1.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when ((

let uu____9384 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals uu____9384 FStar_Parser_Const.prims_lid)) && (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "GTot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Parser_Const.effect_GTot_lid head1.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when (((Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Type") || (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Type0")) || (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Effect")) -> begin
(((((FStar_Ident.set_lid_range FStar_Parser_Const.effect_Tot_lid head1.FStar_Parser_AST.range)), ([]))), ((((t1), (FStar_Parser_AST.Nothing)))::[]))
end
| uu____9422 -> begin
(

let default_effect = (

let uu____9424 = (FStar_Options.ml_ish ())
in (match (uu____9424) with
| true -> begin
FStar_Parser_Const.effect_ML_lid
end
| uu____9425 -> begin
((

let uu____9427 = (FStar_Options.warn_default_effects ())
in (match (uu____9427) with
| true -> begin
(FStar_Errors.warn head1.FStar_Parser_AST.range "Using default effect Tot")
end
| uu____9428 -> begin
()
end));
FStar_Parser_Const.effect_Tot_lid;
)
end))
in (((((FStar_Ident.set_lid_range default_effect head1.FStar_Parser_AST.range)), ([]))), ((((t1), (FStar_Parser_AST.Nothing)))::[])))
end)
end)))
in (

let uu____9451 = (pre_process_comp_typ t)
in (match (uu____9451) with
| ((eff, cattributes), args) -> begin
((match ((Prims.op_Equality (FStar_List.length args) (Prims.parse_int "0"))) with
| true -> begin
(

let uu____9500 = (

let uu____9501 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" uu____9501))
in (fail uu____9500))
end
| uu____9502 -> begin
()
end);
(

let is_universe = (fun uu____9510 -> (match (uu____9510) with
| (uu____9515, imp) -> begin
(Prims.op_Equality imp FStar_Parser_AST.UnivApp)
end))
in (

let uu____9517 = (FStar_Util.take is_universe args)
in (match (uu____9517) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun uu____9576 -> (match (uu____9576) with
| (u, imp) -> begin
(desugar_universe u)
end)) universes)
in (

let uu____9583 = (

let uu____9598 = (FStar_List.hd args1)
in (

let uu____9607 = (FStar_List.tl args1)
in ((uu____9598), (uu____9607))))
in (match (uu____9583) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (FStar_Pervasives_Native.fst result_arg))
in (

let rest1 = (desugar_args env rest)
in (

let uu____9662 = (

let is_decrease = (fun uu____9698 -> (match (uu____9698) with
| (t1, uu____9708) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____9718; FStar_Syntax_Syntax.vars = uu____9719}, (uu____9720)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.decreases_lid)
end
| uu____9751 -> begin
false
end)
end))
in (FStar_All.pipe_right rest1 (FStar_List.partition is_decrease)))
in (match (uu____9662) with
| (dec, rest2) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun uu____9865 -> (match (uu____9865) with
| (t1, uu____9875) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____9884, ((arg, uu____9886))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| uu____9915 -> begin
(failwith "impos")
end)
end))))
in (

let no_additional_args = (

let is_empty = (fun l -> (match (l) with
| [] -> begin
true
end
| uu____9929 -> begin
false
end))
in ((((is_empty decreases_clause) && (is_empty rest2)) && (is_empty cattributes)) && (is_empty universes1)))
in (match ((no_additional_args && (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid))) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end
| uu____9942 -> begin
(match ((no_additional_args && (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid))) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end
| uu____9945 -> begin
(

let flags = (match ((FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Lemma_lid)) with
| true -> begin
(FStar_Syntax_Syntax.LEMMA)::[]
end
| uu____9951 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____9954 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Parser_Const.effect_ML_lid)) with
| true -> begin
(FStar_Syntax_Syntax.MLEFFECT)::[]
end
| uu____9957 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____9960 -> begin
[]
end)
end)
end)
end)
in (

let flags1 = (FStar_List.append flags cattributes)
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
| uu____10077 -> begin
pat
end)
in (

let uu____10078 = (

let uu____10089 = (

let uu____10100 = (

let uu____10109 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat1), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) FStar_Pervasives_Native.None pat1.FStar_Syntax_Syntax.pos)
in ((uu____10109), (aq)))
in (uu____10100)::[])
in (ens)::uu____10089)
in (req)::uu____10078))
end
| uu____10150 -> begin
rest2
end)
end
| uu____10161 -> begin
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
| uu____10172 -> begin
FStar_Pervasives_Native.None
end))
in (

let mk1 = (fun t -> (FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let uu___249_10189 = t
in {FStar_Syntax_Syntax.n = uu___249_10189.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___249_10189.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let uu___250_10223 = b
in {FStar_Parser_AST.b = uu___250_10223.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___250_10223.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___250_10223.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env1 pats1 -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (

let uu____10282 = (desugar_term env1 e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) uu____10282)))))) pats1))
in (match (tk) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____10295 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____10295) with
| (env1, a1) -> begin
(

let a2 = (

let uu___251_10305 = a1
in {FStar_Syntax_Syntax.ppname = uu___251_10305.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___251_10305.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats1 = (desugar_pats env1 pats)
in (

let body1 = (desugar_formula env1 body)
in (

let body2 = (match (pats1) with
| [] -> begin
body1
end
| uu____10327 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_meta (((body1), (FStar_Syntax_Syntax.Meta_pattern (pats1))))))
end)
in (

let body3 = (

let uu____10341 = (

let uu____10344 = (

let uu____10345 = (FStar_Syntax_Syntax.mk_binder a2)
in (uu____10345)::[])
in (no_annot_abs uu____10344 body2))
in (FStar_All.pipe_left setpos uu____10341))
in (

let uu____10350 = (

let uu____10351 = (

let uu____10366 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let uu____10367 = (

let uu____10370 = (FStar_Syntax_Syntax.as_arg body3)
in (uu____10370)::[])
in ((uu____10366), (uu____10367))))
in FStar_Syntax_Syntax.Tm_app (uu____10351))
in (FStar_All.pipe_left mk1 uu____10350)))))))
end))
end
| uu____10375 -> begin
(failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body1 = (

let uu____10447 = (q ((rest), (pats), (body)))
in (

let uu____10454 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term uu____10447 uu____10454 FStar_Parser_AST.Formula)))
in (

let uu____10455 = (q (((b)::[]), ([]), (body1)))
in (FStar_Parser_AST.mk_term uu____10455 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| uu____10464 -> begin
(failwith "impossible")
end))
in (

let uu____10467 = (

let uu____10468 = (unparen f)
in uu____10468.FStar_Parser_AST.tm)
in (match (uu____10467) with
| FStar_Parser_AST.Labeled (f1, l, p) -> begin
(

let f2 = (desugar_formula env f1)
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((f2), (FStar_Syntax_Syntax.Meta_labeled (((l), (f2.FStar_Syntax_Syntax.pos), (p)))))))))
end
| FStar_Parser_AST.QForall ([], uu____10475, uu____10476) -> begin
(failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QExists ([], uu____10487, uu____10488) -> begin
(failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____10519 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env uu____10519)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____10555 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env uu____10555)))
end
| FStar_Parser_AST.QForall ((b)::[], pats, body) -> begin
(desugar_quant FStar_Parser_Const.forall_lid b pats body)
end
| FStar_Parser_AST.QExists ((b)::[], pats, body) -> begin
(desugar_quant FStar_Parser_Const.exists_lid b pats body)
end
| FStar_Parser_AST.Paren (f1) -> begin
(desugar_formula env f1)
end
| uu____10598 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_ToSyntax_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list) = (fun env bs -> (

let uu____10603 = (FStar_List.fold_left (fun uu____10639 b -> (match (uu____10639) with
| (env1, out) -> begin
(

let tk = (desugar_binder env1 (

let uu___252_10691 = b
in {FStar_Parser_AST.b = uu___252_10691.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___252_10691.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___252_10691.FStar_Parser_AST.aqual}))
in (match (tk) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____10708 = (FStar_ToSyntax_Env.push_bv env1 a)
in (match (uu____10708) with
| (env2, a1) -> begin
(

let a2 = (

let uu___253_10728 = a1
in {FStar_Syntax_Syntax.ppname = uu___253_10728.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___253_10728.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in ((env2), ((((a2), ((trans_aqual b.FStar_Parser_AST.aqual))))::out)))
end))
end
| uu____10745 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (uu____10603) with
| (env1, tpars) -> begin
((env1), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.TAnnotated (x, t) -> begin
(

let uu____10832 = (desugar_typ env t)
in ((FStar_Pervasives_Native.Some (x)), (uu____10832)))
end
| FStar_Parser_AST.Annotated (x, t) -> begin
(

let uu____10837 = (desugar_typ env t)
in ((FStar_Pervasives_Native.Some (x)), (uu____10837)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____10841 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) FStar_Pervasives_Native.None x.FStar_Ident.idRange)
in ((FStar_Pervasives_Native.Some (x)), (uu____10841)))
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____10849 = (desugar_typ env t)
in ((FStar_Pervasives_Native.None), (uu____10849)))
end
| FStar_Parser_AST.Variable (x) -> begin
((FStar_Pervasives_Native.Some (x)), (FStar_Syntax_Syntax.tun))
end))


let mk_data_discriminators : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_ToSyntax_Env.env  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun quals env datas -> (

let quals1 = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___221_10885 -> (match (uu___221_10885) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____10886 -> begin
false
end))))
in (

let quals2 = (fun q -> (

let uu____10897 = ((

let uu____10900 = (FStar_ToSyntax_Env.iface env)
in (not (uu____10900))) || (FStar_ToSyntax_Env.admitted_iface env))
in (match (uu____10897) with
| true -> begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals1)
end
| uu____10903 -> begin
(FStar_List.append q quals1)
end)))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (

let uu____10913 = (quals2 ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((disc_name), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid disc_name); FStar_Syntax_Syntax.sigquals = uu____10913; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))))))))


let mk_indexed_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  FStar_ToSyntax_Env.env  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq env lid fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let uu____10949 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____10979 -> (match (uu____10979) with
| (x, uu____10987) -> begin
(

let uu____10988 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____10988) with
| (field_name, uu____10996) -> begin
(

let only_decl = (((

let uu____11000 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____11000)) || (Prims.op_disEquality fvq FStar_Syntax_Syntax.Data_ctor)) || (

let uu____11002 = (

let uu____11003 = (FStar_ToSyntax_Env.current_module env)
in uu____11003.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____11002)))
in (

let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____11017 = (FStar_List.filter (fun uu___222_11021 -> (match (uu___222_11021) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____11022 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____11017)
end
| uu____11023 -> begin
q
end))
in (

let quals1 = (

let iquals1 = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___223_11035 -> (match (uu___223_11035) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____11036 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals1)))
in (

let decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid field_name); FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____11042 -> begin
(

let dd = (

let uu____11044 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____11044) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____11047 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lb = (

let uu____11049 = (

let uu____11054 = (FStar_Syntax_Syntax.lid_as_fv field_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____11054))
in {FStar_Syntax_Syntax.lbname = uu____11049; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = FStar_Syntax_Syntax.tun})
in (

let impl = (

let uu____11056 = (

let uu____11057 = (

let uu____11064 = (

let uu____11067 = (

let uu____11068 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____11068 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____11067)::[])
in ((((false), ((lb)::[]))), (uu____11064)))
in FStar_Syntax_Syntax.Sig_let (uu____11057))
in {FStar_Syntax_Syntax.sigel = uu____11056; FStar_Syntax_Syntax.sigrng = p; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____11087 -> begin
(decl)::(impl)::[]
end))))
end))))))
end))
end))))
in (FStar_All.pipe_right uu____10949 FStar_List.flatten))))


let mk_data_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_ToSyntax_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____11115, t, uu____11117, n1, uu____11119) when (not ((FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid))) -> begin
(

let uu____11124 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____11124) with
| (formals, uu____11140) -> begin
(match (formals) with
| [] -> begin
[]
end
| uu____11163 -> begin
(

let filter_records = (fun uu___224_11175 -> (match (uu___224_11175) with
| FStar_Syntax_Syntax.RecordConstructor (uu____11178, fns) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| uu____11190 -> begin
FStar_Pervasives_Native.None
end))
in (

let fv_qual = (

let uu____11192 = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals filter_records)
in (match (uu____11192) with
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
| uu____11201 -> begin
iquals
end)
in (

let uu____11202 = (FStar_Util.first_N n1 formals)
in (match (uu____11202) with
| (uu____11225, rest) -> begin
(mk_indexed_projector_names iquals1 fv_qual env lid rest)
end)))))
end)
end))
end
| uu____11251 -> begin
[]
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (

let dd = (

let uu____11309 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____11309) with
| true -> begin
(

let uu____11312 = (FStar_Syntax_Util.incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (uu____11312))
end
| uu____11313 -> begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end))
in (

let lb = (

let uu____11315 = (

let uu____11320 = (FStar_Syntax_Syntax.lid_as_fv lid dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____11320))
in (

let uu____11321 = (

let uu____11324 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars uu____11324))
in (

let uu____11327 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = uu____11315; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____11321; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____11327})))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (lids))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))


let rec desugar_tycon : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d quals tcs -> (

let rng = d.FStar_Parser_AST.drange
in (

let tycon_id = (fun uu___225_11376 -> (match (uu___225_11376) with
| FStar_Parser_AST.TyconAbstract (id, uu____11378, uu____11379) -> begin
id
end
| FStar_Parser_AST.TyconAbbrev (id, uu____11389, uu____11390, uu____11391) -> begin
id
end
| FStar_Parser_AST.TyconRecord (id, uu____11401, uu____11402, uu____11403) -> begin
id
end
| FStar_Parser_AST.TyconVariant (id, uu____11433, uu____11434, uu____11435) -> begin
id
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (x, uu____11477) -> begin
(

let uu____11478 = (

let uu____11479 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____11479))
in (FStar_Parser_AST.mk_term uu____11478 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| FStar_Parser_AST.Variable (x) -> begin
(

let uu____11481 = (

let uu____11482 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____11482))
in (FStar_Parser_AST.mk_term uu____11481 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| FStar_Parser_AST.TAnnotated (a, uu____11484) -> begin
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
| uu____11507 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (

let uu____11513 = (

let uu____11514 = (

let uu____11521 = (binder_to_term b)
in ((out), (uu____11521), ((imp_of_aqual b))))
in FStar_Parser_AST.App (uu____11514))
in (FStar_Parser_AST.mk_term uu____11513 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun uu___226_11531 -> (match (uu___226_11531) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun uu____11586 -> (match (uu____11586) with
| (x, t, uu____11597) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Syntax_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr FStar_Pervasives_Native.None)
end)) fields)
in (

let result = (

let uu____11603 = (

let uu____11604 = (

let uu____11605 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (uu____11605))
in (FStar_Parser_AST.mk_term uu____11604 id.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____11603 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type_level)
in (

let uu____11609 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____11636 -> (match (uu____11636) with
| (x, uu____11646, uu____11647) -> begin
(FStar_Syntax_Util.unmangle_field_name x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (FStar_Pervasives_Native.Some (constrTyp)), (FStar_Pervasives_Native.None), (false)))::[])))), (uu____11609)))))))
end
| uu____11700 -> begin
(failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals1 _env mutuals uu___227_11731 -> (match (uu___227_11731) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let uu____11755 = (typars_of_binders _env binders)
in (match (uu____11755) with
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

let uu____11801 = (

let uu____11802 = (

let uu____11803 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (uu____11803))
in (FStar_Parser_AST.mk_term uu____11802 id.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____11801 binders))
in (

let qlid = (FStar_ToSyntax_Env.qualify _env id)
in (

let typars1 = (FStar_Syntax_Subst.close_binders typars)
in (

let k1 = (FStar_Syntax_Subst.close typars1 k)
in (

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((qlid), ([]), (typars1), (k1), (mutuals), ([]))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (

let _env1 = (FStar_ToSyntax_Env.push_top_level_rec_binding _env id FStar_Syntax_Syntax.Delta_constant)
in (

let _env2 = (FStar_ToSyntax_Env.push_top_level_rec_binding _env' id FStar_Syntax_Syntax.Delta_constant)
in ((_env1), (_env2), (se), (tconstr))))))))))
end))
end
| uu____11816 -> begin
(failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env1 bs -> (

let uu____11860 = (FStar_List.fold_left (fun uu____11900 uu____11901 -> (match (((uu____11900), (uu____11901))) with
| ((env2, tps), (x, imp)) -> begin
(

let uu____11992 = (FStar_ToSyntax_Env.push_bv env2 x.FStar_Syntax_Syntax.ppname)
in (match (uu____11992) with
| (env3, y) -> begin
((env3), ((((y), (imp)))::tps))
end))
end)) ((env1), ([])) bs)
in (match (uu____11860) with
| (env2, bs1) -> begin
((env2), ((FStar_List.rev bs1)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id, bs, kopt))::[] -> begin
(

let kopt1 = (match (kopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____12105 = (tm_type_z id.FStar_Ident.idRange)
in FStar_Pervasives_Native.Some (uu____12105))
end
| uu____12106 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id), (bs), (kopt1)))
in (

let uu____12114 = (desugar_abstract_tc quals env [] tc)
in (match (uu____12114) with
| (uu____12127, uu____12128, se, uu____12130) -> begin
(

let se1 = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, uu____12133, typars, k, [], []) -> begin
(

let quals1 = se.FStar_Syntax_Syntax.sigquals
in (

let quals2 = (match ((FStar_List.contains FStar_Syntax_Syntax.Assumption quals1)) with
| true -> begin
quals1
end
| uu____12148 -> begin
((

let uu____12150 = (

let uu____12151 = (FStar_Options.ml_ish ())
in (not (uu____12151)))
in (match (uu____12150) with
| true -> begin
(

let uu____12152 = (

let uu____12153 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Adding an implicit \'assume new\' qualifier on %s" uu____12153))
in (FStar_Errors.warn se.FStar_Syntax_Syntax.sigrng uu____12152))
end
| uu____12154 -> begin
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
| uu____12160 -> begin
(

let uu____12161 = (

let uu____12164 = (

let uu____12165 = (

let uu____12178 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (uu____12178)))
in FStar_Syntax_Syntax.Tm_arrow (uu____12165))
in (FStar_Syntax_Syntax.mk uu____12164))
in (uu____12161 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
end)
in (

let uu___254_12182 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t))); FStar_Syntax_Syntax.sigrng = uu___254_12182.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = uu___254_12182.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___254_12182.FStar_Syntax_Syntax.sigattrs}))))
end
| uu____12185 -> begin
(failwith "Impossible")
end)
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env se1)
in (

let env2 = (

let uu____12188 = (FStar_ToSyntax_Env.qualify env1 id)
in (FStar_ToSyntax_Env.push_doc env1 uu____12188 d.FStar_Parser_AST.doc))
in ((env2), ((se1)::[])))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let uu____12203 = (typars_of_binders env binders)
in (match (uu____12203) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____12239 = (FStar_Util.for_some (fun uu___228_12241 -> (match (uu___228_12241) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| uu____12242 -> begin
false
end)) quals)
in (match (uu____12239) with
| true -> begin
FStar_Syntax_Syntax.teff
end
| uu____12243 -> begin
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

let uu____12249 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___229_12253 -> (match (uu___229_12253) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| uu____12254 -> begin
false
end))))
in (match (uu____12249) with
| true -> begin
quals
end
| uu____12257 -> begin
(match ((Prims.op_Equality t0.FStar_Parser_AST.level FStar_Parser_AST.Formula)) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals
end
| uu____12260 -> begin
quals
end)
end))
in (

let qlid = (FStar_ToSyntax_Env.qualify env id)
in (

let se = (

let uu____12263 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Effect))
in (match (uu____12263) with
| true -> begin
(

let uu____12266 = (

let uu____12273 = (

let uu____12274 = (unparen t)
in uu____12274.FStar_Parser_AST.tm)
in (match (uu____12273) with
| FStar_Parser_AST.Construct (head1, args) -> begin
(

let uu____12295 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____12325))::args_rev -> begin
(

let uu____12337 = (

let uu____12338 = (unparen last_arg)
in uu____12338.FStar_Parser_AST.tm)
in (match (uu____12337) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____12366 -> begin
(([]), (args))
end))
end
| uu____12375 -> begin
(([]), (args))
end)
in (match (uu____12295) with
| (cattributes, args1) -> begin
(

let uu____12414 = (desugar_attributes env cattributes)
in (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((head1), (args1)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (uu____12414)))
end))
end
| uu____12425 -> begin
((t), ([]))
end))
in (match (uu____12266) with
| (t1, cattributes) -> begin
(

let c = (desugar_comp t1.FStar_Parser_AST.range env' t1)
in (

let typars1 = (FStar_Syntax_Subst.close_binders typars)
in (

let c1 = (FStar_Syntax_Subst.close_comp typars1 c)
in (

let quals2 = (FStar_All.pipe_right quals1 (FStar_List.filter (fun uu___230_12447 -> (match (uu___230_12447) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| uu____12448 -> begin
true
end))))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((qlid), ([]), (typars1), (c1), ((FStar_List.append cattributes (FStar_Syntax_Util.comp_flags c1))))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))))
end))
end
| uu____12453 -> begin
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
| (FStar_Parser_AST.TyconRecord (uu____12459))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let uu____12483 = (tycon_record_as_variant trec)
in (match (uu____12483) with
| (t, fs) -> begin
(

let uu____12500 = (

let uu____12503 = (

let uu____12504 = (

let uu____12513 = (

let uu____12516 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.ids_of_lid uu____12516))
in ((uu____12513), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____12504))
in (uu____12503)::quals)
in (desugar_tycon env d uu____12500 ((t)::[])))
end)))
end
| (uu____12521)::uu____12522 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals1 et tc -> (

let uu____12683 = et
in (match (uu____12683) with
| (env1, tcs1) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (uu____12908) -> begin
(

let trec = tc
in (

let uu____12932 = (tycon_record_as_variant trec)
in (match (uu____12932) with
| (t, fs) -> begin
(

let uu____12991 = (

let uu____12994 = (

let uu____12995 = (

let uu____13004 = (

let uu____13007 = (FStar_ToSyntax_Env.current_module env1)
in (FStar_Ident.ids_of_lid uu____13007))
in ((uu____13004), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____12995))
in (uu____12994)::quals1)
in (collect_tcs uu____12991 ((env1), (tcs1)) t))
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let uu____13094 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (uu____13094) with
| (env2, uu____13154, se, tconstr) -> begin
((env2), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals1))))::tcs1))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let uu____13303 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (uu____13303) with
| (env2, uu____13363, se, tconstr) -> begin
((env2), ((FStar_Util.Inr (((se), (binders), (t), (quals1))))::tcs1))
end))
end
| uu____13488 -> begin
(failwith "Unrecognized mutual type definition")
end)
end)))
in (

let uu____13535 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (uu____13535) with
| (env1, tcs1) -> begin
(

let tcs2 = (FStar_List.rev tcs1)
in (

let docs_tps_sigelts = (FStar_All.pipe_right tcs2 (FStar_List.collect (fun uu___232_14046 -> (match (uu___232_14046) with
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, uu____14113, uu____14114); FStar_Syntax_Syntax.sigrng = uu____14115; FStar_Syntax_Syntax.sigquals = uu____14116; FStar_Syntax_Syntax.sigmeta = uu____14117; FStar_Syntax_Syntax.sigattrs = uu____14118}, binders, t, quals1) -> begin
(

let t1 = (

let uu____14179 = (typars_of_binders env1 binders)
in (match (uu____14179) with
| (env2, tpars1) -> begin
(

let uu____14210 = (push_tparams env2 tpars1)
in (match (uu____14210) with
| (env_tps, tpars2) -> begin
(

let t1 = (desugar_typ env_tps t)
in (

let tpars3 = (FStar_Syntax_Subst.close_binders tpars2)
in (FStar_Syntax_Subst.close tpars3 t1)))
end))
end))
in (

let uu____14243 = (

let uu____14264 = (mk_typ_abbrev id uvs tpars k t1 ((id)::[]) quals1 rng)
in ((((id), (d.FStar_Parser_AST.doc))), ([]), (uu____14264)))
in (uu____14243)::[]))
end
| FStar_Util.Inl ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs1, tpars, k, mutuals1, uu____14332); FStar_Syntax_Syntax.sigrng = uu____14333; FStar_Syntax_Syntax.sigquals = tname_quals; FStar_Syntax_Syntax.sigmeta = uu____14335; FStar_Syntax_Syntax.sigattrs = uu____14336}, constrs, tconstr, quals1) -> begin
(

let mk_tot = (fun t -> (

let tot1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((tot1), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)))
in (

let tycon = ((tname), (tpars), (k))
in (

let uu____14432 = (push_tparams env1 tpars)
in (match (uu____14432) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun uu____14509 -> (match (uu____14509) with
| (x, uu____14523) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let tot_tconstr = (mk_tot tconstr)
in (

let uu____14531 = (

let uu____14560 = (FStar_All.pipe_right constrs (FStar_List.map (fun uu____14674 -> (match (uu____14674) with
| (id, topt, doc1, of_notation) -> begin
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
| uu____14727 -> begin
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

let uu____14730 = (close env_tps t)
in (desugar_term env_tps uu____14730))
in (

let name = (FStar_ToSyntax_Env.qualify env1 id)
in (

let quals2 = (FStar_All.pipe_right tname_quals (FStar_List.collect (fun uu___231_14741 -> (match (uu___231_14741) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| uu____14753 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (

let uu____14761 = (

let uu____14782 = (

let uu____14783 = (

let uu____14784 = (

let uu____14799 = (

let uu____14802 = (

let uu____14805 = (FStar_All.pipe_right t1 FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total uu____14805))
in (FStar_Syntax_Util.arrow data_tpars uu____14802))
in ((name), (univs1), (uu____14799), (tname), (ntps), (mutuals1)))
in FStar_Syntax_Syntax.Sig_datacon (uu____14784))
in {FStar_Syntax_Syntax.sigel = uu____14783; FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in ((((name), (doc1))), (tps), (uu____14782)))
in ((name), (uu____14761))))))))
end))))
in (FStar_All.pipe_left FStar_List.split uu____14560))
in (match (uu____14531) with
| (constrNames, constrs1) -> begin
(((((tname), (d.FStar_Parser_AST.doc))), ([]), ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs1), (tpars), (k), (mutuals1), (constrNames))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = tname_quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))::constrs1
end))))
end))))
end
| uu____15044 -> begin
(failwith "impossible")
end))))
in (

let name_docs = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.map (fun uu____15176 -> (match (uu____15176) with
| (name_doc, uu____15204, uu____15205) -> begin
name_doc
end))))
in (

let sigelts = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.map (fun uu____15285 -> (match (uu____15285) with
| (uu____15306, uu____15307, se) -> begin
se
end))))
in (

let uu____15337 = (

let uu____15344 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle sigelts quals uu____15344 rng))
in (match (uu____15337) with
| (bundle, abbrevs) -> begin
(

let env2 = (FStar_ToSyntax_Env.push_sigelt env0 bundle)
in (

let env3 = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2 abbrevs)
in (

let data_ops = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.collect (fun uu____15410 -> (match (uu____15410) with
| (uu____15433, tps, se) -> begin
(mk_data_projector_names quals env3 se)
end))))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, uu____15484, tps, k, uu____15487, constrs) when ((FStar_List.length constrs) > (Prims.parse_int "1")) -> begin
(

let quals1 = se.FStar_Syntax_Syntax.sigquals
in (

let quals2 = (match ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals1)) with
| true -> begin
(FStar_Syntax_Syntax.Private)::quals1
end
| uu____15505 -> begin
quals1
end)
in (mk_data_discriminators quals2 env3 constrs)))
end
| uu____15506 -> begin
[]
end))))
in (

let ops = (FStar_List.append discs data_ops)
in (

let env4 = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env3 ops)
in (

let env5 = (FStar_List.fold_left (fun acc uu____15523 -> (match (uu____15523) with
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

let uu____15560 = (FStar_List.fold_left (fun uu____15583 b -> (match (uu____15583) with
| (env1, binders1) -> begin
(

let uu____15603 = (desugar_binder env1 b)
in (match (uu____15603) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____15620 = (as_binder env1 b.FStar_Parser_AST.aqual ((FStar_Pervasives_Native.Some (a)), (k)))
in (match (uu____15620) with
| (binder, env2) -> begin
((env2), ((binder)::binders1))
end))
end
| uu____15637 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) binders)
in (match (uu____15560) with
| (env1, binders1) -> begin
((env1), ((FStar_List.rev binders1)))
end)))


let rec desugar_effect : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_typ eff_decls -> (

let env0 = env
in (

let monad_env = (FStar_ToSyntax_Env.enter_monad_scope env eff_name)
in (

let uu____15755 = (desugar_binders monad_env eff_binders)
in (match (uu____15755) with
| (env1, binders) -> begin
(

let eff_t = (desugar_term env1 eff_typ)
in (

let for_free = (

let uu____15776 = (

let uu____15777 = (

let uu____15784 = (FStar_Syntax_Util.arrow_formals eff_t)
in (FStar_Pervasives_Native.fst uu____15784))
in (FStar_List.length uu____15777))
in (Prims.op_Equality uu____15776 (Prims.parse_int "1")))
in (

let mandatory_members = (

let rr_members = ("repr")::("return")::("bind")::[]
in (match (for_free) with
| true -> begin
rr_members
end
| uu____15821 -> begin
(FStar_List.append rr_members (("return_wp")::("bind_wp")::("if_then_else")::("ite_wp")::("stronger")::("close_wp")::("assert_p")::("assume_p")::("null_wp")::("trivial")::[]))
end))
in (

let name_of_eff_decl = (fun decl -> (match (decl.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____15826, ((FStar_Parser_AST.TyconAbbrev (name, uu____15828, uu____15829, uu____15830), uu____15831))::[]) -> begin
(FStar_Ident.text_of_id name)
end
| uu____15864 -> begin
(failwith "Malformed effect member declaration.")
end))
in (

let uu____15865 = (FStar_List.partition (fun decl -> (

let uu____15877 = (name_of_eff_decl decl)
in (FStar_List.mem uu____15877 mandatory_members))) eff_decls)
in (match (uu____15865) with
| (mandatory_members_decls, actions) -> begin
(

let uu____15894 = (FStar_All.pipe_right mandatory_members_decls (FStar_List.fold_left (fun uu____15923 decl -> (match (uu____15923) with
| (env2, out) -> begin
(

let uu____15943 = (desugar_decl env2 decl)
in (match (uu____15943) with
| (env3, ses) -> begin
(

let uu____15956 = (

let uu____15959 = (FStar_List.hd ses)
in (uu____15959)::out)
in ((env3), (uu____15956)))
end))
end)) ((env1), ([]))))
in (match (uu____15894) with
| (env2, decls) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (

let actions_docs = (FStar_All.pipe_right actions (FStar_List.map (fun d1 -> (match (d1.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____16027, ((FStar_Parser_AST.TyconAbbrev (name, action_params, uu____16030, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (uu____16031, ((def, uu____16033))::((cps_type, uu____16035))::[]); FStar_Parser_AST.range = uu____16036; FStar_Parser_AST.level = uu____16037}), doc1))::[]) when (not (for_free)) -> begin
(

let uu____16089 = (desugar_binders env2 action_params)
in (match (uu____16089) with
| (env3, action_params1) -> begin
(

let action_params2 = (FStar_Syntax_Subst.close_binders action_params1)
in (

let uu____16109 = (

let uu____16110 = (FStar_ToSyntax_Env.qualify env3 name)
in (

let uu____16111 = (

let uu____16112 = (desugar_term env3 def)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____16112))
in (

let uu____16117 = (

let uu____16118 = (desugar_typ env3 cps_type)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____16118))
in {FStar_Syntax_Syntax.action_name = uu____16110; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = action_params2; FStar_Syntax_Syntax.action_defn = uu____16111; FStar_Syntax_Syntax.action_typ = uu____16117})))
in ((uu____16109), (doc1))))
end))
end
| FStar_Parser_AST.Tycon (uu____16125, ((FStar_Parser_AST.TyconAbbrev (name, action_params, uu____16128, defn), doc1))::[]) when for_free -> begin
(

let uu____16163 = (desugar_binders env2 action_params)
in (match (uu____16163) with
| (env3, action_params1) -> begin
(

let action_params2 = (FStar_Syntax_Subst.close_binders action_params1)
in (

let uu____16183 = (

let uu____16184 = (FStar_ToSyntax_Env.qualify env3 name)
in (

let uu____16185 = (

let uu____16186 = (desugar_term env3 defn)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____16186))
in {FStar_Syntax_Syntax.action_name = uu____16184; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = action_params2; FStar_Syntax_Syntax.action_defn = uu____16185; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
in ((uu____16183), (doc1))))
end))
end
| uu____16193 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples)."), (d1.FStar_Parser_AST.drange)))))
end))))
in (

let actions1 = (FStar_List.map FStar_Pervasives_Native.fst actions_docs)
in (

let eff_t1 = (FStar_Syntax_Subst.close binders1 eff_t)
in (

let lookup = (fun s -> (

let l = (FStar_ToSyntax_Env.qualify env2 (FStar_Ident.mk_ident ((s), (d.FStar_Parser_AST.drange))))
in (

let uu____16223 = (

let uu____16224 = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_definition env2) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders1) uu____16224))
in (([]), (uu____16223)))))
in (

let mname = (FStar_ToSyntax_Env.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange (FStar_Pervasives_Native.Some (mname))) quals)
in (

let se = (match (for_free) with
| true -> begin
(

let dummy_tscheme = (

let uu____16241 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (([]), (uu____16241)))
in (

let uu____16248 = (

let uu____16249 = (

let uu____16250 = (

let uu____16251 = (lookup "repr")
in (FStar_Pervasives_Native.snd uu____16251))
in (

let uu____16260 = (lookup "return")
in (

let uu____16261 = (lookup "bind")
in {FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = eff_t1; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = uu____16250; FStar_Syntax_Syntax.return_repr = uu____16260; FStar_Syntax_Syntax.bind_repr = uu____16261; FStar_Syntax_Syntax.actions = actions1})))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____16249))
in {FStar_Syntax_Syntax.sigel = uu____16248; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qualifiers; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))
end
| uu____16262 -> begin
(

let rr = (FStar_Util.for_some (fun uu___233_16265 -> (match (uu___233_16265) with
| FStar_Syntax_Syntax.Reifiable -> begin
true
end
| FStar_Syntax_Syntax.Reflectable (uu____16266) -> begin
true
end
| uu____16267 -> begin
false
end)) qualifiers)
in (

let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in (

let uu____16277 = (

let uu____16278 = (

let uu____16279 = (lookup "return_wp")
in (

let uu____16280 = (lookup "bind_wp")
in (

let uu____16281 = (lookup "if_then_else")
in (

let uu____16282 = (lookup "ite_wp")
in (

let uu____16283 = (lookup "stronger")
in (

let uu____16284 = (lookup "close_wp")
in (

let uu____16285 = (lookup "assert_p")
in (

let uu____16286 = (lookup "assume_p")
in (

let uu____16287 = (lookup "null_wp")
in (

let uu____16288 = (lookup "trivial")
in (

let uu____16289 = (match (rr) with
| true -> begin
(

let uu____16290 = (lookup "repr")
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____16290))
end
| uu____16305 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let uu____16306 = (match (rr) with
| true -> begin
(lookup "return")
end
| uu____16307 -> begin
un_ts
end)
in (

let uu____16308 = (match (rr) with
| true -> begin
(lookup "bind")
end
| uu____16309 -> begin
un_ts
end)
in {FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = eff_t1; FStar_Syntax_Syntax.ret_wp = uu____16279; FStar_Syntax_Syntax.bind_wp = uu____16280; FStar_Syntax_Syntax.if_then_else = uu____16281; FStar_Syntax_Syntax.ite_wp = uu____16282; FStar_Syntax_Syntax.stronger = uu____16283; FStar_Syntax_Syntax.close_wp = uu____16284; FStar_Syntax_Syntax.assert_p = uu____16285; FStar_Syntax_Syntax.assume_p = uu____16286; FStar_Syntax_Syntax.null_wp = uu____16287; FStar_Syntax_Syntax.trivial = uu____16288; FStar_Syntax_Syntax.repr = uu____16289; FStar_Syntax_Syntax.return_repr = uu____16306; FStar_Syntax_Syntax.bind_repr = uu____16308; FStar_Syntax_Syntax.actions = actions1})))))))))))))
in FStar_Syntax_Syntax.Sig_new_effect (uu____16278))
in {FStar_Syntax_Syntax.sigel = uu____16277; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qualifiers; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))
end)
in (

let env3 = (FStar_ToSyntax_Env.push_sigelt env0 se)
in (

let env4 = (FStar_ToSyntax_Env.push_doc env3 mname d.FStar_Parser_AST.doc)
in (

let env5 = (FStar_All.pipe_right actions_docs (FStar_List.fold_left (fun env5 uu____16333 -> (match (uu____16333) with
| (a, doc1) -> begin
(

let env6 = (

let uu____16347 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_ToSyntax_Env.push_sigelt env5 uu____16347))
in (FStar_ToSyntax_Env.push_doc env6 a.FStar_Syntax_Syntax.action_name doc1))
end)) env4))
in (

let env6 = (

let uu____16349 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____16349) with
| true -> begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_ToSyntax_Env.qualify monad_env))
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]
in (

let refl_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (FStar_ToSyntax_Env.push_sigelt env5 refl_decl))))
end
| uu____16357 -> begin
env5
end))
in (

let env7 = (FStar_ToSyntax_Env.push_doc env6 mname d.FStar_Parser_AST.doc)
in ((env7), ((se)::[])))))))))))))))
end))
end))))))
end)))))
and desugar_redefine_effect : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  (FStar_Ident.lident FStar_Pervasives_Native.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier)  ->  FStar_Parser_AST.qualifier Prims.list  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d trans_qual1 quals eff_name eff_binders defn -> (

let env0 = env
in (

let env1 = (FStar_ToSyntax_Env.enter_monad_scope env eff_name)
in (

let uu____16380 = (desugar_binders env1 eff_binders)
in (match (uu____16380) with
| (env2, binders) -> begin
(

let uu____16399 = (

let uu____16418 = (head_and_args defn)
in (match (uu____16418) with
| (head1, args) -> begin
(

let lid = (match (head1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
l
end
| uu____16463 -> begin
(

let uu____16464 = (

let uu____16465 = (

let uu____16470 = (

let uu____16471 = (

let uu____16472 = (FStar_Parser_AST.term_to_string head1)
in (Prims.strcat uu____16472 " not found"))
in (Prims.strcat "Effect " uu____16471))
in ((uu____16470), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____16465))
in (FStar_Exn.raise uu____16464))
end)
in (

let ed = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_effect_defn env2) lid)
in (

let uu____16474 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____16504))::args_rev -> begin
(

let uu____16516 = (

let uu____16517 = (unparen last_arg)
in uu____16517.FStar_Parser_AST.tm)
in (match (uu____16516) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____16545 -> begin
(([]), (args))
end))
end
| uu____16554 -> begin
(([]), (args))
end)
in (match (uu____16474) with
| (cattributes, args1) -> begin
(

let uu____16605 = (desugar_args env2 args1)
in (

let uu____16614 = (desugar_attributes env2 cattributes)
in ((lid), (ed), (uu____16605), (uu____16614))))
end))))
end))
in (match (uu____16399) with
| (ed_lid, ed, args, cattributes) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (

let sub1 = (fun uu____16673 -> (match (uu____16673) with
| (uu____16686, x) -> begin
(

let uu____16692 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (uu____16692) with
| (edb, x1) -> begin
((match ((Prims.op_disEquality (FStar_List.length args) (FStar_List.length edb))) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected number of arguments to effect constructor"), (defn.FStar_Parser_AST.range)))))
end
| uu____16716 -> begin
()
end);
(

let s = (FStar_Syntax_Util.subst_of_list edb args)
in (

let uu____16718 = (

let uu____16719 = (FStar_Syntax_Subst.subst s x1)
in (FStar_Syntax_Subst.close binders1 uu____16719))
in (([]), (uu____16718))));
)
end))
end))
in (

let mname = (FStar_ToSyntax_Env.qualify env0 eff_name)
in (

let ed1 = (

let uu____16724 = (

let uu____16725 = (sub1 (([]), (ed.FStar_Syntax_Syntax.signature)))
in (FStar_Pervasives_Native.snd uu____16725))
in (

let uu____16736 = (sub1 ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____16737 = (sub1 ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____16738 = (sub1 ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____16739 = (sub1 ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____16740 = (sub1 ed.FStar_Syntax_Syntax.stronger)
in (

let uu____16741 = (sub1 ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____16742 = (sub1 ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____16743 = (sub1 ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____16744 = (sub1 ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____16745 = (sub1 ed.FStar_Syntax_Syntax.trivial)
in (

let uu____16746 = (

let uu____16747 = (sub1 (([]), (ed.FStar_Syntax_Syntax.repr)))
in (FStar_Pervasives_Native.snd uu____16747))
in (

let uu____16758 = (sub1 ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____16759 = (sub1 ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____16760 = (FStar_List.map (fun action -> (

let uu____16768 = (FStar_ToSyntax_Env.qualify env2 action.FStar_Syntax_Syntax.action_unqualified_name)
in (

let uu____16769 = (

let uu____16770 = (sub1 (([]), (action.FStar_Syntax_Syntax.action_defn)))
in (FStar_Pervasives_Native.snd uu____16770))
in (

let uu____16781 = (

let uu____16782 = (sub1 (([]), (action.FStar_Syntax_Syntax.action_typ)))
in (FStar_Pervasives_Native.snd uu____16782))
in {FStar_Syntax_Syntax.action_name = uu____16768; FStar_Syntax_Syntax.action_unqualified_name = action.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = action.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = uu____16769; FStar_Syntax_Syntax.action_typ = uu____16781})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = cattributes; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = uu____16724; FStar_Syntax_Syntax.ret_wp = uu____16736; FStar_Syntax_Syntax.bind_wp = uu____16737; FStar_Syntax_Syntax.if_then_else = uu____16738; FStar_Syntax_Syntax.ite_wp = uu____16739; FStar_Syntax_Syntax.stronger = uu____16740; FStar_Syntax_Syntax.close_wp = uu____16741; FStar_Syntax_Syntax.assert_p = uu____16742; FStar_Syntax_Syntax.assume_p = uu____16743; FStar_Syntax_Syntax.null_wp = uu____16744; FStar_Syntax_Syntax.trivial = uu____16745; FStar_Syntax_Syntax.repr = uu____16746; FStar_Syntax_Syntax.return_repr = uu____16758; FStar_Syntax_Syntax.bind_repr = uu____16759; FStar_Syntax_Syntax.actions = uu____16760})))))))))))))))
in (

let se = (

let for_free = (

let uu____16795 = (

let uu____16796 = (

let uu____16803 = (FStar_Syntax_Util.arrow_formals ed1.FStar_Syntax_Syntax.signature)
in (FStar_Pervasives_Native.fst uu____16803))
in (FStar_List.length uu____16796))
in (Prims.op_Equality uu____16795 (Prims.parse_int "1")))
in (

let uu____16832 = (

let uu____16835 = (trans_qual1 (FStar_Pervasives_Native.Some (mname)))
in (FStar_List.map uu____16835 quals))
in {FStar_Syntax_Syntax.sigel = (match (for_free) with
| true -> begin
FStar_Syntax_Syntax.Sig_new_effect_for_free (ed1)
end
| uu____16838 -> begin
FStar_Syntax_Syntax.Sig_new_effect (ed1)
end); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = uu____16832; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))
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

let uu____16855 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_ToSyntax_Env.push_sigelt env5 uu____16855))
in (FStar_ToSyntax_Env.push_doc env6 a.FStar_Syntax_Syntax.action_name doc1)))) env4))
in (

let env6 = (

let uu____16857 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____16857) with
| true -> begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_ToSyntax_Env.qualify monad_env))
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]
in (

let refl_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (FStar_ToSyntax_Env.push_sigelt env5 refl_decl))))
end
| uu____16867 -> begin
env5
end))
in (

let env7 = (FStar_ToSyntax_Env.push_doc env6 mname d.FStar_Parser_AST.doc)
in ((env7), ((se)::[])))))))))))))
end))
end)))))
and mk_comment_attr : FStar_Parser_AST.decl  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun d -> (

let uu____16872 = (match (d.FStar_Parser_AST.doc) with
| FStar_Pervasives_Native.None -> begin
((""), ([]))
end
| FStar_Pervasives_Native.Some (fsdoc) -> begin
fsdoc
end)
in (match (uu____16872) with
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
| FStar_Pervasives_Native.Some (uu____16923) -> begin
(

let uu____16924 = (

let uu____16925 = (FStar_Parser_ToDocument.signature_to_document d)
in (FStar_Pprint.pretty_string 0.950000 (Prims.parse_int "80") uu____16925))
in (Prims.strcat "\n  " uu____16924))
end
| uu____16926 -> begin
""
end)
in (

let other = (FStar_List.filter_map (fun uu____16939 -> (match (uu____16939) with
| (k, v1) -> begin
(match (((Prims.op_disEquality k "summary") && (Prims.op_disEquality k "type"))) with
| true -> begin
FStar_Pervasives_Native.Some ((Prims.strcat k (Prims.strcat ": " v1)))
end
| uu____16950 -> begin
FStar_Pervasives_Native.None
end)
end)) kv)
in (

let other1 = (match ((Prims.op_disEquality other [])) with
| true -> begin
(Prims.strcat (FStar_String.concat "\n" other) "\n")
end
| uu____16954 -> begin
""
end)
in (

let str = (Prims.strcat summary (Prims.strcat pp (Prims.strcat other1 text)))
in (

let fv = (

let uu____16957 = (FStar_Ident.lid_of_str "FStar.Pervasives.Comment")
in (FStar_Syntax_Syntax.fvar uu____16957 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in (

let arg = (FStar_Syntax_Util.exp_string str)
in (

let uu____16959 = (

let uu____16968 = (FStar_Syntax_Syntax.as_arg arg)
in (uu____16968)::[])
in (FStar_Syntax_Util.mk_app fv uu____16959)))))))))
end)))
and desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (

let uu____16975 = (desugar_decl_noattrs env d)
in (match (uu____16975) with
| (env1, sigelts) -> begin
(

let attrs = d.FStar_Parser_AST.attrs
in (

let attrs1 = (FStar_List.map (desugar_term env1) attrs)
in (

let attrs2 = (

let uu____16995 = (mk_comment_attr d)
in (uu____16995)::attrs1)
in (

let uu____17000 = (FStar_List.map (fun sigelt -> (

let uu___255_17006 = sigelt
in {FStar_Syntax_Syntax.sigel = uu___255_17006.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___255_17006.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___255_17006.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___255_17006.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = attrs2})) sigelts)
in ((env1), (uu____17000))))))
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
| uu____17029 -> begin
()
end);
((env), ((se)::[]));
))
end
| FStar_Parser_AST.Fsdoc (uu____17032) -> begin
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

let uu____17048 = (FStar_ToSyntax_Env.push_module_abbrev env x l)
in ((uu____17048), ([])))
end
| FStar_Parser_AST.Tycon (is_effect, tcs) -> begin
(

let quals = (match (is_effect) with
| true -> begin
(FStar_Parser_AST.Effect_qual)::d.FStar_Parser_AST.quals
end
| uu____17074 -> begin
d.FStar_Parser_AST.quals
end)
in (

let tcs1 = (FStar_List.map (fun uu____17087 -> (match (uu____17087) with
| (x, uu____17095) -> begin
x
end)) tcs)
in (

let uu____17100 = (FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals)
in (desugar_tycon env d uu____17100 tcs1))))
end
| FStar_Parser_AST.TopLevelLet (isrec, lets) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let expand_toplevel_pattern = ((Prims.op_Equality isrec FStar_Parser_AST.NoLetQualifier) && (match (lets) with
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatOp (uu____17122); FStar_Parser_AST.prange = uu____17123}, uu____17124))::[] -> begin
false
end
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____17133); FStar_Parser_AST.prange = uu____17134}, uu____17135))::[] -> begin
false
end
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____17150); FStar_Parser_AST.prange = uu____17151}, uu____17152); FStar_Parser_AST.prange = uu____17153}, uu____17154))::[] -> begin
false
end
| ((p, uu____17170))::[] -> begin
(

let uu____17179 = (is_app_pattern p)
in (not (uu____17179)))
end
| uu____17180 -> begin
false
end))
in (match ((not (expand_toplevel_pattern))) with
| true -> begin
(

let as_inner_let = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)
in (

let ds_lets = (desugar_term_maybe_top true env as_inner_let)
in (

let uu____17199 = (

let uu____17200 = (FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets)
in uu____17200.FStar_Syntax_Syntax.n)
in (match (uu____17199) with
| FStar_Syntax_Syntax.Tm_let (lbs, uu____17208) -> begin
(

let fvs = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals1 = (match (quals) with
| (uu____17241)::uu____17242 -> begin
(FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals)
end
| uu____17245 -> begin
(FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.collect (fun uu___234_17258 -> (match (uu___234_17258) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (uu____17261); FStar_Syntax_Syntax.lbunivs = uu____17262; FStar_Syntax_Syntax.lbtyp = uu____17263; FStar_Syntax_Syntax.lbeff = uu____17264; FStar_Syntax_Syntax.lbdef = uu____17265} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____17273; FStar_Syntax_Syntax.lbtyp = uu____17274; FStar_Syntax_Syntax.lbeff = uu____17275; FStar_Syntax_Syntax.lbdef = uu____17276} -> begin
(FStar_ToSyntax_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals2 = (

let uu____17286 = (FStar_All.pipe_right lets (FStar_Util.for_some (fun uu____17300 -> (match (uu____17300) with
| (uu____17305, t) -> begin
(Prims.op_Equality t.FStar_Parser_AST.level FStar_Parser_AST.Formula)
end))))
in (match (uu____17286) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals1
end
| uu____17309 -> begin
quals1
end))
in (

let lbs1 = (

let uu____17317 = (FStar_All.pipe_right quals2 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____17317) with
| true -> begin
(

let uu____17326 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu___256_17340 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let uu___257_17342 = fv
in {FStar_Syntax_Syntax.fv_name = uu___257_17342.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = uu___257_17342.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = uu___256_17340.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___256_17340.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___256_17340.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___256_17340.FStar_Syntax_Syntax.lbdef})))))
in (((FStar_Pervasives_Native.fst lbs)), (uu____17326)))
end
| uu____17347 -> begin
lbs
end))
in (

let names1 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (

let s = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((lbs1), (names1))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env s)
in (

let env2 = (FStar_List.fold_left (fun env2 id -> (FStar_ToSyntax_Env.push_doc env2 id d.FStar_Parser_AST.doc)) env1 names1)
in ((env2), ((s)::[]))))))))))
end
| uu____17374 -> begin
(failwith "Desugaring a let did not produce a let")
end))))
end
| uu____17379 -> begin
(

let uu____17380 = (match (lets) with
| ((pat, body))::[] -> begin
((pat), (body))
end
| uu____17399 -> begin
(failwith "expand_toplevel_pattern should only allow single definition lets")
end)
in (match (uu____17380) with
| (pat, body) -> begin
(

let fresh_toplevel_name = (FStar_Ident.gen FStar_Range.dummyRange)
in (

let fresh_pat = (

let var_pat = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((fresh_toplevel_name), (FStar_Pervasives_Native.None)))) FStar_Range.dummyRange)
in (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat1, ty) -> begin
(

let uu___258_17423 = pat1
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed (((var_pat), (ty))); FStar_Parser_AST.prange = uu___258_17423.FStar_Parser_AST.prange})
end
| uu____17424 -> begin
var_pat
end))
in (

let main_let = (desugar_decl env (

let uu___259_17431 = d
in {FStar_Parser_AST.d = FStar_Parser_AST.TopLevelLet (((isrec), ((((fresh_pat), (body)))::[]))); FStar_Parser_AST.drange = uu___259_17431.FStar_Parser_AST.drange; FStar_Parser_AST.doc = uu___259_17431.FStar_Parser_AST.doc; FStar_Parser_AST.quals = (FStar_Parser_AST.Private)::d.FStar_Parser_AST.quals; FStar_Parser_AST.attrs = uu___259_17431.FStar_Parser_AST.attrs}))
in (

let build_projection = (fun uu____17463 id -> (match (uu____17463) with
| (env1, ses) -> begin
(

let main = (

let uu____17484 = (

let uu____17485 = (FStar_Ident.lid_of_ids ((fresh_toplevel_name)::[]))
in FStar_Parser_AST.Var (uu____17485))
in (FStar_Parser_AST.mk_term uu____17484 FStar_Range.dummyRange FStar_Parser_AST.Expr))
in (

let lid = (FStar_Ident.lid_of_ids ((id)::[]))
in (

let projectee = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (lid)) FStar_Range.dummyRange FStar_Parser_AST.Expr)
in (

let body1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Match (((main), ((((pat), (FStar_Pervasives_Native.None), (projectee)))::[])))) FStar_Range.dummyRange FStar_Parser_AST.Expr)
in (

let bv_pat = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((id), (FStar_Pervasives_Native.None)))) FStar_Range.dummyRange)
in (

let id_decl = (FStar_Parser_AST.mk_decl (FStar_Parser_AST.TopLevelLet (((FStar_Parser_AST.NoLetQualifier), ((((bv_pat), (body1)))::[])))) FStar_Range.dummyRange [])
in (

let uu____17535 = (desugar_decl env1 id_decl)
in (match (uu____17535) with
| (env2, ses') -> begin
((env2), ((FStar_List.append ses ses')))
end))))))))
end))
in (

let bvs = (

let uu____17553 = (gather_pattern_bound_vars pat)
in (FStar_All.pipe_right uu____17553 FStar_Util.set_elements))
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
| FStar_Parser_AST.Assume (id, t) -> begin
(

let f = (desugar_formula env t)
in (

let lid = (FStar_ToSyntax_Env.qualify env id)
in (

let env1 = (FStar_ToSyntax_Env.push_doc env lid d.FStar_Parser_AST.doc)
in ((env1), (({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_assume (((lid), ([]), (f))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = (FStar_Syntax_Syntax.Assumption)::[]; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})::[])))))
end
| FStar_Parser_AST.Val (id, t) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let t1 = (

let uu____17584 = (close_fun env t)
in (desugar_term env uu____17584))
in (

let quals1 = (

let uu____17588 = ((FStar_ToSyntax_Env.iface env) && (FStar_ToSyntax_Env.admitted_iface env))
in (match (uu____17588) with
| true -> begin
(FStar_Parser_AST.Assumption)::quals
end
| uu____17591 -> begin
quals
end))
in (

let lid = (FStar_ToSyntax_Env.qualify env id)
in (

let se = (

let uu____17594 = (FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals1)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), ([]), (t1))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = uu____17594; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env se)
in (

let env2 = (FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc)
in ((env2), ((se)::[])))))))))
end
| FStar_Parser_AST.Exception (id, FStar_Pervasives_Native.None) -> begin
(

let uu____17606 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) FStar_Parser_Const.exn_lid)
in (match (uu____17606) with
| (t, uu____17620) -> begin
(

let l = (FStar_ToSyntax_Env.qualify env id)
in (

let qual1 = (FStar_Syntax_Syntax.ExceptionConstructor)::[]
in (

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((l), ([]), (t), (FStar_Parser_Const.exn_lid), ((Prims.parse_int "0")), ((FStar_Parser_Const.exn_lid)::[]))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qual1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (

let se' = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((se)::[]), ((l)::[]))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qual1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env se')
in (

let env2 = (FStar_ToSyntax_Env.push_doc env1 l d.FStar_Parser_AST.doc)
in (

let data_ops = (mk_data_projector_names [] env2 se)
in (

let discs = (mk_data_discriminators [] env2 ((l)::[]))
in (

let env3 = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2 (FStar_List.append discs data_ops))
in ((env3), ((FStar_List.append ((se')::discs) data_ops))))))))))))
end))
end
| FStar_Parser_AST.Exception (id, FStar_Pervasives_Native.Some (term)) -> begin
(

let t = (desugar_term env term)
in (

let t1 = (

let uu____17654 = (

let uu____17661 = (FStar_Syntax_Syntax.null_binder t)
in (uu____17661)::[])
in (

let uu____17662 = (

let uu____17665 = (

let uu____17666 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) FStar_Parser_Const.exn_lid)
in (FStar_Pervasives_Native.fst uu____17666))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____17665))
in (FStar_Syntax_Util.arrow uu____17654 uu____17662)))
in (

let l = (FStar_ToSyntax_Env.qualify env id)
in (

let qual1 = (FStar_Syntax_Syntax.ExceptionConstructor)::[]
in (

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (((l), ([]), (t1), (FStar_Parser_Const.exn_lid), ((Prims.parse_int "0")), ((FStar_Parser_Const.exn_lid)::[]))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qual1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (

let se' = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle ((((se)::[]), ((l)::[]))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qual1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env se')
in (

let env2 = (FStar_ToSyntax_Env.push_doc env1 l d.FStar_Parser_AST.doc)
in (

let data_ops = (mk_data_projector_names [] env2 se)
in (

let discs = (mk_data_discriminators [] env2 ((l)::[]))
in (

let env3 = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2 (FStar_List.append discs data_ops))
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
in (desugar_effect env d quals eff_name eff_binders eff_typ eff_decls))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(

let lookup = (fun l1 -> (

let uu____17728 = (FStar_ToSyntax_Env.try_lookup_effect_name env l1)
in (match (uu____17728) with
| FStar_Pervasives_Native.None -> begin
(

let uu____17731 = (

let uu____17732 = (

let uu____17737 = (

let uu____17738 = (

let uu____17739 = (FStar_Syntax_Print.lid_to_string l1)
in (Prims.strcat uu____17739 " not found"))
in (Prims.strcat "Effect name " uu____17738))
in ((uu____17737), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____17732))
in (FStar_Exn.raise uu____17731))
end
| FStar_Pervasives_Native.Some (l2) -> begin
l2
end)))
in (

let src = (lookup l.FStar_Parser_AST.msource)
in (

let dst = (lookup l.FStar_Parser_AST.mdest)
in (

let uu____17743 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(

let uu____17785 = (

let uu____17794 = (

let uu____17801 = (desugar_term env t)
in (([]), (uu____17801)))
in FStar_Pervasives_Native.Some (uu____17794))
in ((uu____17785), (FStar_Pervasives_Native.None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(

let uu____17834 = (

let uu____17843 = (

let uu____17850 = (desugar_term env wp)
in (([]), (uu____17850)))
in FStar_Pervasives_Native.Some (uu____17843))
in (

let uu____17859 = (

let uu____17868 = (

let uu____17875 = (desugar_term env t)
in (([]), (uu____17875)))
in FStar_Pervasives_Native.Some (uu____17868))
in ((uu____17834), (uu____17859))))
end
| FStar_Parser_AST.LiftForFree (t) -> begin
(

let uu____17901 = (

let uu____17910 = (

let uu____17917 = (desugar_term env t)
in (([]), (uu____17917)))
in FStar_Pervasives_Native.Some (uu____17910))
in ((FStar_Pervasives_Native.None), (uu____17901)))
end)
in (match (uu____17743) with
| (lift_wp, lift) -> begin
(

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect ({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift}); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in ((env), ((se)::[])))
end)))))
end)))


let desugar_decls : env_t  ->  FStar_Parser_AST.decl Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env decls -> (

let uu____18007 = (FStar_List.fold_left (fun uu____18027 d -> (match (uu____18027) with
| (env1, sigelts) -> begin
(

let uu____18047 = (desugar_decl env1 d)
in (match (uu____18047) with
| (env2, se) -> begin
((env2), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls)
in (match (uu____18007) with
| (env1, sigelts) -> begin
(

let rec forward = (fun acc uu___236_18088 -> (match (uu___236_18088) with
| (se1)::(se2)::sigelts1 -> begin
(match (((se1.FStar_Syntax_Syntax.sigel), (se2.FStar_Syntax_Syntax.sigel))) with
| (FStar_Syntax_Syntax.Sig_declare_typ (uu____18102), FStar_Syntax_Syntax.Sig_let (uu____18103)) -> begin
(

let uu____18116 = (

let uu____18119 = (

let uu___260_18120 = se2
in (

let uu____18121 = (

let uu____18124 = (FStar_List.filter (fun uu___235_18138 -> (match (uu___235_18138) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____18142; FStar_Syntax_Syntax.vars = uu____18143}, uu____18144); FStar_Syntax_Syntax.pos = uu____18145; FStar_Syntax_Syntax.vars = uu____18146} when (

let uu____18169 = (

let uu____18170 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____18170))
in (Prims.op_Equality uu____18169 "FStar.Pervasives.Comment")) -> begin
true
end
| uu____18171 -> begin
false
end)) se1.FStar_Syntax_Syntax.sigattrs)
in (FStar_List.append uu____18124 se2.FStar_Syntax_Syntax.sigattrs))
in {FStar_Syntax_Syntax.sigel = uu___260_18120.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___260_18120.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___260_18120.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___260_18120.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu____18121}))
in (uu____18119)::(se1)::acc)
in (forward uu____18116 sigelts1))
end
| uu____18176 -> begin
(forward ((se1)::acc) ((se2)::sigelts1))
end)
end
| sigelts1 -> begin
(FStar_List.rev_append acc sigelts1)
end))
in (

let uu____18184 = (forward [] sigelts)
in ((env1), (uu____18184))))
end)))


let open_prims_all : (FStar_Parser_AST.decoration Prims.list  ->  FStar_Parser_AST.decl) Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Parser_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Parser_Const.all_lid)) FStar_Range.dummyRange))::[]


let desugar_modul_common : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let env1 = (match (((curmod), (m))) with
| (FStar_Pervasives_Native.None, uu____18238) -> begin
env
end
| (FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.name = prev_lid; FStar_Syntax_Syntax.declarations = uu____18242; FStar_Syntax_Syntax.exports = uu____18243; FStar_Syntax_Syntax.is_interface = uu____18244}), FStar_Parser_AST.Module (current_lid, uu____18246)) when ((FStar_Ident.lid_equals prev_lid current_lid) && (FStar_Options.interactive ())) -> begin
env
end
| (FStar_Pervasives_Native.Some (prev_mod), uu____18254) -> begin
(FStar_ToSyntax_Env.finish_module_or_interface env prev_mod)
end)
in (

let uu____18257 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(

let uu____18293 = (FStar_ToSyntax_Env.prepare_module_or_interface true admitted env1 mname FStar_ToSyntax_Env.default_mii)
in ((uu____18293), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(

let uu____18310 = (FStar_ToSyntax_Env.prepare_module_or_interface false false env1 mname FStar_ToSyntax_Env.default_mii)
in ((uu____18310), (mname), (decls), (false)))
end)
in (match (uu____18257) with
| ((env2, pop_when_done), mname, decls, intf) -> begin
(

let uu____18340 = (desugar_decls env2 decls)
in (match (uu____18340) with
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

let uu____18398 = ((FStar_Options.interactive ()) && (

let uu____18400 = (

let uu____18401 = (

let uu____18402 = (FStar_Options.file_list ())
in (FStar_List.hd uu____18402))
in (FStar_Util.get_file_extension uu____18401))
in (FStar_List.mem uu____18400 (("fsti")::("fsi")::[]))))
in (match (uu____18398) with
| true -> begin
(as_interface m)
end
| uu____18405 -> begin
m
end))
in (

let uu____18406 = (desugar_modul_common curmod env m1)
in (match (uu____18406) with
| (x, y, pop_when_done) -> begin
((match (pop_when_done) with
| true -> begin
(

let uu____18421 = (FStar_ToSyntax_Env.pop ())
in ())
end
| uu____18422 -> begin
()
end);
((x), (y));
)
end))))


let desugar_modul : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (

let uu____18439 = (desugar_modul_common FStar_Pervasives_Native.None env m)
in (match (uu____18439) with
| (env1, modul, pop_when_done) -> begin
(

let env2 = (FStar_ToSyntax_Env.finish_module_or_interface env1 modul)
in ((

let uu____18455 = (FStar_Options.dump_module modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____18455) with
| true -> begin
(

let uu____18456 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" uu____18456))
end
| uu____18457 -> begin
()
end));
(

let uu____18458 = (match (pop_when_done) with
| true -> begin
(FStar_ToSyntax_Env.export_interface modul.FStar_Syntax_Syntax.name env2)
end
| uu____18459 -> begin
env2
end)
in ((uu____18458), (modul)));
))
end)))


let ast_modul_to_modul : FStar_Parser_AST.modul  ->  FStar_Syntax_Syntax.modul FStar_ToSyntax_Env.withenv = (fun modul env -> (

let uu____18473 = (desugar_modul env modul)
in (match (uu____18473) with
| (env1, modul1) -> begin
((modul1), (env1))
end)))


let decls_to_sigelts : FStar_Parser_AST.decl Prims.list  ->  FStar_Syntax_Syntax.sigelts FStar_ToSyntax_Env.withenv = (fun decls env -> (

let uu____18501 = (desugar_decls env decls)
in (match (uu____18501) with
| (env1, sigelts) -> begin
((sigelts), (env1))
end)))


let partial_ast_modul_to_modul : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Parser_AST.modul  ->  FStar_Syntax_Syntax.modul FStar_ToSyntax_Env.withenv = (fun modul a_modul env -> (

let uu____18541 = (desugar_partial_modul modul env a_modul)
in (match (uu____18541) with
| (env1, modul1) -> begin
((modul1), (env1))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_ToSyntax_Env.module_inclusion_info  ->  Prims.unit FStar_ToSyntax_Env.withenv = (fun m mii en -> (

let uu____18569 = (FStar_ToSyntax_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name mii)
in (match (uu____18569) with
| (en1, pop_when_done) -> begin
(

let en2 = (

let uu____18581 = (FStar_ToSyntax_Env.set_current_module en1 m.FStar_Syntax_Syntax.name)
in (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____18581 m.FStar_Syntax_Syntax.exports))
in (

let env = (FStar_ToSyntax_Env.finish en2 m)
in (

let uu____18583 = (match (pop_when_done) with
| true -> begin
(FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name env)
end
| uu____18584 -> begin
env
end)
in ((()), (uu____18583)))))
end)))




