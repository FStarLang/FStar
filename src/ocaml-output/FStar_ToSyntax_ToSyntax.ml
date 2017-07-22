
open Prims
open FStar_Pervasives

let desugar_disjunctive_pattern : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.branch Prims.list = (fun pats when_opt branch1 -> (FStar_All.pipe_right pats (FStar_List.map (fun pat -> (FStar_Syntax_Util.branch ((pat), (when_opt), (branch1)))))))


let trans_aqual : FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option = (fun uu___200_62 -> (match (uu___200_62) with
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)
end
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality)
end
| uu____67 -> begin
FStar_Pervasives_Native.None
end))


let trans_qual : FStar_Range.range  ->  FStar_Ident.lident FStar_Pervasives_Native.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun r maybe_effect_id uu___201_83 -> (match (uu___201_83) with
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
(FStar_Pervasives.raise (FStar_Errors.Error ((("Qualifier reflect only supported on effects"), (r)))))
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
(FStar_Pervasives.raise (FStar_Errors.Error ((("The \'default\' qualifier on effects is no longer supported"), (r)))))
end
| FStar_Parser_AST.Inline -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Unsupported qualifier"), (r)))))
end
| FStar_Parser_AST.Visible -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Unsupported qualifier"), (r)))))
end))


let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun uu___202_91 -> (match (uu___202_91) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end
| FStar_Parser_AST.LightOff -> begin
FStar_Syntax_Syntax.LightOff
end))


let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option = (fun uu___203_101 -> (match (uu___203_101) with
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

let uu____259 = (FStar_Parser_AST.compile_op n1 s)
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
| "-" when (arity = (Prims.parse_int "1")) -> begin
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

let uu____351 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
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
in (match (((FStar_List.length ftv) = (Prims.parse_int "0"))) with
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
in (match (((FStar_List.length ftv) = (Prims.parse_int "0"))) with
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

let acc = (FStar_Util.new_set (fun id1 id2 -> (match ((id1.FStar_Ident.idText = id2.FStar_Ident.idText)) with
| true -> begin
(Prims.parse_int "0")
end
| uu____1370 -> begin
(Prims.parse_int "1")
end)) (fun uu____1372 -> (Prims.parse_int "0")))
in (fun p -> (gather_pattern_bound_vars_maybe_top acc p)))

type bnd =
| LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * FStar_Syntax_Syntax.term)


let uu___is_LocalBinder : bnd  ->  Prims.bool = (fun projectee -> (match (projectee) with
| LocalBinder (_0) -> begin
true
end
| uu____1399 -> begin
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
| uu____1429 -> begin
false
end))


let __proj__LetBinder__item___0 : bnd  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| LetBinder (_0) -> begin
_0
end))


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun uu___204_1457 -> (match (uu___204_1457) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| uu____1464 -> begin
(failwith "Impossible")
end))


let as_binder : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  (FStar_Ident.ident FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_ToSyntax_Env.env) = (fun env imp uu___205_1492 -> (match (uu___205_1492) with
| (FStar_Pervasives_Native.None, k) -> begin
(

let uu____1508 = (FStar_Syntax_Syntax.null_binder k)
in ((uu____1508), (env)))
end
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____1513 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____1513) with
| (env1, a1) -> begin
(((((

let uu___226_1533 = a1
in {FStar_Syntax_Syntax.ppname = uu___226_1533.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___226_1533.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), ((trans_aqual imp)))), (env1))
end))
end))


type env_t =
FStar_ToSyntax_Env.env


type lenv_t =
FStar_Syntax_Syntax.bv Prims.list


let mk_lb : ((FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  FStar_Syntax_Syntax.letbinding = (fun uu____1553 -> (match (uu____1553) with
| (n1, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n1; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))


let no_annot_abs : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t FStar_Pervasives_Native.None))


let mk_ref_read : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun tm -> (

let tm' = (

let uu____1606 = (

let uu____1621 = (

let uu____1622 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.sread_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____1622))
in (

let uu____1623 = (

let uu____1632 = (

let uu____1639 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (uu____1639)))
in (uu____1632)::[])
in ((uu____1621), (uu____1623))))
in FStar_Syntax_Syntax.Tm_app (uu____1606))
in (FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_alloc : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun tm -> (

let tm' = (

let uu____1673 = (

let uu____1688 = (

let uu____1689 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.salloc_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____1689))
in (

let uu____1690 = (

let uu____1699 = (

let uu____1706 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (uu____1706)))
in (uu____1699)::[])
in ((uu____1688), (uu____1690))))
in FStar_Syntax_Syntax.Tm_app (uu____1673))
in (FStar_Syntax_Syntax.mk tm' FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_assign : FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun t1 t2 pos -> (

let tm = (

let uu____1752 = (

let uu____1767 = (

let uu____1768 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.swrite_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Syntax.fv_to_tm uu____1768))
in (

let uu____1769 = (

let uu____1778 = (

let uu____1785 = (FStar_Syntax_Syntax.as_implicit false)
in ((t1), (uu____1785)))
in (

let uu____1788 = (

let uu____1797 = (

let uu____1804 = (FStar_Syntax_Syntax.as_implicit false)
in ((t2), (uu____1804)))
in (uu____1797)::[])
in (uu____1778)::uu____1788))
in ((uu____1767), (uu____1769))))
in FStar_Syntax_Syntax.Tm_app (uu____1752))
in (FStar_Syntax_Syntax.mk tm FStar_Pervasives_Native.None pos)))


let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun uu___206_1836 -> (match (uu___206_1836) with
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
| uu____1837 -> begin
false
end))


let rec sum_to_universe : FStar_Syntax_Syntax.universe  ->  Prims.int  ->  FStar_Syntax_Syntax.universe = (fun u n1 -> (match ((n1 = (Prims.parse_int "0"))) with
| true -> begin
u
end
| uu____1846 -> begin
(

let uu____1847 = (sum_to_universe u (n1 - (Prims.parse_int "1")))
in FStar_Syntax_Syntax.U_succ (uu____1847))
end))


let int_to_universe : Prims.int  ->  FStar_Syntax_Syntax.universe = (fun n1 -> (sum_to_universe FStar_Syntax_Syntax.U_zero n1))


let rec desugar_maybe_non_constant_universe : FStar_Parser_AST.term  ->  (Prims.int, FStar_Syntax_Syntax.universe) FStar_Util.either = (fun t -> (

let uu____1864 = (

let uu____1865 = (unparen t)
in uu____1865.FStar_Parser_AST.tm)
in (match (uu____1864) with
| FStar_Parser_AST.Wild -> begin
(

let uu____1870 = (

let uu____1871 = (FStar_Syntax_Unionfind.univ_fresh ())
in FStar_Syntax_Syntax.U_unif (uu____1871))
in FStar_Util.Inr (uu____1870))
end
| FStar_Parser_AST.Uvar (u) -> begin
FStar_Util.Inr (FStar_Syntax_Syntax.U_name (u))
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (repr, uu____1882)) -> begin
(

let n1 = (FStar_Util.int_of_string repr)
in ((match ((n1 < (Prims.parse_int "0"))) with
| true -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((((Prims.strcat "Negative universe constant  are not supported : " repr)), (t.FStar_Parser_AST.range)))))
end
| uu____1897 -> begin
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

let uu____1948 = (sum_to_universe u n1)
in FStar_Util.Inr (uu____1948))
end
| (FStar_Util.Inr (u), FStar_Util.Inl (n1)) -> begin
(

let uu____1959 = (sum_to_universe u n1)
in FStar_Util.Inr (uu____1959))
end
| (FStar_Util.Inr (u11), FStar_Util.Inr (u21)) -> begin
(

let uu____1970 = (

let uu____1971 = (

let uu____1976 = (

let uu____1977 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "This universe might contain a sum of two universe variables " uu____1977))
in ((uu____1976), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____1971))
in (FStar_Pervasives.raise uu____1970))
end)))
end
| FStar_Parser_AST.App (uu____1982) -> begin
(

let rec aux = (fun t1 univargs -> (

let uu____2012 = (

let uu____2013 = (unparen t1)
in uu____2013.FStar_Parser_AST.tm)
in (match (uu____2012) with
| FStar_Parser_AST.App (t2, targ, uu____2020) -> begin
(

let uarg = (desugar_maybe_non_constant_universe targ)
in (aux t2 ((uarg)::univargs)))
end
| FStar_Parser_AST.Var (max_lid1) -> begin
(match ((FStar_List.existsb (fun uu___207_2044 -> (match (uu___207_2044) with
| FStar_Util.Inr (uu____2049) -> begin
true
end
| uu____2050 -> begin
false
end)) univargs)) with
| true -> begin
(

let uu____2055 = (

let uu____2056 = (FStar_List.map (fun uu___208_2065 -> (match (uu___208_2065) with
| FStar_Util.Inl (n1) -> begin
(int_to_universe n1)
end
| FStar_Util.Inr (u) -> begin
u
end)) univargs)
in FStar_Syntax_Syntax.U_max (uu____2056))
in FStar_Util.Inr (uu____2055))
end
| uu____2072 -> begin
(

let nargs = (FStar_List.map (fun uu___209_2082 -> (match (uu___209_2082) with
| FStar_Util.Inl (n1) -> begin
n1
end
| FStar_Util.Inr (uu____2088) -> begin
(failwith "impossible")
end)) univargs)
in (

let uu____2089 = (FStar_List.fold_left (fun m n1 -> (match ((m > n1)) with
| true -> begin
m
end
| uu____2094 -> begin
n1
end)) (Prims.parse_int "0") nargs)
in FStar_Util.Inl (uu____2089)))
end)
end
| uu____2095 -> begin
(

let uu____2096 = (

let uu____2097 = (

let uu____2102 = (

let uu____2103 = (

let uu____2104 = (FStar_Parser_AST.term_to_string t1)
in (Prims.strcat uu____2104 " in universe context"))
in (Prims.strcat "Unexpected term " uu____2103))
in ((uu____2102), (t1.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____2097))
in (FStar_Pervasives.raise uu____2096))
end)))
in (aux t []))
end
| uu____2113 -> begin
(

let uu____2114 = (

let uu____2115 = (

let uu____2120 = (

let uu____2121 = (

let uu____2122 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat uu____2122 " in universe context"))
in (Prims.strcat "Unexpected term " uu____2121))
in ((uu____2120), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____2115))
in (FStar_Pervasives.raise uu____2114))
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


let check_fields : 'Auu____2146 . FStar_ToSyntax_Env.env  ->  (FStar_Ident.lident * 'Auu____2146) Prims.list  ->  FStar_Range.range  ->  FStar_ToSyntax_Env.record_or_dc = (fun env fields rg -> (

let uu____2171 = (FStar_List.hd fields)
in (match (uu____2171) with
| (f, uu____2181) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f);
(

let record = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_record_by_field_name env) f)
in (

let check_field = (fun uu____2191 -> (match (uu____2191) with
| (f', uu____2197) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f');
(

let uu____2199 = (FStar_ToSyntax_Env.belongs_to_record env f' record)
in (match (uu____2199) with
| true -> begin
()
end
| uu____2200 -> begin
(

let msg = (FStar_Util.format3 "Field %s belongs to record type %s, whereas field %s does not" f.FStar_Ident.str record.FStar_ToSyntax_Env.typename.FStar_Ident.str f'.FStar_Ident.str)
in (FStar_Pervasives.raise (FStar_Errors.Error (((msg), (rg))))))
end));
)
end))
in ((

let uu____2203 = (FStar_List.tl fields)
in (FStar_List.iter check_field uu____2203));
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
| FStar_Syntax_Syntax.Pat_dot_term (uu____2413) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_wild (uu____2420) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_constant (uu____2421) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (uu____2423, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out uu____2463 -> (match (uu____2463) with
| (p3, uu____2473) -> begin
(

let uu____2474 = (pat_vars p3)
in (FStar_Util.set_union out uu____2474))
end)) FStar_Syntax_Syntax.no_names))
end))
in (pat_vars p1)))
in ((match (((is_mut), (p.FStar_Parser_AST.pat))) with
| (false, uu____2478) -> begin
()
end
| (true, FStar_Parser_AST.PatVar (uu____2479)) -> begin
()
end
| (true, uu____2486) -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("let-mutable is for variables only"), (p.FStar_Parser_AST.prange)))))
end);
(

let push_bv_maybe_mut = (match (is_mut) with
| true -> begin
FStar_ToSyntax_Env.push_bv_mutable
end
| uu____2504 -> begin
FStar_ToSyntax_Env.push_bv
end)
in (

let resolvex = (fun l e x -> (

let uu____2521 = (FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText))))
in (match (uu____2521) with
| FStar_Pervasives_Native.Some (y) -> begin
((l), (e), (y))
end
| uu____2535 -> begin
(

let uu____2538 = (push_bv_maybe_mut e x)
in (match (uu____2538) with
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
| FStar_Parser_AST.PatOr (uu____2602) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.PatOp (op) -> begin
(

let uu____2618 = (

let uu____2619 = (

let uu____2620 = (

let uu____2627 = (

let uu____2628 = (

let uu____2633 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") op.FStar_Ident.idText)
in ((uu____2633), (op.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____2628))
in ((uu____2627), (FStar_Pervasives_Native.None)))
in FStar_Parser_AST.PatVar (uu____2620))
in {FStar_Parser_AST.pat = uu____2619; FStar_Parser_AST.prange = p1.FStar_Parser_AST.prange})
in (aux loc env1 uu____2618))
end
| FStar_Parser_AST.PatAscribed (p2, t) -> begin
(

let uu____2638 = (aux loc env1 p2)
in (match (uu____2638) with
| (loc1, env', binder, p3, imp) -> begin
(

let binder1 = (match (binder) with
| LetBinder (uu____2673) -> begin
(failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t1 = (

let uu____2681 = (close_fun env1 t)
in (desugar_term env1 uu____2681))
in ((match ((match (x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
false
end
| uu____2683 -> begin
true
end)) with
| true -> begin
(

let uu____2684 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____2685 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____2686 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3_warning "Multiple ascriptions for %s in pattern, type %s was shadowed by %s" uu____2684 uu____2685 uu____2686))))
end
| uu____2687 -> begin
()
end);
LocalBinder ((((

let uu___227_2689 = x
in {FStar_Syntax_Syntax.ppname = uu___227_2689.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___227_2689.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})), (aq)));
))
end)
in ((loc1), (env'), (binder1), (p3), (imp)))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____2693 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____2693), (false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____2704 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____2704), (false))))
end
| FStar_Parser_AST.PatTvar (x, aq) -> begin
(

let imp = (aq = FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit))
in (

let aq1 = (trans_aqual aq)
in (

let uu____2725 = (resolvex loc env1 x)
in (match (uu____2725) with
| (loc1, env2, xbv) -> begin
(

let uu____2747 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc1), (env2), (LocalBinder (((xbv), (aq1)))), (uu____2747), (imp)))
end))))
end
| FStar_Parser_AST.PatVar (x, aq) -> begin
(

let imp = (aq = FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit))
in (

let aq1 = (trans_aqual aq)
in (

let uu____2768 = (resolvex loc env1 x)
in (match (uu____2768) with
| (loc1, env2, xbv) -> begin
(

let uu____2790 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc1), (env2), (LocalBinder (((xbv), (aq1)))), (uu____2790), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l1 = (FStar_ToSyntax_Env.fail_or env1 (FStar_ToSyntax_Env.try_lookup_datacon env1) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____2802 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), ([])))))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____2802), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = uu____2826}, args) -> begin
(

let uu____2832 = (FStar_List.fold_right (fun arg uu____2873 -> (match (uu____2873) with
| (loc1, env2, args1) -> begin
(

let uu____2921 = (aux loc1 env2 arg)
in (match (uu____2921) with
| (loc2, env3, uu____2950, arg1, imp) -> begin
((loc2), (env3), ((((arg1), (imp)))::args1))
end))
end)) args ((loc), (env1), ([])))
in (match (uu____2832) with
| (loc1, env2, args1) -> begin
(

let l1 = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_datacon env2) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____3020 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args1)))))
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3020), (false)))))
end))
end
| FStar_Parser_AST.PatApp (uu____3037) -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Unexpected pattern"), (p1.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____3059 = (FStar_List.fold_right (fun pat uu____3092 -> (match (uu____3092) with
| (loc1, env2, pats1) -> begin
(

let uu____3124 = (aux loc1 env2 pat)
in (match (uu____3124) with
| (loc2, env3, uu____3149, pat1, uu____3151) -> begin
((loc2), (env3), ((pat1)::pats1))
end))
end)) pats ((loc), (env1), ([])))
in (match (uu____3059) with
| (loc1, env2, pats1) -> begin
(

let pat = (

let uu____3194 = (

let uu____3197 = (

let uu____3202 = (FStar_Range.end_range p1.FStar_Parser_AST.prange)
in (pos_r uu____3202))
in (

let uu____3203 = (

let uu____3204 = (

let uu____3217 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____3217), ([])))
in FStar_Syntax_Syntax.Pat_cons (uu____3204))
in (FStar_All.pipe_left uu____3197 uu____3203)))
in (FStar_List.fold_right (fun hd1 tl1 -> (

let r = (FStar_Range.union_ranges hd1.FStar_Syntax_Syntax.p tl1.FStar_Syntax_Syntax.p)
in (

let uu____3249 = (

let uu____3250 = (

let uu____3263 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____3263), ((((hd1), (false)))::(((tl1), (false)))::[])))
in FStar_Syntax_Syntax.Pat_cons (uu____3250))
in (FStar_All.pipe_left (pos_r r) uu____3249)))) pats1 uu____3194))
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep1) -> begin
(

let uu____3307 = (FStar_List.fold_left (fun uu____3347 p2 -> (match (uu____3347) with
| (loc1, env2, pats) -> begin
(

let uu____3396 = (aux loc1 env2 p2)
in (match (uu____3396) with
| (loc2, env3, uu____3425, pat, uu____3427) -> begin
((loc2), (env3), ((((pat), (false)))::pats))
end))
end)) ((loc), (env1), ([])) args)
in (match (uu____3307) with
| (loc1, env2, args1) -> begin
(

let args2 = (FStar_List.rev args1)
in (

let l = (match (dep1) with
| true -> begin
(FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end
| uu____3515 -> begin
(FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end)
in (

let uu____3522 = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_lid env2) l)
in (match (uu____3522) with
| (constr, uu____3544) -> begin
(

let l1 = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____3547 -> begin
(failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____3549 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args2)))))
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3549), (false)))))
end))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Unexpected pattern"), (p1.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(

let record = (check_fields env1 fields p1.FStar_Parser_AST.prange)
in (

let fields1 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____3620 -> (match (uu____3620) with
| (f, p2) -> begin
((f.FStar_Ident.ident), (p2))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____3650 -> (match (uu____3650) with
| (f, uu____3656) -> begin
(

let uu____3657 = (FStar_All.pipe_right fields1 (FStar_List.tryFind (fun uu____3683 -> (match (uu____3683) with
| (g, uu____3689) -> begin
(f.FStar_Ident.idText = g.FStar_Ident.idText)
end))))
in (match (uu____3657) with
| FStar_Pervasives_Native.None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p1.FStar_Parser_AST.prange)
end
| FStar_Pervasives_Native.Some (uu____3694, p2) -> begin
p2
end))
end))))
in (

let app = (

let uu____3701 = (

let uu____3702 = (

let uu____3709 = (

let uu____3710 = (

let uu____3711 = (FStar_Ident.lid_of_ids (FStar_List.append record.FStar_ToSyntax_Env.typename.FStar_Ident.ns ((record.FStar_ToSyntax_Env.constrname)::[])))
in FStar_Parser_AST.PatName (uu____3711))
in (FStar_Parser_AST.mk_pattern uu____3710 p1.FStar_Parser_AST.prange))
in ((uu____3709), (args)))
in FStar_Parser_AST.PatApp (uu____3702))
in (FStar_Parser_AST.mk_pattern uu____3701 p1.FStar_Parser_AST.prange))
in (

let uu____3714 = (aux loc env1 app)
in (match (uu____3714) with
| (env2, e, b, p2, uu____3743) -> begin
(

let p3 = (match (p2.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args1) -> begin
(

let uu____3771 = (

let uu____3772 = (

let uu____3785 = (

let uu___228_3786 = fv
in (

let uu____3787 = (

let uu____3790 = (

let uu____3791 = (

let uu____3798 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map FStar_Pervasives_Native.fst))
in ((record.FStar_ToSyntax_Env.typename), (uu____3798)))
in FStar_Syntax_Syntax.Record_ctor (uu____3791))
in FStar_Pervasives_Native.Some (uu____3790))
in {FStar_Syntax_Syntax.fv_name = uu___228_3786.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = uu___228_3786.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu____3787}))
in ((uu____3785), (args1)))
in FStar_Syntax_Syntax.Pat_cons (uu____3772))
in (FStar_All.pipe_left pos uu____3771))
end
| uu____3825 -> begin
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

let uu____3872 = (aux loc env1 p2)
in (match (uu____3872) with
| (loc1, env2, var, p3, uu____3899) -> begin
(

let uu____3904 = (FStar_List.fold_left (fun uu____3936 p4 -> (match (uu____3936) with
| (loc2, env3, ps1) -> begin
(

let uu____3969 = (aux loc2 env3 p4)
in (match (uu____3969) with
| (loc3, env4, uu____3994, p5, uu____3996) -> begin
((loc3), (env4), ((p5)::ps1))
end))
end)) ((loc1), (env2), ([])) ps)
in (match (uu____3904) with
| (loc2, env3, ps1) -> begin
(

let pats = (p3)::(FStar_List.rev ps1)
in ((env3), (var), (pats)))
end))
end))
end
| uu____4047 -> begin
(

let uu____4048 = (aux loc env1 p1)
in (match (uu____4048) with
| (loc1, env2, vars, pat, b) -> begin
((env2), (vars), ((pat)::[]))
end))
end)))
in (

let uu____4088 = (aux_maybe_or env p)
in (match (uu____4088) with
| (env1, b, pats) -> begin
((

let uu____4119 = (FStar_List.map check_linear_pattern_variables pats)
in (FStar_All.pipe_left FStar_Pervasives.ignore uu____4119));
((env1), (b), (pats));
)
end))))));
)))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.list) = (fun top env p is_mut -> (

let mklet = (fun x -> (

let uu____4154 = (

let uu____4155 = (

let uu____4160 = (FStar_ToSyntax_Env.qualify env x)
in ((uu____4160), (FStar_Syntax_Syntax.tun)))
in LetBinder (uu____4155))
in ((env), (uu____4154), ([]))))
in (match (top) with
| true -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(

let uu____4180 = (

let uu____4181 = (

let uu____4186 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") x.FStar_Ident.idText)
in ((uu____4186), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____4181))
in (mklet uu____4180))
end
| FStar_Parser_AST.PatVar (x, uu____4188) -> begin
(mklet x)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____4194); FStar_Parser_AST.prange = uu____4195}, t) -> begin
(

let uu____4201 = (

let uu____4202 = (

let uu____4207 = (FStar_ToSyntax_Env.qualify env x)
in (

let uu____4208 = (desugar_term env t)
in ((uu____4207), (uu____4208))))
in LetBinder (uu____4202))
in ((env), (uu____4201), ([])))
end
| uu____4211 -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end
| uu____4220 -> begin
(

let uu____4221 = (desugar_data_pat env p is_mut)
in (match (uu____4221) with
| (env1, binder, p1) -> begin
(

let p2 = (match (p1) with
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (uu____4250); FStar_Syntax_Syntax.p = uu____4251})::[] -> begin
[]
end
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (uu____4256); FStar_Syntax_Syntax.p = uu____4257})::[] -> begin
[]
end
| uu____4262 -> begin
p1
end)
in ((env1), (binder), (p2)))
end))
end)))
and desugar_binding_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.list) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat Prims.list) = (fun uu____4269 env pat -> (

let uu____4272 = (desugar_data_pat env pat false)
in (match (uu____4272) with
| (env1, uu____4288, pat1) -> begin
((env1), (pat1))
end)))
and desugar_match_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat Prims.list) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env1 = (FStar_ToSyntax_Env.set_expect_typ env false)
in (desugar_term_maybe_top false env1 e)))
and desugar_typ : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env1 = (FStar_ToSyntax_Env.set_expect_typ env true)
in (desugar_term_maybe_top false env1 e)))
and desugar_machine_integer : FStar_ToSyntax_Env.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun env repr uu____4306 range -> (match (uu____4306) with
| (signedness, width) -> begin
(

let uu____4316 = (FStar_Const.bounds signedness width)
in (match (uu____4316) with
| (lower, upper) -> begin
(

let value = (

let uu____4326 = (FStar_Util.ensure_decimal repr)
in (FStar_Util.int_of_string uu____4326))
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

let uu____4329 = (

let uu____4330 = (

let uu____4335 = (FStar_Util.format2 "%s is not in the expected range for %s" repr tnm)
in ((uu____4335), (range)))
in FStar_Errors.Error (uu____4330))
in (FStar_Pervasives.raise uu____4329))
end
| uu____4336 -> begin
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

let uu____4343 = (FStar_ToSyntax_Env.try_lookup_lid env lid)
in (match (uu____4343) with
| FStar_Pervasives_Native.Some (intro_term, uu____4353) -> begin
(match (intro_term.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let private_lid = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text private_intro_nm) range)
in (

let private_fv = (

let uu____4363 = (FStar_Syntax_Util.incr_delta_depth fv.FStar_Syntax_Syntax.fv_delta)
in (FStar_Syntax_Syntax.lid_as_fv private_lid uu____4363 fv.FStar_Syntax_Syntax.fv_qual))
in (

let uu___229_4364 = intro_term
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (private_fv); FStar_Syntax_Syntax.pos = uu___229_4364.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___229_4364.FStar_Syntax_Syntax.vars})))
end
| uu____4365 -> begin
(failwith (Prims.strcat "Unexpected non-fvar for " intro_nm))
end)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4372 = (

let uu____4373 = (

let uu____4378 = (FStar_Util.format1 "Unexpected numeric literal.  Restart F* to load %s." tnm)
in ((uu____4378), (range)))
in FStar_Errors.Error (uu____4373))
in (FStar_Pervasives.raise uu____4372))
end))
in (

let repr1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (FStar_Pervasives_Native.None))))) FStar_Pervasives_Native.None range)
in (

let uu____4394 = (

let uu____4397 = (

let uu____4398 = (

let uu____4413 = (

let uu____4422 = (

let uu____4429 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr1), (uu____4429)))
in (uu____4422)::[])
in ((lid1), (uu____4413)))
in FStar_Syntax_Syntax.Tm_app (uu____4398))
in (FStar_Syntax_Syntax.mk uu____4397))
in (uu____4394 FStar_Pervasives_Native.None range)))))));
)))
end))
end))
and desugar_name : (FStar_Syntax_Syntax.term'  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  env_t  ->  Prims.bool  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.term = (fun mk1 setpos env resolve l -> (

let uu____4468 = (FStar_ToSyntax_Env.fail_or env ((match (resolve) with
| true -> begin
FStar_ToSyntax_Env.try_lookup_lid
end
| uu____4477 -> begin
FStar_ToSyntax_Env.try_lookup_lid_no_resolve
end) env) l)
in (match (uu____4468) with
| (tm, mut) -> begin
(

let tm1 = (setpos tm)
in (match (mut) with
| true -> begin
(

let uu____4483 = (

let uu____4484 = (

let uu____4491 = (mk_ref_read tm1)
in ((uu____4491), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval))))
in FStar_Syntax_Syntax.Tm_meta (uu____4484))
in (FStar_All.pipe_left mk1 uu____4483))
end
| uu____4496 -> begin
tm1
end))
end)))
and desugar_attributes : env_t  ->  FStar_Parser_AST.term Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun env cattributes -> (

let desugar_attribute = (fun t -> (

let uu____4507 = (

let uu____4508 = (unparen t)
in uu____4508.FStar_Parser_AST.tm)
in (match (uu____4507) with
| FStar_Parser_AST.Var ({FStar_Ident.ns = uu____4509; FStar_Ident.ident = uu____4510; FStar_Ident.nsstr = uu____4511; FStar_Ident.str = "cps"}) -> begin
FStar_Syntax_Syntax.CPS
end
| uu____4514 -> begin
(

let uu____4515 = (

let uu____4516 = (

let uu____4521 = (

let uu____4522 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "Unknown attribute " uu____4522))
in ((uu____4521), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____4516))
in (FStar_Pervasives.raise uu____4515))
end)))
in (FStar_List.map desugar_attribute cattributes)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (

let mk1 = (fun e -> (FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let uu___230_4542 = e
in {FStar_Syntax_Syntax.n = uu___230_4542.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___230_4542.FStar_Syntax_Syntax.vars}))
in (

let uu____4545 = (

let uu____4546 = (unparen top)
in uu____4546.FStar_Parser_AST.tm)
in (match (uu____4545) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (uu____4547) -> begin
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
| FStar_Parser_AST.Op (op_star, (uu____4598)::(uu____4599)::[]) when (((FStar_Ident.text_of_id op_star) = "*") && (

let uu____4603 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range op_star)
in (FStar_All.pipe_right uu____4603 FStar_Option.isNone))) -> begin
(

let rec flatten1 = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4616}, (t1)::(t2)::[]) -> begin
(

let uu____4621 = (flatten1 t1)
in (FStar_List.append uu____4621 ((t2)::[])))
end
| uu____4624 -> begin
(t)::[]
end))
in (

let targs = (

let uu____4628 = (

let uu____4631 = (unparen top)
in (flatten1 uu____4631))
in (FStar_All.pipe_right uu____4628 (FStar_List.map (fun t -> (

let uu____4639 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg uu____4639))))))
in (

let uu____4640 = (

let uu____4645 = (FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) uu____4645))
in (match (uu____4640) with
| (tup, uu____4651) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____4655 = (

let uu____4658 = (FStar_ToSyntax_Env.fail_or2 (FStar_ToSyntax_Env.try_lookup_id env) a)
in (FStar_Pervasives_Native.fst uu____4658))
in (FStar_All.pipe_left setpos uu____4655))
end
| FStar_Parser_AST.Uvar (u) -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected universe variable " (Prims.strcat (FStar_Ident.text_of_id u) " in non-universe context"))), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(

let uu____4678 = (op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)
in (match (uu____4678) with
| FStar_Pervasives_Native.None -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected or unbound operator: " (FStar_Ident.text_of_id s))), (top.FStar_Parser_AST.range)))))
end
| FStar_Pervasives_Native.Some (op) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let args1 = (FStar_All.pipe_right args (FStar_List.map (fun t -> (

let uu____4710 = (desugar_term env t)
in ((uu____4710), (FStar_Pervasives_Native.None))))))
in (mk1 (FStar_Syntax_Syntax.Tm_app (((op), (args1))))))
end
| uu____4721 -> begin
op
end)
end))
end
| FStar_Parser_AST.Construct (n1, ((a, uu____4724))::[]) when (n1.FStar_Ident.str = "SMTPat") -> begin
(

let uu____4739 = (

let uu___231_4740 = top
in (

let uu____4741 = (

let uu____4742 = (

let uu____4749 = (

let uu___232_4750 = top
in (

let uu____4751 = (

let uu____4752 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____4752))
in {FStar_Parser_AST.tm = uu____4751; FStar_Parser_AST.range = uu___232_4750.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___232_4750.FStar_Parser_AST.level}))
in ((uu____4749), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____4742))
in {FStar_Parser_AST.tm = uu____4741; FStar_Parser_AST.range = uu___231_4740.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___231_4740.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____4739))
end
| FStar_Parser_AST.Construct (n1, ((a, uu____4755))::[]) when (n1.FStar_Ident.str = "SMTPatT") -> begin
(

let uu____4770 = (

let uu___233_4771 = top
in (

let uu____4772 = (

let uu____4773 = (

let uu____4780 = (

let uu___234_4781 = top
in (

let uu____4782 = (

let uu____4783 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____4783))
in {FStar_Parser_AST.tm = uu____4782; FStar_Parser_AST.range = uu___234_4781.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___234_4781.FStar_Parser_AST.level}))
in ((uu____4780), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____4773))
in {FStar_Parser_AST.tm = uu____4772; FStar_Parser_AST.range = uu___233_4771.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___233_4771.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____4770))
end
| FStar_Parser_AST.Construct (n1, ((a, uu____4786))::[]) when (n1.FStar_Ident.str = "SMTPatOr") -> begin
(

let uu____4801 = (

let uu___235_4802 = top
in (

let uu____4803 = (

let uu____4804 = (

let uu____4811 = (

let uu___236_4812 = top
in (

let uu____4813 = (

let uu____4814 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat_or")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____4814))
in {FStar_Parser_AST.tm = uu____4813; FStar_Parser_AST.range = uu___236_4812.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___236_4812.FStar_Parser_AST.level}))
in ((uu____4811), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____4804))
in {FStar_Parser_AST.tm = uu____4803; FStar_Parser_AST.range = uu___235_4802.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___235_4802.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____4801))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____4815; FStar_Ident.ident = uu____4816; FStar_Ident.nsstr = uu____4817; FStar_Ident.str = "Type0"}) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____4820; FStar_Ident.ident = uu____4821; FStar_Ident.nsstr = uu____4822; FStar_Ident.str = "Type"}) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Construct ({FStar_Ident.ns = uu____4825; FStar_Ident.ident = uu____4826; FStar_Ident.nsstr = uu____4827; FStar_Ident.str = "Type"}, ((t, FStar_Parser_AST.UnivApp))::[]) -> begin
(

let uu____4845 = (

let uu____4846 = (desugar_universe t)
in FStar_Syntax_Syntax.Tm_type (uu____4846))
in (mk1 uu____4845))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____4847; FStar_Ident.ident = uu____4848; FStar_Ident.nsstr = uu____4849; FStar_Ident.str = "Effect"}) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____4852; FStar_Ident.ident = uu____4853; FStar_Ident.nsstr = uu____4854; FStar_Ident.str = "True"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____4857; FStar_Ident.ident = uu____4858; FStar_Ident.nsstr = uu____4859; FStar_Ident.str = "False"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
end
| FStar_Parser_AST.Projector (eff_name, {FStar_Ident.idText = txt; FStar_Ident.idRange = uu____4864}) when ((is_special_effect_combinator txt) && (FStar_ToSyntax_Env.is_effect_name env eff_name)) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name);
(

let uu____4866 = (FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name)
in (match (uu____4866) with
| FStar_Pervasives_Native.Some (ed) -> begin
(

let lid = (FStar_Syntax_Util.dm4f_lid ed txt)
in (FStar_Syntax_Syntax.fvar lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4871 = (FStar_Util.format2 "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)" (FStar_Ident.text_of_lid eff_name) txt)
in (failwith uu____4871))
end));
)
end
| FStar_Parser_AST.Assign (ident, t2) -> begin
(

let t21 = (desugar_term env t2)
in (

let uu____4875 = (FStar_ToSyntax_Env.fail_or2 (FStar_ToSyntax_Env.try_lookup_id env) ident)
in (match (uu____4875) with
| (t1, mut) -> begin
((match ((not (mut))) with
| true -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Can only assign to mutable values"), (top.FStar_Parser_AST.range)))))
end
| uu____4887 -> begin
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

let uu____4902 = (FStar_ToSyntax_Env.try_lookup_datacon env l)
in (match (uu____4902) with
| FStar_Pervasives_Native.Some (uu____4911) -> begin
FStar_Pervasives_Native.Some (((true), (l)))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4916 = (FStar_ToSyntax_Env.try_lookup_root_effect_name env l)
in (match (uu____4916) with
| FStar_Pervasives_Native.Some (new_name) -> begin
FStar_Pervasives_Native.Some (((false), (new_name)))
end
| uu____4930 -> begin
FStar_Pervasives_Native.None
end))
end))
in (match (name) with
| FStar_Pervasives_Native.Some (resolve, new_name) -> begin
(

let uu____4943 = (FStar_Syntax_Util.mk_field_projector_name_from_ident new_name i)
in (desugar_name mk1 setpos env resolve uu____4943))
end
| uu____4944 -> begin
(

let uu____4951 = (

let uu____4952 = (

let uu____4957 = (FStar_Util.format1 "Data constructor or effect %s not found" l.FStar_Ident.str)
in ((uu____4957), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____4952))
in (FStar_Pervasives.raise uu____4951))
end));
)
end
| FStar_Parser_AST.Discrim (lid) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid);
(

let uu____4960 = (FStar_ToSyntax_Env.try_lookup_datacon env lid)
in (match (uu____4960) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4963 = (

let uu____4964 = (

let uu____4969 = (FStar_Util.format1 "Data constructor %s not found" lid.FStar_Ident.str)
in ((uu____4969), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____4964))
in (FStar_Pervasives.raise uu____4963))
end
| uu____4970 -> begin
(

let lid' = (FStar_Syntax_Util.mk_discriminator lid)
in (desugar_name mk1 setpos env true lid'))
end));
)
end
| FStar_Parser_AST.Construct (l, args) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l);
(

let uu____4989 = (FStar_ToSyntax_Env.try_lookup_datacon env l)
in (match (uu____4989) with
| FStar_Pervasives_Native.Some (head1) -> begin
(

let uu____4993 = (

let uu____5000 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (head1)))
in ((uu____5000), (true)))
in (match (uu____4993) with
| (head2, is_data) -> begin
(match (args) with
| [] -> begin
head2
end
| uu____5015 -> begin
(

let uu____5022 = (FStar_Util.take (fun uu____5046 -> (match (uu____5046) with
| (uu____5051, imp) -> begin
(imp = FStar_Parser_AST.UnivApp)
end)) args)
in (match (uu____5022) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun x -> (desugar_universe (FStar_Pervasives_Native.fst x))) universes)
in (

let args2 = (FStar_List.map (fun uu____5115 -> (match (uu____5115) with
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
| uu____5136 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_uinst (((head2), (universes1)))))
end)
in (

let app = (mk1 (FStar_Syntax_Syntax.Tm_app (((head3), (args2)))))
in (match (is_data) with
| true -> begin
(mk1 (FStar_Syntax_Syntax.Tm_meta (((app), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end
| uu____5156 -> begin
app
end)))))
end))
end)
end))
end
| FStar_Pervasives_Native.None -> begin
(

let error_msg = (

let uu____5158 = (FStar_ToSyntax_Env.try_lookup_effect_name env l)
in (match (uu____5158) with
| FStar_Pervasives_Native.None -> begin
(Prims.strcat "Constructor " (Prims.strcat l.FStar_Ident.str " not found"))
end
| FStar_Pervasives_Native.Some (uu____5161) -> begin
(Prims.strcat "Effect " (Prims.strcat l.FStar_Ident.str " used at an unexpected position"))
end))
in (FStar_Pervasives.raise (FStar_Errors.Error (((error_msg), (top.FStar_Parser_AST.range))))))
end));
)
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let uu____5168 = (FStar_List.fold_left (fun uu____5213 b -> (match (uu____5213) with
| (env1, tparams, typs) -> begin
(

let uu____5270 = (desugar_binder env1 b)
in (match (uu____5270) with
| (xopt, t1) -> begin
(

let uu____5299 = (match (xopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5308 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env1), (uu____5308)))
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_ToSyntax_Env.push_bv env1 x)
end)
in (match (uu____5299) with
| (env2, x) -> begin
(

let uu____5328 = (

let uu____5331 = (

let uu____5334 = (

let uu____5335 = (no_annot_abs tparams t1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____5335))
in (uu____5334)::[])
in (FStar_List.append typs uu____5331))
in ((env2), ((FStar_List.append tparams (((((

let uu___237_5361 = x
in {FStar_Syntax_Syntax.ppname = uu___237_5361.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___237_5361.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})), (FStar_Pervasives_Native.None)))::[]))), (uu____5328)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type_level FStar_Pervasives_Native.None))::[])))
in (match (uu____5168) with
| (env1, uu____5385, targs) -> begin
(

let uu____5407 = (

let uu____5412 = (FStar_Parser_Const.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_ToSyntax_Env.fail_or env1 (FStar_ToSyntax_Env.try_lookup_lid env1) uu____5412))
in (match (uu____5407) with
| (tup, uu____5418) -> begin
(FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let uu____5429 = (uncurry binders t)
in (match (uu____5429) with
| (bs, t1) -> begin
(

let rec aux = (fun env1 bs1 uu___210_5461 -> (match (uu___210_5461) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range env1 t1)
in (

let uu____5475 = (FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod)
in (FStar_All.pipe_left setpos uu____5475)))
end
| (hd1)::tl1 -> begin
(

let bb = (desugar_binder env1 hd1)
in (

let uu____5497 = (as_binder env1 hd1.FStar_Parser_AST.aqual bb)
in (match (uu____5497) with
| (b, env2) -> begin
(aux env2 ((b)::bs1) tl1)
end)))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(

let uu____5512 = (desugar_binder env b)
in (match (uu____5512) with
| (FStar_Pervasives_Native.None, uu____5519) -> begin
(failwith "Missing binder in refinement")
end
| b1 -> begin
(

let uu____5529 = (as_binder env FStar_Pervasives_Native.None b1)
in (match (uu____5529) with
| ((x, uu____5535), env1) -> begin
(

let f1 = (desugar_formula env1 f)
in (

let uu____5542 = (FStar_Syntax_Util.refine x f1)
in (FStar_All.pipe_left setpos uu____5542)))
end))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let binders1 = (FStar_All.pipe_right binders (FStar_List.map replace_unit_pattern))
in (

let uu____5562 = (FStar_List.fold_left (fun uu____5582 pat -> (match (uu____5582) with
| (env1, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (uu____5608, t) -> begin
(

let uu____5610 = (

let uu____5613 = (free_type_vars env1 t)
in (FStar_List.append uu____5613 ftvs))
in ((env1), (uu____5610)))
end
| uu____5618 -> begin
((env1), (ftvs))
end)
end)) ((env), ([])) binders1)
in (match (uu____5562) with
| (uu____5623, ftv) -> begin
(

let ftv1 = (sort_ftv ftv)
in (

let binders2 = (

let uu____5635 = (FStar_All.pipe_right ftv1 (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append uu____5635 binders1))
in (

let rec aux = (fun env1 bs sc_pat_opt uu___211_5676 -> (match (uu___211_5676) with
| [] -> begin
(

let body1 = (desugar_term env1 body)
in (

let body2 = (match (sc_pat_opt) with
| FStar_Pervasives_Native.Some (sc, pat) -> begin
(

let body2 = (

let uu____5714 = (

let uu____5715 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right uu____5715 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close uu____5714 body1))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (FStar_Pervasives_Native.None), (body2)))::[])))) FStar_Pervasives_Native.None body2.FStar_Syntax_Syntax.pos))
end
| FStar_Pervasives_Native.None -> begin
body1
end)
in (

let uu____5768 = (no_annot_abs (FStar_List.rev bs) body2)
in (setpos uu____5768))))
end
| (p)::rest -> begin
(

let uu____5779 = (desugar_binding_pat env1 p)
in (match (uu____5779) with
| (env2, b, pat) -> begin
(

let pat1 = (match (pat) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (p1)::[] -> begin
FStar_Pervasives_Native.Some (p1)
end
| uu____5803 -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Disjunctive patterns are not supported in abstractions"), (p.FStar_Parser_AST.prange)))))
end)
in (

let uu____5808 = (match (b) with
| LetBinder (uu____5841) -> begin
(failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt1 = (match (((pat1), (sc_pat_opt))) with
| (FStar_Pervasives_Native.None, uu____5891) -> begin
sc_pat_opt
end
| (FStar_Pervasives_Native.Some (p1), FStar_Pervasives_Native.None) -> begin
(

let uu____5927 = (

let uu____5932 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____5932), (p1)))
in FStar_Pervasives_Native.Some (uu____5927))
end
| (FStar_Pervasives_Native.Some (p1), FStar_Pervasives_Native.Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (uu____5968), uu____5969) -> begin
(

let tup2 = (

let uu____5971 = (FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____5971 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____5975 = (

let uu____5978 = (

let uu____5979 = (

let uu____5994 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (

let uu____5997 = (

let uu____6000 = (FStar_Syntax_Syntax.as_arg sc)
in (

let uu____6001 = (

let uu____6004 = (

let uu____6005 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____6005))
in (uu____6004)::[])
in (uu____6000)::uu____6001))
in ((uu____5994), (uu____5997))))
in FStar_Syntax_Syntax.Tm_app (uu____5979))
in (FStar_Syntax_Syntax.mk uu____5978))
in (uu____5975 FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
in (

let p2 = (

let uu____6016 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p1), (false)))::[])))) uu____6016))
in FStar_Pervasives_Native.Some (((sc1), (p2))))))
end
| (FStar_Syntax_Syntax.Tm_app (uu____6047, args), FStar_Syntax_Syntax.Pat_cons (uu____6049, pats)) -> begin
(

let tupn = (

let uu____6088 = (FStar_Parser_Const.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____6088 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____6098 = (

let uu____6099 = (

let uu____6114 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (

let uu____6117 = (

let uu____6126 = (

let uu____6135 = (

let uu____6136 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____6136))
in (uu____6135)::[])
in (FStar_List.append args uu____6126))
in ((uu____6114), (uu____6117))))
in FStar_Syntax_Syntax.Tm_app (uu____6099))
in (mk1 uu____6098))
in (

let p2 = (

let uu____6156 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p1), (false)))::[])))))) uu____6156))
in FStar_Pervasives_Native.Some (((sc1), (p2))))))
end
| uu____6191 -> begin
(failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt1)))
end)
in (match (uu____5808) with
| (b1, sc_pat_opt1) -> begin
(aux env2 ((b1)::bs) sc_pat_opt1 rest)
end)))
end))
end))
in (aux env [] FStar_Pervasives_Native.None binders2))))
end)))
end
| FStar_Parser_AST.App (uu____6258, uu____6259, FStar_Parser_AST.UnivApp) -> begin
(

let rec aux = (fun universes e -> (

let uu____6273 = (

let uu____6274 = (unparen e)
in uu____6274.FStar_Parser_AST.tm)
in (match (uu____6273) with
| FStar_Parser_AST.App (e1, t, FStar_Parser_AST.UnivApp) -> begin
(

let univ_arg = (desugar_universe t)
in (aux ((univ_arg)::universes) e1))
end
| uu____6280 -> begin
(

let head1 = (desugar_term env e)
in (mk1 (FStar_Syntax_Syntax.Tm_uinst (((head1), (universes))))))
end)))
in (aux [] top))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (lid); FStar_Parser_AST.range = uu____6285; FStar_Parser_AST.level = uu____6286}, tau, FStar_Parser_AST.Nothing) when (FStar_Ident.lid_equals lid FStar_Parser_Const.assert_by_tactic_lid) -> begin
(

let l = (

let uu____6289 = (

let uu____6290 = (unparen top)
in uu____6290.FStar_Parser_AST.tm)
in (match (uu____6289) with
| FStar_Parser_AST.App (l, uu____6292, uu____6293) -> begin
l
end
| uu____6294 -> begin
(failwith "impossible")
end))
in (

let tactic_unit_type = (

let uu____6296 = (

let uu____6297 = (

let uu____6304 = (

let uu____6305 = (

let uu____6306 = (FStar_Ident.lid_of_path (("FStar")::("Tactics")::("Effect")::("tactic")::[]) tau.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____6306))
in (FStar_Parser_AST.mk_term uu____6305 tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level))
in (

let uu____6307 = (

let uu____6308 = (

let uu____6309 = (FStar_Ident.lid_of_path (("Prims")::("unit")::[]) tau.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____6309))
in (FStar_Parser_AST.mk_term uu____6308 tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level))
in ((uu____6304), (uu____6307), (FStar_Parser_AST.Nothing))))
in FStar_Parser_AST.App (uu____6297))
in (FStar_Parser_AST.mk_term uu____6296 tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level))
in (

let t' = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((l), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((tau), (tactic_unit_type), (FStar_Pervasives_Native.None)))) tau.FStar_Parser_AST.range tau.FStar_Parser_AST.level)), (FStar_Parser_AST.Nothing)))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (desugar_term env t'))))
end
| FStar_Parser_AST.App (uu____6313) -> begin
(

let rec aux = (fun args e -> (

let uu____6345 = (

let uu____6346 = (unparen e)
in uu____6346.FStar_Parser_AST.tm)
in (match (uu____6345) with
| FStar_Parser_AST.App (e1, t, imp) when (imp <> FStar_Parser_AST.UnivApp) -> begin
(

let arg = (

let uu____6359 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) uu____6359))
in (aux ((arg)::args) e1))
end
| uu____6372 -> begin
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

let uu____6398 = (

let uu____6399 = (FStar_Ident.lid_of_path (("bind")::[]) x.FStar_Ident.idRange)
in FStar_Parser_AST.Var (uu____6399))
in (FStar_Parser_AST.mk_term uu____6398 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let uu____6400 = (FStar_Parser_AST.mkExplicitApp bind1 ((t1)::(k)::[]) top.FStar_Parser_AST.range)
in (desugar_term env uu____6400)))))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(

let uu____6403 = (

let uu____6404 = (

let uu____6411 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((uu____6411), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))
in FStar_Syntax_Syntax.Tm_meta (uu____6404))
in (mk1 uu____6403))
end
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(

let env1 = (FStar_ToSyntax_Env.push_namespace env lid)
in (

let uu____6429 = (

let uu____6434 = (FStar_ToSyntax_Env.expect_typ env1)
in (match (uu____6434) with
| true -> begin
desugar_typ
end
| uu____6439 -> begin
desugar_term
end))
in (uu____6429 env1 e)))
end
| FStar_Parser_AST.Let (qual1, ((pat, _snd))::_tl, body) -> begin
(

let is_rec = (qual1 = FStar_Parser_AST.Rec)
in (

let ds_let_rec_or_app = (fun uu____6467 -> (

let bindings = (((pat), (_snd)))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun uu____6553 -> (match (uu____6553) with
| (p, def) -> begin
(

let uu____6578 = (is_app_pattern p)
in (match (uu____6578) with
| true -> begin
(

let uu____6597 = (destruct_app_pattern env top_level p)
in ((uu____6597), (def)))
end
| uu____6626 -> begin
(match ((FStar_Parser_AST.un_function p def)) with
| FStar_Pervasives_Native.Some (p1, def1) -> begin
(

let uu____6651 = (destruct_app_pattern env top_level p1)
in ((uu____6651), (def1)))
end
| uu____6680 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, uu____6706); FStar_Parser_AST.prange = uu____6707}, t) -> begin
(match (top_level) with
| true -> begin
(

let uu____6731 = (

let uu____6746 = (

let uu____6751 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (uu____6751))
in ((uu____6746), ([]), (FStar_Pervasives_Native.Some (t))))
in ((uu____6731), (def)))
end
| uu____6774 -> begin
((((FStar_Util.Inl (id)), ([]), (FStar_Pervasives_Native.Some (t)))), (def))
end)
end
| FStar_Parser_AST.PatVar (id, uu____6798) -> begin
(match (top_level) with
| true -> begin
(

let uu____6821 = (

let uu____6836 = (

let uu____6841 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (uu____6841))
in ((uu____6836), ([]), (FStar_Pervasives_Native.None)))
in ((uu____6821), (def)))
end
| uu____6864 -> begin
((((FStar_Util.Inl (id)), ([]), (FStar_Pervasives_Native.None))), (def))
end)
end
| uu____6887 -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end))
end))))
in (

let uu____6906 = (FStar_List.fold_left (fun uu____6966 uu____6967 -> (match (((uu____6966), (uu____6967))) with
| ((env1, fnames, rec_bindings), ((f, uu____7050, uu____7051), uu____7052)) -> begin
(

let uu____7131 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let uu____7157 = (FStar_ToSyntax_Env.push_bv env1 x)
in (match (uu____7157) with
| (env2, xx) -> begin
(

let uu____7176 = (

let uu____7179 = (FStar_Syntax_Syntax.mk_binder xx)
in (uu____7179)::rec_bindings)
in ((env2), (FStar_Util.Inl (xx)), (uu____7176)))
end))
end
| FStar_Util.Inr (l) -> begin
(

let uu____7187 = (FStar_ToSyntax_Env.push_top_level_rec_binding env1 l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in ((uu____7187), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (uu____7131) with
| (env2, lbname, rec_bindings1) -> begin
((env2), ((lbname)::fnames), (rec_bindings1))
end))
end)) ((env), ([]), ([])) funs)
in (match (uu____6906) with
| (env', fnames, rec_bindings) -> begin
(

let fnames1 = (FStar_List.rev fnames)
in (

let rec_bindings1 = (FStar_List.rev rec_bindings)
in (

let desugar_one_def = (fun env1 lbname uu____7313 -> (match (uu____7313) with
| ((uu____7336, args, result_t), def) -> begin
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

let uu____7380 = (is_comp_type env1 t)
in (match (uu____7380) with
| true -> begin
((

let uu____7382 = (FStar_All.pipe_right args1 (FStar_List.tryFind (fun x -> (

let uu____7392 = (is_var_pattern x)
in (not (uu____7392))))))
in (match (uu____7382) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (p) -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable"), (p.FStar_Parser_AST.prange)))))
end));
t;
)
end
| uu____7394 -> begin
(

let uu____7395 = (((FStar_Options.ml_ish ()) && (

let uu____7397 = (FStar_ToSyntax_Env.try_lookup_effect_name env1 FStar_Parser_Const.effect_ML_lid)
in (FStar_Option.isSome uu____7397))) && ((not (is_rec)) || ((FStar_List.length args1) <> (Prims.parse_int "0"))))
in (match (uu____7395) with
| true -> begin
(FStar_Parser_AST.ml_comp t)
end
| uu____7400 -> begin
(FStar_Parser_AST.tot_comp t)
end))
end))
in (

let uu____7401 = (FStar_Range.union_ranges t1.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t1), (FStar_Pervasives_Native.None)))) uu____7401 FStar_Parser_AST.Expr)))
end)
in (

let def2 = (match (args1) with
| [] -> begin
def1
end
| uu____7405 -> begin
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

let uu____7420 = (

let uu____7421 = (FStar_Syntax_Util.incr_delta_qualifier body1)
in (FStar_Syntax_Syntax.lid_as_fv l uu____7421 FStar_Pervasives_Native.None))
in FStar_Util.Inr (uu____7420))
end)
in (

let body2 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.close rec_bindings1 body1)
end
| uu____7423 -> begin
body1
end)
in (mk_lb ((lbname1), (FStar_Syntax_Syntax.tun), (body2)))))))))
end))
in (

let lbs = (FStar_List.map2 (desugar_one_def (match (is_rec) with
| true -> begin
env'
end
| uu____7453 -> begin
env
end)) fnames1 funs)
in (

let body1 = (desugar_term env' body)
in (

let uu____7455 = (

let uu____7456 = (

let uu____7469 = (FStar_Syntax_Subst.close rec_bindings1 body1)
in ((((is_rec), (lbs))), (uu____7469)))
in FStar_Syntax_Syntax.Tm_let (uu____7456))
in (FStar_All.pipe_left mk1 uu____7455)))))))
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
| uu____7499 -> begin
t11
end)
in (

let uu____7500 = (desugar_binding_pat_maybe_top top_level env pat1 is_mutable)
in (match (uu____7500) with
| (env1, binder, pat2) -> begin
(

let tm = (match (binder) with
| LetBinder (l, t) -> begin
(

let body1 = (desugar_term env1 t2)
in (

let fv = (

let uu____7527 = (FStar_Syntax_Util.incr_delta_qualifier t12)
in (FStar_Syntax_Syntax.lid_as_fv l uu____7527 FStar_Pervasives_Native.None))
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_let (((((false), (({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t12})::[]))), (body1)))))))
end
| LocalBinder (x, uu____7539) -> begin
(

let body1 = (desugar_term env1 t2)
in (

let body2 = (match (pat2) with
| [] -> begin
body1
end
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (uu____7542); FStar_Syntax_Syntax.p = uu____7543})::[] -> begin
body1
end
| uu____7548 -> begin
(

let uu____7551 = (

let uu____7554 = (

let uu____7555 = (

let uu____7578 = (FStar_Syntax_Syntax.bv_to_name x)
in (

let uu____7579 = (desugar_disjunctive_pattern pat2 FStar_Pervasives_Native.None body1)
in ((uu____7578), (uu____7579))))
in FStar_Syntax_Syntax.Tm_match (uu____7555))
in (FStar_Syntax_Syntax.mk uu____7554))
in (uu____7551 FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
end)
in (

let uu____7589 = (

let uu____7590 = (

let uu____7603 = (

let uu____7604 = (

let uu____7605 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____7605)::[])
in (FStar_Syntax_Subst.close uu____7604 body2))
in ((((false), (((mk_lb ((FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t12))))::[]))), (uu____7603)))
in FStar_Syntax_Syntax.Tm_let (uu____7590))
in (FStar_All.pipe_left mk1 uu____7589))))
end)
in (match (is_mutable) with
| true -> begin
(FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((tm), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc))))))
end
| uu____7630 -> begin
tm
end))
end))))))
in (

let uu____7631 = (is_rec || (is_app_pattern pat))
in (match (uu____7631) with
| true -> begin
(ds_let_rec_or_app ())
end
| uu____7632 -> begin
(ds_non_rec pat _snd body)
end)))))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (

let t_bool1 = (

let uu____7640 = (

let uu____7641 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Syntax_Syntax.Tm_fvar (uu____7641))
in (mk1 uu____7640))
in (

let uu____7642 = (

let uu____7643 = (

let uu____7666 = (

let uu____7669 = (desugar_term env t1)
in (FStar_Syntax_Util.ascribe uu____7669 ((FStar_Util.Inl (t_bool1)), (FStar_Pervasives_Native.None))))
in (

let uu____7690 = (

let uu____7705 = (

let uu____7718 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) t2.FStar_Parser_AST.range)
in (

let uu____7721 = (desugar_term env t2)
in ((uu____7718), (FStar_Pervasives_Native.None), (uu____7721))))
in (

let uu____7730 = (

let uu____7745 = (

let uu____7758 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) t3.FStar_Parser_AST.range)
in (

let uu____7761 = (desugar_term env t3)
in ((uu____7758), (FStar_Pervasives_Native.None), (uu____7761))))
in (uu____7745)::[])
in (uu____7705)::uu____7730))
in ((uu____7666), (uu____7690))))
in FStar_Syntax_Syntax.Tm_match (uu____7643))
in (mk1 uu____7642))))
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

let desugar_branch = (fun uu____7902 -> (match (uu____7902) with
| (pat, wopt, b) -> begin
(

let uu____7920 = (desugar_match_pat env pat)
in (match (uu____7920) with
| (env1, pat1) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (e1) -> begin
(

let uu____7941 = (desugar_term env1 e1)
in FStar_Pervasives_Native.Some (uu____7941))
end)
in (

let b1 = (desugar_term env1 b)
in (desugar_disjunctive_pattern pat1 wopt1 b1)))
end))
end))
in (

let uu____7943 = (

let uu____7944 = (

let uu____7967 = (desugar_term env e)
in (

let uu____7968 = (FStar_List.collect desugar_branch branches)
in ((uu____7967), (uu____7968))))
in FStar_Syntax_Syntax.Tm_match (uu____7944))
in (FStar_All.pipe_left mk1 uu____7943)))
end
| FStar_Parser_AST.Ascribed (e, t, tac_opt) -> begin
(

let annot = (

let uu____7997 = (is_comp_type env t)
in (match (uu____7997) with
| true -> begin
(

let uu____8004 = (desugar_comp t.FStar_Parser_AST.range env t)
in FStar_Util.Inr (uu____8004))
end
| uu____8009 -> begin
(

let uu____8010 = (desugar_term env t)
in FStar_Util.Inl (uu____8010))
end))
in (

let tac_opt1 = (FStar_Util.map_opt tac_opt (desugar_term env))
in (

let uu____8016 = (

let uu____8017 = (

let uu____8044 = (desugar_term env e)
in ((uu____8044), (((annot), (tac_opt1))), (FStar_Pervasives_Native.None)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____8017))
in (FStar_All.pipe_left mk1 uu____8016))))
end
| FStar_Parser_AST.Record (uu____8069, []) -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let record = (check_fields env fields top.FStar_Parser_AST.range)
in (

let user_ns = (

let uu____8106 = (FStar_List.hd fields)
in (match (uu____8106) with
| (f, uu____8118) -> begin
f.FStar_Ident.ns
end))
in (

let get_field = (fun xopt f -> (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun uu____8160 -> (match (uu____8160) with
| (g, uu____8166) -> begin
(f.FStar_Ident.idText = g.FStar_Ident.ident.FStar_Ident.idText)
end))))
in (

let fn = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((f)::[])))
in (match (found) with
| FStar_Pervasives_Native.Some (uu____8172, e) -> begin
((fn), (e))
end
| FStar_Pervasives_Native.None -> begin
(match (xopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8186 = (

let uu____8187 = (

let uu____8192 = (FStar_Util.format2 "Field %s of record type %s is missing" f.FStar_Ident.idText record.FStar_ToSyntax_Env.typename.FStar_Ident.str)
in ((uu____8192), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____8187))
in (FStar_Pervasives.raise uu____8186))
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

let uu____8200 = (

let uu____8211 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____8242 -> (match (uu____8242) with
| (f, uu____8252) -> begin
(

let uu____8253 = (

let uu____8254 = (get_field FStar_Pervasives_Native.None f)
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____8254))
in ((uu____8253), (FStar_Parser_AST.Nothing)))
end))))
in ((user_constrname), (uu____8211)))
in FStar_Parser_AST.Construct (uu____8200))
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (

let uu____8272 = (

let uu____8273 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____8273))
in (FStar_Parser_AST.mk_term uu____8272 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record1 = (

let uu____8275 = (

let uu____8288 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____8318 -> (match (uu____8318) with
| (f, uu____8328) -> begin
(get_field (FStar_Pervasives_Native.Some (xterm)) f)
end))))
in ((FStar_Pervasives_Native.None), (uu____8288)))
in FStar_Parser_AST.Record (uu____8275))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (FStar_Pervasives_Native.None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record1 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm1 = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_term env recterm1)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____8356; FStar_Syntax_Syntax.vars = uu____8357}, args); FStar_Syntax_Syntax.pos = uu____8359; FStar_Syntax_Syntax.vars = uu____8360}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(

let e1 = (

let uu____8388 = (

let uu____8389 = (

let uu____8404 = (

let uu____8405 = (

let uu____8408 = (

let uu____8409 = (

let uu____8416 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map FStar_Pervasives_Native.fst))
in ((record.FStar_ToSyntax_Env.typename), (uu____8416)))
in FStar_Syntax_Syntax.Record_ctor (uu____8409))
in FStar_Pervasives_Native.Some (uu____8408))
in (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant uu____8405))
in ((uu____8404), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____8389))
in (FStar_All.pipe_left mk1 uu____8388))
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((e1), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))))))
end
| uu____8447 -> begin
e
end))))))))
end
| FStar_Parser_AST.Project (e, f) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f);
(

let uu____8451 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f)
in (match (uu____8451) with
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
| uu____8469 -> begin
FStar_Pervasives_Native.None
end)
in (

let uu____8470 = (

let uu____8471 = (

let uu____8486 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projname (FStar_Ident.range_of_lid f)) FStar_Syntax_Syntax.Delta_equational qual1)
in (

let uu____8487 = (

let uu____8490 = (FStar_Syntax_Syntax.as_arg e1)
in (uu____8490)::[])
in ((uu____8486), (uu____8487))))
in FStar_Syntax_Syntax.Tm_app (uu____8471))
in (FStar_All.pipe_left mk1 uu____8470)))))
end));
)
end
| FStar_Parser_AST.NamedTyp (uu____8495, e) -> begin
(desugar_term env e)
end
| FStar_Parser_AST.Paren (e) -> begin
(desugar_term env e)
end
| uu____8498 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| uu____8499 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Let (uu____8500, uu____8501, uu____8502) -> begin
(failwith "Not implemented yet")
end
| FStar_Parser_AST.QForall (uu____8515, uu____8516, uu____8517) -> begin
(failwith "Not implemented yet")
end
| FStar_Parser_AST.QExists (uu____8530, uu____8531, uu____8532) -> begin
(failwith "Not implemented yet")
end)))))
and desugar_args : FStar_ToSyntax_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____8581 -> (match (uu____8581) with
| (a, imp) -> begin
(

let uu____8594 = (desugar_term env a)
in (arg_withimp_e imp uu____8594))
end)))))
and desugar_comp : FStar_Range.range  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun r env t -> (

let fail = (fun msg -> (FStar_Pervasives.raise (FStar_Errors.Error (((msg), (r))))))
in (

let is_requires = (fun uu____8613 -> (match (uu____8613) with
| (t1, uu____8619) -> begin
(

let uu____8620 = (

let uu____8621 = (unparen t1)
in uu____8621.FStar_Parser_AST.tm)
in (match (uu____8620) with
| FStar_Parser_AST.Requires (uu____8622) -> begin
true
end
| uu____8629 -> begin
false
end))
end))
in (

let is_ensures = (fun uu____8637 -> (match (uu____8637) with
| (t1, uu____8643) -> begin
(

let uu____8644 = (

let uu____8645 = (unparen t1)
in uu____8645.FStar_Parser_AST.tm)
in (match (uu____8644) with
| FStar_Parser_AST.Ensures (uu____8646) -> begin
true
end
| uu____8653 -> begin
false
end))
end))
in (

let is_app = (fun head1 uu____8664 -> (match (uu____8664) with
| (t1, uu____8670) -> begin
(

let uu____8671 = (

let uu____8672 = (unparen t1)
in uu____8672.FStar_Parser_AST.tm)
in (match (uu____8671) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = uu____8674; FStar_Parser_AST.level = uu____8675}, uu____8676, uu____8677) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head1)
end
| uu____8678 -> begin
false
end))
end))
in (

let is_smt_pat = (fun uu____8686 -> (match (uu____8686) with
| (t1, uu____8692) -> begin
(

let uu____8693 = (

let uu____8694 = (unparen t1)
in uu____8694.FStar_Parser_AST.tm)
in (match (uu____8693) with
| FStar_Parser_AST.Construct (cons1, (({FStar_Parser_AST.tm = FStar_Parser_AST.Construct (smtpat, uu____8697); FStar_Parser_AST.range = uu____8698; FStar_Parser_AST.level = uu____8699}, uu____8700))::(uu____8701)::[]) -> begin
((FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid) && (FStar_Util.for_some (fun s -> (smtpat.FStar_Ident.str = s)) (("SMTPat")::("SMTPatT")::("SMTPatOr")::[])))
end
| FStar_Parser_AST.Construct (cons1, (({FStar_Parser_AST.tm = FStar_Parser_AST.Var (smtpat); FStar_Parser_AST.range = uu____8740; FStar_Parser_AST.level = uu____8741}, uu____8742))::(uu____8743)::[]) -> begin
((FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid) && (FStar_Util.for_some (fun s -> (smtpat.FStar_Ident.str = s)) (("smt_pat")::("smt_pat_or")::[])))
end
| uu____8768 -> begin
false
end))
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t1 -> (

let uu____8796 = (head_and_args t1)
in (match (uu____8796) with
| (head1, args) -> begin
(match (head1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(

let unit_tm = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.unit_lid)) t1.FStar_Parser_AST.range FStar_Parser_AST.Type_level)), (FStar_Parser_AST.Nothing))
in (

let nil_pat = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.nil_lid)) t1.FStar_Parser_AST.range FStar_Parser_AST.Expr)), (FStar_Parser_AST.Nothing))
in (

let req_true = (

let req = FStar_Parser_AST.Requires ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.true_lid)) t1.FStar_Parser_AST.range FStar_Parser_AST.Formula)), (FStar_Pervasives_Native.None)))
in (((FStar_Parser_AST.mk_term req t1.FStar_Parser_AST.range FStar_Parser_AST.Type_level)), (FStar_Parser_AST.Nothing)))
in (

let args1 = (match (args) with
| [] -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Not enough arguments to \'Lemma\'"), (t1.FStar_Parser_AST.range)))))
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

let uu____9205 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes env) l)
in ((uu____9205), (args)))
end
| FStar_Parser_AST.Name (l) when ((

let uu____9233 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals uu____9233 FStar_Parser_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Parser_Const.effect_Tot_lid head1.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when ((

let uu____9251 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals uu____9251 FStar_Parser_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Parser_Const.effect_GTot_lid head1.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when (((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) -> begin
(((((FStar_Ident.set_lid_range FStar_Parser_Const.effect_Tot_lid head1.FStar_Parser_AST.range)), ([]))), ((((t1), (FStar_Parser_AST.Nothing)))::[]))
end
| uu____9289 -> begin
(

let default_effect = (

let uu____9291 = (FStar_Options.ml_ish ())
in (match (uu____9291) with
| true -> begin
FStar_Parser_Const.effect_ML_lid
end
| uu____9292 -> begin
((

let uu____9294 = (FStar_Options.warn_default_effects ())
in (match (uu____9294) with
| true -> begin
(FStar_Errors.warn head1.FStar_Parser_AST.range "Using default effect Tot")
end
| uu____9295 -> begin
()
end));
FStar_Parser_Const.effect_Tot_lid;
)
end))
in (((((FStar_Ident.set_lid_range default_effect head1.FStar_Parser_AST.range)), ([]))), ((((t1), (FStar_Parser_AST.Nothing)))::[])))
end)
end)))
in (

let uu____9318 = (pre_process_comp_typ t)
in (match (uu____9318) with
| ((eff, cattributes), args) -> begin
((match (((FStar_List.length args) = (Prims.parse_int "0"))) with
| true -> begin
(

let uu____9367 = (

let uu____9368 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" uu____9368))
in (fail uu____9367))
end
| uu____9369 -> begin
()
end);
(

let is_universe = (fun uu____9377 -> (match (uu____9377) with
| (uu____9382, imp) -> begin
(imp = FStar_Parser_AST.UnivApp)
end))
in (

let uu____9384 = (FStar_Util.take is_universe args)
in (match (uu____9384) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun uu____9443 -> (match (uu____9443) with
| (u, imp) -> begin
(desugar_universe u)
end)) universes)
in (

let uu____9450 = (

let uu____9465 = (FStar_List.hd args1)
in (

let uu____9474 = (FStar_List.tl args1)
in ((uu____9465), (uu____9474))))
in (match (uu____9450) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (FStar_Pervasives_Native.fst result_arg))
in (

let rest1 = (desugar_args env rest)
in (

let uu____9529 = (

let is_decrease = (fun uu____9565 -> (match (uu____9565) with
| (t1, uu____9575) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____9585; FStar_Syntax_Syntax.vars = uu____9586}, (uu____9587)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.decreases_lid)
end
| uu____9618 -> begin
false
end)
end))
in (FStar_All.pipe_right rest1 (FStar_List.partition is_decrease)))
in (match (uu____9529) with
| (dec, rest2) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun uu____9732 -> (match (uu____9732) with
| (t1, uu____9742) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____9751, ((arg, uu____9753))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| uu____9782 -> begin
(failwith "impos")
end)
end))))
in (

let no_additional_args = (

let is_empty = (fun l -> (match (l) with
| [] -> begin
true
end
| uu____9796 -> begin
false
end))
in ((((is_empty decreases_clause) && (is_empty rest2)) && (is_empty cattributes)) && (is_empty universes1)))
in (match ((no_additional_args && (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid))) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end
| uu____9809 -> begin
(match ((no_additional_args && (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid))) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end
| uu____9812 -> begin
(

let flags = (match ((FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Lemma_lid)) with
| true -> begin
(FStar_Syntax_Syntax.LEMMA)::[]
end
| uu____9818 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____9821 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Parser_Const.effect_ML_lid)) with
| true -> begin
(FStar_Syntax_Syntax.MLEFFECT)::[]
end
| uu____9824 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____9827 -> begin
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
| uu____9944 -> begin
pat
end)
in (

let uu____9945 = (

let uu____9956 = (

let uu____9967 = (

let uu____9976 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat1), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) FStar_Pervasives_Native.None pat1.FStar_Syntax_Syntax.pos)
in ((uu____9976), (aq)))
in (uu____9967)::[])
in (ens)::uu____9956)
in (req)::uu____9945))
end
| uu____10017 -> begin
rest2
end)
end
| uu____10028 -> begin
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
| uu____10039 -> begin
FStar_Pervasives_Native.None
end))
in (

let mk1 = (fun t -> (FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let uu___238_10056 = t
in {FStar_Syntax_Syntax.n = uu___238_10056.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___238_10056.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let uu___239_10090 = b
in {FStar_Parser_AST.b = uu___239_10090.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___239_10090.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___239_10090.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env1 pats1 -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (

let uu____10149 = (desugar_term env1 e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) uu____10149)))))) pats1))
in (match (tk) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____10162 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____10162) with
| (env1, a1) -> begin
(

let a2 = (

let uu___240_10172 = a1
in {FStar_Syntax_Syntax.ppname = uu___240_10172.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___240_10172.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats1 = (desugar_pats env1 pats)
in (

let body1 = (desugar_formula env1 body)
in (

let body2 = (match (pats1) with
| [] -> begin
body1
end
| uu____10194 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_meta (((body1), (FStar_Syntax_Syntax.Meta_pattern (pats1))))))
end)
in (

let body3 = (

let uu____10208 = (

let uu____10211 = (

let uu____10212 = (FStar_Syntax_Syntax.mk_binder a2)
in (uu____10212)::[])
in (no_annot_abs uu____10211 body2))
in (FStar_All.pipe_left setpos uu____10208))
in (

let uu____10217 = (

let uu____10218 = (

let uu____10233 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let uu____10234 = (

let uu____10237 = (FStar_Syntax_Syntax.as_arg body3)
in (uu____10237)::[])
in ((uu____10233), (uu____10234))))
in FStar_Syntax_Syntax.Tm_app (uu____10218))
in (FStar_All.pipe_left mk1 uu____10217)))))))
end))
end
| uu____10242 -> begin
(failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body1 = (

let uu____10314 = (q ((rest), (pats), (body)))
in (

let uu____10321 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term uu____10314 uu____10321 FStar_Parser_AST.Formula)))
in (

let uu____10322 = (q (((b)::[]), ([]), (body1)))
in (FStar_Parser_AST.mk_term uu____10322 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| uu____10331 -> begin
(failwith "impossible")
end))
in (

let uu____10334 = (

let uu____10335 = (unparen f)
in uu____10335.FStar_Parser_AST.tm)
in (match (uu____10334) with
| FStar_Parser_AST.Labeled (f1, l, p) -> begin
(

let f2 = (desugar_formula env f1)
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((f2), (FStar_Syntax_Syntax.Meta_labeled (((l), (f2.FStar_Syntax_Syntax.pos), (p)))))))))
end
| FStar_Parser_AST.QForall ([], uu____10342, uu____10343) -> begin
(failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QExists ([], uu____10354, uu____10355) -> begin
(failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____10386 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env uu____10386)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____10422 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env uu____10422)))
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
| uu____10465 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_ToSyntax_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list) = (fun env bs -> (

let uu____10470 = (FStar_List.fold_left (fun uu____10506 b -> (match (uu____10506) with
| (env1, out) -> begin
(

let tk = (desugar_binder env1 (

let uu___241_10558 = b
in {FStar_Parser_AST.b = uu___241_10558.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___241_10558.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___241_10558.FStar_Parser_AST.aqual}))
in (match (tk) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____10575 = (FStar_ToSyntax_Env.push_bv env1 a)
in (match (uu____10575) with
| (env2, a1) -> begin
(

let a2 = (

let uu___242_10595 = a1
in {FStar_Syntax_Syntax.ppname = uu___242_10595.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___242_10595.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in ((env2), ((((a2), ((trans_aqual b.FStar_Parser_AST.aqual))))::out)))
end))
end
| uu____10612 -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (uu____10470) with
| (env1, tpars) -> begin
((env1), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.TAnnotated (x, t) -> begin
(

let uu____10699 = (desugar_typ env t)
in ((FStar_Pervasives_Native.Some (x)), (uu____10699)))
end
| FStar_Parser_AST.Annotated (x, t) -> begin
(

let uu____10704 = (desugar_typ env t)
in ((FStar_Pervasives_Native.Some (x)), (uu____10704)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____10708 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) FStar_Pervasives_Native.None x.FStar_Ident.idRange)
in ((FStar_Pervasives_Native.Some (x)), (uu____10708)))
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____10716 = (desugar_typ env t)
in ((FStar_Pervasives_Native.None), (uu____10716)))
end
| FStar_Parser_AST.Variable (x) -> begin
((FStar_Pervasives_Native.Some (x)), (FStar_Syntax_Syntax.tun))
end))


let mk_data_discriminators : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_ToSyntax_Env.env  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun quals env datas -> (

let quals1 = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___212_10752 -> (match (uu___212_10752) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____10753 -> begin
false
end))))
in (

let quals2 = (fun q -> (

let uu____10764 = ((

let uu____10767 = (FStar_ToSyntax_Env.iface env)
in (not (uu____10767))) || (FStar_ToSyntax_Env.admitted_iface env))
in (match (uu____10764) with
| true -> begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals1)
end
| uu____10770 -> begin
(FStar_List.append q quals1)
end)))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (

let uu____10780 = (quals2 ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((disc_name), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid disc_name); FStar_Syntax_Syntax.sigquals = uu____10780; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))))))))


let mk_indexed_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  FStar_ToSyntax_Env.env  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq env lid fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let uu____10816 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____10846 -> (match (uu____10846) with
| (x, uu____10854) -> begin
(

let uu____10855 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____10855) with
| (field_name, uu____10863) -> begin
(

let only_decl = (((

let uu____10867 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____10867)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (

let uu____10869 = (

let uu____10870 = (FStar_ToSyntax_Env.current_module env)
in uu____10870.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____10869)))
in (

let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____10884 = (FStar_List.filter (fun uu___213_10888 -> (match (uu___213_10888) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____10889 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____10884)
end
| uu____10890 -> begin
q
end))
in (

let quals1 = (

let iquals1 = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___214_10902 -> (match (uu___214_10902) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____10903 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals1)))
in (

let decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid field_name); FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____10909 -> begin
(

let dd = (

let uu____10911 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____10911) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____10914 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lb = (

let uu____10916 = (

let uu____10921 = (FStar_Syntax_Syntax.lid_as_fv field_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____10921))
in {FStar_Syntax_Syntax.lbname = uu____10916; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = FStar_Syntax_Syntax.tun})
in (

let impl = (

let uu____10923 = (

let uu____10924 = (

let uu____10931 = (

let uu____10934 = (

let uu____10935 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____10935 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____10934)::[])
in ((((false), ((lb)::[]))), (uu____10931)))
in FStar_Syntax_Syntax.Sig_let (uu____10924))
in {FStar_Syntax_Syntax.sigel = uu____10923; FStar_Syntax_Syntax.sigrng = p; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____10954 -> begin
(decl)::(impl)::[]
end))))
end))))))
end))
end))))
in (FStar_All.pipe_right uu____10816 FStar_List.flatten))))


let mk_data_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_ToSyntax_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____10982, t, uu____10984, n1, uu____10986) when (not ((FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid))) -> begin
(

let uu____10991 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____10991) with
| (formals, uu____11007) -> begin
(match (formals) with
| [] -> begin
[]
end
| uu____11030 -> begin
(

let filter_records = (fun uu___215_11042 -> (match (uu___215_11042) with
| FStar_Syntax_Syntax.RecordConstructor (uu____11045, fns) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| uu____11057 -> begin
FStar_Pervasives_Native.None
end))
in (

let fv_qual = (

let uu____11059 = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals filter_records)
in (match (uu____11059) with
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
| uu____11068 -> begin
iquals
end)
in (

let uu____11069 = (FStar_Util.first_N n1 formals)
in (match (uu____11069) with
| (uu____11092, rest) -> begin
(mk_indexed_projector_names iquals1 fv_qual env lid rest)
end)))))
end)
end))
end
| uu____11118 -> begin
[]
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (

let dd = (

let uu____11176 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____11176) with
| true -> begin
(

let uu____11179 = (FStar_Syntax_Util.incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (uu____11179))
end
| uu____11180 -> begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end))
in (

let lb = (

let uu____11182 = (

let uu____11187 = (FStar_Syntax_Syntax.lid_as_fv lid dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____11187))
in (

let uu____11188 = (

let uu____11191 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars uu____11191))
in (

let uu____11194 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = uu____11182; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____11188; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____11194})))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (lids))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))


let rec desugar_tycon : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d quals tcs -> (

let rng = d.FStar_Parser_AST.drange
in (

let tycon_id = (fun uu___216_11243 -> (match (uu___216_11243) with
| FStar_Parser_AST.TyconAbstract (id, uu____11245, uu____11246) -> begin
id
end
| FStar_Parser_AST.TyconAbbrev (id, uu____11256, uu____11257, uu____11258) -> begin
id
end
| FStar_Parser_AST.TyconRecord (id, uu____11268, uu____11269, uu____11270) -> begin
id
end
| FStar_Parser_AST.TyconVariant (id, uu____11300, uu____11301, uu____11302) -> begin
id
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (x, uu____11344) -> begin
(

let uu____11345 = (

let uu____11346 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____11346))
in (FStar_Parser_AST.mk_term uu____11345 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| FStar_Parser_AST.Variable (x) -> begin
(

let uu____11348 = (

let uu____11349 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____11349))
in (FStar_Parser_AST.mk_term uu____11348 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| FStar_Parser_AST.TAnnotated (a, uu____11351) -> begin
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
| uu____11374 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (

let uu____11380 = (

let uu____11381 = (

let uu____11388 = (binder_to_term b)
in ((out), (uu____11388), ((imp_of_aqual b))))
in FStar_Parser_AST.App (uu____11381))
in (FStar_Parser_AST.mk_term uu____11380 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun uu___217_11398 -> (match (uu___217_11398) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun uu____11453 -> (match (uu____11453) with
| (x, t, uu____11464) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Syntax_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr FStar_Pervasives_Native.None)
end)) fields)
in (

let result = (

let uu____11470 = (

let uu____11471 = (

let uu____11472 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (uu____11472))
in (FStar_Parser_AST.mk_term uu____11471 id.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____11470 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type_level)
in (

let uu____11476 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____11503 -> (match (uu____11503) with
| (x, uu____11513, uu____11514) -> begin
(FStar_Syntax_Util.unmangle_field_name x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (FStar_Pervasives_Native.Some (constrTyp)), (FStar_Pervasives_Native.None), (false)))::[])))), (uu____11476)))))))
end
| uu____11567 -> begin
(failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals1 _env mutuals uu___218_11598 -> (match (uu___218_11598) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let uu____11622 = (typars_of_binders _env binders)
in (match (uu____11622) with
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

let uu____11668 = (

let uu____11669 = (

let uu____11670 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (uu____11670))
in (FStar_Parser_AST.mk_term uu____11669 id.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____11668 binders))
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
| uu____11683 -> begin
(failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env1 bs -> (

let uu____11727 = (FStar_List.fold_left (fun uu____11767 uu____11768 -> (match (((uu____11767), (uu____11768))) with
| ((env2, tps), (x, imp)) -> begin
(

let uu____11859 = (FStar_ToSyntax_Env.push_bv env2 x.FStar_Syntax_Syntax.ppname)
in (match (uu____11859) with
| (env3, y) -> begin
((env3), ((((y), (imp)))::tps))
end))
end)) ((env1), ([])) bs)
in (match (uu____11727) with
| (env2, bs1) -> begin
((env2), ((FStar_List.rev bs1)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id, bs, kopt))::[] -> begin
(

let kopt1 = (match (kopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____11972 = (tm_type_z id.FStar_Ident.idRange)
in FStar_Pervasives_Native.Some (uu____11972))
end
| uu____11973 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id), (bs), (kopt1)))
in (

let uu____11981 = (desugar_abstract_tc quals env [] tc)
in (match (uu____11981) with
| (uu____11994, uu____11995, se, uu____11997) -> begin
(

let se1 = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, uu____12000, typars, k, [], []) -> begin
(

let quals1 = se.FStar_Syntax_Syntax.sigquals
in (

let quals2 = (

let uu____12013 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Assumption))
in (match (uu____12013) with
| true -> begin
quals1
end
| uu____12018 -> begin
((

let uu____12020 = (FStar_Range.string_of_range se.FStar_Syntax_Syntax.sigrng)
in (

let uu____12021 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" uu____12020 uu____12021)));
(FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals1;
)
end))
in (

let t = (match (typars) with
| [] -> begin
k
end
| uu____12027 -> begin
(

let uu____12028 = (

let uu____12031 = (

let uu____12032 = (

let uu____12045 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (uu____12045)))
in FStar_Syntax_Syntax.Tm_arrow (uu____12032))
in (FStar_Syntax_Syntax.mk uu____12031))
in (uu____12028 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
end)
in (

let uu___243_12049 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t))); FStar_Syntax_Syntax.sigrng = uu___243_12049.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = uu___243_12049.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___243_12049.FStar_Syntax_Syntax.sigattrs}))))
end
| uu____12052 -> begin
(failwith "Impossible")
end)
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env se1)
in (

let env2 = (

let uu____12055 = (FStar_ToSyntax_Env.qualify env1 id)
in (FStar_ToSyntax_Env.push_doc env1 uu____12055 d.FStar_Parser_AST.doc))
in ((env2), ((se1)::[])))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let uu____12070 = (typars_of_binders env binders)
in (match (uu____12070) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____12106 = (FStar_Util.for_some (fun uu___219_12108 -> (match (uu___219_12108) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| uu____12109 -> begin
false
end)) quals)
in (match (uu____12106) with
| true -> begin
FStar_Syntax_Syntax.teff
end
| uu____12110 -> begin
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

let uu____12116 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___220_12120 -> (match (uu___220_12120) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| uu____12121 -> begin
false
end))))
in (match (uu____12116) with
| true -> begin
quals
end
| uu____12124 -> begin
(match ((t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula)) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals
end
| uu____12127 -> begin
quals
end)
end))
in (

let qlid = (FStar_ToSyntax_Env.qualify env id)
in (

let se = (

let uu____12130 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Effect))
in (match (uu____12130) with
| true -> begin
(

let uu____12133 = (

let uu____12140 = (

let uu____12141 = (unparen t)
in uu____12141.FStar_Parser_AST.tm)
in (match (uu____12140) with
| FStar_Parser_AST.Construct (head1, args) -> begin
(

let uu____12162 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____12192))::args_rev -> begin
(

let uu____12204 = (

let uu____12205 = (unparen last_arg)
in uu____12205.FStar_Parser_AST.tm)
in (match (uu____12204) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____12233 -> begin
(([]), (args))
end))
end
| uu____12242 -> begin
(([]), (args))
end)
in (match (uu____12162) with
| (cattributes, args1) -> begin
(

let uu____12281 = (desugar_attributes env cattributes)
in (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((head1), (args1)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (uu____12281)))
end))
end
| uu____12292 -> begin
((t), ([]))
end))
in (match (uu____12133) with
| (t1, cattributes) -> begin
(

let c = (desugar_comp t1.FStar_Parser_AST.range env' t1)
in (

let typars1 = (FStar_Syntax_Subst.close_binders typars)
in (

let c1 = (FStar_Syntax_Subst.close_comp typars1 c)
in (

let quals2 = (FStar_All.pipe_right quals1 (FStar_List.filter (fun uu___221_12314 -> (match (uu___221_12314) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| uu____12315 -> begin
true
end))))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((qlid), ([]), (typars1), (c1), ((FStar_List.append cattributes (FStar_Syntax_Util.comp_flags c1))))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))))
end))
end
| uu____12320 -> begin
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
| (FStar_Parser_AST.TyconRecord (uu____12326))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let uu____12350 = (tycon_record_as_variant trec)
in (match (uu____12350) with
| (t, fs) -> begin
(

let uu____12367 = (

let uu____12370 = (

let uu____12371 = (

let uu____12380 = (

let uu____12383 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.ids_of_lid uu____12383))
in ((uu____12380), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____12371))
in (uu____12370)::quals)
in (desugar_tycon env d uu____12367 ((t)::[])))
end)))
end
| (uu____12388)::uu____12389 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals1 et tc -> (

let uu____12550 = et
in (match (uu____12550) with
| (env1, tcs1) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (uu____12775) -> begin
(

let trec = tc
in (

let uu____12799 = (tycon_record_as_variant trec)
in (match (uu____12799) with
| (t, fs) -> begin
(

let uu____12858 = (

let uu____12861 = (

let uu____12862 = (

let uu____12871 = (

let uu____12874 = (FStar_ToSyntax_Env.current_module env1)
in (FStar_Ident.ids_of_lid uu____12874))
in ((uu____12871), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____12862))
in (uu____12861)::quals1)
in (collect_tcs uu____12858 ((env1), (tcs1)) t))
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let uu____12961 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (uu____12961) with
| (env2, uu____13021, se, tconstr) -> begin
((env2), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals1))))::tcs1))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let uu____13170 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (uu____13170) with
| (env2, uu____13230, se, tconstr) -> begin
((env2), ((FStar_Util.Inr (((se), (binders), (t), (quals1))))::tcs1))
end))
end
| uu____13355 -> begin
(failwith "Unrecognized mutual type definition")
end)
end)))
in (

let uu____13402 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (uu____13402) with
| (env1, tcs1) -> begin
(

let tcs2 = (FStar_List.rev tcs1)
in (

let docs_tps_sigelts = (FStar_All.pipe_right tcs2 (FStar_List.collect (fun uu___223_13913 -> (match (uu___223_13913) with
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, uu____13980, uu____13981); FStar_Syntax_Syntax.sigrng = uu____13982; FStar_Syntax_Syntax.sigquals = uu____13983; FStar_Syntax_Syntax.sigmeta = uu____13984; FStar_Syntax_Syntax.sigattrs = uu____13985}, binders, t, quals1) -> begin
(

let t1 = (

let uu____14046 = (typars_of_binders env1 binders)
in (match (uu____14046) with
| (env2, tpars1) -> begin
(

let uu____14077 = (push_tparams env2 tpars1)
in (match (uu____14077) with
| (env_tps, tpars2) -> begin
(

let t1 = (desugar_typ env_tps t)
in (

let tpars3 = (FStar_Syntax_Subst.close_binders tpars2)
in (FStar_Syntax_Subst.close tpars3 t1)))
end))
end))
in (

let uu____14110 = (

let uu____14131 = (mk_typ_abbrev id uvs tpars k t1 ((id)::[]) quals1 rng)
in ((((id), (d.FStar_Parser_AST.doc))), ([]), (uu____14131)))
in (uu____14110)::[]))
end
| FStar_Util.Inl ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs1, tpars, k, mutuals1, uu____14199); FStar_Syntax_Syntax.sigrng = uu____14200; FStar_Syntax_Syntax.sigquals = tname_quals; FStar_Syntax_Syntax.sigmeta = uu____14202; FStar_Syntax_Syntax.sigattrs = uu____14203}, constrs, tconstr, quals1) -> begin
(

let mk_tot = (fun t -> (

let tot1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((tot1), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)))
in (

let tycon = ((tname), (tpars), (k))
in (

let uu____14299 = (push_tparams env1 tpars)
in (match (uu____14299) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun uu____14376 -> (match (uu____14376) with
| (x, uu____14390) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let tot_tconstr = (mk_tot tconstr)
in (

let uu____14398 = (

let uu____14427 = (FStar_All.pipe_right constrs (FStar_List.map (fun uu____14541 -> (match (uu____14541) with
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
| uu____14594 -> begin
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

let uu____14597 = (close env_tps t)
in (desugar_term env_tps uu____14597))
in (

let name = (FStar_ToSyntax_Env.qualify env1 id)
in (

let quals2 = (FStar_All.pipe_right tname_quals (FStar_List.collect (fun uu___222_14608 -> (match (uu___222_14608) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| uu____14620 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (

let uu____14628 = (

let uu____14649 = (

let uu____14650 = (

let uu____14651 = (

let uu____14666 = (

let uu____14669 = (

let uu____14672 = (FStar_All.pipe_right t1 FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total uu____14672))
in (FStar_Syntax_Util.arrow data_tpars uu____14669))
in ((name), (univs1), (uu____14666), (tname), (ntps), (mutuals1)))
in FStar_Syntax_Syntax.Sig_datacon (uu____14651))
in {FStar_Syntax_Syntax.sigel = uu____14650; FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in ((((name), (doc1))), (tps), (uu____14649)))
in ((name), (uu____14628))))))))
end))))
in (FStar_All.pipe_left FStar_List.split uu____14427))
in (match (uu____14398) with
| (constrNames, constrs1) -> begin
(((((tname), (d.FStar_Parser_AST.doc))), ([]), ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs1), (tpars), (k), (mutuals1), (constrNames))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = tname_quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))::constrs1
end))))
end))))
end
| uu____14911 -> begin
(failwith "impossible")
end))))
in (

let name_docs = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.map (fun uu____15043 -> (match (uu____15043) with
| (name_doc, uu____15071, uu____15072) -> begin
name_doc
end))))
in (

let sigelts = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.map (fun uu____15152 -> (match (uu____15152) with
| (uu____15173, uu____15174, se) -> begin
se
end))))
in (

let uu____15204 = (

let uu____15211 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle sigelts quals uu____15211 rng))
in (match (uu____15204) with
| (bundle, abbrevs) -> begin
(

let env2 = (FStar_ToSyntax_Env.push_sigelt env0 bundle)
in (

let env3 = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2 abbrevs)
in (

let data_ops = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.collect (fun uu____15277 -> (match (uu____15277) with
| (uu____15300, tps, se) -> begin
(mk_data_projector_names quals env3 se)
end))))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, uu____15351, tps, k, uu____15354, constrs) when ((FStar_List.length constrs) > (Prims.parse_int "1")) -> begin
(

let quals1 = se.FStar_Syntax_Syntax.sigquals
in (

let quals2 = (match ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals1)) with
| true -> begin
(FStar_Syntax_Syntax.Private)::quals1
end
| uu____15372 -> begin
quals1
end)
in (mk_data_discriminators quals2 env3 constrs)))
end
| uu____15373 -> begin
[]
end))))
in (

let ops = (FStar_List.append discs data_ops)
in (

let env4 = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env3 ops)
in (

let env5 = (FStar_List.fold_left (fun acc uu____15390 -> (match (uu____15390) with
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

let uu____15427 = (FStar_List.fold_left (fun uu____15450 b -> (match (uu____15450) with
| (env1, binders1) -> begin
(

let uu____15470 = (desugar_binder env1 b)
in (match (uu____15470) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____15487 = (as_binder env1 b.FStar_Parser_AST.aqual ((FStar_Pervasives_Native.Some (a)), (k)))
in (match (uu____15487) with
| (binder, env2) -> begin
((env2), ((binder)::binders1))
end))
end
| uu____15504 -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) binders)
in (match (uu____15427) with
| (env1, binders1) -> begin
((env1), ((FStar_List.rev binders1)))
end)))


let rec desugar_effect : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_typ eff_decls -> (

let env0 = env
in (

let monad_env = (FStar_ToSyntax_Env.enter_monad_scope env eff_name)
in (

let uu____15618 = (desugar_binders monad_env eff_binders)
in (match (uu____15618) with
| (env1, binders) -> begin
(

let eff_t = (desugar_term env1 eff_typ)
in (

let for_free = (

let uu____15639 = (

let uu____15640 = (

let uu____15647 = (FStar_Syntax_Util.arrow_formals eff_t)
in (FStar_Pervasives_Native.fst uu____15647))
in (FStar_List.length uu____15640))
in (uu____15639 = (Prims.parse_int "1")))
in (

let mandatory_members = (

let rr_members = ("repr")::("return")::("bind")::[]
in (match (for_free) with
| true -> begin
rr_members
end
| uu____15684 -> begin
(FStar_List.append rr_members (("return_wp")::("bind_wp")::("if_then_else")::("ite_wp")::("stronger")::("close_wp")::("assert_p")::("assume_p")::("null_wp")::("trivial")::[]))
end))
in (

let name_of_eff_decl = (fun decl -> (match (decl.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____15689, ((FStar_Parser_AST.TyconAbbrev (name, uu____15691, uu____15692, uu____15693), uu____15694))::[]) -> begin
(FStar_Ident.text_of_id name)
end
| uu____15727 -> begin
(failwith "Malformed effect member declaration.")
end))
in (

let uu____15728 = (FStar_List.partition (fun decl -> (

let uu____15740 = (name_of_eff_decl decl)
in (FStar_List.mem uu____15740 mandatory_members))) eff_decls)
in (match (uu____15728) with
| (mandatory_members_decls, actions) -> begin
(

let uu____15757 = (FStar_All.pipe_right mandatory_members_decls (FStar_List.fold_left (fun uu____15786 decl -> (match (uu____15786) with
| (env2, out) -> begin
(

let uu____15806 = (desugar_decl env2 decl)
in (match (uu____15806) with
| (env3, ses) -> begin
(

let uu____15819 = (

let uu____15822 = (FStar_List.hd ses)
in (uu____15822)::out)
in ((env3), (uu____15819)))
end))
end)) ((env1), ([]))))
in (match (uu____15757) with
| (env2, decls) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (

let actions_docs = (FStar_All.pipe_right actions (FStar_List.map (fun d1 -> (match (d1.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____15890, ((FStar_Parser_AST.TyconAbbrev (name, action_params, uu____15893, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (uu____15894, ((def, uu____15896))::((cps_type, uu____15898))::[]); FStar_Parser_AST.range = uu____15899; FStar_Parser_AST.level = uu____15900}), doc1))::[]) when (not (for_free)) -> begin
(

let uu____15952 = (desugar_binders env2 action_params)
in (match (uu____15952) with
| (env3, action_params1) -> begin
(

let action_params2 = (FStar_Syntax_Subst.close_binders action_params1)
in (

let uu____15972 = (

let uu____15973 = (FStar_ToSyntax_Env.qualify env3 name)
in (

let uu____15974 = (

let uu____15975 = (desugar_term env3 def)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____15975))
in (

let uu____15980 = (

let uu____15981 = (desugar_typ env3 cps_type)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____15981))
in {FStar_Syntax_Syntax.action_name = uu____15973; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = action_params2; FStar_Syntax_Syntax.action_defn = uu____15974; FStar_Syntax_Syntax.action_typ = uu____15980})))
in ((uu____15972), (doc1))))
end))
end
| FStar_Parser_AST.Tycon (uu____15988, ((FStar_Parser_AST.TyconAbbrev (name, action_params, uu____15991, defn), doc1))::[]) when for_free -> begin
(

let uu____16026 = (desugar_binders env2 action_params)
in (match (uu____16026) with
| (env3, action_params1) -> begin
(

let action_params2 = (FStar_Syntax_Subst.close_binders action_params1)
in (

let uu____16046 = (

let uu____16047 = (FStar_ToSyntax_Env.qualify env3 name)
in (

let uu____16048 = (

let uu____16049 = (desugar_term env3 defn)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____16049))
in {FStar_Syntax_Syntax.action_name = uu____16047; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = action_params2; FStar_Syntax_Syntax.action_defn = uu____16048; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
in ((uu____16046), (doc1))))
end))
end
| uu____16056 -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples)."), (d1.FStar_Parser_AST.drange)))))
end))))
in (

let actions1 = (FStar_List.map FStar_Pervasives_Native.fst actions_docs)
in (

let eff_t1 = (FStar_Syntax_Subst.close binders1 eff_t)
in (

let lookup = (fun s -> (

let l = (FStar_ToSyntax_Env.qualify env2 (FStar_Ident.mk_ident ((s), (d.FStar_Parser_AST.drange))))
in (

let uu____16086 = (

let uu____16087 = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_definition env2) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders1) uu____16087))
in (([]), (uu____16086)))))
in (

let mname = (FStar_ToSyntax_Env.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange (FStar_Pervasives_Native.Some (mname))) quals)
in (

let se = (match (for_free) with
| true -> begin
(

let dummy_tscheme = (

let uu____16104 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (([]), (uu____16104)))
in (

let uu____16111 = (

let uu____16112 = (

let uu____16113 = (

let uu____16114 = (lookup "repr")
in (FStar_Pervasives_Native.snd uu____16114))
in (

let uu____16123 = (lookup "return")
in (

let uu____16124 = (lookup "bind")
in {FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = eff_t1; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = uu____16113; FStar_Syntax_Syntax.return_repr = uu____16123; FStar_Syntax_Syntax.bind_repr = uu____16124; FStar_Syntax_Syntax.actions = actions1})))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____16112))
in {FStar_Syntax_Syntax.sigel = uu____16111; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qualifiers; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))
end
| uu____16125 -> begin
(

let rr = (FStar_Util.for_some (fun uu___224_16128 -> (match (uu___224_16128) with
| FStar_Syntax_Syntax.Reifiable -> begin
true
end
| FStar_Syntax_Syntax.Reflectable (uu____16129) -> begin
true
end
| uu____16130 -> begin
false
end)) qualifiers)
in (

let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in (

let uu____16140 = (

let uu____16141 = (

let uu____16142 = (lookup "return_wp")
in (

let uu____16143 = (lookup "bind_wp")
in (

let uu____16144 = (lookup "if_then_else")
in (

let uu____16145 = (lookup "ite_wp")
in (

let uu____16146 = (lookup "stronger")
in (

let uu____16147 = (lookup "close_wp")
in (

let uu____16148 = (lookup "assert_p")
in (

let uu____16149 = (lookup "assume_p")
in (

let uu____16150 = (lookup "null_wp")
in (

let uu____16151 = (lookup "trivial")
in (

let uu____16152 = (match (rr) with
| true -> begin
(

let uu____16153 = (lookup "repr")
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____16153))
end
| uu____16168 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let uu____16169 = (match (rr) with
| true -> begin
(lookup "return")
end
| uu____16170 -> begin
un_ts
end)
in (

let uu____16171 = (match (rr) with
| true -> begin
(lookup "bind")
end
| uu____16172 -> begin
un_ts
end)
in {FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = eff_t1; FStar_Syntax_Syntax.ret_wp = uu____16142; FStar_Syntax_Syntax.bind_wp = uu____16143; FStar_Syntax_Syntax.if_then_else = uu____16144; FStar_Syntax_Syntax.ite_wp = uu____16145; FStar_Syntax_Syntax.stronger = uu____16146; FStar_Syntax_Syntax.close_wp = uu____16147; FStar_Syntax_Syntax.assert_p = uu____16148; FStar_Syntax_Syntax.assume_p = uu____16149; FStar_Syntax_Syntax.null_wp = uu____16150; FStar_Syntax_Syntax.trivial = uu____16151; FStar_Syntax_Syntax.repr = uu____16152; FStar_Syntax_Syntax.return_repr = uu____16169; FStar_Syntax_Syntax.bind_repr = uu____16171; FStar_Syntax_Syntax.actions = actions1})))))))))))))
in FStar_Syntax_Syntax.Sig_new_effect (uu____16141))
in {FStar_Syntax_Syntax.sigel = uu____16140; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qualifiers; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))
end)
in (

let env3 = (FStar_ToSyntax_Env.push_sigelt env0 se)
in (

let env4 = (FStar_ToSyntax_Env.push_doc env3 mname d.FStar_Parser_AST.doc)
in (

let env5 = (FStar_All.pipe_right actions_docs (FStar_List.fold_left (fun env5 uu____16196 -> (match (uu____16196) with
| (a, doc1) -> begin
(

let env6 = (

let uu____16210 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_ToSyntax_Env.push_sigelt env5 uu____16210))
in (FStar_ToSyntax_Env.push_doc env6 a.FStar_Syntax_Syntax.action_name doc1))
end)) env4))
in (

let env6 = (

let uu____16212 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____16212) with
| true -> begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_ToSyntax_Env.qualify monad_env))
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]
in (

let refl_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (FStar_ToSyntax_Env.push_sigelt env5 refl_decl))))
end
| uu____16220 -> begin
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

let uu____16243 = (desugar_binders env1 eff_binders)
in (match (uu____16243) with
| (env2, binders) -> begin
(

let uu____16262 = (

let uu____16281 = (head_and_args defn)
in (match (uu____16281) with
| (head1, args) -> begin
(

let lid = (match (head1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
l
end
| uu____16326 -> begin
(

let uu____16327 = (

let uu____16328 = (

let uu____16333 = (

let uu____16334 = (

let uu____16335 = (FStar_Parser_AST.term_to_string head1)
in (Prims.strcat uu____16335 " not found"))
in (Prims.strcat "Effect " uu____16334))
in ((uu____16333), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____16328))
in (FStar_Pervasives.raise uu____16327))
end)
in (

let ed = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_effect_defn env2) lid)
in (

let uu____16337 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____16367))::args_rev -> begin
(

let uu____16379 = (

let uu____16380 = (unparen last_arg)
in uu____16380.FStar_Parser_AST.tm)
in (match (uu____16379) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____16408 -> begin
(([]), (args))
end))
end
| uu____16417 -> begin
(([]), (args))
end)
in (match (uu____16337) with
| (cattributes, args1) -> begin
(

let uu____16468 = (desugar_args env2 args1)
in (

let uu____16477 = (desugar_attributes env2 cattributes)
in ((lid), (ed), (uu____16468), (uu____16477))))
end))))
end))
in (match (uu____16262) with
| (ed_lid, ed, args, cattributes) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (

let sub1 = (fun uu____16536 -> (match (uu____16536) with
| (uu____16549, x) -> begin
(

let uu____16555 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (uu____16555) with
| (edb, x1) -> begin
((match (((FStar_List.length args) <> (FStar_List.length edb))) with
| true -> begin
(FStar_Pervasives.raise (FStar_Errors.Error ((("Unexpected number of arguments to effect constructor"), (defn.FStar_Parser_AST.range)))))
end
| uu____16579 -> begin
()
end);
(

let s = (FStar_Syntax_Util.subst_of_list edb args)
in (

let uu____16581 = (

let uu____16582 = (FStar_Syntax_Subst.subst s x1)
in (FStar_Syntax_Subst.close binders1 uu____16582))
in (([]), (uu____16581))));
)
end))
end))
in (

let mname = (FStar_ToSyntax_Env.qualify env0 eff_name)
in (

let ed1 = (

let uu____16587 = (

let uu____16588 = (sub1 (([]), (ed.FStar_Syntax_Syntax.signature)))
in (FStar_Pervasives_Native.snd uu____16588))
in (

let uu____16599 = (sub1 ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____16600 = (sub1 ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____16601 = (sub1 ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____16602 = (sub1 ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____16603 = (sub1 ed.FStar_Syntax_Syntax.stronger)
in (

let uu____16604 = (sub1 ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____16605 = (sub1 ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____16606 = (sub1 ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____16607 = (sub1 ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____16608 = (sub1 ed.FStar_Syntax_Syntax.trivial)
in (

let uu____16609 = (

let uu____16610 = (sub1 (([]), (ed.FStar_Syntax_Syntax.repr)))
in (FStar_Pervasives_Native.snd uu____16610))
in (

let uu____16621 = (sub1 ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____16622 = (sub1 ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____16623 = (FStar_List.map (fun action -> (

let uu____16631 = (FStar_ToSyntax_Env.qualify env2 action.FStar_Syntax_Syntax.action_unqualified_name)
in (

let uu____16632 = (

let uu____16633 = (sub1 (([]), (action.FStar_Syntax_Syntax.action_defn)))
in (FStar_Pervasives_Native.snd uu____16633))
in (

let uu____16644 = (

let uu____16645 = (sub1 (([]), (action.FStar_Syntax_Syntax.action_typ)))
in (FStar_Pervasives_Native.snd uu____16645))
in {FStar_Syntax_Syntax.action_name = uu____16631; FStar_Syntax_Syntax.action_unqualified_name = action.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = action.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = uu____16632; FStar_Syntax_Syntax.action_typ = uu____16644})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = cattributes; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = uu____16587; FStar_Syntax_Syntax.ret_wp = uu____16599; FStar_Syntax_Syntax.bind_wp = uu____16600; FStar_Syntax_Syntax.if_then_else = uu____16601; FStar_Syntax_Syntax.ite_wp = uu____16602; FStar_Syntax_Syntax.stronger = uu____16603; FStar_Syntax_Syntax.close_wp = uu____16604; FStar_Syntax_Syntax.assert_p = uu____16605; FStar_Syntax_Syntax.assume_p = uu____16606; FStar_Syntax_Syntax.null_wp = uu____16607; FStar_Syntax_Syntax.trivial = uu____16608; FStar_Syntax_Syntax.repr = uu____16609; FStar_Syntax_Syntax.return_repr = uu____16621; FStar_Syntax_Syntax.bind_repr = uu____16622; FStar_Syntax_Syntax.actions = uu____16623})))))))))))))))
in (

let se = (

let for_free = (

let uu____16658 = (

let uu____16659 = (

let uu____16666 = (FStar_Syntax_Util.arrow_formals ed1.FStar_Syntax_Syntax.signature)
in (FStar_Pervasives_Native.fst uu____16666))
in (FStar_List.length uu____16659))
in (uu____16658 = (Prims.parse_int "1")))
in (

let uu____16695 = (

let uu____16698 = (trans_qual1 (FStar_Pervasives_Native.Some (mname)))
in (FStar_List.map uu____16698 quals))
in {FStar_Syntax_Syntax.sigel = (match (for_free) with
| true -> begin
FStar_Syntax_Syntax.Sig_new_effect_for_free (ed1)
end
| uu____16701 -> begin
FStar_Syntax_Syntax.Sig_new_effect (ed1)
end); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = uu____16695; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))
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

let uu____16718 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_ToSyntax_Env.push_sigelt env5 uu____16718))
in (FStar_ToSyntax_Env.push_doc env6 a.FStar_Syntax_Syntax.action_name doc1)))) env4))
in (

let env6 = (

let uu____16720 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____16720) with
| true -> begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_ToSyntax_Env.qualify monad_env))
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]
in (

let refl_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (FStar_ToSyntax_Env.push_sigelt env5 refl_decl))))
end
| uu____16730 -> begin
env5
end))
in (

let env7 = (FStar_ToSyntax_Env.push_doc env6 mname d.FStar_Parser_AST.doc)
in ((env7), ((se)::[])))))))))))))
end))
end)))))
and desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (

let uu____16740 = (desugar_decl_noattrs env d)
in (match (uu____16740) with
| (env1, sigelts) -> begin
(

let attrs = d.FStar_Parser_AST.attrs
in (

let attrs1 = (FStar_List.map (desugar_term env1) attrs)
in ((FStar_List.iter (fun a -> (

let uu____16759 = (FStar_Syntax_Print.term_to_string a)
in (FStar_Util.print1 "Desugared attribute: %s\n" uu____16759))) attrs1);
(

let uu____16760 = (FStar_List.map (fun sigelt -> (

let uu___244_16766 = sigelt
in {FStar_Syntax_Syntax.sigel = uu___244_16766.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___244_16766.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___244_16766.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___244_16766.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = attrs1})) sigelts)
in ((env1), (uu____16760)));
)))
end)))
and desugar_decl_noattrs : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (

let trans_qual1 = (trans_qual d.FStar_Parser_AST.drange)
in (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_pragma ((trans_pragma p)); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in ((match ((p = FStar_Parser_AST.LightOff)) with
| true -> begin
(FStar_Options.set_ml_ish ())
end
| uu____16789 -> begin
()
end);
((env), ((se)::[]));
))
end
| FStar_Parser_AST.Fsdoc (uu____16792) -> begin
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

let uu____16808 = (FStar_ToSyntax_Env.push_module_abbrev env x l)
in ((uu____16808), ([])))
end
| FStar_Parser_AST.Tycon (is_effect, tcs) -> begin
(

let quals = (match (is_effect) with
| true -> begin
(FStar_Parser_AST.Effect_qual)::d.FStar_Parser_AST.quals
end
| uu____16834 -> begin
d.FStar_Parser_AST.quals
end)
in (

let tcs1 = (FStar_List.map (fun uu____16847 -> (match (uu____16847) with
| (x, uu____16855) -> begin
x
end)) tcs)
in (

let uu____16860 = (FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals)
in (desugar_tycon env d uu____16860 tcs1))))
end
| FStar_Parser_AST.TopLevelLet (isrec, lets) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let expand_toplevel_pattern = ((isrec = FStar_Parser_AST.NoLetQualifier) && (match (lets) with
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatOp (uu____16882); FStar_Parser_AST.prange = uu____16883}, uu____16884))::[] -> begin
false
end
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____16893); FStar_Parser_AST.prange = uu____16894}, uu____16895))::[] -> begin
false
end
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____16910); FStar_Parser_AST.prange = uu____16911}, uu____16912); FStar_Parser_AST.prange = uu____16913}, uu____16914))::[] -> begin
false
end
| ((p, uu____16930))::[] -> begin
(

let uu____16939 = (is_app_pattern p)
in (not (uu____16939)))
end
| uu____16940 -> begin
false
end))
in (match ((not (expand_toplevel_pattern))) with
| true -> begin
(

let as_inner_let = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)
in (

let ds_lets = (desugar_term_maybe_top true env as_inner_let)
in (

let uu____16959 = (

let uu____16960 = (FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets)
in uu____16960.FStar_Syntax_Syntax.n)
in (match (uu____16959) with
| FStar_Syntax_Syntax.Tm_let (lbs, uu____16968) -> begin
(

let fvs = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals1 = (match (quals) with
| (uu____17001)::uu____17002 -> begin
(FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals)
end
| uu____17005 -> begin
(FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.collect (fun uu___225_17018 -> (match (uu___225_17018) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (uu____17021); FStar_Syntax_Syntax.lbunivs = uu____17022; FStar_Syntax_Syntax.lbtyp = uu____17023; FStar_Syntax_Syntax.lbeff = uu____17024; FStar_Syntax_Syntax.lbdef = uu____17025} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____17033; FStar_Syntax_Syntax.lbtyp = uu____17034; FStar_Syntax_Syntax.lbeff = uu____17035; FStar_Syntax_Syntax.lbdef = uu____17036} -> begin
(FStar_ToSyntax_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals2 = (

let uu____17046 = (FStar_All.pipe_right lets (FStar_Util.for_some (fun uu____17060 -> (match (uu____17060) with
| (uu____17065, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end))))
in (match (uu____17046) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals1
end
| uu____17069 -> begin
quals1
end))
in (

let lbs1 = (

let uu____17077 = (FStar_All.pipe_right quals2 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____17077) with
| true -> begin
(

let uu____17086 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu___245_17100 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let uu___246_17102 = fv
in {FStar_Syntax_Syntax.fv_name = uu___246_17102.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = uu___246_17102.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = uu___245_17100.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___245_17100.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___245_17100.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___245_17100.FStar_Syntax_Syntax.lbdef})))))
in (((FStar_Pervasives_Native.fst lbs)), (uu____17086)))
end
| uu____17107 -> begin
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
| uu____17134 -> begin
(failwith "Desugaring a let did not produce a let")
end))))
end
| uu____17139 -> begin
(

let uu____17140 = (match (lets) with
| ((pat, body))::[] -> begin
((pat), (body))
end
| uu____17159 -> begin
(failwith "expand_toplevel_pattern should only allow single definition lets")
end)
in (match (uu____17140) with
| (pat, body) -> begin
(

let fresh_toplevel_name = (FStar_Ident.gen FStar_Range.dummyRange)
in (

let fresh_pat = (

let var_pat = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((fresh_toplevel_name), (FStar_Pervasives_Native.None)))) FStar_Range.dummyRange)
in (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat1, ty) -> begin
(

let uu___247_17183 = pat1
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed (((var_pat), (ty))); FStar_Parser_AST.prange = uu___247_17183.FStar_Parser_AST.prange})
end
| uu____17184 -> begin
var_pat
end))
in (

let main_let = (desugar_decl env (

let uu___248_17191 = d
in {FStar_Parser_AST.d = FStar_Parser_AST.TopLevelLet (((isrec), ((((fresh_pat), (body)))::[]))); FStar_Parser_AST.drange = uu___248_17191.FStar_Parser_AST.drange; FStar_Parser_AST.doc = uu___248_17191.FStar_Parser_AST.doc; FStar_Parser_AST.quals = (FStar_Parser_AST.Private)::d.FStar_Parser_AST.quals; FStar_Parser_AST.attrs = uu___248_17191.FStar_Parser_AST.attrs}))
in (

let build_projection = (fun uu____17223 id -> (match (uu____17223) with
| (env1, ses) -> begin
(

let main = (

let uu____17244 = (

let uu____17245 = (FStar_Ident.lid_of_ids ((fresh_toplevel_name)::[]))
in FStar_Parser_AST.Var (uu____17245))
in (FStar_Parser_AST.mk_term uu____17244 FStar_Range.dummyRange FStar_Parser_AST.Expr))
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

let uu____17295 = (desugar_decl env1 id_decl)
in (match (uu____17295) with
| (env2, ses') -> begin
((env2), ((FStar_List.append ses ses')))
end))))))))
end))
in (

let bvs = (

let uu____17313 = (gather_pattern_bound_vars pat)
in (FStar_All.pipe_right uu____17313 FStar_Util.set_elements))
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

let uu____17344 = (close_fun env t)
in (desugar_term env uu____17344))
in (

let quals1 = (

let uu____17348 = ((FStar_ToSyntax_Env.iface env) && (FStar_ToSyntax_Env.admitted_iface env))
in (match (uu____17348) with
| true -> begin
(FStar_Parser_AST.Assumption)::quals
end
| uu____17351 -> begin
quals
end))
in (

let lid = (FStar_ToSyntax_Env.qualify env id)
in (

let se = (

let uu____17354 = (FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals1)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), ([]), (t1))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = uu____17354; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env se)
in (

let env2 = (FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc)
in ((env2), ((se)::[])))))))))
end
| FStar_Parser_AST.Exception (id, FStar_Pervasives_Native.None) -> begin
(

let uu____17366 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) FStar_Parser_Const.exn_lid)
in (match (uu____17366) with
| (t, uu____17380) -> begin
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

let uu____17414 = (

let uu____17421 = (FStar_Syntax_Syntax.null_binder t)
in (uu____17421)::[])
in (

let uu____17422 = (

let uu____17425 = (

let uu____17426 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) FStar_Parser_Const.exn_lid)
in (FStar_Pervasives_Native.fst uu____17426))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____17425))
in (FStar_Syntax_Util.arrow uu____17414 uu____17422)))
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

let uu____17488 = (FStar_ToSyntax_Env.try_lookup_effect_name env l1)
in (match (uu____17488) with
| FStar_Pervasives_Native.None -> begin
(

let uu____17491 = (

let uu____17492 = (

let uu____17497 = (

let uu____17498 = (

let uu____17499 = (FStar_Syntax_Print.lid_to_string l1)
in (Prims.strcat uu____17499 " not found"))
in (Prims.strcat "Effect name " uu____17498))
in ((uu____17497), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____17492))
in (FStar_Pervasives.raise uu____17491))
end
| FStar_Pervasives_Native.Some (l2) -> begin
l2
end)))
in (

let src = (lookup l.FStar_Parser_AST.msource)
in (

let dst = (lookup l.FStar_Parser_AST.mdest)
in (

let uu____17503 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(

let uu____17545 = (

let uu____17554 = (

let uu____17561 = (desugar_term env t)
in (([]), (uu____17561)))
in FStar_Pervasives_Native.Some (uu____17554))
in ((uu____17545), (FStar_Pervasives_Native.None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(

let uu____17594 = (

let uu____17603 = (

let uu____17610 = (desugar_term env wp)
in (([]), (uu____17610)))
in FStar_Pervasives_Native.Some (uu____17603))
in (

let uu____17619 = (

let uu____17628 = (

let uu____17635 = (desugar_term env t)
in (([]), (uu____17635)))
in FStar_Pervasives_Native.Some (uu____17628))
in ((uu____17594), (uu____17619))))
end
| FStar_Parser_AST.LiftForFree (t) -> begin
(

let uu____17661 = (

let uu____17670 = (

let uu____17677 = (desugar_term env t)
in (([]), (uu____17677)))
in FStar_Pervasives_Native.Some (uu____17670))
in ((FStar_Pervasives_Native.None), (uu____17661)))
end)
in (match (uu____17503) with
| (lift_wp, lift) -> begin
(

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect ({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift}); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in ((env), ((se)::[])))
end)))))
end)))


let desugar_decls : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun uu____17778 d -> (match (uu____17778) with
| (env1, sigelts) -> begin
(

let uu____17798 = (desugar_decl env1 d)
in (match (uu____17798) with
| (env2, se) -> begin
((env2), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls))


let open_prims_all : (FStar_Parser_AST.decoration Prims.list  ->  FStar_Parser_AST.decl) Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Parser_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Parser_Const.all_lid)) FStar_Range.dummyRange))::[]


let desugar_modul_common : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let env1 = (match (((curmod), (m))) with
| (FStar_Pervasives_Native.None, uu____17864) -> begin
env
end
| (FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.name = prev_lid; FStar_Syntax_Syntax.declarations = uu____17868; FStar_Syntax_Syntax.exports = uu____17869; FStar_Syntax_Syntax.is_interface = uu____17870}), FStar_Parser_AST.Module (current_lid, uu____17872)) when ((FStar_Ident.lid_equals prev_lid current_lid) && (FStar_Options.interactive ())) -> begin
env
end
| (FStar_Pervasives_Native.Some (prev_mod), uu____17880) -> begin
(FStar_ToSyntax_Env.finish_module_or_interface env prev_mod)
end)
in (

let uu____17883 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(

let uu____17919 = (FStar_ToSyntax_Env.prepare_module_or_interface true admitted env1 mname)
in ((uu____17919), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(

let uu____17936 = (FStar_ToSyntax_Env.prepare_module_or_interface false false env1 mname)
in ((uu____17936), (mname), (decls), (false)))
end)
in (match (uu____17883) with
| ((env2, pop_when_done), mname, decls, intf) -> begin
(

let uu____17966 = (desugar_decls env2 decls)
in (match (uu____17966) with
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


let desugar_partial_modul : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (

let m1 = (

let uu____18018 = ((FStar_Options.interactive ()) && (

let uu____18020 = (

let uu____18021 = (

let uu____18022 = (FStar_Options.file_list ())
in (FStar_List.hd uu____18022))
in (FStar_Util.get_file_extension uu____18021))
in (uu____18020 = "fsti")))
in (match (uu____18018) with
| true -> begin
(as_interface m)
end
| uu____18025 -> begin
m
end))
in (

let uu____18026 = (desugar_modul_common curmod env m1)
in (match (uu____18026) with
| (x, y, pop_when_done) -> begin
((match (pop_when_done) with
| true -> begin
(

let uu____18041 = (FStar_ToSyntax_Env.pop ())
in ())
end
| uu____18042 -> begin
()
end);
((x), (y));
)
end))))


let desugar_modul : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul) = (fun env m -> (

let uu____18059 = (desugar_modul_common FStar_Pervasives_Native.None env m)
in (match (uu____18059) with
| (env1, modul, pop_when_done) -> begin
(

let env2 = (FStar_ToSyntax_Env.finish_module_or_interface env1 modul)
in ((

let uu____18075 = (FStar_Options.dump_module modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____18075) with
| true -> begin
(

let uu____18076 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" uu____18076))
end
| uu____18077 -> begin
()
end));
(

let uu____18078 = (match (pop_when_done) with
| true -> begin
(FStar_ToSyntax_Env.export_interface modul.FStar_Syntax_Syntax.name env2)
end
| uu____18079 -> begin
env2
end)
in ((uu____18078), (modul)));
))
end)))


let desugar_file : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (

let uu____18094 = (FStar_List.fold_left (fun uu____18114 m -> (match (uu____18114) with
| (env1, mods) -> begin
(

let uu____18134 = (desugar_modul env1 m)
in (match (uu____18134) with
| (env2, m1) -> begin
((env2), ((m1)::mods))
end))
end)) ((env), ([])) f)
in (match (uu____18094) with
| (env1, mods) -> begin
((env1), ((FStar_List.rev mods)))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_ToSyntax_Env.env  ->  FStar_ToSyntax_Env.env = (fun m en -> (

let uu____18173 = (FStar_ToSyntax_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (uu____18173) with
| (en1, pop_when_done) -> begin
(

let en2 = (

let uu____18181 = (FStar_ToSyntax_Env.set_current_module en1 m.FStar_Syntax_Syntax.name)
in (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____18181 m.FStar_Syntax_Syntax.exports))
in (

let env = (FStar_ToSyntax_Env.finish_module_or_interface en2 m)
in (match (pop_when_done) with
| true -> begin
(FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name env)
end
| uu____18183 -> begin
env
end)))
end)))




