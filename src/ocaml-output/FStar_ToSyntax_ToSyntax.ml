
open Prims
open FStar_Pervasives

let desugar_disjunctive_pattern : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.branch Prims.list = (fun pats when_opt branch1 -> (FStar_All.pipe_right pats (FStar_List.map (fun pat -> (FStar_Syntax_Util.branch ((pat), (when_opt), (branch1)))))))


let trans_aqual : FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option = (fun uu___204_62 -> (match (uu___204_62) with
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)
end
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality)
end
| uu____67 -> begin
FStar_Pervasives_Native.None
end))


let trans_qual : FStar_Range.range  ->  FStar_Ident.lident FStar_Pervasives_Native.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun r maybe_effect_id uu___205_83 -> (match (uu___205_83) with
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


let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun uu___206_91 -> (match (uu___206_91) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end
| FStar_Parser_AST.LightOff -> begin
FStar_Syntax_Syntax.LightOff
end))


let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option = (fun uu___207_101 -> (match (uu___207_101) with
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


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun uu___208_1455 -> (match (uu___208_1455) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| uu____1462 -> begin
(failwith "Impossible")
end))


let as_binder : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  (FStar_Ident.ident FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_ToSyntax_Env.env) = (fun env imp uu___209_1490 -> (match (uu___209_1490) with
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

let uu___230_1531 = a1
in {FStar_Syntax_Syntax.ppname = uu___230_1531.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___230_1531.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), ((trans_aqual imp)))), (env1))
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


let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun uu___210_1834 -> (match (uu___210_1834) with
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


let rec sum_to_universe : FStar_Syntax_Syntax.universe  ->  Prims.int  ->  FStar_Syntax_Syntax.universe = (fun u n1 -> (match ((n1 = (Prims.parse_int "0"))) with
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
(match ((FStar_List.existsb (fun uu___211_2042 -> (match (uu___211_2042) with
| FStar_Util.Inr (uu____2047) -> begin
true
end
| uu____2048 -> begin
false
end)) univargs)) with
| true -> begin
(

let uu____2053 = (

let uu____2054 = (FStar_List.map (fun uu___212_2063 -> (match (uu___212_2063) with
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

let nargs = (FStar_List.map (fun uu___213_2080 -> (match (uu___213_2080) with
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
| FStar_Syntax_Syntax.Pat_dot_term (uu____2417) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_wild (uu____2424) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_constant (uu____2425) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (uu____2427, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out uu____2467 -> (match (uu____2467) with
| (p3, uu____2477) -> begin
(

let uu____2478 = (pat_vars p3)
in (FStar_Util.set_union out uu____2478))
end)) FStar_Syntax_Syntax.no_names))
end))
in (pat_vars p1)))
in ((match (((is_mut), (p.FStar_Parser_AST.pat))) with
| (false, uu____2482) -> begin
()
end
| (true, FStar_Parser_AST.PatVar (uu____2483)) -> begin
()
end
| (true, uu____2490) -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("let-mutable is for variables only"), (p.FStar_Parser_AST.prange)))))
end);
(

let push_bv_maybe_mut = (match (is_mut) with
| true -> begin
FStar_ToSyntax_Env.push_bv_mutable
end
| uu____2508 -> begin
FStar_ToSyntax_Env.push_bv
end)
in (

let resolvex = (fun l e x -> (

let uu____2525 = (FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText))))
in (match (uu____2525) with
| FStar_Pervasives_Native.Some (y) -> begin
((l), (e), (y))
end
| uu____2539 -> begin
(

let uu____2542 = (push_bv_maybe_mut e x)
in (match (uu____2542) with
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
| FStar_Parser_AST.PatOr (uu____2606) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.PatOp (op) -> begin
(

let uu____2622 = (

let uu____2623 = (

let uu____2624 = (

let uu____2631 = (

let uu____2632 = (

let uu____2637 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") op.FStar_Ident.idText op.FStar_Ident.idRange)
in ((uu____2637), (op.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____2632))
in ((uu____2631), (FStar_Pervasives_Native.None)))
in FStar_Parser_AST.PatVar (uu____2624))
in {FStar_Parser_AST.pat = uu____2623; FStar_Parser_AST.prange = p1.FStar_Parser_AST.prange})
in (aux loc env1 uu____2622))
end
| FStar_Parser_AST.PatAscribed (p2, t) -> begin
(

let uu____2642 = (aux loc env1 p2)
in (match (uu____2642) with
| (loc1, env', binder, p3, imp) -> begin
(

let binder1 = (match (binder) with
| LetBinder (uu____2677) -> begin
(failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t1 = (

let uu____2685 = (close_fun env1 t)
in (desugar_term env1 uu____2685))
in ((match ((match (x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
false
end
| uu____2687 -> begin
true
end)) with
| true -> begin
(

let uu____2688 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____2689 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____2690 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3_warning "Multiple ascriptions for %s in pattern, type %s was shadowed by %s" uu____2688 uu____2689 uu____2690))))
end
| uu____2691 -> begin
()
end);
LocalBinder ((((

let uu___231_2693 = x
in {FStar_Syntax_Syntax.ppname = uu___231_2693.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___231_2693.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})), (aq)));
))
end)
in ((loc1), (env'), (binder1), (p3), (imp)))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____2697 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____2697), (false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____2708 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____2708), (false))))
end
| FStar_Parser_AST.PatTvar (x, aq) -> begin
(

let imp = (aq = FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit))
in (

let aq1 = (trans_aqual aq)
in (

let uu____2729 = (resolvex loc env1 x)
in (match (uu____2729) with
| (loc1, env2, xbv) -> begin
(

let uu____2751 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc1), (env2), (LocalBinder (((xbv), (aq1)))), (uu____2751), (imp)))
end))))
end
| FStar_Parser_AST.PatVar (x, aq) -> begin
(

let imp = (aq = FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit))
in (

let aq1 = (trans_aqual aq)
in (

let uu____2772 = (resolvex loc env1 x)
in (match (uu____2772) with
| (loc1, env2, xbv) -> begin
(

let uu____2794 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc1), (env2), (LocalBinder (((xbv), (aq1)))), (uu____2794), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l1 = (FStar_ToSyntax_Env.fail_or env1 (FStar_ToSyntax_Env.try_lookup_datacon env1) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____2806 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), ([])))))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____2806), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = uu____2830}, args) -> begin
(

let uu____2836 = (FStar_List.fold_right (fun arg uu____2877 -> (match (uu____2877) with
| (loc1, env2, args1) -> begin
(

let uu____2925 = (aux loc1 env2 arg)
in (match (uu____2925) with
| (loc2, env3, uu____2954, arg1, imp) -> begin
((loc2), (env3), ((((arg1), (imp)))::args1))
end))
end)) args ((loc), (env1), ([])))
in (match (uu____2836) with
| (loc1, env2, args1) -> begin
(

let l1 = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_datacon env2) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____3024 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args1)))))
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3024), (false)))))
end))
end
| FStar_Parser_AST.PatApp (uu____3041) -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected pattern"), (p1.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____3063 = (FStar_List.fold_right (fun pat uu____3096 -> (match (uu____3096) with
| (loc1, env2, pats1) -> begin
(

let uu____3128 = (aux loc1 env2 pat)
in (match (uu____3128) with
| (loc2, env3, uu____3153, pat1, uu____3155) -> begin
((loc2), (env3), ((pat1)::pats1))
end))
end)) pats ((loc), (env1), ([])))
in (match (uu____3063) with
| (loc1, env2, pats1) -> begin
(

let pat = (

let uu____3198 = (

let uu____3201 = (

let uu____3206 = (FStar_Range.end_range p1.FStar_Parser_AST.prange)
in (pos_r uu____3206))
in (

let uu____3207 = (

let uu____3208 = (

let uu____3221 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____3221), ([])))
in FStar_Syntax_Syntax.Pat_cons (uu____3208))
in (FStar_All.pipe_left uu____3201 uu____3207)))
in (FStar_List.fold_right (fun hd1 tl1 -> (

let r = (FStar_Range.union_ranges hd1.FStar_Syntax_Syntax.p tl1.FStar_Syntax_Syntax.p)
in (

let uu____3253 = (

let uu____3254 = (

let uu____3267 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____3267), ((((hd1), (false)))::(((tl1), (false)))::[])))
in FStar_Syntax_Syntax.Pat_cons (uu____3254))
in (FStar_All.pipe_left (pos_r r) uu____3253)))) pats1 uu____3198))
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep1) -> begin
(

let uu____3311 = (FStar_List.fold_left (fun uu____3351 p2 -> (match (uu____3351) with
| (loc1, env2, pats) -> begin
(

let uu____3400 = (aux loc1 env2 p2)
in (match (uu____3400) with
| (loc2, env3, uu____3429, pat, uu____3431) -> begin
((loc2), (env3), ((((pat), (false)))::pats))
end))
end)) ((loc), (env1), ([])) args)
in (match (uu____3311) with
| (loc1, env2, args1) -> begin
(

let args2 = (FStar_List.rev args1)
in (

let l = (match (dep1) with
| true -> begin
(FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end
| uu____3519 -> begin
(FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end)
in (

let uu____3526 = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_lid env2) l)
in (match (uu____3526) with
| (constr, uu____3548) -> begin
(

let l1 = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____3551 -> begin
(failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____3553 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args2)))))
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3553), (false)))))
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

let fields1 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____3624 -> (match (uu____3624) with
| (f, p2) -> begin
((f.FStar_Ident.ident), (p2))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____3654 -> (match (uu____3654) with
| (f, uu____3660) -> begin
(

let uu____3661 = (FStar_All.pipe_right fields1 (FStar_List.tryFind (fun uu____3687 -> (match (uu____3687) with
| (g, uu____3693) -> begin
(f.FStar_Ident.idText = g.FStar_Ident.idText)
end))))
in (match (uu____3661) with
| FStar_Pervasives_Native.None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p1.FStar_Parser_AST.prange)
end
| FStar_Pervasives_Native.Some (uu____3698, p2) -> begin
p2
end))
end))))
in (

let app = (

let uu____3705 = (

let uu____3706 = (

let uu____3713 = (

let uu____3714 = (

let uu____3715 = (FStar_Ident.lid_of_ids (FStar_List.append record.FStar_ToSyntax_Env.typename.FStar_Ident.ns ((record.FStar_ToSyntax_Env.constrname)::[])))
in FStar_Parser_AST.PatName (uu____3715))
in (FStar_Parser_AST.mk_pattern uu____3714 p1.FStar_Parser_AST.prange))
in ((uu____3713), (args)))
in FStar_Parser_AST.PatApp (uu____3706))
in (FStar_Parser_AST.mk_pattern uu____3705 p1.FStar_Parser_AST.prange))
in (

let uu____3718 = (aux loc env1 app)
in (match (uu____3718) with
| (env2, e, b, p2, uu____3747) -> begin
(

let p3 = (match (p2.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args1) -> begin
(

let uu____3775 = (

let uu____3776 = (

let uu____3789 = (

let uu___232_3790 = fv
in (

let uu____3791 = (

let uu____3794 = (

let uu____3795 = (

let uu____3802 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map FStar_Pervasives_Native.fst))
in ((record.FStar_ToSyntax_Env.typename), (uu____3802)))
in FStar_Syntax_Syntax.Record_ctor (uu____3795))
in FStar_Pervasives_Native.Some (uu____3794))
in {FStar_Syntax_Syntax.fv_name = uu___232_3790.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = uu___232_3790.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu____3791}))
in ((uu____3789), (args1)))
in FStar_Syntax_Syntax.Pat_cons (uu____3776))
in (FStar_All.pipe_left pos uu____3775))
end
| uu____3829 -> begin
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

let uu____3876 = (aux loc env1 p2)
in (match (uu____3876) with
| (loc1, env2, var, p3, uu____3903) -> begin
(

let uu____3908 = (FStar_List.fold_left (fun uu____3940 p4 -> (match (uu____3940) with
| (loc2, env3, ps1) -> begin
(

let uu____3973 = (aux loc2 env3 p4)
in (match (uu____3973) with
| (loc3, env4, uu____3998, p5, uu____4000) -> begin
((loc3), (env4), ((p5)::ps1))
end))
end)) ((loc1), (env2), ([])) ps)
in (match (uu____3908) with
| (loc2, env3, ps1) -> begin
(

let pats = (p3)::(FStar_List.rev ps1)
in ((env3), (var), (pats)))
end))
end))
end
| uu____4051 -> begin
(

let uu____4052 = (aux loc env1 p1)
in (match (uu____4052) with
| (loc1, env2, vars, pat, b) -> begin
((env2), (vars), ((pat)::[]))
end))
end)))
in (

let uu____4092 = (aux_maybe_or env p)
in (match (uu____4092) with
| (env1, b, pats) -> begin
((

let uu____4123 = (FStar_List.map check_linear_pattern_variables pats)
in (FStar_All.pipe_left FStar_Pervasives.ignore uu____4123));
((env1), (b), (pats));
)
end))))));
)))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.list) = (fun top env p is_mut -> (

let mklet = (fun x -> (

let uu____4158 = (

let uu____4159 = (

let uu____4164 = (FStar_ToSyntax_Env.qualify env x)
in ((uu____4164), (FStar_Syntax_Syntax.tun)))
in LetBinder (uu____4159))
in ((env), (uu____4158), ([]))))
in (match (top) with
| true -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(

let uu____4184 = (

let uu____4185 = (

let uu____4190 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") x.FStar_Ident.idText x.FStar_Ident.idRange)
in ((uu____4190), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____4185))
in (mklet uu____4184))
end
| FStar_Parser_AST.PatVar (x, uu____4192) -> begin
(mklet x)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____4198); FStar_Parser_AST.prange = uu____4199}, t) -> begin
(

let uu____4205 = (

let uu____4206 = (

let uu____4211 = (FStar_ToSyntax_Env.qualify env x)
in (

let uu____4212 = (desugar_term env t)
in ((uu____4211), (uu____4212))))
in LetBinder (uu____4206))
in ((env), (uu____4205), ([])))
end
| uu____4215 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end
| uu____4224 -> begin
(

let uu____4225 = (desugar_data_pat env p is_mut)
in (match (uu____4225) with
| (env1, binder, p1) -> begin
(

let p2 = (match (p1) with
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (uu____4254); FStar_Syntax_Syntax.p = uu____4255})::[] -> begin
[]
end
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (uu____4260); FStar_Syntax_Syntax.p = uu____4261})::[] -> begin
[]
end
| uu____4266 -> begin
p1
end)
in ((env1), (binder), (p2)))
end))
end)))
and desugar_binding_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.list) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat Prims.list) = (fun uu____4273 env pat -> (

let uu____4276 = (desugar_data_pat env pat false)
in (match (uu____4276) with
| (env1, uu____4292, pat1) -> begin
((env1), (pat1))
end)))
and desugar_match_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat Prims.list) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env1 = (FStar_ToSyntax_Env.set_expect_typ env false)
in (desugar_term_maybe_top false env1 e)))
and desugar_typ : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env1 = (FStar_ToSyntax_Env.set_expect_typ env true)
in (desugar_term_maybe_top false env1 e)))
and desugar_machine_integer : FStar_ToSyntax_Env.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun env repr uu____4310 range -> (match (uu____4310) with
| (signedness, width) -> begin
(

let uu____4320 = (FStar_Const.bounds signedness width)
in (match (uu____4320) with
| (lower, upper) -> begin
(

let value = (

let uu____4330 = (FStar_Util.ensure_decimal repr)
in (FStar_Util.int_of_string uu____4330))
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

let uu____4333 = (

let uu____4334 = (

let uu____4339 = (FStar_Util.format2 "%s is not in the expected range for %s" repr tnm)
in ((uu____4339), (range)))
in FStar_Errors.Error (uu____4334))
in (FStar_Exn.raise uu____4333))
end
| uu____4340 -> begin
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

let uu____4347 = (FStar_ToSyntax_Env.try_lookup_lid env lid)
in (match (uu____4347) with
| FStar_Pervasives_Native.Some (intro_term, uu____4357) -> begin
(match (intro_term.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let private_lid = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text private_intro_nm) range)
in (

let private_fv = (

let uu____4367 = (FStar_Syntax_Util.incr_delta_depth fv.FStar_Syntax_Syntax.fv_delta)
in (FStar_Syntax_Syntax.lid_as_fv private_lid uu____4367 fv.FStar_Syntax_Syntax.fv_qual))
in (

let uu___233_4368 = intro_term
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (private_fv); FStar_Syntax_Syntax.pos = uu___233_4368.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___233_4368.FStar_Syntax_Syntax.vars})))
end
| uu____4369 -> begin
(failwith (Prims.strcat "Unexpected non-fvar for " intro_nm))
end)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4376 = (

let uu____4377 = (

let uu____4382 = (FStar_Util.format1 "Unexpected numeric literal.  Restart F* to load %s." tnm)
in ((uu____4382), (range)))
in FStar_Errors.Error (uu____4377))
in (FStar_Exn.raise uu____4376))
end))
in (

let repr1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (FStar_Pervasives_Native.None))))) FStar_Pervasives_Native.None range)
in (

let uu____4398 = (

let uu____4401 = (

let uu____4402 = (

let uu____4417 = (

let uu____4426 = (

let uu____4433 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr1), (uu____4433)))
in (uu____4426)::[])
in ((lid1), (uu____4417)))
in FStar_Syntax_Syntax.Tm_app (uu____4402))
in (FStar_Syntax_Syntax.mk uu____4401))
in (uu____4398 FStar_Pervasives_Native.None range)))))));
)))
end))
end))
and desugar_name : (FStar_Syntax_Syntax.term'  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  env_t  ->  Prims.bool  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.term = (fun mk1 setpos env resolve l -> (

let uu____4472 = (FStar_ToSyntax_Env.fail_or env ((match (resolve) with
| true -> begin
FStar_ToSyntax_Env.try_lookup_lid
end
| uu____4481 -> begin
FStar_ToSyntax_Env.try_lookup_lid_no_resolve
end) env) l)
in (match (uu____4472) with
| (tm, mut) -> begin
(

let tm1 = (setpos tm)
in (match (mut) with
| true -> begin
(

let uu____4487 = (

let uu____4488 = (

let uu____4495 = (mk_ref_read tm1)
in ((uu____4495), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval))))
in FStar_Syntax_Syntax.Tm_meta (uu____4488))
in (FStar_All.pipe_left mk1 uu____4487))
end
| uu____4500 -> begin
tm1
end))
end)))
and desugar_attributes : env_t  ->  FStar_Parser_AST.term Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun env cattributes -> (

let desugar_attribute = (fun t -> (

let uu____4511 = (

let uu____4512 = (unparen t)
in uu____4512.FStar_Parser_AST.tm)
in (match (uu____4511) with
| FStar_Parser_AST.Var ({FStar_Ident.ns = uu____4513; FStar_Ident.ident = uu____4514; FStar_Ident.nsstr = uu____4515; FStar_Ident.str = "cps"}) -> begin
FStar_Syntax_Syntax.CPS
end
| uu____4518 -> begin
(

let uu____4519 = (

let uu____4520 = (

let uu____4525 = (

let uu____4526 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "Unknown attribute " uu____4526))
in ((uu____4525), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____4520))
in (FStar_Exn.raise uu____4519))
end)))
in (FStar_List.map desugar_attribute cattributes)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (

let mk1 = (fun e -> (FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let uu___234_4546 = e
in {FStar_Syntax_Syntax.n = uu___234_4546.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___234_4546.FStar_Syntax_Syntax.vars}))
in (

let uu____4549 = (

let uu____4550 = (unparen top)
in uu____4550.FStar_Parser_AST.tm)
in (match (uu____4549) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (uu____4551) -> begin
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
| FStar_Parser_AST.Op (op_star, (uu____4602)::(uu____4603)::[]) when (((FStar_Ident.text_of_id op_star) = "*") && (

let uu____4607 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range op_star)
in (FStar_All.pipe_right uu____4607 FStar_Option.isNone))) -> begin
(

let rec flatten1 = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4620}, (t1)::(t2)::[]) -> begin
(

let uu____4625 = (flatten1 t1)
in (FStar_List.append uu____4625 ((t2)::[])))
end
| uu____4628 -> begin
(t)::[]
end))
in (

let targs = (

let uu____4632 = (

let uu____4635 = (unparen top)
in (flatten1 uu____4635))
in (FStar_All.pipe_right uu____4632 (FStar_List.map (fun t -> (

let uu____4643 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg uu____4643))))))
in (

let uu____4644 = (

let uu____4649 = (FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) uu____4649))
in (match (uu____4644) with
| (tup, uu____4655) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____4659 = (

let uu____4662 = (FStar_ToSyntax_Env.fail_or2 (FStar_ToSyntax_Env.try_lookup_id env) a)
in (FStar_Pervasives_Native.fst uu____4662))
in (FStar_All.pipe_left setpos uu____4659))
end
| FStar_Parser_AST.Uvar (u) -> begin
(FStar_Exn.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected universe variable " (Prims.strcat (FStar_Ident.text_of_id u) " in non-universe context"))), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(

let uu____4682 = (op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)
in (match (uu____4682) with
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected or unbound operator: " (FStar_Ident.text_of_id s))), (top.FStar_Parser_AST.range)))))
end
| FStar_Pervasives_Native.Some (op) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let args1 = (FStar_All.pipe_right args (FStar_List.map (fun t -> (

let uu____4714 = (desugar_term env t)
in ((uu____4714), (FStar_Pervasives_Native.None))))))
in (mk1 (FStar_Syntax_Syntax.Tm_app (((op), (args1))))))
end
| uu____4725 -> begin
op
end)
end))
end
| FStar_Parser_AST.Construct (n1, ((a, uu____4728))::[]) when (n1.FStar_Ident.str = "SMTPat") -> begin
(

let uu____4743 = (

let uu___235_4744 = top
in (

let uu____4745 = (

let uu____4746 = (

let uu____4753 = (

let uu___236_4754 = top
in (

let uu____4755 = (

let uu____4756 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____4756))
in {FStar_Parser_AST.tm = uu____4755; FStar_Parser_AST.range = uu___236_4754.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___236_4754.FStar_Parser_AST.level}))
in ((uu____4753), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____4746))
in {FStar_Parser_AST.tm = uu____4745; FStar_Parser_AST.range = uu___235_4744.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___235_4744.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____4743))
end
| FStar_Parser_AST.Construct (n1, ((a, uu____4759))::[]) when (n1.FStar_Ident.str = "SMTPatT") -> begin
(

let uu____4774 = (

let uu___237_4775 = top
in (

let uu____4776 = (

let uu____4777 = (

let uu____4784 = (

let uu___238_4785 = top
in (

let uu____4786 = (

let uu____4787 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____4787))
in {FStar_Parser_AST.tm = uu____4786; FStar_Parser_AST.range = uu___238_4785.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___238_4785.FStar_Parser_AST.level}))
in ((uu____4784), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____4777))
in {FStar_Parser_AST.tm = uu____4776; FStar_Parser_AST.range = uu___237_4775.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___237_4775.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____4774))
end
| FStar_Parser_AST.Construct (n1, ((a, uu____4790))::[]) when (n1.FStar_Ident.str = "SMTPatOr") -> begin
(

let uu____4805 = (

let uu___239_4806 = top
in (

let uu____4807 = (

let uu____4808 = (

let uu____4815 = (

let uu___240_4816 = top
in (

let uu____4817 = (

let uu____4818 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat_or")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____4818))
in {FStar_Parser_AST.tm = uu____4817; FStar_Parser_AST.range = uu___240_4816.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___240_4816.FStar_Parser_AST.level}))
in ((uu____4815), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____4808))
in {FStar_Parser_AST.tm = uu____4807; FStar_Parser_AST.range = uu___239_4806.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___239_4806.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____4805))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____4819; FStar_Ident.ident = uu____4820; FStar_Ident.nsstr = uu____4821; FStar_Ident.str = "Type0"}) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____4824; FStar_Ident.ident = uu____4825; FStar_Ident.nsstr = uu____4826; FStar_Ident.str = "Type"}) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Construct ({FStar_Ident.ns = uu____4829; FStar_Ident.ident = uu____4830; FStar_Ident.nsstr = uu____4831; FStar_Ident.str = "Type"}, ((t, FStar_Parser_AST.UnivApp))::[]) -> begin
(

let uu____4849 = (

let uu____4850 = (desugar_universe t)
in FStar_Syntax_Syntax.Tm_type (uu____4850))
in (mk1 uu____4849))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____4851; FStar_Ident.ident = uu____4852; FStar_Ident.nsstr = uu____4853; FStar_Ident.str = "Effect"}) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____4856; FStar_Ident.ident = uu____4857; FStar_Ident.nsstr = uu____4858; FStar_Ident.str = "True"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____4861; FStar_Ident.ident = uu____4862; FStar_Ident.nsstr = uu____4863; FStar_Ident.str = "False"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
end
| FStar_Parser_AST.Projector (eff_name, {FStar_Ident.idText = txt; FStar_Ident.idRange = uu____4868}) when ((is_special_effect_combinator txt) && (FStar_ToSyntax_Env.is_effect_name env eff_name)) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name);
(

let uu____4870 = (FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name)
in (match (uu____4870) with
| FStar_Pervasives_Native.Some (ed) -> begin
(

let lid = (FStar_Syntax_Util.dm4f_lid ed txt)
in (FStar_Syntax_Syntax.fvar lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4875 = (FStar_Util.format2 "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)" (FStar_Ident.text_of_lid eff_name) txt)
in (failwith uu____4875))
end));
)
end
| FStar_Parser_AST.Assign (ident, t2) -> begin
(

let t21 = (desugar_term env t2)
in (

let uu____4879 = (FStar_ToSyntax_Env.fail_or2 (FStar_ToSyntax_Env.try_lookup_id env) ident)
in (match (uu____4879) with
| (t1, mut) -> begin
((match ((not (mut))) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Can only assign to mutable values"), (top.FStar_Parser_AST.range)))))
end
| uu____4891 -> begin
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

let uu____4906 = (FStar_ToSyntax_Env.try_lookup_datacon env l)
in (match (uu____4906) with
| FStar_Pervasives_Native.Some (uu____4915) -> begin
FStar_Pervasives_Native.Some (((true), (l)))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4920 = (FStar_ToSyntax_Env.try_lookup_root_effect_name env l)
in (match (uu____4920) with
| FStar_Pervasives_Native.Some (new_name) -> begin
FStar_Pervasives_Native.Some (((false), (new_name)))
end
| uu____4934 -> begin
FStar_Pervasives_Native.None
end))
end))
in (match (name) with
| FStar_Pervasives_Native.Some (resolve, new_name) -> begin
(

let uu____4947 = (FStar_Syntax_Util.mk_field_projector_name_from_ident new_name i)
in (desugar_name mk1 setpos env resolve uu____4947))
end
| uu____4948 -> begin
(

let uu____4955 = (

let uu____4956 = (

let uu____4961 = (FStar_Util.format1 "Data constructor or effect %s not found" l.FStar_Ident.str)
in ((uu____4961), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____4956))
in (FStar_Exn.raise uu____4955))
end));
)
end
| FStar_Parser_AST.Discrim (lid) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid);
(

let uu____4964 = (FStar_ToSyntax_Env.try_lookup_datacon env lid)
in (match (uu____4964) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4967 = (

let uu____4968 = (

let uu____4973 = (FStar_Util.format1 "Data constructor %s not found" lid.FStar_Ident.str)
in ((uu____4973), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____4968))
in (FStar_Exn.raise uu____4967))
end
| uu____4974 -> begin
(

let lid' = (FStar_Syntax_Util.mk_discriminator lid)
in (desugar_name mk1 setpos env true lid'))
end));
)
end
| FStar_Parser_AST.Construct (l, args) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l);
(

let uu____4993 = (FStar_ToSyntax_Env.try_lookup_datacon env l)
in (match (uu____4993) with
| FStar_Pervasives_Native.Some (head1) -> begin
(

let uu____4997 = (

let uu____5004 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (head1)))
in ((uu____5004), (true)))
in (match (uu____4997) with
| (head2, is_data) -> begin
(match (args) with
| [] -> begin
head2
end
| uu____5019 -> begin
(

let uu____5026 = (FStar_Util.take (fun uu____5050 -> (match (uu____5050) with
| (uu____5055, imp) -> begin
(imp = FStar_Parser_AST.UnivApp)
end)) args)
in (match (uu____5026) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun x -> (desugar_universe (FStar_Pervasives_Native.fst x))) universes)
in (

let args2 = (FStar_List.map (fun uu____5119 -> (match (uu____5119) with
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
| uu____5140 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_uinst (((head2), (universes1)))))
end)
in (

let app = (mk1 (FStar_Syntax_Syntax.Tm_app (((head3), (args2)))))
in (match (is_data) with
| true -> begin
(mk1 (FStar_Syntax_Syntax.Tm_meta (((app), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end
| uu____5160 -> begin
app
end)))))
end))
end)
end))
end
| FStar_Pervasives_Native.None -> begin
(

let error_msg = (

let uu____5162 = (FStar_ToSyntax_Env.try_lookup_effect_name env l)
in (match (uu____5162) with
| FStar_Pervasives_Native.None -> begin
(Prims.strcat "Constructor " (Prims.strcat l.FStar_Ident.str " not found"))
end
| FStar_Pervasives_Native.Some (uu____5165) -> begin
(Prims.strcat "Effect " (Prims.strcat l.FStar_Ident.str " used at an unexpected position"))
end))
in (FStar_Exn.raise (FStar_Errors.Error (((error_msg), (top.FStar_Parser_AST.range))))))
end));
)
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let uu____5172 = (FStar_List.fold_left (fun uu____5217 b -> (match (uu____5217) with
| (env1, tparams, typs) -> begin
(

let uu____5274 = (desugar_binder env1 b)
in (match (uu____5274) with
| (xopt, t1) -> begin
(

let uu____5303 = (match (xopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5312 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env1), (uu____5312)))
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_ToSyntax_Env.push_bv env1 x)
end)
in (match (uu____5303) with
| (env2, x) -> begin
(

let uu____5332 = (

let uu____5335 = (

let uu____5338 = (

let uu____5339 = (no_annot_abs tparams t1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____5339))
in (uu____5338)::[])
in (FStar_List.append typs uu____5335))
in ((env2), ((FStar_List.append tparams (((((

let uu___241_5365 = x
in {FStar_Syntax_Syntax.ppname = uu___241_5365.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___241_5365.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})), (FStar_Pervasives_Native.None)))::[]))), (uu____5332)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type_level FStar_Pervasives_Native.None))::[])))
in (match (uu____5172) with
| (env1, uu____5389, targs) -> begin
(

let uu____5411 = (

let uu____5416 = (FStar_Parser_Const.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_ToSyntax_Env.fail_or env1 (FStar_ToSyntax_Env.try_lookup_lid env1) uu____5416))
in (match (uu____5411) with
| (tup, uu____5422) -> begin
(FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let uu____5433 = (uncurry binders t)
in (match (uu____5433) with
| (bs, t1) -> begin
(

let rec aux = (fun env1 bs1 uu___214_5465 -> (match (uu___214_5465) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range env1 t1)
in (

let uu____5479 = (FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod)
in (FStar_All.pipe_left setpos uu____5479)))
end
| (hd1)::tl1 -> begin
(

let bb = (desugar_binder env1 hd1)
in (

let uu____5501 = (as_binder env1 hd1.FStar_Parser_AST.aqual bb)
in (match (uu____5501) with
| (b, env2) -> begin
(aux env2 ((b)::bs1) tl1)
end)))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(

let uu____5516 = (desugar_binder env b)
in (match (uu____5516) with
| (FStar_Pervasives_Native.None, uu____5523) -> begin
(failwith "Missing binder in refinement")
end
| b1 -> begin
(

let uu____5533 = (as_binder env FStar_Pervasives_Native.None b1)
in (match (uu____5533) with
| ((x, uu____5539), env1) -> begin
(

let f1 = (desugar_formula env1 f)
in (

let uu____5546 = (FStar_Syntax_Util.refine x f1)
in (FStar_All.pipe_left setpos uu____5546)))
end))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let binders1 = (FStar_All.pipe_right binders (FStar_List.map replace_unit_pattern))
in (

let uu____5566 = (FStar_List.fold_left (fun uu____5586 pat -> (match (uu____5586) with
| (env1, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (uu____5612, t) -> begin
(

let uu____5614 = (

let uu____5617 = (free_type_vars env1 t)
in (FStar_List.append uu____5617 ftvs))
in ((env1), (uu____5614)))
end
| uu____5622 -> begin
((env1), (ftvs))
end)
end)) ((env), ([])) binders1)
in (match (uu____5566) with
| (uu____5627, ftv) -> begin
(

let ftv1 = (sort_ftv ftv)
in (

let binders2 = (

let uu____5639 = (FStar_All.pipe_right ftv1 (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append uu____5639 binders1))
in (

let rec aux = (fun env1 bs sc_pat_opt uu___215_5680 -> (match (uu___215_5680) with
| [] -> begin
(

let body1 = (desugar_term env1 body)
in (

let body2 = (match (sc_pat_opt) with
| FStar_Pervasives_Native.Some (sc, pat) -> begin
(

let body2 = (

let uu____5718 = (

let uu____5719 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right uu____5719 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close uu____5718 body1))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (FStar_Pervasives_Native.None), (body2)))::[])))) FStar_Pervasives_Native.None body2.FStar_Syntax_Syntax.pos))
end
| FStar_Pervasives_Native.None -> begin
body1
end)
in (

let uu____5772 = (no_annot_abs (FStar_List.rev bs) body2)
in (setpos uu____5772))))
end
| (p)::rest -> begin
(

let uu____5783 = (desugar_binding_pat env1 p)
in (match (uu____5783) with
| (env2, b, pat) -> begin
(

let pat1 = (match (pat) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (p1)::[] -> begin
FStar_Pervasives_Native.Some (p1)
end
| uu____5807 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Disjunctive patterns are not supported in abstractions"), (p.FStar_Parser_AST.prange)))))
end)
in (

let uu____5812 = (match (b) with
| LetBinder (uu____5845) -> begin
(failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt1 = (match (((pat1), (sc_pat_opt))) with
| (FStar_Pervasives_Native.None, uu____5895) -> begin
sc_pat_opt
end
| (FStar_Pervasives_Native.Some (p1), FStar_Pervasives_Native.None) -> begin
(

let uu____5931 = (

let uu____5936 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____5936), (p1)))
in FStar_Pervasives_Native.Some (uu____5931))
end
| (FStar_Pervasives_Native.Some (p1), FStar_Pervasives_Native.Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (uu____5972), uu____5973) -> begin
(

let tup2 = (

let uu____5975 = (FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____5975 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____5979 = (

let uu____5982 = (

let uu____5983 = (

let uu____5998 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (

let uu____6001 = (

let uu____6004 = (FStar_Syntax_Syntax.as_arg sc)
in (

let uu____6005 = (

let uu____6008 = (

let uu____6009 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____6009))
in (uu____6008)::[])
in (uu____6004)::uu____6005))
in ((uu____5998), (uu____6001))))
in FStar_Syntax_Syntax.Tm_app (uu____5983))
in (FStar_Syntax_Syntax.mk uu____5982))
in (uu____5979 FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
in (

let p2 = (

let uu____6020 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p1), (false)))::[])))) uu____6020))
in FStar_Pervasives_Native.Some (((sc1), (p2))))))
end
| (FStar_Syntax_Syntax.Tm_app (uu____6051, args), FStar_Syntax_Syntax.Pat_cons (uu____6053, pats)) -> begin
(

let tupn = (

let uu____6092 = (FStar_Parser_Const.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____6092 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____6102 = (

let uu____6103 = (

let uu____6118 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (

let uu____6121 = (

let uu____6130 = (

let uu____6139 = (

let uu____6140 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____6140))
in (uu____6139)::[])
in (FStar_List.append args uu____6130))
in ((uu____6118), (uu____6121))))
in FStar_Syntax_Syntax.Tm_app (uu____6103))
in (mk1 uu____6102))
in (

let p2 = (

let uu____6160 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p1), (false)))::[])))))) uu____6160))
in FStar_Pervasives_Native.Some (((sc1), (p2))))))
end
| uu____6195 -> begin
(failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt1)))
end)
in (match (uu____5812) with
| (b1, sc_pat_opt1) -> begin
(aux env2 ((b1)::bs) sc_pat_opt1 rest)
end)))
end))
end))
in (aux env [] FStar_Pervasives_Native.None binders2))))
end)))
end
| FStar_Parser_AST.App (uu____6262, uu____6263, FStar_Parser_AST.UnivApp) -> begin
(

let rec aux = (fun universes e -> (

let uu____6277 = (

let uu____6278 = (unparen e)
in uu____6278.FStar_Parser_AST.tm)
in (match (uu____6277) with
| FStar_Parser_AST.App (e1, t, FStar_Parser_AST.UnivApp) -> begin
(

let univ_arg = (desugar_universe t)
in (aux ((univ_arg)::universes) e1))
end
| uu____6284 -> begin
(

let head1 = (desugar_term env e)
in (mk1 (FStar_Syntax_Syntax.Tm_uinst (((head1), (universes))))))
end)))
in (aux [] top))
end
| FStar_Parser_AST.App (uu____6288) -> begin
(

let rec aux = (fun args e -> (

let uu____6320 = (

let uu____6321 = (unparen e)
in uu____6321.FStar_Parser_AST.tm)
in (match (uu____6320) with
| FStar_Parser_AST.App (e1, t, imp) when (imp <> FStar_Parser_AST.UnivApp) -> begin
(

let arg = (

let uu____6334 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) uu____6334))
in (aux ((arg)::args) e1))
end
| uu____6347 -> begin
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

let uu____6373 = (

let uu____6374 = (FStar_Ident.lid_of_path (("bind")::[]) x.FStar_Ident.idRange)
in FStar_Parser_AST.Var (uu____6374))
in (FStar_Parser_AST.mk_term uu____6373 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let uu____6375 = (FStar_Parser_AST.mkExplicitApp bind1 ((t1)::(k)::[]) top.FStar_Parser_AST.range)
in (desugar_term env uu____6375)))))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(

let uu____6378 = (

let uu____6379 = (

let uu____6386 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((uu____6386), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))
in FStar_Syntax_Syntax.Tm_meta (uu____6379))
in (mk1 uu____6378))
end
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(

let env1 = (FStar_ToSyntax_Env.push_namespace env lid)
in (

let uu____6404 = (

let uu____6409 = (FStar_ToSyntax_Env.expect_typ env1)
in (match (uu____6409) with
| true -> begin
desugar_typ
end
| uu____6414 -> begin
desugar_term
end))
in (uu____6404 env1 e)))
end
| FStar_Parser_AST.Let (qual1, ((pat, _snd))::_tl, body) -> begin
(

let is_rec = (qual1 = FStar_Parser_AST.Rec)
in (

let ds_let_rec_or_app = (fun uu____6442 -> (

let bindings = (((pat), (_snd)))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun uu____6528 -> (match (uu____6528) with
| (p, def) -> begin
(

let uu____6553 = (is_app_pattern p)
in (match (uu____6553) with
| true -> begin
(

let uu____6572 = (destruct_app_pattern env top_level p)
in ((uu____6572), (def)))
end
| uu____6601 -> begin
(match ((FStar_Parser_AST.un_function p def)) with
| FStar_Pervasives_Native.Some (p1, def1) -> begin
(

let uu____6626 = (destruct_app_pattern env top_level p1)
in ((uu____6626), (def1)))
end
| uu____6655 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, uu____6681); FStar_Parser_AST.prange = uu____6682}, t) -> begin
(match (top_level) with
| true -> begin
(

let uu____6706 = (

let uu____6721 = (

let uu____6726 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (uu____6726))
in ((uu____6721), ([]), (FStar_Pervasives_Native.Some (t))))
in ((uu____6706), (def)))
end
| uu____6749 -> begin
((((FStar_Util.Inl (id)), ([]), (FStar_Pervasives_Native.Some (t)))), (def))
end)
end
| FStar_Parser_AST.PatVar (id, uu____6773) -> begin
(match (top_level) with
| true -> begin
(

let uu____6796 = (

let uu____6811 = (

let uu____6816 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (uu____6816))
in ((uu____6811), ([]), (FStar_Pervasives_Native.None)))
in ((uu____6796), (def)))
end
| uu____6839 -> begin
((((FStar_Util.Inl (id)), ([]), (FStar_Pervasives_Native.None))), (def))
end)
end
| uu____6862 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end))
end))))
in (

let uu____6881 = (FStar_List.fold_left (fun uu____6941 uu____6942 -> (match (((uu____6941), (uu____6942))) with
| ((env1, fnames, rec_bindings), ((f, uu____7025, uu____7026), uu____7027)) -> begin
(

let uu____7106 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let uu____7132 = (FStar_ToSyntax_Env.push_bv env1 x)
in (match (uu____7132) with
| (env2, xx) -> begin
(

let uu____7151 = (

let uu____7154 = (FStar_Syntax_Syntax.mk_binder xx)
in (uu____7154)::rec_bindings)
in ((env2), (FStar_Util.Inl (xx)), (uu____7151)))
end))
end
| FStar_Util.Inr (l) -> begin
(

let uu____7162 = (FStar_ToSyntax_Env.push_top_level_rec_binding env1 l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in ((uu____7162), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (uu____7106) with
| (env2, lbname, rec_bindings1) -> begin
((env2), ((lbname)::fnames), (rec_bindings1))
end))
end)) ((env), ([]), ([])) funs)
in (match (uu____6881) with
| (env', fnames, rec_bindings) -> begin
(

let fnames1 = (FStar_List.rev fnames)
in (

let rec_bindings1 = (FStar_List.rev rec_bindings)
in (

let desugar_one_def = (fun env1 lbname uu____7288 -> (match (uu____7288) with
| ((uu____7311, args, result_t), def) -> begin
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

let uu____7355 = (is_comp_type env1 t)
in (match (uu____7355) with
| true -> begin
((

let uu____7357 = (FStar_All.pipe_right args1 (FStar_List.tryFind (fun x -> (

let uu____7367 = (is_var_pattern x)
in (not (uu____7367))))))
in (match (uu____7357) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (p) -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable"), (p.FStar_Parser_AST.prange)))))
end));
t;
)
end
| uu____7369 -> begin
(

let uu____7370 = (((FStar_Options.ml_ish ()) && (

let uu____7372 = (FStar_ToSyntax_Env.try_lookup_effect_name env1 FStar_Parser_Const.effect_ML_lid)
in (FStar_Option.isSome uu____7372))) && ((not (is_rec)) || ((FStar_List.length args1) <> (Prims.parse_int "0"))))
in (match (uu____7370) with
| true -> begin
(FStar_Parser_AST.ml_comp t)
end
| uu____7375 -> begin
(FStar_Parser_AST.tot_comp t)
end))
end))
in (

let uu____7376 = (FStar_Range.union_ranges t1.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t1), (FStar_Pervasives_Native.None)))) uu____7376 FStar_Parser_AST.Expr)))
end)
in (

let def2 = (match (args1) with
| [] -> begin
def1
end
| uu____7380 -> begin
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

let uu____7395 = (

let uu____7396 = (FStar_Syntax_Util.incr_delta_qualifier body1)
in (FStar_Syntax_Syntax.lid_as_fv l uu____7396 FStar_Pervasives_Native.None))
in FStar_Util.Inr (uu____7395))
end)
in (

let body2 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.close rec_bindings1 body1)
end
| uu____7398 -> begin
body1
end)
in (mk_lb ((lbname1), (FStar_Syntax_Syntax.tun), (body2)))))))))
end))
in (

let lbs = (FStar_List.map2 (desugar_one_def (match (is_rec) with
| true -> begin
env'
end
| uu____7428 -> begin
env
end)) fnames1 funs)
in (

let body1 = (desugar_term env' body)
in (

let uu____7430 = (

let uu____7431 = (

let uu____7444 = (FStar_Syntax_Subst.close rec_bindings1 body1)
in ((((is_rec), (lbs))), (uu____7444)))
in FStar_Syntax_Syntax.Tm_let (uu____7431))
in (FStar_All.pipe_left mk1 uu____7430)))))))
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
| uu____7474 -> begin
t11
end)
in (

let uu____7475 = (desugar_binding_pat_maybe_top top_level env pat1 is_mutable)
in (match (uu____7475) with
| (env1, binder, pat2) -> begin
(

let tm = (match (binder) with
| LetBinder (l, t) -> begin
(

let body1 = (desugar_term env1 t2)
in (

let fv = (

let uu____7502 = (FStar_Syntax_Util.incr_delta_qualifier t12)
in (FStar_Syntax_Syntax.lid_as_fv l uu____7502 FStar_Pervasives_Native.None))
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_let (((((false), (({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t12})::[]))), (body1)))))))
end
| LocalBinder (x, uu____7514) -> begin
(

let body1 = (desugar_term env1 t2)
in (

let body2 = (match (pat2) with
| [] -> begin
body1
end
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (uu____7517); FStar_Syntax_Syntax.p = uu____7518})::[] -> begin
body1
end
| uu____7523 -> begin
(

let uu____7526 = (

let uu____7529 = (

let uu____7530 = (

let uu____7553 = (FStar_Syntax_Syntax.bv_to_name x)
in (

let uu____7554 = (desugar_disjunctive_pattern pat2 FStar_Pervasives_Native.None body1)
in ((uu____7553), (uu____7554))))
in FStar_Syntax_Syntax.Tm_match (uu____7530))
in (FStar_Syntax_Syntax.mk uu____7529))
in (uu____7526 FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
end)
in (

let uu____7564 = (

let uu____7565 = (

let uu____7578 = (

let uu____7579 = (

let uu____7580 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____7580)::[])
in (FStar_Syntax_Subst.close uu____7579 body2))
in ((((false), (((mk_lb ((FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t12))))::[]))), (uu____7578)))
in FStar_Syntax_Syntax.Tm_let (uu____7565))
in (FStar_All.pipe_left mk1 uu____7564))))
end)
in (match (is_mutable) with
| true -> begin
(FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((tm), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc))))))
end
| uu____7605 -> begin
tm
end))
end))))))
in (

let uu____7606 = (is_rec || (is_app_pattern pat))
in (match (uu____7606) with
| true -> begin
(ds_let_rec_or_app ())
end
| uu____7607 -> begin
(ds_non_rec pat _snd body)
end)))))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (

let t_bool1 = (

let uu____7615 = (

let uu____7616 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Syntax_Syntax.Tm_fvar (uu____7616))
in (mk1 uu____7615))
in (

let uu____7617 = (

let uu____7618 = (

let uu____7641 = (

let uu____7644 = (desugar_term env t1)
in (FStar_Syntax_Util.ascribe uu____7644 ((FStar_Util.Inl (t_bool1)), (FStar_Pervasives_Native.None))))
in (

let uu____7665 = (

let uu____7680 = (

let uu____7693 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) t2.FStar_Parser_AST.range)
in (

let uu____7696 = (desugar_term env t2)
in ((uu____7693), (FStar_Pervasives_Native.None), (uu____7696))))
in (

let uu____7705 = (

let uu____7720 = (

let uu____7733 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) t3.FStar_Parser_AST.range)
in (

let uu____7736 = (desugar_term env t3)
in ((uu____7733), (FStar_Pervasives_Native.None), (uu____7736))))
in (uu____7720)::[])
in (uu____7680)::uu____7705))
in ((uu____7641), (uu____7665))))
in FStar_Syntax_Syntax.Tm_match (uu____7618))
in (mk1 uu____7617))))
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

let desugar_branch = (fun uu____7877 -> (match (uu____7877) with
| (pat, wopt, b) -> begin
(

let uu____7895 = (desugar_match_pat env pat)
in (match (uu____7895) with
| (env1, pat1) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (e1) -> begin
(

let uu____7916 = (desugar_term env1 e1)
in FStar_Pervasives_Native.Some (uu____7916))
end)
in (

let b1 = (desugar_term env1 b)
in (desugar_disjunctive_pattern pat1 wopt1 b1)))
end))
end))
in (

let uu____7918 = (

let uu____7919 = (

let uu____7942 = (desugar_term env e)
in (

let uu____7943 = (FStar_List.collect desugar_branch branches)
in ((uu____7942), (uu____7943))))
in FStar_Syntax_Syntax.Tm_match (uu____7919))
in (FStar_All.pipe_left mk1 uu____7918)))
end
| FStar_Parser_AST.Ascribed (e, t, tac_opt) -> begin
(

let annot = (

let uu____7972 = (is_comp_type env t)
in (match (uu____7972) with
| true -> begin
(

let uu____7979 = (desugar_comp t.FStar_Parser_AST.range env t)
in FStar_Util.Inr (uu____7979))
end
| uu____7984 -> begin
(

let uu____7985 = (desugar_term env t)
in FStar_Util.Inl (uu____7985))
end))
in (

let tac_opt1 = (FStar_Util.map_opt tac_opt (desugar_term env))
in (

let uu____7991 = (

let uu____7992 = (

let uu____8019 = (desugar_term env e)
in ((uu____8019), (((annot), (tac_opt1))), (FStar_Pervasives_Native.None)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____7992))
in (FStar_All.pipe_left mk1 uu____7991))))
end
| FStar_Parser_AST.Record (uu____8044, []) -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let record = (check_fields env fields top.FStar_Parser_AST.range)
in (

let user_ns = (

let uu____8081 = (FStar_List.hd fields)
in (match (uu____8081) with
| (f, uu____8093) -> begin
f.FStar_Ident.ns
end))
in (

let get_field = (fun xopt f -> (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun uu____8135 -> (match (uu____8135) with
| (g, uu____8141) -> begin
(f.FStar_Ident.idText = g.FStar_Ident.ident.FStar_Ident.idText)
end))))
in (

let fn = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((f)::[])))
in (match (found) with
| FStar_Pervasives_Native.Some (uu____8147, e) -> begin
((fn), (e))
end
| FStar_Pervasives_Native.None -> begin
(match (xopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8161 = (

let uu____8162 = (

let uu____8167 = (FStar_Util.format2 "Field %s of record type %s is missing" f.FStar_Ident.idText record.FStar_ToSyntax_Env.typename.FStar_Ident.str)
in ((uu____8167), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____8162))
in (FStar_Exn.raise uu____8161))
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

let uu____8175 = (

let uu____8186 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____8217 -> (match (uu____8217) with
| (f, uu____8227) -> begin
(

let uu____8228 = (

let uu____8229 = (get_field FStar_Pervasives_Native.None f)
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____8229))
in ((uu____8228), (FStar_Parser_AST.Nothing)))
end))))
in ((user_constrname), (uu____8186)))
in FStar_Parser_AST.Construct (uu____8175))
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (

let uu____8247 = (

let uu____8248 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____8248))
in (FStar_Parser_AST.mk_term uu____8247 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record1 = (

let uu____8250 = (

let uu____8263 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____8293 -> (match (uu____8293) with
| (f, uu____8303) -> begin
(get_field (FStar_Pervasives_Native.Some (xterm)) f)
end))))
in ((FStar_Pervasives_Native.None), (uu____8263)))
in FStar_Parser_AST.Record (uu____8250))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (FStar_Pervasives_Native.None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record1 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm1 = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_term env recterm1)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____8331; FStar_Syntax_Syntax.vars = uu____8332}, args); FStar_Syntax_Syntax.pos = uu____8334; FStar_Syntax_Syntax.vars = uu____8335}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(

let e1 = (

let uu____8363 = (

let uu____8364 = (

let uu____8379 = (

let uu____8380 = (

let uu____8383 = (

let uu____8384 = (

let uu____8391 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map FStar_Pervasives_Native.fst))
in ((record.FStar_ToSyntax_Env.typename), (uu____8391)))
in FStar_Syntax_Syntax.Record_ctor (uu____8384))
in FStar_Pervasives_Native.Some (uu____8383))
in (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant uu____8380))
in ((uu____8379), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____8364))
in (FStar_All.pipe_left mk1 uu____8363))
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((e1), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))))))
end
| uu____8422 -> begin
e
end))))))))
end
| FStar_Parser_AST.Project (e, f) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f);
(

let uu____8426 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f)
in (match (uu____8426) with
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
| uu____8444 -> begin
FStar_Pervasives_Native.None
end)
in (

let uu____8445 = (

let uu____8446 = (

let uu____8461 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projname (FStar_Ident.range_of_lid f)) FStar_Syntax_Syntax.Delta_equational qual1)
in (

let uu____8462 = (

let uu____8465 = (FStar_Syntax_Syntax.as_arg e1)
in (uu____8465)::[])
in ((uu____8461), (uu____8462))))
in FStar_Syntax_Syntax.Tm_app (uu____8446))
in (FStar_All.pipe_left mk1 uu____8445)))))
end));
)
end
| FStar_Parser_AST.NamedTyp (uu____8470, e) -> begin
(desugar_term env e)
end
| FStar_Parser_AST.Paren (e) -> begin
(desugar_term env e)
end
| uu____8473 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| uu____8474 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Let (uu____8475, uu____8476, uu____8477) -> begin
(failwith "Not implemented yet")
end
| FStar_Parser_AST.QForall (uu____8490, uu____8491, uu____8492) -> begin
(failwith "Not implemented yet")
end
| FStar_Parser_AST.QExists (uu____8505, uu____8506, uu____8507) -> begin
(failwith "Not implemented yet")
end)))))
and not_ascribed : FStar_Parser_AST.term  ->  Prims.bool = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Ascribed (uu____8521) -> begin
false
end
| uu____8530 -> begin
true
end))
and is_synth_by_tactic : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun e t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (l, r, FStar_Parser_AST.Hash) -> begin
(is_synth_by_tactic e l)
end
| FStar_Parser_AST.Var (lid) -> begin
(

let uu____8536 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name e lid)
in (match (uu____8536) with
| FStar_Pervasives_Native.Some (lid1) -> begin
(FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid)
end
| FStar_Pervasives_Native.None -> begin
false
end))
end
| uu____8540 -> begin
false
end))
and desugar_args : FStar_ToSyntax_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____8577 -> (match (uu____8577) with
| (a, imp) -> begin
(

let uu____8590 = (desugar_term env a)
in (arg_withimp_e imp uu____8590))
end)))))
and desugar_comp : FStar_Range.range  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun r env t -> (

let fail = (fun msg -> (FStar_Exn.raise (FStar_Errors.Error (((msg), (r))))))
in (

let is_requires = (fun uu____8609 -> (match (uu____8609) with
| (t1, uu____8615) -> begin
(

let uu____8616 = (

let uu____8617 = (unparen t1)
in uu____8617.FStar_Parser_AST.tm)
in (match (uu____8616) with
| FStar_Parser_AST.Requires (uu____8618) -> begin
true
end
| uu____8625 -> begin
false
end))
end))
in (

let is_ensures = (fun uu____8633 -> (match (uu____8633) with
| (t1, uu____8639) -> begin
(

let uu____8640 = (

let uu____8641 = (unparen t1)
in uu____8641.FStar_Parser_AST.tm)
in (match (uu____8640) with
| FStar_Parser_AST.Ensures (uu____8642) -> begin
true
end
| uu____8649 -> begin
false
end))
end))
in (

let is_app = (fun head1 uu____8660 -> (match (uu____8660) with
| (t1, uu____8666) -> begin
(

let uu____8667 = (

let uu____8668 = (unparen t1)
in uu____8668.FStar_Parser_AST.tm)
in (match (uu____8667) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = uu____8670; FStar_Parser_AST.level = uu____8671}, uu____8672, uu____8673) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head1)
end
| uu____8674 -> begin
false
end))
end))
in (

let is_smt_pat = (fun uu____8682 -> (match (uu____8682) with
| (t1, uu____8688) -> begin
(

let uu____8689 = (

let uu____8690 = (unparen t1)
in uu____8690.FStar_Parser_AST.tm)
in (match (uu____8689) with
| FStar_Parser_AST.Construct (cons1, (({FStar_Parser_AST.tm = FStar_Parser_AST.Construct (smtpat, uu____8693); FStar_Parser_AST.range = uu____8694; FStar_Parser_AST.level = uu____8695}, uu____8696))::(uu____8697)::[]) -> begin
((FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid) && (FStar_Util.for_some (fun s -> (smtpat.FStar_Ident.str = s)) (("SMTPat")::("SMTPatT")::("SMTPatOr")::[])))
end
| FStar_Parser_AST.Construct (cons1, (({FStar_Parser_AST.tm = FStar_Parser_AST.Var (smtpat); FStar_Parser_AST.range = uu____8736; FStar_Parser_AST.level = uu____8737}, uu____8738))::(uu____8739)::[]) -> begin
((FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid) && (FStar_Util.for_some (fun s -> (smtpat.FStar_Ident.str = s)) (("smt_pat")::("smt_pat_or")::[])))
end
| uu____8764 -> begin
false
end))
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t1 -> (

let uu____8792 = (head_and_args t1)
in (match (uu____8792) with
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
(FStar_Exn.raise (FStar_Errors.Error ((("Not enough arguments to \'Lemma\'"), (t1.FStar_Parser_AST.range)))))
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

let uu____9201 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes env) l)
in ((uu____9201), (args)))
end
| FStar_Parser_AST.Name (l) when ((

let uu____9229 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals uu____9229 FStar_Parser_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Parser_Const.effect_Tot_lid head1.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when ((

let uu____9247 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals uu____9247 FStar_Parser_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Parser_Const.effect_GTot_lid head1.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when (((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) -> begin
(((((FStar_Ident.set_lid_range FStar_Parser_Const.effect_Tot_lid head1.FStar_Parser_AST.range)), ([]))), ((((t1), (FStar_Parser_AST.Nothing)))::[]))
end
| uu____9285 -> begin
(

let default_effect = (

let uu____9287 = (FStar_Options.ml_ish ())
in (match (uu____9287) with
| true -> begin
FStar_Parser_Const.effect_ML_lid
end
| uu____9288 -> begin
((

let uu____9290 = (FStar_Options.warn_default_effects ())
in (match (uu____9290) with
| true -> begin
(FStar_Errors.warn head1.FStar_Parser_AST.range "Using default effect Tot")
end
| uu____9291 -> begin
()
end));
FStar_Parser_Const.effect_Tot_lid;
)
end))
in (((((FStar_Ident.set_lid_range default_effect head1.FStar_Parser_AST.range)), ([]))), ((((t1), (FStar_Parser_AST.Nothing)))::[])))
end)
end)))
in (

let uu____9314 = (pre_process_comp_typ t)
in (match (uu____9314) with
| ((eff, cattributes), args) -> begin
((match (((FStar_List.length args) = (Prims.parse_int "0"))) with
| true -> begin
(

let uu____9363 = (

let uu____9364 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" uu____9364))
in (fail uu____9363))
end
| uu____9365 -> begin
()
end);
(

let is_universe = (fun uu____9373 -> (match (uu____9373) with
| (uu____9378, imp) -> begin
(imp = FStar_Parser_AST.UnivApp)
end))
in (

let uu____9380 = (FStar_Util.take is_universe args)
in (match (uu____9380) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun uu____9439 -> (match (uu____9439) with
| (u, imp) -> begin
(desugar_universe u)
end)) universes)
in (

let uu____9446 = (

let uu____9461 = (FStar_List.hd args1)
in (

let uu____9470 = (FStar_List.tl args1)
in ((uu____9461), (uu____9470))))
in (match (uu____9446) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (FStar_Pervasives_Native.fst result_arg))
in (

let rest1 = (desugar_args env rest)
in (

let uu____9525 = (

let is_decrease = (fun uu____9561 -> (match (uu____9561) with
| (t1, uu____9571) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____9581; FStar_Syntax_Syntax.vars = uu____9582}, (uu____9583)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.decreases_lid)
end
| uu____9614 -> begin
false
end)
end))
in (FStar_All.pipe_right rest1 (FStar_List.partition is_decrease)))
in (match (uu____9525) with
| (dec, rest2) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun uu____9728 -> (match (uu____9728) with
| (t1, uu____9738) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____9747, ((arg, uu____9749))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| uu____9778 -> begin
(failwith "impos")
end)
end))))
in (

let no_additional_args = (

let is_empty = (fun l -> (match (l) with
| [] -> begin
true
end
| uu____9792 -> begin
false
end))
in ((((is_empty decreases_clause) && (is_empty rest2)) && (is_empty cattributes)) && (is_empty universes1)))
in (match ((no_additional_args && (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid))) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end
| uu____9805 -> begin
(match ((no_additional_args && (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid))) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end
| uu____9808 -> begin
(

let flags = (match ((FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Lemma_lid)) with
| true -> begin
(FStar_Syntax_Syntax.LEMMA)::[]
end
| uu____9814 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____9817 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Parser_Const.effect_ML_lid)) with
| true -> begin
(FStar_Syntax_Syntax.MLEFFECT)::[]
end
| uu____9820 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____9823 -> begin
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
| uu____9940 -> begin
pat
end)
in (

let uu____9941 = (

let uu____9952 = (

let uu____9963 = (

let uu____9972 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat1), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) FStar_Pervasives_Native.None pat1.FStar_Syntax_Syntax.pos)
in ((uu____9972), (aq)))
in (uu____9963)::[])
in (ens)::uu____9952)
in (req)::uu____9941))
end
| uu____10013 -> begin
rest2
end)
end
| uu____10024 -> begin
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
| uu____10035 -> begin
FStar_Pervasives_Native.None
end))
in (

let mk1 = (fun t -> (FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let uu___242_10052 = t
in {FStar_Syntax_Syntax.n = uu___242_10052.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___242_10052.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let uu___243_10086 = b
in {FStar_Parser_AST.b = uu___243_10086.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___243_10086.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___243_10086.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env1 pats1 -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (

let uu____10145 = (desugar_term env1 e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) uu____10145)))))) pats1))
in (match (tk) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____10158 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____10158) with
| (env1, a1) -> begin
(

let a2 = (

let uu___244_10168 = a1
in {FStar_Syntax_Syntax.ppname = uu___244_10168.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___244_10168.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats1 = (desugar_pats env1 pats)
in (

let body1 = (desugar_formula env1 body)
in (

let body2 = (match (pats1) with
| [] -> begin
body1
end
| uu____10190 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_meta (((body1), (FStar_Syntax_Syntax.Meta_pattern (pats1))))))
end)
in (

let body3 = (

let uu____10204 = (

let uu____10207 = (

let uu____10208 = (FStar_Syntax_Syntax.mk_binder a2)
in (uu____10208)::[])
in (no_annot_abs uu____10207 body2))
in (FStar_All.pipe_left setpos uu____10204))
in (

let uu____10213 = (

let uu____10214 = (

let uu____10229 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let uu____10230 = (

let uu____10233 = (FStar_Syntax_Syntax.as_arg body3)
in (uu____10233)::[])
in ((uu____10229), (uu____10230))))
in FStar_Syntax_Syntax.Tm_app (uu____10214))
in (FStar_All.pipe_left mk1 uu____10213)))))))
end))
end
| uu____10238 -> begin
(failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body1 = (

let uu____10310 = (q ((rest), (pats), (body)))
in (

let uu____10317 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term uu____10310 uu____10317 FStar_Parser_AST.Formula)))
in (

let uu____10318 = (q (((b)::[]), ([]), (body1)))
in (FStar_Parser_AST.mk_term uu____10318 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| uu____10327 -> begin
(failwith "impossible")
end))
in (

let uu____10330 = (

let uu____10331 = (unparen f)
in uu____10331.FStar_Parser_AST.tm)
in (match (uu____10330) with
| FStar_Parser_AST.Labeled (f1, l, p) -> begin
(

let f2 = (desugar_formula env f1)
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((f2), (FStar_Syntax_Syntax.Meta_labeled (((l), (f2.FStar_Syntax_Syntax.pos), (p)))))))))
end
| FStar_Parser_AST.QForall ([], uu____10338, uu____10339) -> begin
(failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QExists ([], uu____10350, uu____10351) -> begin
(failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____10382 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env uu____10382)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____10418 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env uu____10418)))
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
| uu____10461 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_ToSyntax_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list) = (fun env bs -> (

let uu____10466 = (FStar_List.fold_left (fun uu____10502 b -> (match (uu____10502) with
| (env1, out) -> begin
(

let tk = (desugar_binder env1 (

let uu___245_10554 = b
in {FStar_Parser_AST.b = uu___245_10554.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___245_10554.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___245_10554.FStar_Parser_AST.aqual}))
in (match (tk) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____10571 = (FStar_ToSyntax_Env.push_bv env1 a)
in (match (uu____10571) with
| (env2, a1) -> begin
(

let a2 = (

let uu___246_10591 = a1
in {FStar_Syntax_Syntax.ppname = uu___246_10591.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___246_10591.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in ((env2), ((((a2), ((trans_aqual b.FStar_Parser_AST.aqual))))::out)))
end))
end
| uu____10608 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (uu____10466) with
| (env1, tpars) -> begin
((env1), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.TAnnotated (x, t) -> begin
(

let uu____10695 = (desugar_typ env t)
in ((FStar_Pervasives_Native.Some (x)), (uu____10695)))
end
| FStar_Parser_AST.Annotated (x, t) -> begin
(

let uu____10700 = (desugar_typ env t)
in ((FStar_Pervasives_Native.Some (x)), (uu____10700)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____10704 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) FStar_Pervasives_Native.None x.FStar_Ident.idRange)
in ((FStar_Pervasives_Native.Some (x)), (uu____10704)))
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____10712 = (desugar_typ env t)
in ((FStar_Pervasives_Native.None), (uu____10712)))
end
| FStar_Parser_AST.Variable (x) -> begin
((FStar_Pervasives_Native.Some (x)), (FStar_Syntax_Syntax.tun))
end))


let mk_data_discriminators : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_ToSyntax_Env.env  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun quals env datas -> (

let quals1 = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___216_10748 -> (match (uu___216_10748) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____10749 -> begin
false
end))))
in (

let quals2 = (fun q -> (

let uu____10760 = ((

let uu____10763 = (FStar_ToSyntax_Env.iface env)
in (not (uu____10763))) || (FStar_ToSyntax_Env.admitted_iface env))
in (match (uu____10760) with
| true -> begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals1)
end
| uu____10766 -> begin
(FStar_List.append q quals1)
end)))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (

let uu____10776 = (quals2 ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((disc_name), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid disc_name); FStar_Syntax_Syntax.sigquals = uu____10776; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))))))))


let mk_indexed_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  FStar_ToSyntax_Env.env  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq env lid fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let uu____10812 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____10842 -> (match (uu____10842) with
| (x, uu____10850) -> begin
(

let uu____10851 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____10851) with
| (field_name, uu____10859) -> begin
(

let only_decl = (((

let uu____10863 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____10863)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (

let uu____10865 = (

let uu____10866 = (FStar_ToSyntax_Env.current_module env)
in uu____10866.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____10865)))
in (

let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____10880 = (FStar_List.filter (fun uu___217_10884 -> (match (uu___217_10884) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____10885 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____10880)
end
| uu____10886 -> begin
q
end))
in (

let quals1 = (

let iquals1 = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___218_10898 -> (match (uu___218_10898) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____10899 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals1)))
in (

let decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid field_name); FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____10905 -> begin
(

let dd = (

let uu____10907 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____10907) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____10910 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lb = (

let uu____10912 = (

let uu____10917 = (FStar_Syntax_Syntax.lid_as_fv field_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____10917))
in {FStar_Syntax_Syntax.lbname = uu____10912; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = FStar_Syntax_Syntax.tun})
in (

let impl = (

let uu____10919 = (

let uu____10920 = (

let uu____10927 = (

let uu____10930 = (

let uu____10931 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____10931 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____10930)::[])
in ((((false), ((lb)::[]))), (uu____10927)))
in FStar_Syntax_Syntax.Sig_let (uu____10920))
in {FStar_Syntax_Syntax.sigel = uu____10919; FStar_Syntax_Syntax.sigrng = p; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____10950 -> begin
(decl)::(impl)::[]
end))))
end))))))
end))
end))))
in (FStar_All.pipe_right uu____10812 FStar_List.flatten))))


let mk_data_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_ToSyntax_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____10978, t, uu____10980, n1, uu____10982) when (not ((FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid))) -> begin
(

let uu____10987 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____10987) with
| (formals, uu____11003) -> begin
(match (formals) with
| [] -> begin
[]
end
| uu____11026 -> begin
(

let filter_records = (fun uu___219_11038 -> (match (uu___219_11038) with
| FStar_Syntax_Syntax.RecordConstructor (uu____11041, fns) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| uu____11053 -> begin
FStar_Pervasives_Native.None
end))
in (

let fv_qual = (

let uu____11055 = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals filter_records)
in (match (uu____11055) with
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
| uu____11064 -> begin
iquals
end)
in (

let uu____11065 = (FStar_Util.first_N n1 formals)
in (match (uu____11065) with
| (uu____11088, rest) -> begin
(mk_indexed_projector_names iquals1 fv_qual env lid rest)
end)))))
end)
end))
end
| uu____11114 -> begin
[]
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (

let dd = (

let uu____11172 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____11172) with
| true -> begin
(

let uu____11175 = (FStar_Syntax_Util.incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (uu____11175))
end
| uu____11176 -> begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end))
in (

let lb = (

let uu____11178 = (

let uu____11183 = (FStar_Syntax_Syntax.lid_as_fv lid dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____11183))
in (

let uu____11184 = (

let uu____11187 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars uu____11187))
in (

let uu____11190 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = uu____11178; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____11184; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____11190})))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (lids))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))


let rec desugar_tycon : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d quals tcs -> (

let rng = d.FStar_Parser_AST.drange
in (

let tycon_id = (fun uu___220_11239 -> (match (uu___220_11239) with
| FStar_Parser_AST.TyconAbstract (id, uu____11241, uu____11242) -> begin
id
end
| FStar_Parser_AST.TyconAbbrev (id, uu____11252, uu____11253, uu____11254) -> begin
id
end
| FStar_Parser_AST.TyconRecord (id, uu____11264, uu____11265, uu____11266) -> begin
id
end
| FStar_Parser_AST.TyconVariant (id, uu____11296, uu____11297, uu____11298) -> begin
id
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (x, uu____11340) -> begin
(

let uu____11341 = (

let uu____11342 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____11342))
in (FStar_Parser_AST.mk_term uu____11341 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| FStar_Parser_AST.Variable (x) -> begin
(

let uu____11344 = (

let uu____11345 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____11345))
in (FStar_Parser_AST.mk_term uu____11344 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| FStar_Parser_AST.TAnnotated (a, uu____11347) -> begin
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
| uu____11370 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (

let uu____11376 = (

let uu____11377 = (

let uu____11384 = (binder_to_term b)
in ((out), (uu____11384), ((imp_of_aqual b))))
in FStar_Parser_AST.App (uu____11377))
in (FStar_Parser_AST.mk_term uu____11376 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun uu___221_11394 -> (match (uu___221_11394) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun uu____11449 -> (match (uu____11449) with
| (x, t, uu____11460) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Syntax_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr FStar_Pervasives_Native.None)
end)) fields)
in (

let result = (

let uu____11466 = (

let uu____11467 = (

let uu____11468 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (uu____11468))
in (FStar_Parser_AST.mk_term uu____11467 id.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____11466 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type_level)
in (

let uu____11472 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____11499 -> (match (uu____11499) with
| (x, uu____11509, uu____11510) -> begin
(FStar_Syntax_Util.unmangle_field_name x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (FStar_Pervasives_Native.Some (constrTyp)), (FStar_Pervasives_Native.None), (false)))::[])))), (uu____11472)))))))
end
| uu____11563 -> begin
(failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals1 _env mutuals uu___222_11594 -> (match (uu___222_11594) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let uu____11618 = (typars_of_binders _env binders)
in (match (uu____11618) with
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

let uu____11664 = (

let uu____11665 = (

let uu____11666 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (uu____11666))
in (FStar_Parser_AST.mk_term uu____11665 id.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____11664 binders))
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
| uu____11679 -> begin
(failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env1 bs -> (

let uu____11723 = (FStar_List.fold_left (fun uu____11763 uu____11764 -> (match (((uu____11763), (uu____11764))) with
| ((env2, tps), (x, imp)) -> begin
(

let uu____11855 = (FStar_ToSyntax_Env.push_bv env2 x.FStar_Syntax_Syntax.ppname)
in (match (uu____11855) with
| (env3, y) -> begin
((env3), ((((y), (imp)))::tps))
end))
end)) ((env1), ([])) bs)
in (match (uu____11723) with
| (env2, bs1) -> begin
((env2), ((FStar_List.rev bs1)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id, bs, kopt))::[] -> begin
(

let kopt1 = (match (kopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____11968 = (tm_type_z id.FStar_Ident.idRange)
in FStar_Pervasives_Native.Some (uu____11968))
end
| uu____11969 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id), (bs), (kopt1)))
in (

let uu____11977 = (desugar_abstract_tc quals env [] tc)
in (match (uu____11977) with
| (uu____11990, uu____11991, se, uu____11993) -> begin
(

let se1 = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, uu____11996, typars, k, [], []) -> begin
(

let quals1 = se.FStar_Syntax_Syntax.sigquals
in (

let quals2 = (match ((FStar_List.contains FStar_Syntax_Syntax.Assumption quals1)) with
| true -> begin
quals1
end
| uu____12011 -> begin
((

let uu____12013 = (

let uu____12014 = (FStar_Options.ml_ish ())
in (not (uu____12014)))
in (match (uu____12013) with
| true -> begin
(

let uu____12015 = (FStar_Range.string_of_range se.FStar_Syntax_Syntax.sigrng)
in (

let uu____12016 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" uu____12015 uu____12016)))
end
| uu____12017 -> begin
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
| uu____12023 -> begin
(

let uu____12024 = (

let uu____12027 = (

let uu____12028 = (

let uu____12041 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (uu____12041)))
in FStar_Syntax_Syntax.Tm_arrow (uu____12028))
in (FStar_Syntax_Syntax.mk uu____12027))
in (uu____12024 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
end)
in (

let uu___247_12045 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t))); FStar_Syntax_Syntax.sigrng = uu___247_12045.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = uu___247_12045.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___247_12045.FStar_Syntax_Syntax.sigattrs}))))
end
| uu____12048 -> begin
(failwith "Impossible")
end)
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env se1)
in (

let env2 = (

let uu____12051 = (FStar_ToSyntax_Env.qualify env1 id)
in (FStar_ToSyntax_Env.push_doc env1 uu____12051 d.FStar_Parser_AST.doc))
in ((env2), ((se1)::[])))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let uu____12066 = (typars_of_binders env binders)
in (match (uu____12066) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____12102 = (FStar_Util.for_some (fun uu___223_12104 -> (match (uu___223_12104) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| uu____12105 -> begin
false
end)) quals)
in (match (uu____12102) with
| true -> begin
FStar_Syntax_Syntax.teff
end
| uu____12106 -> begin
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

let uu____12112 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___224_12116 -> (match (uu___224_12116) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| uu____12117 -> begin
false
end))))
in (match (uu____12112) with
| true -> begin
quals
end
| uu____12120 -> begin
(match ((t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula)) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals
end
| uu____12123 -> begin
quals
end)
end))
in (

let qlid = (FStar_ToSyntax_Env.qualify env id)
in (

let se = (

let uu____12126 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Effect))
in (match (uu____12126) with
| true -> begin
(

let uu____12129 = (

let uu____12136 = (

let uu____12137 = (unparen t)
in uu____12137.FStar_Parser_AST.tm)
in (match (uu____12136) with
| FStar_Parser_AST.Construct (head1, args) -> begin
(

let uu____12158 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____12188))::args_rev -> begin
(

let uu____12200 = (

let uu____12201 = (unparen last_arg)
in uu____12201.FStar_Parser_AST.tm)
in (match (uu____12200) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____12229 -> begin
(([]), (args))
end))
end
| uu____12238 -> begin
(([]), (args))
end)
in (match (uu____12158) with
| (cattributes, args1) -> begin
(

let uu____12277 = (desugar_attributes env cattributes)
in (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((head1), (args1)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (uu____12277)))
end))
end
| uu____12288 -> begin
((t), ([]))
end))
in (match (uu____12129) with
| (t1, cattributes) -> begin
(

let c = (desugar_comp t1.FStar_Parser_AST.range env' t1)
in (

let typars1 = (FStar_Syntax_Subst.close_binders typars)
in (

let c1 = (FStar_Syntax_Subst.close_comp typars1 c)
in (

let quals2 = (FStar_All.pipe_right quals1 (FStar_List.filter (fun uu___225_12310 -> (match (uu___225_12310) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| uu____12311 -> begin
true
end))))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((qlid), ([]), (typars1), (c1), ((FStar_List.append cattributes (FStar_Syntax_Util.comp_flags c1))))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))))
end))
end
| uu____12316 -> begin
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
| (FStar_Parser_AST.TyconRecord (uu____12322))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let uu____12346 = (tycon_record_as_variant trec)
in (match (uu____12346) with
| (t, fs) -> begin
(

let uu____12363 = (

let uu____12366 = (

let uu____12367 = (

let uu____12376 = (

let uu____12379 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.ids_of_lid uu____12379))
in ((uu____12376), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____12367))
in (uu____12366)::quals)
in (desugar_tycon env d uu____12363 ((t)::[])))
end)))
end
| (uu____12384)::uu____12385 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals1 et tc -> (

let uu____12546 = et
in (match (uu____12546) with
| (env1, tcs1) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (uu____12771) -> begin
(

let trec = tc
in (

let uu____12795 = (tycon_record_as_variant trec)
in (match (uu____12795) with
| (t, fs) -> begin
(

let uu____12854 = (

let uu____12857 = (

let uu____12858 = (

let uu____12867 = (

let uu____12870 = (FStar_ToSyntax_Env.current_module env1)
in (FStar_Ident.ids_of_lid uu____12870))
in ((uu____12867), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____12858))
in (uu____12857)::quals1)
in (collect_tcs uu____12854 ((env1), (tcs1)) t))
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let uu____12957 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (uu____12957) with
| (env2, uu____13017, se, tconstr) -> begin
((env2), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals1))))::tcs1))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let uu____13166 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (uu____13166) with
| (env2, uu____13226, se, tconstr) -> begin
((env2), ((FStar_Util.Inr (((se), (binders), (t), (quals1))))::tcs1))
end))
end
| uu____13351 -> begin
(failwith "Unrecognized mutual type definition")
end)
end)))
in (

let uu____13398 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (uu____13398) with
| (env1, tcs1) -> begin
(

let tcs2 = (FStar_List.rev tcs1)
in (

let docs_tps_sigelts = (FStar_All.pipe_right tcs2 (FStar_List.collect (fun uu___227_13909 -> (match (uu___227_13909) with
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, uu____13976, uu____13977); FStar_Syntax_Syntax.sigrng = uu____13978; FStar_Syntax_Syntax.sigquals = uu____13979; FStar_Syntax_Syntax.sigmeta = uu____13980; FStar_Syntax_Syntax.sigattrs = uu____13981}, binders, t, quals1) -> begin
(

let t1 = (

let uu____14042 = (typars_of_binders env1 binders)
in (match (uu____14042) with
| (env2, tpars1) -> begin
(

let uu____14073 = (push_tparams env2 tpars1)
in (match (uu____14073) with
| (env_tps, tpars2) -> begin
(

let t1 = (desugar_typ env_tps t)
in (

let tpars3 = (FStar_Syntax_Subst.close_binders tpars2)
in (FStar_Syntax_Subst.close tpars3 t1)))
end))
end))
in (

let uu____14106 = (

let uu____14127 = (mk_typ_abbrev id uvs tpars k t1 ((id)::[]) quals1 rng)
in ((((id), (d.FStar_Parser_AST.doc))), ([]), (uu____14127)))
in (uu____14106)::[]))
end
| FStar_Util.Inl ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs1, tpars, k, mutuals1, uu____14195); FStar_Syntax_Syntax.sigrng = uu____14196; FStar_Syntax_Syntax.sigquals = tname_quals; FStar_Syntax_Syntax.sigmeta = uu____14198; FStar_Syntax_Syntax.sigattrs = uu____14199}, constrs, tconstr, quals1) -> begin
(

let mk_tot = (fun t -> (

let tot1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((tot1), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)))
in (

let tycon = ((tname), (tpars), (k))
in (

let uu____14295 = (push_tparams env1 tpars)
in (match (uu____14295) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun uu____14372 -> (match (uu____14372) with
| (x, uu____14386) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let tot_tconstr = (mk_tot tconstr)
in (

let uu____14394 = (

let uu____14423 = (FStar_All.pipe_right constrs (FStar_List.map (fun uu____14537 -> (match (uu____14537) with
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
| uu____14590 -> begin
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

let uu____14593 = (close env_tps t)
in (desugar_term env_tps uu____14593))
in (

let name = (FStar_ToSyntax_Env.qualify env1 id)
in (

let quals2 = (FStar_All.pipe_right tname_quals (FStar_List.collect (fun uu___226_14604 -> (match (uu___226_14604) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| uu____14616 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (

let uu____14624 = (

let uu____14645 = (

let uu____14646 = (

let uu____14647 = (

let uu____14662 = (

let uu____14665 = (

let uu____14668 = (FStar_All.pipe_right t1 FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total uu____14668))
in (FStar_Syntax_Util.arrow data_tpars uu____14665))
in ((name), (univs1), (uu____14662), (tname), (ntps), (mutuals1)))
in FStar_Syntax_Syntax.Sig_datacon (uu____14647))
in {FStar_Syntax_Syntax.sigel = uu____14646; FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in ((((name), (doc1))), (tps), (uu____14645)))
in ((name), (uu____14624))))))))
end))))
in (FStar_All.pipe_left FStar_List.split uu____14423))
in (match (uu____14394) with
| (constrNames, constrs1) -> begin
(((((tname), (d.FStar_Parser_AST.doc))), ([]), ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs1), (tpars), (k), (mutuals1), (constrNames))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = tname_quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))::constrs1
end))))
end))))
end
| uu____14907 -> begin
(failwith "impossible")
end))))
in (

let name_docs = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.map (fun uu____15039 -> (match (uu____15039) with
| (name_doc, uu____15067, uu____15068) -> begin
name_doc
end))))
in (

let sigelts = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.map (fun uu____15148 -> (match (uu____15148) with
| (uu____15169, uu____15170, se) -> begin
se
end))))
in (

let uu____15200 = (

let uu____15207 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle sigelts quals uu____15207 rng))
in (match (uu____15200) with
| (bundle, abbrevs) -> begin
(

let env2 = (FStar_ToSyntax_Env.push_sigelt env0 bundle)
in (

let env3 = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2 abbrevs)
in (

let data_ops = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.collect (fun uu____15273 -> (match (uu____15273) with
| (uu____15296, tps, se) -> begin
(mk_data_projector_names quals env3 se)
end))))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, uu____15347, tps, k, uu____15350, constrs) when ((FStar_List.length constrs) > (Prims.parse_int "1")) -> begin
(

let quals1 = se.FStar_Syntax_Syntax.sigquals
in (

let quals2 = (match ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals1)) with
| true -> begin
(FStar_Syntax_Syntax.Private)::quals1
end
| uu____15368 -> begin
quals1
end)
in (mk_data_discriminators quals2 env3 constrs)))
end
| uu____15369 -> begin
[]
end))))
in (

let ops = (FStar_List.append discs data_ops)
in (

let env4 = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env3 ops)
in (

let env5 = (FStar_List.fold_left (fun acc uu____15386 -> (match (uu____15386) with
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

let uu____15423 = (FStar_List.fold_left (fun uu____15446 b -> (match (uu____15446) with
| (env1, binders1) -> begin
(

let uu____15466 = (desugar_binder env1 b)
in (match (uu____15466) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____15483 = (as_binder env1 b.FStar_Parser_AST.aqual ((FStar_Pervasives_Native.Some (a)), (k)))
in (match (uu____15483) with
| (binder, env2) -> begin
((env2), ((binder)::binders1))
end))
end
| uu____15500 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) binders)
in (match (uu____15423) with
| (env1, binders1) -> begin
((env1), ((FStar_List.rev binders1)))
end)))


let rec desugar_effect : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_typ eff_decls -> (

let env0 = env
in (

let monad_env = (FStar_ToSyntax_Env.enter_monad_scope env eff_name)
in (

let uu____15614 = (desugar_binders monad_env eff_binders)
in (match (uu____15614) with
| (env1, binders) -> begin
(

let eff_t = (desugar_term env1 eff_typ)
in (

let for_free = (

let uu____15635 = (

let uu____15636 = (

let uu____15643 = (FStar_Syntax_Util.arrow_formals eff_t)
in (FStar_Pervasives_Native.fst uu____15643))
in (FStar_List.length uu____15636))
in (uu____15635 = (Prims.parse_int "1")))
in (

let mandatory_members = (

let rr_members = ("repr")::("return")::("bind")::[]
in (match (for_free) with
| true -> begin
rr_members
end
| uu____15680 -> begin
(FStar_List.append rr_members (("return_wp")::("bind_wp")::("if_then_else")::("ite_wp")::("stronger")::("close_wp")::("assert_p")::("assume_p")::("null_wp")::("trivial")::[]))
end))
in (

let name_of_eff_decl = (fun decl -> (match (decl.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____15685, ((FStar_Parser_AST.TyconAbbrev (name, uu____15687, uu____15688, uu____15689), uu____15690))::[]) -> begin
(FStar_Ident.text_of_id name)
end
| uu____15723 -> begin
(failwith "Malformed effect member declaration.")
end))
in (

let uu____15724 = (FStar_List.partition (fun decl -> (

let uu____15736 = (name_of_eff_decl decl)
in (FStar_List.mem uu____15736 mandatory_members))) eff_decls)
in (match (uu____15724) with
| (mandatory_members_decls, actions) -> begin
(

let uu____15753 = (FStar_All.pipe_right mandatory_members_decls (FStar_List.fold_left (fun uu____15782 decl -> (match (uu____15782) with
| (env2, out) -> begin
(

let uu____15802 = (desugar_decl env2 decl)
in (match (uu____15802) with
| (env3, ses) -> begin
(

let uu____15815 = (

let uu____15818 = (FStar_List.hd ses)
in (uu____15818)::out)
in ((env3), (uu____15815)))
end))
end)) ((env1), ([]))))
in (match (uu____15753) with
| (env2, decls) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (

let actions_docs = (FStar_All.pipe_right actions (FStar_List.map (fun d1 -> (match (d1.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____15886, ((FStar_Parser_AST.TyconAbbrev (name, action_params, uu____15889, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (uu____15890, ((def, uu____15892))::((cps_type, uu____15894))::[]); FStar_Parser_AST.range = uu____15895; FStar_Parser_AST.level = uu____15896}), doc1))::[]) when (not (for_free)) -> begin
(

let uu____15948 = (desugar_binders env2 action_params)
in (match (uu____15948) with
| (env3, action_params1) -> begin
(

let action_params2 = (FStar_Syntax_Subst.close_binders action_params1)
in (

let uu____15968 = (

let uu____15969 = (FStar_ToSyntax_Env.qualify env3 name)
in (

let uu____15970 = (

let uu____15971 = (desugar_term env3 def)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____15971))
in (

let uu____15976 = (

let uu____15977 = (desugar_typ env3 cps_type)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____15977))
in {FStar_Syntax_Syntax.action_name = uu____15969; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = action_params2; FStar_Syntax_Syntax.action_defn = uu____15970; FStar_Syntax_Syntax.action_typ = uu____15976})))
in ((uu____15968), (doc1))))
end))
end
| FStar_Parser_AST.Tycon (uu____15984, ((FStar_Parser_AST.TyconAbbrev (name, action_params, uu____15987, defn), doc1))::[]) when for_free -> begin
(

let uu____16022 = (desugar_binders env2 action_params)
in (match (uu____16022) with
| (env3, action_params1) -> begin
(

let action_params2 = (FStar_Syntax_Subst.close_binders action_params1)
in (

let uu____16042 = (

let uu____16043 = (FStar_ToSyntax_Env.qualify env3 name)
in (

let uu____16044 = (

let uu____16045 = (desugar_term env3 defn)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____16045))
in {FStar_Syntax_Syntax.action_name = uu____16043; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = action_params2; FStar_Syntax_Syntax.action_defn = uu____16044; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
in ((uu____16042), (doc1))))
end))
end
| uu____16052 -> begin
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

let uu____16082 = (

let uu____16083 = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_definition env2) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders1) uu____16083))
in (([]), (uu____16082)))))
in (

let mname = (FStar_ToSyntax_Env.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange (FStar_Pervasives_Native.Some (mname))) quals)
in (

let se = (match (for_free) with
| true -> begin
(

let dummy_tscheme = (

let uu____16100 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (([]), (uu____16100)))
in (

let uu____16107 = (

let uu____16108 = (

let uu____16109 = (

let uu____16110 = (lookup "repr")
in (FStar_Pervasives_Native.snd uu____16110))
in (

let uu____16119 = (lookup "return")
in (

let uu____16120 = (lookup "bind")
in {FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = eff_t1; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = uu____16109; FStar_Syntax_Syntax.return_repr = uu____16119; FStar_Syntax_Syntax.bind_repr = uu____16120; FStar_Syntax_Syntax.actions = actions1})))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____16108))
in {FStar_Syntax_Syntax.sigel = uu____16107; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qualifiers; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))
end
| uu____16121 -> begin
(

let rr = (FStar_Util.for_some (fun uu___228_16124 -> (match (uu___228_16124) with
| FStar_Syntax_Syntax.Reifiable -> begin
true
end
| FStar_Syntax_Syntax.Reflectable (uu____16125) -> begin
true
end
| uu____16126 -> begin
false
end)) qualifiers)
in (

let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in (

let uu____16136 = (

let uu____16137 = (

let uu____16138 = (lookup "return_wp")
in (

let uu____16139 = (lookup "bind_wp")
in (

let uu____16140 = (lookup "if_then_else")
in (

let uu____16141 = (lookup "ite_wp")
in (

let uu____16142 = (lookup "stronger")
in (

let uu____16143 = (lookup "close_wp")
in (

let uu____16144 = (lookup "assert_p")
in (

let uu____16145 = (lookup "assume_p")
in (

let uu____16146 = (lookup "null_wp")
in (

let uu____16147 = (lookup "trivial")
in (

let uu____16148 = (match (rr) with
| true -> begin
(

let uu____16149 = (lookup "repr")
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____16149))
end
| uu____16164 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let uu____16165 = (match (rr) with
| true -> begin
(lookup "return")
end
| uu____16166 -> begin
un_ts
end)
in (

let uu____16167 = (match (rr) with
| true -> begin
(lookup "bind")
end
| uu____16168 -> begin
un_ts
end)
in {FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = eff_t1; FStar_Syntax_Syntax.ret_wp = uu____16138; FStar_Syntax_Syntax.bind_wp = uu____16139; FStar_Syntax_Syntax.if_then_else = uu____16140; FStar_Syntax_Syntax.ite_wp = uu____16141; FStar_Syntax_Syntax.stronger = uu____16142; FStar_Syntax_Syntax.close_wp = uu____16143; FStar_Syntax_Syntax.assert_p = uu____16144; FStar_Syntax_Syntax.assume_p = uu____16145; FStar_Syntax_Syntax.null_wp = uu____16146; FStar_Syntax_Syntax.trivial = uu____16147; FStar_Syntax_Syntax.repr = uu____16148; FStar_Syntax_Syntax.return_repr = uu____16165; FStar_Syntax_Syntax.bind_repr = uu____16167; FStar_Syntax_Syntax.actions = actions1})))))))))))))
in FStar_Syntax_Syntax.Sig_new_effect (uu____16137))
in {FStar_Syntax_Syntax.sigel = uu____16136; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qualifiers; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))
end)
in (

let env3 = (FStar_ToSyntax_Env.push_sigelt env0 se)
in (

let env4 = (FStar_ToSyntax_Env.push_doc env3 mname d.FStar_Parser_AST.doc)
in (

let env5 = (FStar_All.pipe_right actions_docs (FStar_List.fold_left (fun env5 uu____16192 -> (match (uu____16192) with
| (a, doc1) -> begin
(

let env6 = (

let uu____16206 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_ToSyntax_Env.push_sigelt env5 uu____16206))
in (FStar_ToSyntax_Env.push_doc env6 a.FStar_Syntax_Syntax.action_name doc1))
end)) env4))
in (

let env6 = (

let uu____16208 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____16208) with
| true -> begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_ToSyntax_Env.qualify monad_env))
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]
in (

let refl_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (FStar_ToSyntax_Env.push_sigelt env5 refl_decl))))
end
| uu____16216 -> begin
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

let uu____16239 = (desugar_binders env1 eff_binders)
in (match (uu____16239) with
| (env2, binders) -> begin
(

let uu____16258 = (

let uu____16277 = (head_and_args defn)
in (match (uu____16277) with
| (head1, args) -> begin
(

let lid = (match (head1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
l
end
| uu____16322 -> begin
(

let uu____16323 = (

let uu____16324 = (

let uu____16329 = (

let uu____16330 = (

let uu____16331 = (FStar_Parser_AST.term_to_string head1)
in (Prims.strcat uu____16331 " not found"))
in (Prims.strcat "Effect " uu____16330))
in ((uu____16329), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____16324))
in (FStar_Exn.raise uu____16323))
end)
in (

let ed = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_effect_defn env2) lid)
in (

let uu____16333 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____16363))::args_rev -> begin
(

let uu____16375 = (

let uu____16376 = (unparen last_arg)
in uu____16376.FStar_Parser_AST.tm)
in (match (uu____16375) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____16404 -> begin
(([]), (args))
end))
end
| uu____16413 -> begin
(([]), (args))
end)
in (match (uu____16333) with
| (cattributes, args1) -> begin
(

let uu____16464 = (desugar_args env2 args1)
in (

let uu____16473 = (desugar_attributes env2 cattributes)
in ((lid), (ed), (uu____16464), (uu____16473))))
end))))
end))
in (match (uu____16258) with
| (ed_lid, ed, args, cattributes) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (

let sub1 = (fun uu____16532 -> (match (uu____16532) with
| (uu____16545, x) -> begin
(

let uu____16551 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (uu____16551) with
| (edb, x1) -> begin
((match (((FStar_List.length args) <> (FStar_List.length edb))) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected number of arguments to effect constructor"), (defn.FStar_Parser_AST.range)))))
end
| uu____16575 -> begin
()
end);
(

let s = (FStar_Syntax_Util.subst_of_list edb args)
in (

let uu____16577 = (

let uu____16578 = (FStar_Syntax_Subst.subst s x1)
in (FStar_Syntax_Subst.close binders1 uu____16578))
in (([]), (uu____16577))));
)
end))
end))
in (

let mname = (FStar_ToSyntax_Env.qualify env0 eff_name)
in (

let ed1 = (

let uu____16583 = (

let uu____16584 = (sub1 (([]), (ed.FStar_Syntax_Syntax.signature)))
in (FStar_Pervasives_Native.snd uu____16584))
in (

let uu____16595 = (sub1 ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____16596 = (sub1 ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____16597 = (sub1 ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____16598 = (sub1 ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____16599 = (sub1 ed.FStar_Syntax_Syntax.stronger)
in (

let uu____16600 = (sub1 ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____16601 = (sub1 ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____16602 = (sub1 ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____16603 = (sub1 ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____16604 = (sub1 ed.FStar_Syntax_Syntax.trivial)
in (

let uu____16605 = (

let uu____16606 = (sub1 (([]), (ed.FStar_Syntax_Syntax.repr)))
in (FStar_Pervasives_Native.snd uu____16606))
in (

let uu____16617 = (sub1 ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____16618 = (sub1 ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____16619 = (FStar_List.map (fun action -> (

let uu____16627 = (FStar_ToSyntax_Env.qualify env2 action.FStar_Syntax_Syntax.action_unqualified_name)
in (

let uu____16628 = (

let uu____16629 = (sub1 (([]), (action.FStar_Syntax_Syntax.action_defn)))
in (FStar_Pervasives_Native.snd uu____16629))
in (

let uu____16640 = (

let uu____16641 = (sub1 (([]), (action.FStar_Syntax_Syntax.action_typ)))
in (FStar_Pervasives_Native.snd uu____16641))
in {FStar_Syntax_Syntax.action_name = uu____16627; FStar_Syntax_Syntax.action_unqualified_name = action.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = action.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = uu____16628; FStar_Syntax_Syntax.action_typ = uu____16640})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = cattributes; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = uu____16583; FStar_Syntax_Syntax.ret_wp = uu____16595; FStar_Syntax_Syntax.bind_wp = uu____16596; FStar_Syntax_Syntax.if_then_else = uu____16597; FStar_Syntax_Syntax.ite_wp = uu____16598; FStar_Syntax_Syntax.stronger = uu____16599; FStar_Syntax_Syntax.close_wp = uu____16600; FStar_Syntax_Syntax.assert_p = uu____16601; FStar_Syntax_Syntax.assume_p = uu____16602; FStar_Syntax_Syntax.null_wp = uu____16603; FStar_Syntax_Syntax.trivial = uu____16604; FStar_Syntax_Syntax.repr = uu____16605; FStar_Syntax_Syntax.return_repr = uu____16617; FStar_Syntax_Syntax.bind_repr = uu____16618; FStar_Syntax_Syntax.actions = uu____16619})))))))))))))))
in (

let se = (

let for_free = (

let uu____16654 = (

let uu____16655 = (

let uu____16662 = (FStar_Syntax_Util.arrow_formals ed1.FStar_Syntax_Syntax.signature)
in (FStar_Pervasives_Native.fst uu____16662))
in (FStar_List.length uu____16655))
in (uu____16654 = (Prims.parse_int "1")))
in (

let uu____16691 = (

let uu____16694 = (trans_qual1 (FStar_Pervasives_Native.Some (mname)))
in (FStar_List.map uu____16694 quals))
in {FStar_Syntax_Syntax.sigel = (match (for_free) with
| true -> begin
FStar_Syntax_Syntax.Sig_new_effect_for_free (ed1)
end
| uu____16697 -> begin
FStar_Syntax_Syntax.Sig_new_effect (ed1)
end); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = uu____16691; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))
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

let uu____16714 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_ToSyntax_Env.push_sigelt env5 uu____16714))
in (FStar_ToSyntax_Env.push_doc env6 a.FStar_Syntax_Syntax.action_name doc1)))) env4))
in (

let env6 = (

let uu____16716 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____16716) with
| true -> begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_ToSyntax_Env.qualify monad_env))
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]
in (

let refl_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (FStar_ToSyntax_Env.push_sigelt env5 refl_decl))))
end
| uu____16726 -> begin
env5
end))
in (

let env7 = (FStar_ToSyntax_Env.push_doc env6 mname d.FStar_Parser_AST.doc)
in ((env7), ((se)::[])))))))))))))
end))
end)))))
and desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (

let uu____16736 = (desugar_decl_noattrs env d)
in (match (uu____16736) with
| (env1, sigelts) -> begin
(

let attrs = d.FStar_Parser_AST.attrs
in (

let attrs1 = (FStar_List.map (desugar_term env1) attrs)
in (

let uu____16751 = (FStar_List.map (fun sigelt -> (

let uu___248_16757 = sigelt
in {FStar_Syntax_Syntax.sigel = uu___248_16757.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___248_16757.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___248_16757.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___248_16757.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = attrs1})) sigelts)
in ((env1), (uu____16751)))))
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
| uu____16780 -> begin
()
end);
((env), ((se)::[]));
))
end
| FStar_Parser_AST.Fsdoc (uu____16783) -> begin
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

let uu____16799 = (FStar_ToSyntax_Env.push_module_abbrev env x l)
in ((uu____16799), ([])))
end
| FStar_Parser_AST.Tycon (is_effect, tcs) -> begin
(

let quals = (match (is_effect) with
| true -> begin
(FStar_Parser_AST.Effect_qual)::d.FStar_Parser_AST.quals
end
| uu____16825 -> begin
d.FStar_Parser_AST.quals
end)
in (

let tcs1 = (FStar_List.map (fun uu____16838 -> (match (uu____16838) with
| (x, uu____16846) -> begin
x
end)) tcs)
in (

let uu____16851 = (FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals)
in (desugar_tycon env d uu____16851 tcs1))))
end
| FStar_Parser_AST.TopLevelLet (isrec, lets) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let expand_toplevel_pattern = ((isrec = FStar_Parser_AST.NoLetQualifier) && (match (lets) with
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatOp (uu____16873); FStar_Parser_AST.prange = uu____16874}, uu____16875))::[] -> begin
false
end
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____16884); FStar_Parser_AST.prange = uu____16885}, uu____16886))::[] -> begin
false
end
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____16901); FStar_Parser_AST.prange = uu____16902}, uu____16903); FStar_Parser_AST.prange = uu____16904}, uu____16905))::[] -> begin
false
end
| ((p, uu____16921))::[] -> begin
(

let uu____16930 = (is_app_pattern p)
in (not (uu____16930)))
end
| uu____16931 -> begin
false
end))
in (match ((not (expand_toplevel_pattern))) with
| true -> begin
(

let as_inner_let = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)
in (

let ds_lets = (desugar_term_maybe_top true env as_inner_let)
in (

let uu____16950 = (

let uu____16951 = (FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets)
in uu____16951.FStar_Syntax_Syntax.n)
in (match (uu____16950) with
| FStar_Syntax_Syntax.Tm_let (lbs, uu____16959) -> begin
(

let fvs = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals1 = (match (quals) with
| (uu____16992)::uu____16993 -> begin
(FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals)
end
| uu____16996 -> begin
(FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.collect (fun uu___229_17009 -> (match (uu___229_17009) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (uu____17012); FStar_Syntax_Syntax.lbunivs = uu____17013; FStar_Syntax_Syntax.lbtyp = uu____17014; FStar_Syntax_Syntax.lbeff = uu____17015; FStar_Syntax_Syntax.lbdef = uu____17016} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____17024; FStar_Syntax_Syntax.lbtyp = uu____17025; FStar_Syntax_Syntax.lbeff = uu____17026; FStar_Syntax_Syntax.lbdef = uu____17027} -> begin
(FStar_ToSyntax_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals2 = (

let uu____17037 = (FStar_All.pipe_right lets (FStar_Util.for_some (fun uu____17051 -> (match (uu____17051) with
| (uu____17056, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end))))
in (match (uu____17037) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals1
end
| uu____17060 -> begin
quals1
end))
in (

let lbs1 = (

let uu____17068 = (FStar_All.pipe_right quals2 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____17068) with
| true -> begin
(

let uu____17077 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu___249_17091 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let uu___250_17093 = fv
in {FStar_Syntax_Syntax.fv_name = uu___250_17093.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = uu___250_17093.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = uu___249_17091.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___249_17091.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___249_17091.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___249_17091.FStar_Syntax_Syntax.lbdef})))))
in (((FStar_Pervasives_Native.fst lbs)), (uu____17077)))
end
| uu____17098 -> begin
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
| uu____17125 -> begin
(failwith "Desugaring a let did not produce a let")
end))))
end
| uu____17130 -> begin
(

let uu____17131 = (match (lets) with
| ((pat, body))::[] -> begin
((pat), (body))
end
| uu____17150 -> begin
(failwith "expand_toplevel_pattern should only allow single definition lets")
end)
in (match (uu____17131) with
| (pat, body) -> begin
(

let fresh_toplevel_name = (FStar_Ident.gen FStar_Range.dummyRange)
in (

let fresh_pat = (

let var_pat = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((fresh_toplevel_name), (FStar_Pervasives_Native.None)))) FStar_Range.dummyRange)
in (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat1, ty) -> begin
(

let uu___251_17174 = pat1
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed (((var_pat), (ty))); FStar_Parser_AST.prange = uu___251_17174.FStar_Parser_AST.prange})
end
| uu____17175 -> begin
var_pat
end))
in (

let main_let = (desugar_decl env (

let uu___252_17182 = d
in {FStar_Parser_AST.d = FStar_Parser_AST.TopLevelLet (((isrec), ((((fresh_pat), (body)))::[]))); FStar_Parser_AST.drange = uu___252_17182.FStar_Parser_AST.drange; FStar_Parser_AST.doc = uu___252_17182.FStar_Parser_AST.doc; FStar_Parser_AST.quals = (FStar_Parser_AST.Private)::d.FStar_Parser_AST.quals; FStar_Parser_AST.attrs = uu___252_17182.FStar_Parser_AST.attrs}))
in (

let build_projection = (fun uu____17214 id -> (match (uu____17214) with
| (env1, ses) -> begin
(

let main = (

let uu____17235 = (

let uu____17236 = (FStar_Ident.lid_of_ids ((fresh_toplevel_name)::[]))
in FStar_Parser_AST.Var (uu____17236))
in (FStar_Parser_AST.mk_term uu____17235 FStar_Range.dummyRange FStar_Parser_AST.Expr))
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

let uu____17286 = (desugar_decl env1 id_decl)
in (match (uu____17286) with
| (env2, ses') -> begin
((env2), ((FStar_List.append ses ses')))
end))))))))
end))
in (

let bvs = (

let uu____17304 = (gather_pattern_bound_vars pat)
in (FStar_All.pipe_right uu____17304 FStar_Util.set_elements))
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

let uu____17335 = (close_fun env t)
in (desugar_term env uu____17335))
in (

let quals1 = (

let uu____17339 = ((FStar_ToSyntax_Env.iface env) && (FStar_ToSyntax_Env.admitted_iface env))
in (match (uu____17339) with
| true -> begin
(FStar_Parser_AST.Assumption)::quals
end
| uu____17342 -> begin
quals
end))
in (

let lid = (FStar_ToSyntax_Env.qualify env id)
in (

let se = (

let uu____17345 = (FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals1)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), ([]), (t1))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = uu____17345; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env se)
in (

let env2 = (FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc)
in ((env2), ((se)::[])))))))))
end
| FStar_Parser_AST.Exception (id, FStar_Pervasives_Native.None) -> begin
(

let uu____17357 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) FStar_Parser_Const.exn_lid)
in (match (uu____17357) with
| (t, uu____17371) -> begin
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

let uu____17405 = (

let uu____17412 = (FStar_Syntax_Syntax.null_binder t)
in (uu____17412)::[])
in (

let uu____17413 = (

let uu____17416 = (

let uu____17417 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) FStar_Parser_Const.exn_lid)
in (FStar_Pervasives_Native.fst uu____17417))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____17416))
in (FStar_Syntax_Util.arrow uu____17405 uu____17413)))
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

let uu____17479 = (FStar_ToSyntax_Env.try_lookup_effect_name env l1)
in (match (uu____17479) with
| FStar_Pervasives_Native.None -> begin
(

let uu____17482 = (

let uu____17483 = (

let uu____17488 = (

let uu____17489 = (

let uu____17490 = (FStar_Syntax_Print.lid_to_string l1)
in (Prims.strcat uu____17490 " not found"))
in (Prims.strcat "Effect name " uu____17489))
in ((uu____17488), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____17483))
in (FStar_Exn.raise uu____17482))
end
| FStar_Pervasives_Native.Some (l2) -> begin
l2
end)))
in (

let src = (lookup l.FStar_Parser_AST.msource)
in (

let dst = (lookup l.FStar_Parser_AST.mdest)
in (

let uu____17494 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(

let uu____17536 = (

let uu____17545 = (

let uu____17552 = (desugar_term env t)
in (([]), (uu____17552)))
in FStar_Pervasives_Native.Some (uu____17545))
in ((uu____17536), (FStar_Pervasives_Native.None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(

let uu____17585 = (

let uu____17594 = (

let uu____17601 = (desugar_term env wp)
in (([]), (uu____17601)))
in FStar_Pervasives_Native.Some (uu____17594))
in (

let uu____17610 = (

let uu____17619 = (

let uu____17626 = (desugar_term env t)
in (([]), (uu____17626)))
in FStar_Pervasives_Native.Some (uu____17619))
in ((uu____17585), (uu____17610))))
end
| FStar_Parser_AST.LiftForFree (t) -> begin
(

let uu____17652 = (

let uu____17661 = (

let uu____17668 = (desugar_term env t)
in (([]), (uu____17668)))
in FStar_Pervasives_Native.Some (uu____17661))
in ((FStar_Pervasives_Native.None), (uu____17652)))
end)
in (match (uu____17494) with
| (lift_wp, lift) -> begin
(

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect ({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift}); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in ((env), ((se)::[])))
end)))))
end)))


let desugar_decls : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun uu____17769 d -> (match (uu____17769) with
| (env1, sigelts) -> begin
(

let uu____17789 = (desugar_decl env1 d)
in (match (uu____17789) with
| (env2, se) -> begin
((env2), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls))


let open_prims_all : (FStar_Parser_AST.decoration Prims.list  ->  FStar_Parser_AST.decl) Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Parser_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Parser_Const.all_lid)) FStar_Range.dummyRange))::[]


let desugar_modul_common : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let env1 = (match (((curmod), (m))) with
| (FStar_Pervasives_Native.None, uu____17855) -> begin
env
end
| (FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.name = prev_lid; FStar_Syntax_Syntax.declarations = uu____17859; FStar_Syntax_Syntax.exports = uu____17860; FStar_Syntax_Syntax.is_interface = uu____17861}), FStar_Parser_AST.Module (current_lid, uu____17863)) when ((FStar_Ident.lid_equals prev_lid current_lid) && (FStar_Options.interactive ())) -> begin
env
end
| (FStar_Pervasives_Native.Some (prev_mod), uu____17871) -> begin
(FStar_ToSyntax_Env.finish_module_or_interface env prev_mod)
end)
in (

let uu____17874 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(

let uu____17910 = (FStar_ToSyntax_Env.prepare_module_or_interface true admitted env1 mname FStar_ToSyntax_Env.default_mii)
in ((uu____17910), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(

let uu____17927 = (FStar_ToSyntax_Env.prepare_module_or_interface false false env1 mname FStar_ToSyntax_Env.default_mii)
in ((uu____17927), (mname), (decls), (false)))
end)
in (match (uu____17874) with
| ((env2, pop_when_done), mname, decls, intf) -> begin
(

let uu____17957 = (desugar_decls env2 decls)
in (match (uu____17957) with
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

let uu____18009 = ((FStar_Options.interactive ()) && (

let uu____18011 = (

let uu____18012 = (

let uu____18013 = (FStar_Options.file_list ())
in (FStar_List.hd uu____18013))
in (FStar_Util.get_file_extension uu____18012))
in (FStar_List.mem uu____18011 (("fsti")::("fsi")::[]))))
in (match (uu____18009) with
| true -> begin
(as_interface m)
end
| uu____18016 -> begin
m
end))
in (

let uu____18017 = (desugar_modul_common curmod env m1)
in (match (uu____18017) with
| (x, y, pop_when_done) -> begin
((match (pop_when_done) with
| true -> begin
(

let uu____18032 = (FStar_ToSyntax_Env.pop ())
in ())
end
| uu____18033 -> begin
()
end);
((x), (y));
)
end))))


let desugar_modul : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.modul) = (fun env m -> (

let uu____18050 = (desugar_modul_common FStar_Pervasives_Native.None env m)
in (match (uu____18050) with
| (env1, modul, pop_when_done) -> begin
(

let env2 = (FStar_ToSyntax_Env.finish_module_or_interface env1 modul)
in ((

let uu____18066 = (FStar_Options.dump_module modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____18066) with
| true -> begin
(

let uu____18067 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" uu____18067))
end
| uu____18068 -> begin
()
end));
(

let uu____18069 = (match (pop_when_done) with
| true -> begin
(FStar_ToSyntax_Env.export_interface modul.FStar_Syntax_Syntax.name env2)
end
| uu____18070 -> begin
env2
end)
in ((uu____18069), (modul)));
))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_ToSyntax_Env.module_inclusion_info  ->  FStar_ToSyntax_Env.env  ->  FStar_ToSyntax_Env.env = (fun m mii en -> (

let uu____18083 = (FStar_ToSyntax_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name mii)
in (match (uu____18083) with
| (en1, pop_when_done) -> begin
(

let en2 = (

let uu____18091 = (FStar_ToSyntax_Env.set_current_module en1 m.FStar_Syntax_Syntax.name)
in (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____18091 m.FStar_Syntax_Syntax.exports))
in (

let env = (FStar_ToSyntax_Env.finish en2 m)
in (match (pop_when_done) with
| true -> begin
(FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name env)
end
| uu____18093 -> begin
env
end)))
end)))




