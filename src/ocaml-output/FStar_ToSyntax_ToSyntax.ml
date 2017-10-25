
open Prims
open FStar_Pervasives

let desugar_disjunctive_pattern : FStar_Syntax_Syntax.pat' FStar_Syntax_Syntax.withinfo_t Prims.list  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.branch Prims.list = (fun pats when_opt branch1 -> (FStar_All.pipe_right pats (FStar_List.map (fun pat -> (FStar_Syntax_Util.branch ((pat), (when_opt), (branch1)))))))


let trans_aqual : FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option = (fun uu___219_62 -> (match (uu___219_62) with
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.imp_tag)
end
| FStar_Pervasives_Native.Some (FStar_Parser_AST.Equality) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Equality)
end
| uu____67 -> begin
FStar_Pervasives_Native.None
end))


let trans_qual : FStar_Range.range  ->  FStar_Ident.lident FStar_Pervasives_Native.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun r maybe_effect_id uu___220_83 -> (match (uu___220_83) with
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


let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun uu___221_91 -> (match (uu___221_91) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end
| FStar_Parser_AST.LightOff -> begin
FStar_Syntax_Syntax.LightOff
end))


let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option = (fun uu___222_101 -> (match (uu___222_101) with
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


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun uu___223_1455 -> (match (uu___223_1455) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| uu____1462 -> begin
(failwith "Impossible")
end))


let as_binder : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.arg_qualifier FStar_Pervasives_Native.option  ->  (FStar_Ident.ident FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_ToSyntax_Env.env) = (fun env imp uu___224_1490 -> (match (uu___224_1490) with
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

let uu___247_1531 = a1
in {FStar_Syntax_Syntax.ppname = uu___247_1531.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___247_1531.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), ((trans_aqual imp)))), (env1))
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


let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun uu___225_1834 -> (match (uu___225_1834) with
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
(match ((FStar_List.existsb (fun uu___226_2042 -> (match (uu___226_2042) with
| FStar_Util.Inr (uu____2047) -> begin
true
end
| uu____2048 -> begin
false
end)) univargs)) with
| true -> begin
(

let uu____2053 = (

let uu____2054 = (FStar_List.map (fun uu___227_2063 -> (match (uu___227_2063) with
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

let nargs = (FStar_List.map (fun uu___228_2080 -> (match (uu___228_2080) with
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

let check_linear_pattern_variables = (fun p1 r -> (

let rec pat_vars = (fun p2 -> (match (p2.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (uu____2418) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_wild (uu____2425) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_constant (uu____2426) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (uu____2428, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out uu____2469 -> (match (uu____2469) with
| (p3, uu____2479) -> begin
(

let uu____2480 = (

let uu____2481 = (

let uu____2484 = (pat_vars p3)
in (FStar_Util.set_intersect uu____2484 out))
in (FStar_Util.set_is_empty uu____2481))
in (match (uu____2480) with
| true -> begin
(

let uu____2489 = (pat_vars p3)
in (FStar_Util.set_union out uu____2489))
end
| uu____2492 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Non-linear patterns are not permitted."), (r)))))
end))
end)) FStar_Syntax_Syntax.no_names))
end))
in (pat_vars p1)))
in ((match (((is_mut), (p.FStar_Parser_AST.pat))) with
| (false, uu____2496) -> begin
()
end
| (true, FStar_Parser_AST.PatVar (uu____2497)) -> begin
()
end
| (true, uu____2504) -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("let-mutable is for variables only"), (p.FStar_Parser_AST.prange)))))
end);
(

let push_bv_maybe_mut = (match (is_mut) with
| true -> begin
FStar_ToSyntax_Env.push_bv_mutable
end
| uu____2522 -> begin
FStar_ToSyntax_Env.push_bv
end)
in (

let resolvex = (fun l e x -> (

let uu____2539 = (FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (Prims.op_Equality y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText x.FStar_Ident.idText))))
in (match (uu____2539) with
| FStar_Pervasives_Native.Some (y) -> begin
((l), (e), (y))
end
| uu____2553 -> begin
(

let uu____2556 = (push_bv_maybe_mut e x)
in (match (uu____2556) with
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
| FStar_Parser_AST.PatOr (uu____2643) -> begin
(failwith "impossible")
end
| FStar_Parser_AST.PatOp (op) -> begin
(

let uu____2659 = (

let uu____2660 = (

let uu____2661 = (

let uu____2668 = (

let uu____2669 = (

let uu____2674 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") op.FStar_Ident.idText op.FStar_Ident.idRange)
in ((uu____2674), (op.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____2669))
in ((uu____2668), (FStar_Pervasives_Native.None)))
in FStar_Parser_AST.PatVar (uu____2661))
in {FStar_Parser_AST.pat = uu____2660; FStar_Parser_AST.prange = p1.FStar_Parser_AST.prange})
in (aux loc env1 uu____2659))
end
| FStar_Parser_AST.PatAscribed (p2, t) -> begin
(

let uu____2679 = (aux loc env1 p2)
in (match (uu____2679) with
| (loc1, env', binder, p3, imp) -> begin
(

let annot_pat_var = (fun p4 t1 -> (match (p4.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(

let uu___248_2733 = p4
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var ((

let uu___249_2738 = x
in {FStar_Syntax_Syntax.ppname = uu___249_2738.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___249_2738.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})); FStar_Syntax_Syntax.p = uu___248_2733.FStar_Syntax_Syntax.p})
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(

let uu___250_2740 = p4
in {FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild ((

let uu___251_2745 = x
in {FStar_Syntax_Syntax.ppname = uu___251_2745.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___251_2745.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})); FStar_Syntax_Syntax.p = uu___250_2740.FStar_Syntax_Syntax.p})
end
| uu____2746 when top -> begin
p4
end
| uu____2747 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Type ascriptions within patterns are only allowed on variables"), (orig.FStar_Parser_AST.prange)))))
end))
in (

let uu____2750 = (match (binder) with
| LetBinder (uu____2763) -> begin
(failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t1 = (

let uu____2777 = (close_fun env1 t)
in (desugar_term env1 uu____2777))
in ((match ((match (x.FStar_Syntax_Syntax.sort.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
false
end
| uu____2779 -> begin
true
end)) with
| true -> begin
(

let uu____2780 = (FStar_Syntax_Print.bv_to_string x)
in (

let uu____2781 = (FStar_Syntax_Print.term_to_string x.FStar_Syntax_Syntax.sort)
in (

let uu____2782 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print3_warning "Multiple ascriptions for %s in pattern, type %s was shadowed by %s\n" uu____2780 uu____2781 uu____2782))))
end
| uu____2783 -> begin
()
end);
(

let uu____2784 = (annot_pat_var p3 t1)
in ((uu____2784), (LocalBinder ((((

let uu___252_2790 = x
in {FStar_Syntax_Syntax.ppname = uu___252_2790.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___252_2790.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})), (aq))))));
))
end)
in (match (uu____2750) with
| (p4, binder1) -> begin
((loc1), (env'), (binder1), (p4), (imp))
end)))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____2812 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____2812), (false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____2823 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____2823), (false))))
end
| FStar_Parser_AST.PatTvar (x, aq) -> begin
(

let imp = (Prims.op_Equality aq (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))
in (

let aq1 = (trans_aqual aq)
in (

let uu____2844 = (resolvex loc env1 x)
in (match (uu____2844) with
| (loc1, env2, xbv) -> begin
(

let uu____2866 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc1), (env2), (LocalBinder (((xbv), (aq1)))), (uu____2866), (imp)))
end))))
end
| FStar_Parser_AST.PatVar (x, aq) -> begin
(

let imp = (Prims.op_Equality aq (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit)))
in (

let aq1 = (trans_aqual aq)
in (

let uu____2887 = (resolvex loc env1 x)
in (match (uu____2887) with
| (loc1, env2, xbv) -> begin
(

let uu____2909 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc1), (env2), (LocalBinder (((xbv), (aq1)))), (uu____2909), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l1 = (FStar_ToSyntax_Env.fail_or env1 (FStar_ToSyntax_Env.try_lookup_datacon env1) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____2921 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), ([])))))
in ((loc), (env1), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____2921), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = uu____2945}, args) -> begin
(

let uu____2951 = (FStar_List.fold_right (fun arg uu____2992 -> (match (uu____2992) with
| (loc1, env2, args1) -> begin
(

let uu____3040 = (aux loc1 env2 arg)
in (match (uu____3040) with
| (loc2, env3, uu____3069, arg1, imp) -> begin
((loc2), (env3), ((((arg1), (imp)))::args1))
end))
end)) args ((loc), (env1), ([])))
in (match (uu____2951) with
| (loc1, env2, args1) -> begin
(

let l1 = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_datacon env2) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____3139 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args1)))))
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3139), (false)))))
end))
end
| FStar_Parser_AST.PatApp (uu____3156) -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected pattern"), (p1.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let uu____3178 = (FStar_List.fold_right (fun pat uu____3211 -> (match (uu____3211) with
| (loc1, env2, pats1) -> begin
(

let uu____3243 = (aux loc1 env2 pat)
in (match (uu____3243) with
| (loc2, env3, uu____3268, pat1, uu____3270) -> begin
((loc2), (env3), ((pat1)::pats1))
end))
end)) pats ((loc), (env1), ([])))
in (match (uu____3178) with
| (loc1, env2, pats1) -> begin
(

let pat = (

let uu____3313 = (

let uu____3316 = (

let uu____3321 = (FStar_Range.end_range p1.FStar_Parser_AST.prange)
in (pos_r uu____3321))
in (

let uu____3322 = (

let uu____3323 = (

let uu____3336 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____3336), ([])))
in FStar_Syntax_Syntax.Pat_cons (uu____3323))
in (FStar_All.pipe_left uu____3316 uu____3322)))
in (FStar_List.fold_right (fun hd1 tl1 -> (

let r = (FStar_Range.union_ranges hd1.FStar_Syntax_Syntax.p tl1.FStar_Syntax_Syntax.p)
in (

let uu____3368 = (

let uu____3369 = (

let uu____3382 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)))
in ((uu____3382), ((((hd1), (false)))::(((tl1), (false)))::[])))
in FStar_Syntax_Syntax.Pat_cons (uu____3369))
in (FStar_All.pipe_left (pos_r r) uu____3368)))) pats1 uu____3313))
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep1) -> begin
(

let uu____3426 = (FStar_List.fold_left (fun uu____3466 p2 -> (match (uu____3466) with
| (loc1, env2, pats) -> begin
(

let uu____3515 = (aux loc1 env2 p2)
in (match (uu____3515) with
| (loc2, env3, uu____3544, pat, uu____3546) -> begin
((loc2), (env3), ((((pat), (false)))::pats))
end))
end)) ((loc), (env1), ([])) args)
in (match (uu____3426) with
| (loc1, env2, args1) -> begin
(

let args2 = (FStar_List.rev args1)
in (

let l = (match (dep1) with
| true -> begin
(FStar_Parser_Const.mk_dtuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end
| uu____3634 -> begin
(FStar_Parser_Const.mk_tuple_data_lid (FStar_List.length args2) p1.FStar_Parser_AST.prange)
end)
in (

let uu____3641 = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_lid env2) l)
in (match (uu____3641) with
| (constr, uu____3663) -> begin
(

let l1 = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____3666 -> begin
(failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (p1.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (

let uu____3668 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l1), (args2)))))
in ((loc1), (env2), (LocalBinder (((x), (FStar_Pervasives_Native.None)))), (uu____3668), (false)))))
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

let fields1 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____3739 -> (match (uu____3739) with
| (f, p2) -> begin
((f.FStar_Ident.ident), (p2))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____3769 -> (match (uu____3769) with
| (f, uu____3775) -> begin
(

let uu____3776 = (FStar_All.pipe_right fields1 (FStar_List.tryFind (fun uu____3802 -> (match (uu____3802) with
| (g, uu____3808) -> begin
(Prims.op_Equality f.FStar_Ident.idText g.FStar_Ident.idText)
end))))
in (match (uu____3776) with
| FStar_Pervasives_Native.None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p1.FStar_Parser_AST.prange)
end
| FStar_Pervasives_Native.Some (uu____3813, p2) -> begin
p2
end))
end))))
in (

let app = (

let uu____3820 = (

let uu____3821 = (

let uu____3828 = (

let uu____3829 = (

let uu____3830 = (FStar_Ident.lid_of_ids (FStar_List.append record.FStar_ToSyntax_Env.typename.FStar_Ident.ns ((record.FStar_ToSyntax_Env.constrname)::[])))
in FStar_Parser_AST.PatName (uu____3830))
in (FStar_Parser_AST.mk_pattern uu____3829 p1.FStar_Parser_AST.prange))
in ((uu____3828), (args)))
in FStar_Parser_AST.PatApp (uu____3821))
in (FStar_Parser_AST.mk_pattern uu____3820 p1.FStar_Parser_AST.prange))
in (

let uu____3833 = (aux loc env1 app)
in (match (uu____3833) with
| (env2, e, b, p2, uu____3862) -> begin
(

let p3 = (match (p2.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args1) -> begin
(

let uu____3890 = (

let uu____3891 = (

let uu____3904 = (

let uu___253_3905 = fv
in (

let uu____3906 = (

let uu____3909 = (

let uu____3910 = (

let uu____3917 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map FStar_Pervasives_Native.fst))
in ((record.FStar_ToSyntax_Env.typename), (uu____3917)))
in FStar_Syntax_Syntax.Record_ctor (uu____3910))
in FStar_Pervasives_Native.Some (uu____3909))
in {FStar_Syntax_Syntax.fv_name = uu___253_3905.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = uu___253_3905.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = uu____3906}))
in ((uu____3904), (args1)))
in FStar_Syntax_Syntax.Pat_cons (uu____3891))
in (FStar_All.pipe_left pos uu____3890))
end
| uu____3944 -> begin
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

let uu____3994 = (aux' true loc env1 p2)
in (match (uu____3994) with
| (loc1, env2, var, p3, uu____4021) -> begin
(

let uu____4026 = (FStar_List.fold_left (fun uu____4058 p4 -> (match (uu____4058) with
| (loc2, env3, ps1) -> begin
(

let uu____4091 = (aux' true loc2 env3 p4)
in (match (uu____4091) with
| (loc3, env4, uu____4116, p5, uu____4118) -> begin
((loc3), (env4), ((p5)::ps1))
end))
end)) ((loc1), (env2), ([])) ps)
in (match (uu____4026) with
| (loc2, env3, ps1) -> begin
(

let pats = (p3)::(FStar_List.rev ps1)
in ((env3), (var), (pats)))
end))
end))
end
| uu____4169 -> begin
(

let uu____4170 = (aux' true loc env1 p1)
in (match (uu____4170) with
| (loc1, env2, vars, pat, b) -> begin
((env2), (vars), ((pat)::[]))
end))
end)))
in (

let uu____4210 = (aux_maybe_or env p)
in (match (uu____4210) with
| (env1, b, pats) -> begin
((

let uu____4241 = (FStar_List.map (fun pats1 -> (check_linear_pattern_variables pats1 p.FStar_Parser_AST.prange)) pats)
in (FStar_All.pipe_left FStar_Pervasives.ignore uu____4241));
((env1), (b), (pats));
)
end))))));
)))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.list) = (fun top env p is_mut -> (

let mklet = (fun x -> (

let uu____4278 = (

let uu____4279 = (

let uu____4284 = (FStar_ToSyntax_Env.qualify env x)
in ((uu____4284), (FStar_Syntax_Syntax.tun)))
in LetBinder (uu____4279))
in ((env), (uu____4278), ([]))))
in (match (top) with
| true -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(

let uu____4304 = (

let uu____4305 = (

let uu____4310 = (FStar_Parser_AST.compile_op (Prims.parse_int "0") x.FStar_Ident.idText x.FStar_Ident.idRange)
in ((uu____4310), (x.FStar_Ident.idRange)))
in (FStar_Ident.mk_ident uu____4305))
in (mklet uu____4304))
end
| FStar_Parser_AST.PatVar (x, uu____4312) -> begin
(mklet x)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, uu____4318); FStar_Parser_AST.prange = uu____4319}, t) -> begin
(

let uu____4325 = (

let uu____4326 = (

let uu____4331 = (FStar_ToSyntax_Env.qualify env x)
in (

let uu____4332 = (desugar_term env t)
in ((uu____4331), (uu____4332))))
in LetBinder (uu____4326))
in ((env), (uu____4325), ([])))
end
| uu____4335 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end
| uu____4344 -> begin
(

let uu____4345 = (desugar_data_pat env p is_mut)
in (match (uu____4345) with
| (env1, binder, p1) -> begin
(

let p2 = (match (p1) with
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_var (uu____4374); FStar_Syntax_Syntax.p = uu____4375})::[] -> begin
[]
end
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (uu____4380); FStar_Syntax_Syntax.p = uu____4381})::[] -> begin
[]
end
| uu____4386 -> begin
p1
end)
in ((env1), (binder), (p2)))
end))
end)))
and desugar_binding_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.list) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat Prims.list) = (fun uu____4393 env pat -> (

let uu____4396 = (desugar_data_pat env pat false)
in (match (uu____4396) with
| (env1, uu____4412, pat1) -> begin
((env1), (pat1))
end)))
and desugar_match_pat : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat Prims.list) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env1 = (FStar_ToSyntax_Env.set_expect_typ env false)
in (desugar_term_maybe_top false env1 e)))
and desugar_typ : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env1 = (FStar_ToSyntax_Env.set_expect_typ env true)
in (desugar_term_maybe_top false env1 e)))
and desugar_machine_integer : FStar_ToSyntax_Env.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.term = (fun env repr uu____4430 range -> (match (uu____4430) with
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

let uu____4440 = (

let uu____4441 = (FStar_Const.within_bounds repr signedness width)
in (not (uu____4441)))
in (match (uu____4440) with
| true -> begin
(

let uu____4442 = (

let uu____4443 = (

let uu____4448 = (FStar_Util.format2 "%s is not in the expected range for %s" repr tnm)
in ((uu____4448), (range)))
in FStar_Errors.Error (uu____4443))
in (FStar_Exn.raise uu____4442))
end
| uu____4449 -> begin
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

let uu____4456 = (FStar_ToSyntax_Env.try_lookup_lid env lid)
in (match (uu____4456) with
| FStar_Pervasives_Native.Some (intro_term, uu____4466) -> begin
(match (intro_term.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let private_lid = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text private_intro_nm) range)
in (

let private_fv = (

let uu____4476 = (FStar_Syntax_Util.incr_delta_depth fv.FStar_Syntax_Syntax.fv_delta)
in (FStar_Syntax_Syntax.lid_as_fv private_lid uu____4476 fv.FStar_Syntax_Syntax.fv_qual))
in (

let uu___254_4477 = intro_term
in {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (private_fv); FStar_Syntax_Syntax.pos = uu___254_4477.FStar_Syntax_Syntax.pos; FStar_Syntax_Syntax.vars = uu___254_4477.FStar_Syntax_Syntax.vars})))
end
| uu____4478 -> begin
(failwith (Prims.strcat "Unexpected non-fvar for " intro_nm))
end)
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4485 = (

let uu____4486 = (

let uu____4491 = (FStar_Util.format1 "Unexpected numeric literal.  Restart F* to load %s." tnm)
in ((uu____4491), (range)))
in FStar_Errors.Error (uu____4486))
in (FStar_Exn.raise uu____4485))
end))
in (

let repr1 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (FStar_Pervasives_Native.None))))) FStar_Pervasives_Native.None range)
in (

let uu____4507 = (

let uu____4510 = (

let uu____4511 = (

let uu____4526 = (

let uu____4535 = (

let uu____4542 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr1), (uu____4542)))
in (uu____4535)::[])
in ((lid1), (uu____4526)))
in FStar_Syntax_Syntax.Tm_app (uu____4511))
in (FStar_Syntax_Syntax.mk uu____4510))
in (uu____4507 FStar_Pervasives_Native.None range)))))));
))
end))
and desugar_name : (FStar_Syntax_Syntax.term'  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  env_t  ->  Prims.bool  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.term = (fun mk1 setpos env resolve l -> (

let uu____4581 = (FStar_ToSyntax_Env.fail_or env ((match (resolve) with
| true -> begin
FStar_ToSyntax_Env.try_lookup_lid
end
| uu____4590 -> begin
FStar_ToSyntax_Env.try_lookup_lid_no_resolve
end) env) l)
in (match (uu____4581) with
| (tm, mut) -> begin
(

let tm1 = (setpos tm)
in (match (mut) with
| true -> begin
(

let uu____4596 = (

let uu____4597 = (

let uu____4604 = (mk_ref_read tm1)
in ((uu____4604), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval))))
in FStar_Syntax_Syntax.Tm_meta (uu____4597))
in (FStar_All.pipe_left mk1 uu____4596))
end
| uu____4609 -> begin
tm1
end))
end)))
and desugar_attributes : env_t  ->  FStar_Parser_AST.term Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun env cattributes -> (

let desugar_attribute = (fun t -> (

let uu____4620 = (

let uu____4621 = (unparen t)
in uu____4621.FStar_Parser_AST.tm)
in (match (uu____4620) with
| FStar_Parser_AST.Var ({FStar_Ident.ns = uu____4622; FStar_Ident.ident = uu____4623; FStar_Ident.nsstr = uu____4624; FStar_Ident.str = "cps"}) -> begin
FStar_Syntax_Syntax.CPS
end
| uu____4627 -> begin
(

let uu____4628 = (

let uu____4629 = (

let uu____4634 = (

let uu____4635 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "Unknown attribute " uu____4635))
in ((uu____4634), (t.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____4629))
in (FStar_Exn.raise uu____4628))
end)))
in (FStar_List.map desugar_attribute cattributes)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (

let mk1 = (fun e -> (FStar_Syntax_Syntax.mk e FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let uu___255_4655 = e
in {FStar_Syntax_Syntax.n = uu___255_4655.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___255_4655.FStar_Syntax_Syntax.vars}))
in (

let uu____4658 = (

let uu____4659 = (unparen top)
in uu____4659.FStar_Parser_AST.tm)
in (match (uu____4658) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (uu____4660) -> begin
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
| FStar_Parser_AST.Op (op_star, (uu____4711)::(uu____4712)::[]) when ((Prims.op_Equality (FStar_Ident.text_of_id op_star) "*") && (

let uu____4716 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range op_star)
in (FStar_All.pipe_right uu____4716 FStar_Option.isNone))) -> begin
(

let rec flatten1 = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ({FStar_Ident.idText = "*"; FStar_Ident.idRange = uu____4729}, (t1)::(t2)::[]) -> begin
(

let uu____4734 = (flatten1 t1)
in (FStar_List.append uu____4734 ((t2)::[])))
end
| uu____4737 -> begin
(t)::[]
end))
in (

let targs = (

let uu____4741 = (

let uu____4744 = (unparen top)
in (flatten1 uu____4744))
in (FStar_All.pipe_right uu____4741 (FStar_List.map (fun t -> (

let uu____4752 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg uu____4752))))))
in (

let uu____4753 = (

let uu____4758 = (FStar_Parser_Const.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) uu____4758))
in (match (uu____4753) with
| (tup, uu____4764) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(

let uu____4768 = (

let uu____4771 = (FStar_ToSyntax_Env.fail_or2 (FStar_ToSyntax_Env.try_lookup_id env) a)
in (FStar_Pervasives_Native.fst uu____4771))
in (FStar_All.pipe_left setpos uu____4768))
end
| FStar_Parser_AST.Uvar (u) -> begin
(FStar_Exn.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected universe variable " (Prims.strcat (FStar_Ident.text_of_id u) " in non-universe context"))), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(

let uu____4791 = (op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)
in (match (uu____4791) with
| FStar_Pervasives_Native.None -> begin
(FStar_Exn.raise (FStar_Errors.Error ((((Prims.strcat "Unexpected or unbound operator: " (FStar_Ident.text_of_id s))), (top.FStar_Parser_AST.range)))))
end
| FStar_Pervasives_Native.Some (op) -> begin
(match (((FStar_List.length args) > (Prims.parse_int "0"))) with
| true -> begin
(

let args1 = (FStar_All.pipe_right args (FStar_List.map (fun t -> (

let uu____4823 = (desugar_term env t)
in ((uu____4823), (FStar_Pervasives_Native.None))))))
in (mk1 (FStar_Syntax_Syntax.Tm_app (((op), (args1))))))
end
| uu____4834 -> begin
op
end)
end))
end
| FStar_Parser_AST.Construct (n1, ((a, uu____4837))::[]) when (Prims.op_Equality n1.FStar_Ident.str "SMTPat") -> begin
(

let uu____4852 = (

let uu___256_4853 = top
in (

let uu____4854 = (

let uu____4855 = (

let uu____4862 = (

let uu___257_4863 = top
in (

let uu____4864 = (

let uu____4865 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____4865))
in {FStar_Parser_AST.tm = uu____4864; FStar_Parser_AST.range = uu___257_4863.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___257_4863.FStar_Parser_AST.level}))
in ((uu____4862), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____4855))
in {FStar_Parser_AST.tm = uu____4854; FStar_Parser_AST.range = uu___256_4853.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___256_4853.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____4852))
end
| FStar_Parser_AST.Construct (n1, ((a, uu____4868))::[]) when (Prims.op_Equality n1.FStar_Ident.str "SMTPatT") -> begin
((FStar_Errors.warn top.FStar_Parser_AST.range "SMTPatT is deprecated; please just use SMTPat");
(

let uu____4884 = (

let uu___258_4885 = top
in (

let uu____4886 = (

let uu____4887 = (

let uu____4894 = (

let uu___259_4895 = top
in (

let uu____4896 = (

let uu____4897 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____4897))
in {FStar_Parser_AST.tm = uu____4896; FStar_Parser_AST.range = uu___259_4895.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___259_4895.FStar_Parser_AST.level}))
in ((uu____4894), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____4887))
in {FStar_Parser_AST.tm = uu____4886; FStar_Parser_AST.range = uu___258_4885.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___258_4885.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____4884));
)
end
| FStar_Parser_AST.Construct (n1, ((a, uu____4900))::[]) when (Prims.op_Equality n1.FStar_Ident.str "SMTPatOr") -> begin
(

let uu____4915 = (

let uu___260_4916 = top
in (

let uu____4917 = (

let uu____4918 = (

let uu____4925 = (

let uu___261_4926 = top
in (

let uu____4927 = (

let uu____4928 = (FStar_Ident.lid_of_path (("Prims")::("smt_pat_or")::[]) top.FStar_Parser_AST.range)
in FStar_Parser_AST.Var (uu____4928))
in {FStar_Parser_AST.tm = uu____4927; FStar_Parser_AST.range = uu___261_4926.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___261_4926.FStar_Parser_AST.level}))
in ((uu____4925), (a), (FStar_Parser_AST.Nothing)))
in FStar_Parser_AST.App (uu____4918))
in {FStar_Parser_AST.tm = uu____4917; FStar_Parser_AST.range = uu___260_4916.FStar_Parser_AST.range; FStar_Parser_AST.level = uu___260_4916.FStar_Parser_AST.level}))
in (desugar_term_maybe_top top_level env uu____4915))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____4929; FStar_Ident.ident = uu____4930; FStar_Ident.nsstr = uu____4931; FStar_Ident.str = "Type0"}) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____4934; FStar_Ident.ident = uu____4935; FStar_Ident.nsstr = uu____4936; FStar_Ident.str = "Type"}) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Construct ({FStar_Ident.ns = uu____4939; FStar_Ident.ident = uu____4940; FStar_Ident.nsstr = uu____4941; FStar_Ident.str = "Type"}, ((t, FStar_Parser_AST.UnivApp))::[]) -> begin
(

let uu____4959 = (

let uu____4960 = (desugar_universe t)
in FStar_Syntax_Syntax.Tm_type (uu____4960))
in (mk1 uu____4959))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____4961; FStar_Ident.ident = uu____4962; FStar_Ident.nsstr = uu____4963; FStar_Ident.str = "Effect"}) -> begin
(mk1 (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____4966; FStar_Ident.ident = uu____4967; FStar_Ident.nsstr = uu____4968; FStar_Ident.str = "True"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.true_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = uu____4971; FStar_Ident.ident = uu____4972; FStar_Ident.nsstr = uu____4973; FStar_Ident.str = "False"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Parser_Const.false_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
end
| FStar_Parser_AST.Projector (eff_name, {FStar_Ident.idText = txt; FStar_Ident.idRange = uu____4978}) when ((is_special_effect_combinator txt) && (FStar_ToSyntax_Env.is_effect_name env eff_name)) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env eff_name);
(

let uu____4980 = (FStar_ToSyntax_Env.try_lookup_effect_defn env eff_name)
in (match (uu____4980) with
| FStar_Pervasives_Native.Some (ed) -> begin
(

let lid = (FStar_Syntax_Util.dm4f_lid ed txt)
in (FStar_Syntax_Syntax.fvar lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____4985 = (FStar_Util.format2 "Member %s of effect %s is not accessible (using an effect abbreviation instead of the original effect ?)" (FStar_Ident.text_of_lid eff_name) txt)
in (failwith uu____4985))
end));
)
end
| FStar_Parser_AST.Assign (ident, t2) -> begin
(

let t21 = (desugar_term env t2)
in (

let uu____4989 = (FStar_ToSyntax_Env.fail_or2 (FStar_ToSyntax_Env.try_lookup_id env) ident)
in (match (uu____4989) with
| (t1, mut) -> begin
((match ((not (mut))) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Can only assign to mutable values"), (top.FStar_Parser_AST.range)))))
end
| uu____5001 -> begin
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

let uu____5016 = (FStar_ToSyntax_Env.try_lookup_datacon env l)
in (match (uu____5016) with
| FStar_Pervasives_Native.Some (uu____5025) -> begin
FStar_Pervasives_Native.Some (((true), (l)))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____5030 = (FStar_ToSyntax_Env.try_lookup_root_effect_name env l)
in (match (uu____5030) with
| FStar_Pervasives_Native.Some (new_name) -> begin
FStar_Pervasives_Native.Some (((false), (new_name)))
end
| uu____5044 -> begin
FStar_Pervasives_Native.None
end))
end))
in (match (name) with
| FStar_Pervasives_Native.Some (resolve, new_name) -> begin
(

let uu____5057 = (FStar_Syntax_Util.mk_field_projector_name_from_ident new_name i)
in (desugar_name mk1 setpos env resolve uu____5057))
end
| uu____5058 -> begin
(

let uu____5065 = (

let uu____5066 = (

let uu____5071 = (FStar_Util.format1 "Data constructor or effect %s not found" l.FStar_Ident.str)
in ((uu____5071), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____5066))
in (FStar_Exn.raise uu____5065))
end));
)
end
| FStar_Parser_AST.Discrim (lid) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env lid);
(

let uu____5074 = (FStar_ToSyntax_Env.try_lookup_datacon env lid)
in (match (uu____5074) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5077 = (

let uu____5078 = (

let uu____5083 = (FStar_Util.format1 "Data constructor %s not found" lid.FStar_Ident.str)
in ((uu____5083), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____5078))
in (FStar_Exn.raise uu____5077))
end
| uu____5084 -> begin
(

let lid' = (FStar_Syntax_Util.mk_discriminator lid)
in (desugar_name mk1 setpos env true lid'))
end));
)
end
| FStar_Parser_AST.Construct (l, args) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env l);
(

let uu____5103 = (FStar_ToSyntax_Env.try_lookup_datacon env l)
in (match (uu____5103) with
| FStar_Pervasives_Native.Some (head1) -> begin
(

let uu____5107 = (

let uu____5114 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (head1)))
in ((uu____5114), (true)))
in (match (uu____5107) with
| (head2, is_data) -> begin
(match (args) with
| [] -> begin
head2
end
| uu____5129 -> begin
(

let uu____5136 = (FStar_Util.take (fun uu____5160 -> (match (uu____5160) with
| (uu____5165, imp) -> begin
(Prims.op_Equality imp FStar_Parser_AST.UnivApp)
end)) args)
in (match (uu____5136) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun x -> (desugar_universe (FStar_Pervasives_Native.fst x))) universes)
in (

let args2 = (FStar_List.map (fun uu____5229 -> (match (uu____5229) with
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
| uu____5250 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_uinst (((head2), (universes1)))))
end)
in (

let app = (mk1 (FStar_Syntax_Syntax.Tm_app (((head3), (args2)))))
in (match (is_data) with
| true -> begin
(mk1 (FStar_Syntax_Syntax.Tm_meta (((app), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end
| uu____5270 -> begin
app
end)))))
end))
end)
end))
end
| FStar_Pervasives_Native.None -> begin
(

let error_msg = (

let uu____5272 = (FStar_ToSyntax_Env.try_lookup_effect_name env l)
in (match (uu____5272) with
| FStar_Pervasives_Native.None -> begin
(Prims.strcat "Constructor " (Prims.strcat l.FStar_Ident.str " not found"))
end
| FStar_Pervasives_Native.Some (uu____5275) -> begin
(Prims.strcat "Effect " (Prims.strcat l.FStar_Ident.str " used at an unexpected position"))
end))
in (FStar_Exn.raise (FStar_Errors.Error (((error_msg), (top.FStar_Parser_AST.range))))))
end));
)
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let uu____5282 = (FStar_List.fold_left (fun uu____5327 b -> (match (uu____5327) with
| (env1, tparams, typs) -> begin
(

let uu____5384 = (desugar_binder env1 b)
in (match (uu____5384) with
| (xopt, t1) -> begin
(

let uu____5413 = (match (xopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____5422 = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env1), (uu____5422)))
end
| FStar_Pervasives_Native.Some (x) -> begin
(FStar_ToSyntax_Env.push_bv env1 x)
end)
in (match (uu____5413) with
| (env2, x) -> begin
(

let uu____5442 = (

let uu____5445 = (

let uu____5448 = (

let uu____5449 = (no_annot_abs tparams t1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____5449))
in (uu____5448)::[])
in (FStar_List.append typs uu____5445))
in ((env2), ((FStar_List.append tparams (((((

let uu___262_5475 = x
in {FStar_Syntax_Syntax.ppname = uu___262_5475.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___262_5475.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})), (FStar_Pervasives_Native.None)))::[]))), (uu____5442)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type_level FStar_Pervasives_Native.None))::[])))
in (match (uu____5282) with
| (env1, uu____5499, targs) -> begin
(

let uu____5521 = (

let uu____5526 = (FStar_Parser_Const.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_ToSyntax_Env.fail_or env1 (FStar_ToSyntax_Env.try_lookup_lid env1) uu____5526))
in (match (uu____5521) with
| (tup, uu____5532) -> begin
(FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let uu____5543 = (uncurry binders t)
in (match (uu____5543) with
| (bs, t1) -> begin
(

let rec aux = (fun env1 bs1 uu___229_5575 -> (match (uu___229_5575) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range env1 t1)
in (

let uu____5589 = (FStar_Syntax_Util.arrow (FStar_List.rev bs1) cod)
in (FStar_All.pipe_left setpos uu____5589)))
end
| (hd1)::tl1 -> begin
(

let bb = (desugar_binder env1 hd1)
in (

let uu____5611 = (as_binder env1 hd1.FStar_Parser_AST.aqual bb)
in (match (uu____5611) with
| (b, env2) -> begin
(aux env2 ((b)::bs1) tl1)
end)))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(

let uu____5626 = (desugar_binder env b)
in (match (uu____5626) with
| (FStar_Pervasives_Native.None, uu____5633) -> begin
(failwith "Missing binder in refinement")
end
| b1 -> begin
(

let uu____5643 = (as_binder env FStar_Pervasives_Native.None b1)
in (match (uu____5643) with
| ((x, uu____5649), env1) -> begin
(

let f1 = (desugar_formula env1 f)
in (

let uu____5656 = (FStar_Syntax_Util.refine x f1)
in (FStar_All.pipe_left setpos uu____5656)))
end))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let binders1 = (FStar_All.pipe_right binders (FStar_List.map replace_unit_pattern))
in (

let uu____5676 = (FStar_List.fold_left (fun uu____5696 pat -> (match (uu____5696) with
| (env1, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (uu____5722, t) -> begin
(

let uu____5724 = (

let uu____5727 = (free_type_vars env1 t)
in (FStar_List.append uu____5727 ftvs))
in ((env1), (uu____5724)))
end
| uu____5732 -> begin
((env1), (ftvs))
end)
end)) ((env), ([])) binders1)
in (match (uu____5676) with
| (uu____5737, ftv) -> begin
(

let ftv1 = (sort_ftv ftv)
in (

let binders2 = (

let uu____5749 = (FStar_All.pipe_right ftv1 (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (FStar_Pervasives_Native.Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append uu____5749 binders1))
in (

let rec aux = (fun env1 bs sc_pat_opt uu___230_5790 -> (match (uu___230_5790) with
| [] -> begin
(

let body1 = (desugar_term env1 body)
in (

let body2 = (match (sc_pat_opt) with
| FStar_Pervasives_Native.Some (sc, pat) -> begin
(

let body2 = (

let uu____5828 = (

let uu____5829 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right uu____5829 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close uu____5828 body1))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (FStar_Pervasives_Native.None), (body2)))::[])))) FStar_Pervasives_Native.None body2.FStar_Syntax_Syntax.pos))
end
| FStar_Pervasives_Native.None -> begin
body1
end)
in (

let uu____5882 = (no_annot_abs (FStar_List.rev bs) body2)
in (setpos uu____5882))))
end
| (p)::rest -> begin
(

let uu____5893 = (desugar_binding_pat env1 p)
in (match (uu____5893) with
| (env2, b, pat) -> begin
(

let pat1 = (match (pat) with
| [] -> begin
FStar_Pervasives_Native.None
end
| (p1)::[] -> begin
FStar_Pervasives_Native.Some (p1)
end
| uu____5917 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Disjunctive patterns are not supported in abstractions"), (p.FStar_Parser_AST.prange)))))
end)
in (

let uu____5922 = (match (b) with
| LetBinder (uu____5955) -> begin
(failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt1 = (match (((pat1), (sc_pat_opt))) with
| (FStar_Pervasives_Native.None, uu____6005) -> begin
sc_pat_opt
end
| (FStar_Pervasives_Native.Some (p1), FStar_Pervasives_Native.None) -> begin
(

let uu____6041 = (

let uu____6046 = (FStar_Syntax_Syntax.bv_to_name x)
in ((uu____6046), (p1)))
in FStar_Pervasives_Native.Some (uu____6041))
end
| (FStar_Pervasives_Native.Some (p1), FStar_Pervasives_Native.Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (uu____6082), uu____6083) -> begin
(

let tup2 = (

let uu____6085 = (FStar_Parser_Const.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____6085 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____6089 = (

let uu____6092 = (

let uu____6093 = (

let uu____6108 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (

let uu____6111 = (

let uu____6114 = (FStar_Syntax_Syntax.as_arg sc)
in (

let uu____6115 = (

let uu____6118 = (

let uu____6119 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____6119))
in (uu____6118)::[])
in (uu____6114)::uu____6115))
in ((uu____6108), (uu____6111))))
in FStar_Syntax_Syntax.Tm_app (uu____6093))
in (FStar_Syntax_Syntax.mk uu____6092))
in (uu____6089 FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
in (

let p2 = (

let uu____6130 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p1), (false)))::[])))) uu____6130))
in FStar_Pervasives_Native.Some (((sc1), (p2))))))
end
| (FStar_Syntax_Syntax.Tm_app (uu____6161, args), FStar_Syntax_Syntax.Pat_cons (uu____6163, pats)) -> begin
(

let tupn = (

let uu____6202 = (FStar_Parser_Const.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv uu____6202 FStar_Syntax_Syntax.Delta_constant (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc1 = (

let uu____6212 = (

let uu____6213 = (

let uu____6228 = (mk1 (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (

let uu____6231 = (

let uu____6240 = (

let uu____6249 = (

let uu____6250 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____6250))
in (uu____6249)::[])
in (FStar_List.append args uu____6240))
in ((uu____6228), (uu____6231))))
in FStar_Syntax_Syntax.Tm_app (uu____6213))
in (mk1 uu____6212))
in (

let p2 = (

let uu____6270 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p1.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p1), (false)))::[])))))) uu____6270))
in FStar_Pervasives_Native.Some (((sc1), (p2))))))
end
| uu____6305 -> begin
(failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt1)))
end)
in (match (uu____5922) with
| (b1, sc_pat_opt1) -> begin
(aux env2 ((b1)::bs) sc_pat_opt1 rest)
end)))
end))
end))
in (aux env [] FStar_Pervasives_Native.None binders2))))
end)))
end
| FStar_Parser_AST.App (uu____6372, uu____6373, FStar_Parser_AST.UnivApp) -> begin
(

let rec aux = (fun universes e -> (

let uu____6387 = (

let uu____6388 = (unparen e)
in uu____6388.FStar_Parser_AST.tm)
in (match (uu____6387) with
| FStar_Parser_AST.App (e1, t, FStar_Parser_AST.UnivApp) -> begin
(

let univ_arg = (desugar_universe t)
in (aux ((univ_arg)::universes) e1))
end
| uu____6394 -> begin
(

let head1 = (desugar_term env e)
in (mk1 (FStar_Syntax_Syntax.Tm_uinst (((head1), (universes))))))
end)))
in (aux [] top))
end
| FStar_Parser_AST.App (uu____6398) -> begin
(

let rec aux = (fun args e -> (

let uu____6430 = (

let uu____6431 = (unparen e)
in uu____6431.FStar_Parser_AST.tm)
in (match (uu____6430) with
| FStar_Parser_AST.App (e1, t, imp) when (Prims.op_disEquality imp FStar_Parser_AST.UnivApp) -> begin
(

let arg = (

let uu____6444 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) uu____6444))
in (aux ((arg)::args) e1))
end
| uu____6457 -> begin
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

let uu____6483 = (

let uu____6484 = (FStar_Ident.lid_of_path (("bind")::[]) x.FStar_Ident.idRange)
in FStar_Parser_AST.Var (uu____6484))
in (FStar_Parser_AST.mk_term uu____6483 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let uu____6485 = (FStar_Parser_AST.mkExplicitApp bind1 ((t1)::(k)::[]) top.FStar_Parser_AST.range)
in (desugar_term env uu____6485)))))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(

let uu____6488 = (

let uu____6489 = (

let uu____6496 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((uu____6496), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))
in FStar_Syntax_Syntax.Tm_meta (uu____6489))
in (mk1 uu____6488))
end
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(

let env1 = (FStar_ToSyntax_Env.push_namespace env lid)
in (

let uu____6514 = (

let uu____6519 = (FStar_ToSyntax_Env.expect_typ env1)
in (match (uu____6519) with
| true -> begin
desugar_typ
end
| uu____6524 -> begin
desugar_term
end))
in (uu____6514 env1 e)))
end
| FStar_Parser_AST.Let (qual1, ((pat, _snd))::_tl, body) -> begin
(

let is_rec = (Prims.op_Equality qual1 FStar_Parser_AST.Rec)
in (

let ds_let_rec_or_app = (fun uu____6552 -> (

let bindings = (((pat), (_snd)))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun uu____6638 -> (match (uu____6638) with
| (p, def) -> begin
(

let uu____6663 = (is_app_pattern p)
in (match (uu____6663) with
| true -> begin
(

let uu____6682 = (destruct_app_pattern env top_level p)
in ((uu____6682), (def)))
end
| uu____6711 -> begin
(match ((FStar_Parser_AST.un_function p def)) with
| FStar_Pervasives_Native.Some (p1, def1) -> begin
(

let uu____6736 = (destruct_app_pattern env top_level p1)
in ((uu____6736), (def1)))
end
| uu____6765 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, uu____6791); FStar_Parser_AST.prange = uu____6792}, t) -> begin
(match (top_level) with
| true -> begin
(

let uu____6816 = (

let uu____6831 = (

let uu____6836 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (uu____6836))
in ((uu____6831), ([]), (FStar_Pervasives_Native.Some (t))))
in ((uu____6816), (def)))
end
| uu____6859 -> begin
((((FStar_Util.Inl (id)), ([]), (FStar_Pervasives_Native.Some (t)))), (def))
end)
end
| FStar_Parser_AST.PatVar (id, uu____6883) -> begin
(match (top_level) with
| true -> begin
(

let uu____6906 = (

let uu____6921 = (

let uu____6926 = (FStar_ToSyntax_Env.qualify env id)
in FStar_Util.Inr (uu____6926))
in ((uu____6921), ([]), (FStar_Pervasives_Native.None)))
in ((uu____6906), (def)))
end
| uu____6949 -> begin
((((FStar_Util.Inl (id)), ([]), (FStar_Pervasives_Native.None))), (def))
end)
end
| uu____6972 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end))
end))))
in (

let uu____6991 = (FStar_List.fold_left (fun uu____7051 uu____7052 -> (match (((uu____7051), (uu____7052))) with
| ((env1, fnames, rec_bindings), ((f, uu____7135, uu____7136), uu____7137)) -> begin
(

let uu____7216 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let uu____7242 = (FStar_ToSyntax_Env.push_bv env1 x)
in (match (uu____7242) with
| (env2, xx) -> begin
(

let uu____7261 = (

let uu____7264 = (FStar_Syntax_Syntax.mk_binder xx)
in (uu____7264)::rec_bindings)
in ((env2), (FStar_Util.Inl (xx)), (uu____7261)))
end))
end
| FStar_Util.Inr (l) -> begin
(

let uu____7272 = (FStar_ToSyntax_Env.push_top_level_rec_binding env1 l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in ((uu____7272), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (uu____7216) with
| (env2, lbname, rec_bindings1) -> begin
((env2), ((lbname)::fnames), (rec_bindings1))
end))
end)) ((env), ([]), ([])) funs)
in (match (uu____6991) with
| (env', fnames, rec_bindings) -> begin
(

let fnames1 = (FStar_List.rev fnames)
in (

let rec_bindings1 = (FStar_List.rev rec_bindings)
in (

let desugar_one_def = (fun env1 lbname uu____7398 -> (match (uu____7398) with
| ((uu____7421, args, result_t), def) -> begin
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

let uu____7465 = (is_comp_type env1 t)
in (match (uu____7465) with
| true -> begin
((

let uu____7467 = (FStar_All.pipe_right args1 (FStar_List.tryFind (fun x -> (

let uu____7477 = (is_var_pattern x)
in (not (uu____7477))))))
in (match (uu____7467) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (p) -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable"), (p.FStar_Parser_AST.prange)))))
end));
t;
)
end
| uu____7479 -> begin
(

let uu____7480 = (((FStar_Options.ml_ish ()) && (

let uu____7482 = (FStar_ToSyntax_Env.try_lookup_effect_name env1 FStar_Parser_Const.effect_ML_lid)
in (FStar_Option.isSome uu____7482))) && ((not (is_rec)) || (Prims.op_disEquality (FStar_List.length args1) (Prims.parse_int "0"))))
in (match (uu____7480) with
| true -> begin
(FStar_Parser_AST.ml_comp t)
end
| uu____7485 -> begin
(FStar_Parser_AST.tot_comp t)
end))
end))
in (

let uu____7486 = (FStar_Range.union_ranges t1.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t1), (FStar_Pervasives_Native.None)))) uu____7486 FStar_Parser_AST.Expr)))
end)
in (

let def2 = (match (args1) with
| [] -> begin
def1
end
| uu____7490 -> begin
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

let uu____7505 = (

let uu____7506 = (FStar_Syntax_Util.incr_delta_qualifier body1)
in (FStar_Syntax_Syntax.lid_as_fv l uu____7506 FStar_Pervasives_Native.None))
in FStar_Util.Inr (uu____7505))
end)
in (

let body2 = (match (is_rec) with
| true -> begin
(FStar_Syntax_Subst.close rec_bindings1 body1)
end
| uu____7508 -> begin
body1
end)
in (mk_lb ((lbname1), (FStar_Syntax_Syntax.tun), (body2)))))))))
end))
in (

let lbs = (FStar_List.map2 (desugar_one_def (match (is_rec) with
| true -> begin
env'
end
| uu____7538 -> begin
env
end)) fnames1 funs)
in (

let body1 = (desugar_term env' body)
in (

let uu____7540 = (

let uu____7541 = (

let uu____7554 = (FStar_Syntax_Subst.close rec_bindings1 body1)
in ((((is_rec), (lbs))), (uu____7554)))
in FStar_Syntax_Syntax.Tm_let (uu____7541))
in (FStar_All.pipe_left mk1 uu____7540)))))))
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
| uu____7584 -> begin
t11
end)
in (

let uu____7585 = (desugar_binding_pat_maybe_top top_level env pat1 is_mutable)
in (match (uu____7585) with
| (env1, binder, pat2) -> begin
(

let tm = (match (binder) with
| LetBinder (l, t) -> begin
(

let body1 = (desugar_term env1 t2)
in (

let fv = (

let uu____7612 = (FStar_Syntax_Util.incr_delta_qualifier t12)
in (FStar_Syntax_Syntax.lid_as_fv l uu____7612 FStar_Pervasives_Native.None))
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_let (((((false), (({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t12})::[]))), (body1)))))))
end
| LocalBinder (x, uu____7624) -> begin
(

let body1 = (desugar_term env1 t2)
in (

let body2 = (match (pat2) with
| [] -> begin
body1
end
| ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (uu____7627); FStar_Syntax_Syntax.p = uu____7628})::[] -> begin
body1
end
| uu____7633 -> begin
(

let uu____7636 = (

let uu____7639 = (

let uu____7640 = (

let uu____7663 = (FStar_Syntax_Syntax.bv_to_name x)
in (

let uu____7664 = (desugar_disjunctive_pattern pat2 FStar_Pervasives_Native.None body1)
in ((uu____7663), (uu____7664))))
in FStar_Syntax_Syntax.Tm_match (uu____7640))
in (FStar_Syntax_Syntax.mk uu____7639))
in (uu____7636 FStar_Pervasives_Native.None top.FStar_Parser_AST.range))
end)
in (

let uu____7674 = (

let uu____7675 = (

let uu____7688 = (

let uu____7689 = (

let uu____7690 = (FStar_Syntax_Syntax.mk_binder x)
in (uu____7690)::[])
in (FStar_Syntax_Subst.close uu____7689 body2))
in ((((false), (((mk_lb ((FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t12))))::[]))), (uu____7688)))
in FStar_Syntax_Syntax.Tm_let (uu____7675))
in (FStar_All.pipe_left mk1 uu____7674))))
end)
in (match (is_mutable) with
| true -> begin
(FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((tm), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc))))))
end
| uu____7715 -> begin
tm
end))
end))))))
in (

let uu____7716 = (is_rec || (is_app_pattern pat))
in (match (uu____7716) with
| true -> begin
(ds_let_rec_or_app ())
end
| uu____7717 -> begin
(ds_non_rec pat _snd body)
end)))))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (FStar_Pervasives_Native.Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (

let t_bool1 = (

let uu____7725 = (

let uu____7726 = (FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.bool_lid FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None)
in FStar_Syntax_Syntax.Tm_fvar (uu____7726))
in (mk1 uu____7725))
in (

let uu____7727 = (

let uu____7728 = (

let uu____7751 = (

let uu____7754 = (desugar_term env t1)
in (FStar_Syntax_Util.ascribe uu____7754 ((FStar_Util.Inl (t_bool1)), (FStar_Pervasives_Native.None))))
in (

let uu____7775 = (

let uu____7790 = (

let uu____7803 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) t2.FStar_Parser_AST.range)
in (

let uu____7806 = (desugar_term env t2)
in ((uu____7803), (FStar_Pervasives_Native.None), (uu____7806))))
in (

let uu____7815 = (

let uu____7830 = (

let uu____7843 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) t3.FStar_Parser_AST.range)
in (

let uu____7846 = (desugar_term env t3)
in ((uu____7843), (FStar_Pervasives_Native.None), (uu____7846))))
in (uu____7830)::[])
in (uu____7790)::uu____7815))
in ((uu____7751), (uu____7775))))
in FStar_Syntax_Syntax.Tm_match (uu____7728))
in (mk1 uu____7727))))
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

let desugar_branch = (fun uu____7987 -> (match (uu____7987) with
| (pat, wopt, b) -> begin
(

let uu____8005 = (desugar_match_pat env pat)
in (match (uu____8005) with
| (env1, pat1) -> begin
(

let wopt1 = (match (wopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (e1) -> begin
(

let uu____8026 = (desugar_term env1 e1)
in FStar_Pervasives_Native.Some (uu____8026))
end)
in (

let b1 = (desugar_term env1 b)
in (desugar_disjunctive_pattern pat1 wopt1 b1)))
end))
end))
in (

let uu____8028 = (

let uu____8029 = (

let uu____8052 = (desugar_term env e)
in (

let uu____8053 = (FStar_List.collect desugar_branch branches)
in ((uu____8052), (uu____8053))))
in FStar_Syntax_Syntax.Tm_match (uu____8029))
in (FStar_All.pipe_left mk1 uu____8028)))
end
| FStar_Parser_AST.Ascribed (e, t, tac_opt) -> begin
(

let annot = (

let uu____8082 = (is_comp_type env t)
in (match (uu____8082) with
| true -> begin
(

let uu____8089 = (desugar_comp t.FStar_Parser_AST.range env t)
in FStar_Util.Inr (uu____8089))
end
| uu____8094 -> begin
(

let uu____8095 = (desugar_term env t)
in FStar_Util.Inl (uu____8095))
end))
in (

let tac_opt1 = (FStar_Util.map_opt tac_opt (desugar_term env))
in (

let uu____8101 = (

let uu____8102 = (

let uu____8129 = (desugar_term env e)
in ((uu____8129), (((annot), (tac_opt1))), (FStar_Pervasives_Native.None)))
in FStar_Syntax_Syntax.Tm_ascribed (uu____8102))
in (FStar_All.pipe_left mk1 uu____8101))))
end
| FStar_Parser_AST.Record (uu____8154, []) -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let record = (check_fields env fields top.FStar_Parser_AST.range)
in (

let user_ns = (

let uu____8191 = (FStar_List.hd fields)
in (match (uu____8191) with
| (f, uu____8203) -> begin
f.FStar_Ident.ns
end))
in (

let get_field = (fun xopt f -> (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun uu____8245 -> (match (uu____8245) with
| (g, uu____8251) -> begin
(Prims.op_Equality f.FStar_Ident.idText g.FStar_Ident.ident.FStar_Ident.idText)
end))))
in (

let fn = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((f)::[])))
in (match (found) with
| FStar_Pervasives_Native.Some (uu____8257, e) -> begin
((fn), (e))
end
| FStar_Pervasives_Native.None -> begin
(match (xopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____8271 = (

let uu____8272 = (

let uu____8277 = (FStar_Util.format2 "Field %s of record type %s is missing" f.FStar_Ident.idText record.FStar_ToSyntax_Env.typename.FStar_Ident.str)
in ((uu____8277), (top.FStar_Parser_AST.range)))
in FStar_Errors.Error (uu____8272))
in (FStar_Exn.raise uu____8271))
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

let uu____8285 = (

let uu____8296 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____8327 -> (match (uu____8327) with
| (f, uu____8337) -> begin
(

let uu____8338 = (

let uu____8339 = (get_field FStar_Pervasives_Native.None f)
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____8339))
in ((uu____8338), (FStar_Parser_AST.Nothing)))
end))))
in ((user_constrname), (uu____8296)))
in FStar_Parser_AST.Construct (uu____8285))
end
| FStar_Pervasives_Native.Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (

let uu____8357 = (

let uu____8358 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____8358))
in (FStar_Parser_AST.mk_term uu____8357 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record1 = (

let uu____8360 = (

let uu____8373 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map (fun uu____8403 -> (match (uu____8403) with
| (f, uu____8413) -> begin
(get_field (FStar_Pervasives_Native.Some (xterm)) f)
end))))
in ((FStar_Pervasives_Native.None), (uu____8373)))
in FStar_Parser_AST.Record (uu____8360))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (FStar_Pervasives_Native.None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record1 top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm1 = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_term env recterm1)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____8441; FStar_Syntax_Syntax.vars = uu____8442}, args); FStar_Syntax_Syntax.pos = uu____8444; FStar_Syntax_Syntax.vars = uu____8445}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(

let e1 = (

let uu____8473 = (

let uu____8474 = (

let uu____8489 = (

let uu____8490 = (

let uu____8493 = (

let uu____8494 = (

let uu____8501 = (FStar_All.pipe_right record.FStar_ToSyntax_Env.fields (FStar_List.map FStar_Pervasives_Native.fst))
in ((record.FStar_ToSyntax_Env.typename), (uu____8501)))
in FStar_Syntax_Syntax.Record_ctor (uu____8494))
in FStar_Pervasives_Native.Some (uu____8493))
in (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant uu____8490))
in ((uu____8489), (args)))
in FStar_Syntax_Syntax.Tm_app (uu____8474))
in (FStar_All.pipe_left mk1 uu____8473))
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((e1), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))))))
end
| uu____8532 -> begin
e
end))))))))
end
| FStar_Parser_AST.Project (e, f) -> begin
((FStar_ToSyntax_Env.fail_if_qualified_by_curmodule env f);
(

let uu____8536 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_dc_by_field_name env) f)
in (match (uu____8536) with
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
| uu____8554 -> begin
FStar_Pervasives_Native.None
end)
in (

let uu____8555 = (

let uu____8556 = (

let uu____8571 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projname (FStar_Ident.range_of_lid f)) FStar_Syntax_Syntax.Delta_equational qual1)
in (

let uu____8572 = (

let uu____8575 = (FStar_Syntax_Syntax.as_arg e1)
in (uu____8575)::[])
in ((uu____8571), (uu____8572))))
in FStar_Syntax_Syntax.Tm_app (uu____8556))
in (FStar_All.pipe_left mk1 uu____8555)))))
end));
)
end
| FStar_Parser_AST.NamedTyp (uu____8580, e) -> begin
(desugar_term env e)
end
| FStar_Parser_AST.Paren (e) -> begin
(desugar_term env e)
end
| uu____8583 when (Prims.op_Equality top.FStar_Parser_AST.level FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| uu____8584 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Let (uu____8585, uu____8586, uu____8587) -> begin
(failwith "Not implemented yet")
end
| FStar_Parser_AST.QForall (uu____8600, uu____8601, uu____8602) -> begin
(failwith "Not implemented yet")
end
| FStar_Parser_AST.QExists (uu____8615, uu____8616, uu____8617) -> begin
(failwith "Not implemented yet")
end)))))
and not_ascribed : FStar_Parser_AST.term  ->  Prims.bool = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Ascribed (uu____8631) -> begin
false
end
| uu____8640 -> begin
true
end))
and is_synth_by_tactic : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun e t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.App (l, r, FStar_Parser_AST.Hash) -> begin
(is_synth_by_tactic e l)
end
| FStar_Parser_AST.Var (lid) -> begin
(

let uu____8646 = (FStar_ToSyntax_Env.resolve_to_fully_qualified_name e lid)
in (match (uu____8646) with
| FStar_Pervasives_Native.Some (lid1) -> begin
(FStar_Ident.lid_equals lid1 FStar_Parser_Const.synth_lid)
end
| FStar_Pervasives_Native.None -> begin
false
end))
end
| uu____8650 -> begin
false
end))
and desugar_args : FStar_ToSyntax_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun uu____8687 -> (match (uu____8687) with
| (a, imp) -> begin
(

let uu____8700 = (desugar_term env a)
in (arg_withimp_e imp uu____8700))
end)))))
and desugar_comp : FStar_Range.range  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax = (fun r env t -> (

let fail = (fun msg -> (FStar_Exn.raise (FStar_Errors.Error (((msg), (r))))))
in (

let is_requires = (fun uu____8719 -> (match (uu____8719) with
| (t1, uu____8725) -> begin
(

let uu____8726 = (

let uu____8727 = (unparen t1)
in uu____8727.FStar_Parser_AST.tm)
in (match (uu____8726) with
| FStar_Parser_AST.Requires (uu____8728) -> begin
true
end
| uu____8735 -> begin
false
end))
end))
in (

let is_ensures = (fun uu____8743 -> (match (uu____8743) with
| (t1, uu____8749) -> begin
(

let uu____8750 = (

let uu____8751 = (unparen t1)
in uu____8751.FStar_Parser_AST.tm)
in (match (uu____8750) with
| FStar_Parser_AST.Ensures (uu____8752) -> begin
true
end
| uu____8759 -> begin
false
end))
end))
in (

let is_app = (fun head1 uu____8770 -> (match (uu____8770) with
| (t1, uu____8776) -> begin
(

let uu____8777 = (

let uu____8778 = (unparen t1)
in uu____8778.FStar_Parser_AST.tm)
in (match (uu____8777) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = uu____8780; FStar_Parser_AST.level = uu____8781}, uu____8782, uu____8783) -> begin
(Prims.op_Equality d.FStar_Ident.ident.FStar_Ident.idText head1)
end
| uu____8784 -> begin
false
end))
end))
in (

let is_smt_pat = (fun uu____8792 -> (match (uu____8792) with
| (t1, uu____8798) -> begin
(

let uu____8799 = (

let uu____8800 = (unparen t1)
in uu____8800.FStar_Parser_AST.tm)
in (match (uu____8799) with
| FStar_Parser_AST.Construct (cons1, (({FStar_Parser_AST.tm = FStar_Parser_AST.Construct (smtpat, uu____8803); FStar_Parser_AST.range = uu____8804; FStar_Parser_AST.level = uu____8805}, uu____8806))::(uu____8807)::[]) -> begin
((FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid) && (FStar_Util.for_some (fun s -> (Prims.op_Equality smtpat.FStar_Ident.str s)) (("SMTPat")::("SMTPatT")::("SMTPatOr")::[])))
end
| FStar_Parser_AST.Construct (cons1, (({FStar_Parser_AST.tm = FStar_Parser_AST.Var (smtpat); FStar_Parser_AST.range = uu____8846; FStar_Parser_AST.level = uu____8847}, uu____8848))::(uu____8849)::[]) -> begin
((FStar_Ident.lid_equals cons1 FStar_Parser_Const.cons_lid) && (FStar_Util.for_some (fun s -> (Prims.op_Equality smtpat.FStar_Ident.str s)) (("smt_pat")::("smt_pat_or")::[])))
end
| uu____8874 -> begin
false
end))
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t1 -> (

let uu____8902 = (head_and_args t1)
in (match (uu____8902) with
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

let thunk_ens = (fun uu____8996 -> (match (uu____8996) with
| (e, i) -> begin
(

let uu____9007 = (thunk_ens_ e)
in ((uu____9007), (i)))
end))
in (

let fail_lemma = (fun uu____9017 -> (

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
(

let uu____9097 = (

let uu____9104 = (

let uu____9111 = (thunk_ens ens)
in (uu____9111)::(nil_pat)::[])
in (req_true)::uu____9104)
in (unit_tm)::uu____9097)
end
| (req)::(ens)::[] when ((is_requires req) && (is_ensures ens)) -> begin
(

let uu____9158 = (

let uu____9165 = (

let uu____9172 = (thunk_ens ens)
in (uu____9172)::(nil_pat)::[])
in (req)::uu____9165)
in (unit_tm)::uu____9158)
end
| (ens)::(smtpat)::[] when ((((

let uu____9221 = (is_requires ens)
in (not (uu____9221))) && (

let uu____9223 = (is_smt_pat ens)
in (not (uu____9223)))) && (

let uu____9225 = (is_decreases ens)
in (not (uu____9225)))) && (is_smt_pat smtpat)) -> begin
(

let uu____9226 = (

let uu____9233 = (

let uu____9240 = (thunk_ens ens)
in (uu____9240)::(smtpat)::[])
in (req_true)::uu____9233)
in (unit_tm)::uu____9226)
end
| (ens)::(dec)::[] when ((is_ensures ens) && (is_decreases dec)) -> begin
(

let uu____9287 = (

let uu____9294 = (

let uu____9301 = (thunk_ens ens)
in (uu____9301)::(nil_pat)::(dec)::[])
in (req_true)::uu____9294)
in (unit_tm)::uu____9287)
end
| (ens)::(dec)::(smtpat)::[] when (((is_ensures ens) && (is_decreases dec)) && (is_smt_pat smtpat)) -> begin
(

let uu____9361 = (

let uu____9368 = (

let uu____9375 = (thunk_ens ens)
in (uu____9375)::(smtpat)::(dec)::[])
in (req_true)::uu____9368)
in (unit_tm)::uu____9361)
end
| (req)::(ens)::(dec)::[] when (((is_requires req) && (is_ensures ens)) && (is_decreases dec)) -> begin
(

let uu____9435 = (

let uu____9442 = (

let uu____9449 = (thunk_ens ens)
in (uu____9449)::(nil_pat)::(dec)::[])
in (req)::uu____9442)
in (unit_tm)::uu____9435)
end
| (req)::(ens)::(smtpat)::[] when (((is_requires req) && (is_ensures ens)) && (is_smt_pat smtpat)) -> begin
(

let uu____9509 = (

let uu____9516 = (

let uu____9523 = (thunk_ens ens)
in (uu____9523)::(smtpat)::[])
in (req)::uu____9516)
in (unit_tm)::uu____9509)
end
| (req)::(ens)::(dec)::(smtpat)::[] when ((((is_requires req) && (is_ensures ens)) && (is_smt_pat smtpat)) && (is_decreases dec)) -> begin
(

let uu____9588 = (

let uu____9595 = (

let uu____9602 = (thunk_ens ens)
in (uu____9602)::(dec)::(smtpat)::[])
in (req)::uu____9595)
in (unit_tm)::uu____9588)
end
| _other -> begin
(fail_lemma ())
end)
in (

let head_and_attributes = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes env) lemma)
in ((head_and_attributes), (args1))))))))))
end
| FStar_Parser_AST.Name (l) when (FStar_ToSyntax_Env.is_effect_name env l) -> begin
(

let uu____9664 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_effect_name_and_attributes env) l)
in ((uu____9664), (args)))
end
| FStar_Parser_AST.Name (l) when ((

let uu____9692 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals uu____9692 FStar_Parser_Const.prims_lid)) && (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Tot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Parser_Const.effect_Tot_lid head1.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when ((

let uu____9710 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals uu____9710 FStar_Parser_Const.prims_lid)) && (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "GTot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Parser_Const.effect_GTot_lid head1.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when (((Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Type") || (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Type0")) || (Prims.op_Equality l.FStar_Ident.ident.FStar_Ident.idText "Effect")) -> begin
(((((FStar_Ident.set_lid_range FStar_Parser_Const.effect_Tot_lid head1.FStar_Parser_AST.range)), ([]))), ((((t1), (FStar_Parser_AST.Nothing)))::[]))
end
| uu____9748 -> begin
(

let default_effect = (

let uu____9750 = (FStar_Options.ml_ish ())
in (match (uu____9750) with
| true -> begin
FStar_Parser_Const.effect_ML_lid
end
| uu____9751 -> begin
((

let uu____9753 = (FStar_Options.warn_default_effects ())
in (match (uu____9753) with
| true -> begin
(FStar_Errors.warn head1.FStar_Parser_AST.range "Using default effect Tot")
end
| uu____9754 -> begin
()
end));
FStar_Parser_Const.effect_Tot_lid;
)
end))
in (((((FStar_Ident.set_lid_range default_effect head1.FStar_Parser_AST.range)), ([]))), ((((t1), (FStar_Parser_AST.Nothing)))::[])))
end)
end)))
in (

let uu____9777 = (pre_process_comp_typ t)
in (match (uu____9777) with
| ((eff, cattributes), args) -> begin
((match ((Prims.op_Equality (FStar_List.length args) (Prims.parse_int "0"))) with
| true -> begin
(

let uu____9826 = (

let uu____9827 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" uu____9827))
in (fail uu____9826))
end
| uu____9828 -> begin
()
end);
(

let is_universe = (fun uu____9836 -> (match (uu____9836) with
| (uu____9841, imp) -> begin
(Prims.op_Equality imp FStar_Parser_AST.UnivApp)
end))
in (

let uu____9843 = (FStar_Util.take is_universe args)
in (match (uu____9843) with
| (universes, args1) -> begin
(

let universes1 = (FStar_List.map (fun uu____9902 -> (match (uu____9902) with
| (u, imp) -> begin
(desugar_universe u)
end)) universes)
in (

let uu____9909 = (

let uu____9924 = (FStar_List.hd args1)
in (

let uu____9933 = (FStar_List.tl args1)
in ((uu____9924), (uu____9933))))
in (match (uu____9909) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (FStar_Pervasives_Native.fst result_arg))
in (

let rest1 = (desugar_args env rest)
in (

let uu____9988 = (

let is_decrease = (fun uu____10024 -> (match (uu____10024) with
| (t1, uu____10034) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____10044; FStar_Syntax_Syntax.vars = uu____10045}, (uu____10046)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.decreases_lid)
end
| uu____10077 -> begin
false
end)
end))
in (FStar_All.pipe_right rest1 (FStar_List.partition is_decrease)))
in (match (uu____9988) with
| (dec, rest2) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun uu____10191 -> (match (uu____10191) with
| (t1, uu____10201) -> begin
(match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (uu____10210, ((arg, uu____10212))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| uu____10241 -> begin
(failwith "impos")
end)
end))))
in (

let no_additional_args = (

let is_empty = (fun l -> (match (l) with
| [] -> begin
true
end
| uu____10255 -> begin
false
end))
in ((((is_empty decreases_clause) && (is_empty rest2)) && (is_empty cattributes)) && (is_empty universes1)))
in (match ((no_additional_args && (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid))) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end
| uu____10268 -> begin
(match ((no_additional_args && (FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid))) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end
| uu____10271 -> begin
(

let flags = (match ((FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Lemma_lid)) with
| true -> begin
(FStar_Syntax_Syntax.LEMMA)::[]
end
| uu____10277 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.TOTAL)::[]
end
| uu____10280 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Parser_Const.effect_ML_lid)) with
| true -> begin
(FStar_Syntax_Syntax.MLEFFECT)::[]
end
| uu____10283 -> begin
(match ((FStar_Ident.lid_equals eff FStar_Parser_Const.effect_GTot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end
| uu____10286 -> begin
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
| uu____10403 -> begin
pat
end)
in (

let uu____10404 = (

let uu____10415 = (

let uu____10426 = (

let uu____10435 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat1), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) FStar_Pervasives_Native.None pat1.FStar_Syntax_Syntax.pos)
in ((uu____10435), (aq)))
in (uu____10426)::[])
in (ens)::uu____10415)
in (req)::uu____10404))
end
| uu____10476 -> begin
rest2
end)
end
| uu____10487 -> begin
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
| uu____10498 -> begin
FStar_Pervasives_Native.None
end))
in (

let mk1 = (fun t -> (FStar_Syntax_Syntax.mk t FStar_Pervasives_Native.None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let uu___263_10515 = t
in {FStar_Syntax_Syntax.n = uu___263_10515.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = uu___263_10515.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let uu___264_10549 = b
in {FStar_Parser_AST.b = uu___264_10549.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___264_10549.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___264_10549.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env1 pats1 -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (

let uu____10608 = (desugar_term env1 e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) uu____10608)))))) pats1))
in (match (tk) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____10621 = (FStar_ToSyntax_Env.push_bv env a)
in (match (uu____10621) with
| (env1, a1) -> begin
(

let a2 = (

let uu___265_10631 = a1
in {FStar_Syntax_Syntax.ppname = uu___265_10631.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___265_10631.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats1 = (desugar_pats env1 pats)
in (

let body1 = (desugar_formula env1 body)
in (

let body2 = (match (pats1) with
| [] -> begin
body1
end
| uu____10653 -> begin
(mk1 (FStar_Syntax_Syntax.Tm_meta (((body1), (FStar_Syntax_Syntax.Meta_pattern (pats1))))))
end)
in (

let body3 = (

let uu____10667 = (

let uu____10670 = (

let uu____10671 = (FStar_Syntax_Syntax.mk_binder a2)
in (uu____10671)::[])
in (no_annot_abs uu____10670 body2))
in (FStar_All.pipe_left setpos uu____10667))
in (

let uu____10676 = (

let uu____10677 = (

let uu____10692 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) FStar_Pervasives_Native.None)
in (

let uu____10693 = (

let uu____10696 = (FStar_Syntax_Syntax.as_arg body3)
in (uu____10696)::[])
in ((uu____10692), (uu____10693))))
in FStar_Syntax_Syntax.Tm_app (uu____10677))
in (FStar_All.pipe_left mk1 uu____10676)))))))
end))
end
| uu____10701 -> begin
(failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body1 = (

let uu____10773 = (q ((rest), (pats), (body)))
in (

let uu____10780 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term uu____10773 uu____10780 FStar_Parser_AST.Formula)))
in (

let uu____10781 = (q (((b)::[]), ([]), (body1)))
in (FStar_Parser_AST.mk_term uu____10781 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| uu____10790 -> begin
(failwith "impossible")
end))
in (

let uu____10793 = (

let uu____10794 = (unparen f)
in uu____10794.FStar_Parser_AST.tm)
in (match (uu____10793) with
| FStar_Parser_AST.Labeled (f1, l, p) -> begin
(

let f2 = (desugar_formula env f1)
in (FStar_All.pipe_left mk1 (FStar_Syntax_Syntax.Tm_meta (((f2), (FStar_Syntax_Syntax.Meta_labeled (((l), (f2.FStar_Syntax_Syntax.pos), (p)))))))))
end
| FStar_Parser_AST.QForall ([], uu____10801, uu____10802) -> begin
(failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QExists ([], uu____10813, uu____10814) -> begin
(failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____10845 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env uu____10845)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (

let uu____10881 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env uu____10881)))
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
| uu____10924 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_ToSyntax_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier FStar_Pervasives_Native.option) Prims.list) = (fun env bs -> (

let uu____10929 = (FStar_List.fold_left (fun uu____10965 b -> (match (uu____10965) with
| (env1, out) -> begin
(

let tk = (desugar_binder env1 (

let uu___266_11017 = b
in {FStar_Parser_AST.b = uu___266_11017.FStar_Parser_AST.b; FStar_Parser_AST.brange = uu___266_11017.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = uu___266_11017.FStar_Parser_AST.aqual}))
in (match (tk) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____11034 = (FStar_ToSyntax_Env.push_bv env1 a)
in (match (uu____11034) with
| (env2, a1) -> begin
(

let a2 = (

let uu___267_11054 = a1
in {FStar_Syntax_Syntax.ppname = uu___267_11054.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___267_11054.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in ((env2), ((((a2), ((trans_aqual b.FStar_Parser_AST.aqual))))::out)))
end))
end
| uu____11071 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (uu____10929) with
| (env1, tpars) -> begin
((env1), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.TAnnotated (x, t) -> begin
(

let uu____11158 = (desugar_typ env t)
in ((FStar_Pervasives_Native.Some (x)), (uu____11158)))
end
| FStar_Parser_AST.Annotated (x, t) -> begin
(

let uu____11163 = (desugar_typ env t)
in ((FStar_Pervasives_Native.Some (x)), (uu____11163)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let uu____11167 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) FStar_Pervasives_Native.None x.FStar_Ident.idRange)
in ((FStar_Pervasives_Native.Some (x)), (uu____11167)))
end
| FStar_Parser_AST.NoName (t) -> begin
(

let uu____11175 = (desugar_typ env t)
in ((FStar_Pervasives_Native.None), (uu____11175)))
end
| FStar_Parser_AST.Variable (x) -> begin
((FStar_Pervasives_Native.Some (x)), (FStar_Syntax_Syntax.tun))
end))


let mk_data_discriminators : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_ToSyntax_Env.env  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun quals env datas -> (

let quals1 = (FStar_All.pipe_right quals (FStar_List.filter (fun uu___231_11211 -> (match (uu___231_11211) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____11212 -> begin
false
end))))
in (

let quals2 = (fun q -> (

let uu____11223 = ((

let uu____11226 = (FStar_ToSyntax_Env.iface env)
in (not (uu____11226))) || (FStar_ToSyntax_Env.admitted_iface env))
in (match (uu____11223) with
| true -> begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals1)
end
| uu____11229 -> begin
(FStar_List.append q quals1)
end)))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (

let uu____11239 = (quals2 ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((disc_name), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid disc_name); FStar_Syntax_Syntax.sigquals = uu____11239; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))))))))


let mk_indexed_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  FStar_ToSyntax_Env.env  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq env lid fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let uu____11275 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i uu____11305 -> (match (uu____11305) with
| (x, uu____11313) -> begin
(

let uu____11314 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (uu____11314) with
| (field_name, uu____11322) -> begin
(

let only_decl = (((

let uu____11326 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Parser_Const.prims_lid uu____11326)) || (Prims.op_disEquality fvq FStar_Syntax_Syntax.Data_ctor)) || (

let uu____11328 = (

let uu____11329 = (FStar_ToSyntax_Env.current_module env)
in uu____11329.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors uu____11328)))
in (

let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (

let quals = (fun q -> (match (only_decl) with
| true -> begin
(

let uu____11343 = (FStar_List.filter (fun uu___232_11347 -> (match (uu___232_11347) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| uu____11348 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::uu____11343)
end
| uu____11349 -> begin
q
end))
in (

let quals1 = (

let iquals1 = (FStar_All.pipe_right iquals (FStar_List.filter (fun uu___233_11361 -> (match (uu___233_11361) with
| FStar_Syntax_Syntax.Abstract -> begin
true
end
| FStar_Syntax_Syntax.Private -> begin
true
end
| uu____11362 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals1)))
in (

let decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid field_name); FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (match (only_decl) with
| true -> begin
(decl)::[]
end
| uu____11368 -> begin
(

let dd = (

let uu____11370 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____11370) with
| true -> begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end
| uu____11373 -> begin
FStar_Syntax_Syntax.Delta_equational
end))
in (

let lb = (

let uu____11375 = (

let uu____11380 = (FStar_Syntax_Syntax.lid_as_fv field_name dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____11380))
in {FStar_Syntax_Syntax.lbname = uu____11375; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = FStar_Syntax_Syntax.tun})
in (

let impl = (

let uu____11382 = (

let uu____11383 = (

let uu____11390 = (

let uu____11393 = (

let uu____11394 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right uu____11394 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (uu____11393)::[])
in ((((false), ((lb)::[]))), (uu____11390)))
in FStar_Syntax_Syntax.Sig_let (uu____11383))
in {FStar_Syntax_Syntax.sigel = uu____11382; FStar_Syntax_Syntax.sigrng = p; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (match (no_decl) with
| true -> begin
(impl)::[]
end
| uu____11413 -> begin
(decl)::(impl)::[]
end))))
end))))))
end))
end))))
in (FStar_All.pipe_right uu____11275 FStar_List.flatten))))


let mk_data_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_ToSyntax_Env.env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_datacon (lid, uu____11441, t, uu____11443, n1, uu____11445) when (not ((FStar_Ident.lid_equals lid FStar_Parser_Const.lexcons_lid))) -> begin
(

let uu____11450 = (FStar_Syntax_Util.arrow_formals t)
in (match (uu____11450) with
| (formals, uu____11466) -> begin
(match (formals) with
| [] -> begin
[]
end
| uu____11489 -> begin
(

let filter_records = (fun uu___234_11501 -> (match (uu___234_11501) with
| FStar_Syntax_Syntax.RecordConstructor (uu____11504, fns) -> begin
FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| uu____11516 -> begin
FStar_Pervasives_Native.None
end))
in (

let fv_qual = (

let uu____11518 = (FStar_Util.find_map se.FStar_Syntax_Syntax.sigquals filter_records)
in (match (uu____11518) with
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
| uu____11527 -> begin
iquals
end)
in (

let uu____11528 = (FStar_Util.first_N n1 formals)
in (match (uu____11528) with
| (uu____11551, rest) -> begin
(mk_indexed_projector_names iquals1 fv_qual env lid rest)
end)))))
end)
end))
end
| uu____11577 -> begin
[]
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (

let dd = (

let uu____11635 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____11635) with
| true -> begin
(

let uu____11638 = (FStar_Syntax_Util.incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (uu____11638))
end
| uu____11639 -> begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end))
in (

let lb = (

let uu____11641 = (

let uu____11646 = (FStar_Syntax_Syntax.lid_as_fv lid dd FStar_Pervasives_Native.None)
in FStar_Util.Inr (uu____11646))
in (

let uu____11647 = (

let uu____11650 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars uu____11650))
in (

let uu____11653 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = uu____11641; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = uu____11647; FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = uu____11653})))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (lids))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))


let rec desugar_tycon : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d quals tcs -> (

let rng = d.FStar_Parser_AST.drange
in (

let tycon_id = (fun uu___235_11702 -> (match (uu___235_11702) with
| FStar_Parser_AST.TyconAbstract (id, uu____11704, uu____11705) -> begin
id
end
| FStar_Parser_AST.TyconAbbrev (id, uu____11715, uu____11716, uu____11717) -> begin
id
end
| FStar_Parser_AST.TyconRecord (id, uu____11727, uu____11728, uu____11729) -> begin
id
end
| FStar_Parser_AST.TyconVariant (id, uu____11759, uu____11760, uu____11761) -> begin
id
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (x, uu____11803) -> begin
(

let uu____11804 = (

let uu____11805 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____11805))
in (FStar_Parser_AST.mk_term uu____11804 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| FStar_Parser_AST.Variable (x) -> begin
(

let uu____11807 = (

let uu____11808 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (uu____11808))
in (FStar_Parser_AST.mk_term uu____11807 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| FStar_Parser_AST.TAnnotated (a, uu____11810) -> begin
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
| uu____11833 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (

let uu____11839 = (

let uu____11840 = (

let uu____11847 = (binder_to_term b)
in ((out), (uu____11847), ((imp_of_aqual b))))
in FStar_Parser_AST.App (uu____11840))
in (FStar_Parser_AST.mk_term uu____11839 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun uu___236_11857 -> (match (uu___236_11857) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun uu____11912 -> (match (uu____11912) with
| (x, t, uu____11923) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Syntax_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr FStar_Pervasives_Native.None)
end)) fields)
in (

let result = (

let uu____11929 = (

let uu____11930 = (

let uu____11931 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (uu____11931))
in (FStar_Parser_AST.mk_term uu____11930 id.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____11929 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type_level)
in (

let uu____11935 = (FStar_All.pipe_right fields (FStar_List.map (fun uu____11962 -> (match (uu____11962) with
| (x, uu____11972, uu____11973) -> begin
(FStar_Syntax_Util.unmangle_field_name x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (FStar_Pervasives_Native.Some (constrTyp)), (FStar_Pervasives_Native.None), (false)))::[])))), (uu____11935)))))))
end
| uu____12026 -> begin
(failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals1 _env mutuals uu___237_12057 -> (match (uu___237_12057) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let uu____12081 = (typars_of_binders _env binders)
in (match (uu____12081) with
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

let uu____12127 = (

let uu____12128 = (

let uu____12129 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (uu____12129))
in (FStar_Parser_AST.mk_term uu____12128 id.FStar_Ident.idRange FStar_Parser_AST.Type_level))
in (apply_binders uu____12127 binders))
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
| uu____12142 -> begin
(failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env1 bs -> (

let uu____12186 = (FStar_List.fold_left (fun uu____12226 uu____12227 -> (match (((uu____12226), (uu____12227))) with
| ((env2, tps), (x, imp)) -> begin
(

let uu____12318 = (FStar_ToSyntax_Env.push_bv env2 x.FStar_Syntax_Syntax.ppname)
in (match (uu____12318) with
| (env3, y) -> begin
((env3), ((((y), (imp)))::tps))
end))
end)) ((env1), ([])) bs)
in (match (uu____12186) with
| (env2, bs1) -> begin
((env2), ((FStar_List.rev bs1)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id, bs, kopt))::[] -> begin
(

let kopt1 = (match (kopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____12431 = (tm_type_z id.FStar_Ident.idRange)
in FStar_Pervasives_Native.Some (uu____12431))
end
| uu____12432 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id), (bs), (kopt1)))
in (

let uu____12440 = (desugar_abstract_tc quals env [] tc)
in (match (uu____12440) with
| (uu____12453, uu____12454, se, uu____12456) -> begin
(

let se1 = (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, uu____12459, typars, k, [], []) -> begin
(

let quals1 = se.FStar_Syntax_Syntax.sigquals
in (

let quals2 = (match ((FStar_List.contains FStar_Syntax_Syntax.Assumption quals1)) with
| true -> begin
quals1
end
| uu____12474 -> begin
((

let uu____12476 = (

let uu____12477 = (FStar_Options.ml_ish ())
in (not (uu____12477)))
in (match (uu____12476) with
| true -> begin
(

let uu____12478 = (

let uu____12479 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.format1 "Adding an implicit \'assume new\' qualifier on %s" uu____12479))
in (FStar_Errors.warn se.FStar_Syntax_Syntax.sigrng uu____12478))
end
| uu____12480 -> begin
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
| uu____12486 -> begin
(

let uu____12487 = (

let uu____12490 = (

let uu____12491 = (

let uu____12504 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (uu____12504)))
in FStar_Syntax_Syntax.Tm_arrow (uu____12491))
in (FStar_Syntax_Syntax.mk uu____12490))
in (uu____12487 FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng))
end)
in (

let uu___268_12508 = se
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t))); FStar_Syntax_Syntax.sigrng = uu___268_12508.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = uu___268_12508.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu___268_12508.FStar_Syntax_Syntax.sigattrs}))))
end
| uu____12511 -> begin
(failwith "Impossible")
end)
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env se1)
in (

let env2 = (

let uu____12514 = (FStar_ToSyntax_Env.qualify env1 id)
in (FStar_ToSyntax_Env.push_doc env1 uu____12514 d.FStar_Parser_AST.doc))
in ((env2), ((se1)::[])))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let uu____12529 = (typars_of_binders env binders)
in (match (uu____12529) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____12565 = (FStar_Util.for_some (fun uu___238_12567 -> (match (uu___238_12567) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| uu____12568 -> begin
false
end)) quals)
in (match (uu____12565) with
| true -> begin
FStar_Syntax_Syntax.teff
end
| uu____12569 -> begin
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

let uu____12575 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___239_12579 -> (match (uu___239_12579) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| uu____12580 -> begin
false
end))))
in (match (uu____12575) with
| true -> begin
quals
end
| uu____12583 -> begin
(match ((Prims.op_Equality t0.FStar_Parser_AST.level FStar_Parser_AST.Formula)) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals
end
| uu____12586 -> begin
quals
end)
end))
in (

let qlid = (FStar_ToSyntax_Env.qualify env id)
in (

let se = (

let uu____12589 = (FStar_All.pipe_right quals1 (FStar_List.contains FStar_Syntax_Syntax.Effect))
in (match (uu____12589) with
| true -> begin
(

let uu____12592 = (

let uu____12599 = (

let uu____12600 = (unparen t)
in uu____12600.FStar_Parser_AST.tm)
in (match (uu____12599) with
| FStar_Parser_AST.Construct (head1, args) -> begin
(

let uu____12621 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____12651))::args_rev -> begin
(

let uu____12663 = (

let uu____12664 = (unparen last_arg)
in uu____12664.FStar_Parser_AST.tm)
in (match (uu____12663) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____12692 -> begin
(([]), (args))
end))
end
| uu____12701 -> begin
(([]), (args))
end)
in (match (uu____12621) with
| (cattributes, args1) -> begin
(

let uu____12740 = (desugar_attributes env cattributes)
in (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((head1), (args1)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (uu____12740)))
end))
end
| uu____12751 -> begin
((t), ([]))
end))
in (match (uu____12592) with
| (t1, cattributes) -> begin
(

let c = (desugar_comp t1.FStar_Parser_AST.range env' t1)
in (

let typars1 = (FStar_Syntax_Subst.close_binders typars)
in (

let c1 = (FStar_Syntax_Subst.close_comp typars1 c)
in (

let quals2 = (FStar_All.pipe_right quals1 (FStar_List.filter (fun uu___240_12773 -> (match (uu___240_12773) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| uu____12774 -> begin
true
end))))
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (((qlid), ([]), (typars1), (c1), ((FStar_List.append cattributes (FStar_Syntax_Util.comp_flags c1))))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))))
end))
end
| uu____12779 -> begin
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
| (FStar_Parser_AST.TyconRecord (uu____12785))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let uu____12809 = (tycon_record_as_variant trec)
in (match (uu____12809) with
| (t, fs) -> begin
(

let uu____12826 = (

let uu____12829 = (

let uu____12830 = (

let uu____12839 = (

let uu____12842 = (FStar_ToSyntax_Env.current_module env)
in (FStar_Ident.ids_of_lid uu____12842))
in ((uu____12839), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____12830))
in (uu____12829)::quals)
in (desugar_tycon env d uu____12826 ((t)::[])))
end)))
end
| (uu____12847)::uu____12848 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_ToSyntax_Env.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals1 et tc -> (

let uu____13009 = et
in (match (uu____13009) with
| (env1, tcs1) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (uu____13234) -> begin
(

let trec = tc
in (

let uu____13258 = (tycon_record_as_variant trec)
in (match (uu____13258) with
| (t, fs) -> begin
(

let uu____13317 = (

let uu____13320 = (

let uu____13321 = (

let uu____13330 = (

let uu____13333 = (FStar_ToSyntax_Env.current_module env1)
in (FStar_Ident.ids_of_lid uu____13333))
in ((uu____13330), (fs)))
in FStar_Syntax_Syntax.RecordType (uu____13321))
in (uu____13320)::quals1)
in (collect_tcs uu____13317 ((env1), (tcs1)) t))
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let uu____13420 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (uu____13420) with
| (env2, uu____13480, se, tconstr) -> begin
((env2), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals1))))::tcs1))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let uu____13629 = (desugar_abstract_tc quals1 env1 mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (uu____13629) with
| (env2, uu____13689, se, tconstr) -> begin
((env2), ((FStar_Util.Inr (((se), (binders), (t), (quals1))))::tcs1))
end))
end
| uu____13814 -> begin
(failwith "Unrecognized mutual type definition")
end)
end)))
in (

let uu____13861 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (uu____13861) with
| (env1, tcs1) -> begin
(

let tcs2 = (FStar_List.rev tcs1)
in (

let docs_tps_sigelts = (FStar_All.pipe_right tcs2 (FStar_List.collect (fun uu___242_14372 -> (match (uu___242_14372) with
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, uu____14439, uu____14440); FStar_Syntax_Syntax.sigrng = uu____14441; FStar_Syntax_Syntax.sigquals = uu____14442; FStar_Syntax_Syntax.sigmeta = uu____14443; FStar_Syntax_Syntax.sigattrs = uu____14444}, binders, t, quals1) -> begin
(

let t1 = (

let uu____14505 = (typars_of_binders env1 binders)
in (match (uu____14505) with
| (env2, tpars1) -> begin
(

let uu____14536 = (push_tparams env2 tpars1)
in (match (uu____14536) with
| (env_tps, tpars2) -> begin
(

let t1 = (desugar_typ env_tps t)
in (

let tpars3 = (FStar_Syntax_Subst.close_binders tpars2)
in (FStar_Syntax_Subst.close tpars3 t1)))
end))
end))
in (

let uu____14569 = (

let uu____14590 = (mk_typ_abbrev id uvs tpars k t1 ((id)::[]) quals1 rng)
in ((((id), (d.FStar_Parser_AST.doc))), ([]), (uu____14590)))
in (uu____14569)::[]))
end
| FStar_Util.Inl ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs1, tpars, k, mutuals1, uu____14658); FStar_Syntax_Syntax.sigrng = uu____14659; FStar_Syntax_Syntax.sigquals = tname_quals; FStar_Syntax_Syntax.sigmeta = uu____14661; FStar_Syntax_Syntax.sigattrs = uu____14662}, constrs, tconstr, quals1) -> begin
(

let mk_tot = (fun t -> (

let tot1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Parser_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((tot1), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)))
in (

let tycon = ((tname), (tpars), (k))
in (

let uu____14758 = (push_tparams env1 tpars)
in (match (uu____14758) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun uu____14835 -> (match (uu____14835) with
| (x, uu____14849) -> begin
((x), (FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let tot_tconstr = (mk_tot tconstr)
in (

let uu____14857 = (

let uu____14886 = (FStar_All.pipe_right constrs (FStar_List.map (fun uu____15000 -> (match (uu____15000) with
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
| uu____15053 -> begin
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

let uu____15056 = (close env_tps t)
in (desugar_term env_tps uu____15056))
in (

let name = (FStar_ToSyntax_Env.qualify env1 id)
in (

let quals2 = (FStar_All.pipe_right tname_quals (FStar_List.collect (fun uu___241_15067 -> (match (uu___241_15067) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| uu____15079 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (

let uu____15087 = (

let uu____15108 = (

let uu____15109 = (

let uu____15110 = (

let uu____15125 = (

let uu____15128 = (

let uu____15131 = (FStar_All.pipe_right t1 FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total uu____15131))
in (FStar_Syntax_Util.arrow data_tpars uu____15128))
in ((name), (univs1), (uu____15125), (tname), (ntps), (mutuals1)))
in FStar_Syntax_Syntax.Sig_datacon (uu____15110))
in {FStar_Syntax_Syntax.sigel = uu____15109; FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = quals2; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in ((((name), (doc1))), (tps), (uu____15108)))
in ((name), (uu____15087))))))))
end))))
in (FStar_All.pipe_left FStar_List.split uu____14886))
in (match (uu____14857) with
| (constrNames, constrs1) -> begin
(((((tname), (d.FStar_Parser_AST.doc))), ([]), ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs1), (tpars), (k), (mutuals1), (constrNames))); FStar_Syntax_Syntax.sigrng = rng; FStar_Syntax_Syntax.sigquals = tname_quals; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))::constrs1
end))))
end))))
end
| uu____15370 -> begin
(failwith "impossible")
end))))
in (

let name_docs = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.map (fun uu____15502 -> (match (uu____15502) with
| (name_doc, uu____15530, uu____15531) -> begin
name_doc
end))))
in (

let sigelts = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.map (fun uu____15611 -> (match (uu____15611) with
| (uu____15632, uu____15633, se) -> begin
se
end))))
in (

let uu____15663 = (

let uu____15670 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (FStar_Syntax_MutRecTy.disentangle_abbrevs_from_bundle sigelts quals uu____15670 rng))
in (match (uu____15663) with
| (bundle, abbrevs) -> begin
(

let env2 = (FStar_ToSyntax_Env.push_sigelt env0 bundle)
in (

let env3 = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env2 abbrevs)
in (

let data_ops = (FStar_All.pipe_right docs_tps_sigelts (FStar_List.collect (fun uu____15736 -> (match (uu____15736) with
| (uu____15759, tps, se) -> begin
(mk_data_projector_names quals env3 se)
end))))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, uu____15810, tps, k, uu____15813, constrs) when ((FStar_List.length constrs) > (Prims.parse_int "1")) -> begin
(

let quals1 = se.FStar_Syntax_Syntax.sigquals
in (

let quals2 = (match ((FStar_List.contains FStar_Syntax_Syntax.Abstract quals1)) with
| true -> begin
(FStar_Syntax_Syntax.Private)::quals1
end
| uu____15831 -> begin
quals1
end)
in (mk_data_discriminators quals2 env3 constrs)))
end
| uu____15832 -> begin
[]
end))))
in (

let ops = (FStar_List.append discs data_ops)
in (

let env4 = (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt env3 ops)
in (

let env5 = (FStar_List.fold_left (fun acc uu____15849 -> (match (uu____15849) with
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

let uu____15886 = (FStar_List.fold_left (fun uu____15909 b -> (match (uu____15909) with
| (env1, binders1) -> begin
(

let uu____15929 = (desugar_binder env1 b)
in (match (uu____15929) with
| (FStar_Pervasives_Native.Some (a), k) -> begin
(

let uu____15946 = (as_binder env1 b.FStar_Parser_AST.aqual ((FStar_Pervasives_Native.Some (a)), (k)))
in (match (uu____15946) with
| (binder, env2) -> begin
((env2), ((binder)::binders1))
end))
end
| uu____15963 -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) binders)
in (match (uu____15886) with
| (env1, binders1) -> begin
((env1), ((FStar_List.rev binders1)))
end)))


let rec desugar_effect : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_ToSyntax_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_typ eff_decls -> (

let env0 = env
in (

let monad_env = (FStar_ToSyntax_Env.enter_monad_scope env eff_name)
in (

let uu____16081 = (desugar_binders monad_env eff_binders)
in (match (uu____16081) with
| (env1, binders) -> begin
(

let eff_t = (desugar_term env1 eff_typ)
in (

let for_free = (

let uu____16102 = (

let uu____16103 = (

let uu____16110 = (FStar_Syntax_Util.arrow_formals eff_t)
in (FStar_Pervasives_Native.fst uu____16110))
in (FStar_List.length uu____16103))
in (Prims.op_Equality uu____16102 (Prims.parse_int "1")))
in (

let mandatory_members = (

let rr_members = ("repr")::("return")::("bind")::[]
in (match (for_free) with
| true -> begin
rr_members
end
| uu____16147 -> begin
(FStar_List.append rr_members (("return_wp")::("bind_wp")::("if_then_else")::("ite_wp")::("stronger")::("close_wp")::("assert_p")::("assume_p")::("null_wp")::("trivial")::[]))
end))
in (

let name_of_eff_decl = (fun decl -> (match (decl.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____16152, ((FStar_Parser_AST.TyconAbbrev (name, uu____16154, uu____16155, uu____16156), uu____16157))::[]) -> begin
(FStar_Ident.text_of_id name)
end
| uu____16190 -> begin
(failwith "Malformed effect member declaration.")
end))
in (

let uu____16191 = (FStar_List.partition (fun decl -> (

let uu____16203 = (name_of_eff_decl decl)
in (FStar_List.mem uu____16203 mandatory_members))) eff_decls)
in (match (uu____16191) with
| (mandatory_members_decls, actions) -> begin
(

let uu____16220 = (FStar_All.pipe_right mandatory_members_decls (FStar_List.fold_left (fun uu____16249 decl -> (match (uu____16249) with
| (env2, out) -> begin
(

let uu____16269 = (desugar_decl env2 decl)
in (match (uu____16269) with
| (env3, ses) -> begin
(

let uu____16282 = (

let uu____16285 = (FStar_List.hd ses)
in (uu____16285)::out)
in ((env3), (uu____16282)))
end))
end)) ((env1), ([]))))
in (match (uu____16220) with
| (env2, decls) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (

let actions_docs = (FStar_All.pipe_right actions (FStar_List.map (fun d1 -> (match (d1.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (uu____16353, ((FStar_Parser_AST.TyconAbbrev (name, action_params, uu____16356, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (uu____16357, ((def, uu____16359))::((cps_type, uu____16361))::[]); FStar_Parser_AST.range = uu____16362; FStar_Parser_AST.level = uu____16363}), doc1))::[]) when (not (for_free)) -> begin
(

let uu____16415 = (desugar_binders env2 action_params)
in (match (uu____16415) with
| (env3, action_params1) -> begin
(

let action_params2 = (FStar_Syntax_Subst.close_binders action_params1)
in (

let uu____16435 = (

let uu____16436 = (FStar_ToSyntax_Env.qualify env3 name)
in (

let uu____16437 = (

let uu____16438 = (desugar_term env3 def)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____16438))
in (

let uu____16443 = (

let uu____16444 = (desugar_typ env3 cps_type)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____16444))
in {FStar_Syntax_Syntax.action_name = uu____16436; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = action_params2; FStar_Syntax_Syntax.action_defn = uu____16437; FStar_Syntax_Syntax.action_typ = uu____16443})))
in ((uu____16435), (doc1))))
end))
end
| FStar_Parser_AST.Tycon (uu____16451, ((FStar_Parser_AST.TyconAbbrev (name, action_params, uu____16454, defn), doc1))::[]) when for_free -> begin
(

let uu____16489 = (desugar_binders env2 action_params)
in (match (uu____16489) with
| (env3, action_params1) -> begin
(

let action_params2 = (FStar_Syntax_Subst.close_binders action_params1)
in (

let uu____16509 = (

let uu____16510 = (FStar_ToSyntax_Env.qualify env3 name)
in (

let uu____16511 = (

let uu____16512 = (desugar_term env3 defn)
in (FStar_Syntax_Subst.close (FStar_List.append binders1 action_params2) uu____16512))
in {FStar_Syntax_Syntax.action_name = uu____16510; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_params = action_params2; FStar_Syntax_Syntax.action_defn = uu____16511; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
in ((uu____16509), (doc1))))
end))
end
| uu____16519 -> begin
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

let uu____16549 = (

let uu____16550 = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_definition env2) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders1) uu____16550))
in (([]), (uu____16549)))))
in (

let mname = (FStar_ToSyntax_Env.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange (FStar_Pervasives_Native.Some (mname))) quals)
in (

let se = (match (for_free) with
| true -> begin
(

let dummy_tscheme = (

let uu____16567 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (([]), (uu____16567)))
in (

let uu____16574 = (

let uu____16575 = (

let uu____16576 = (

let uu____16577 = (lookup "repr")
in (FStar_Pervasives_Native.snd uu____16577))
in (

let uu____16586 = (lookup "return")
in (

let uu____16587 = (lookup "bind")
in {FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = eff_t1; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = uu____16576; FStar_Syntax_Syntax.return_repr = uu____16586; FStar_Syntax_Syntax.bind_repr = uu____16587; FStar_Syntax_Syntax.actions = actions1})))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (uu____16575))
in {FStar_Syntax_Syntax.sigel = uu____16574; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qualifiers; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))
end
| uu____16588 -> begin
(

let rr = (FStar_Util.for_some (fun uu___243_16591 -> (match (uu___243_16591) with
| FStar_Syntax_Syntax.Reifiable -> begin
true
end
| FStar_Syntax_Syntax.Reflectable (uu____16592) -> begin
true
end
| uu____16593 -> begin
false
end)) qualifiers)
in (

let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in (

let uu____16603 = (

let uu____16604 = (

let uu____16605 = (lookup "return_wp")
in (

let uu____16606 = (lookup "bind_wp")
in (

let uu____16607 = (lookup "if_then_else")
in (

let uu____16608 = (lookup "ite_wp")
in (

let uu____16609 = (lookup "stronger")
in (

let uu____16610 = (lookup "close_wp")
in (

let uu____16611 = (lookup "assert_p")
in (

let uu____16612 = (lookup "assume_p")
in (

let uu____16613 = (lookup "null_wp")
in (

let uu____16614 = (lookup "trivial")
in (

let uu____16615 = (match (rr) with
| true -> begin
(

let uu____16616 = (lookup "repr")
in (FStar_All.pipe_left FStar_Pervasives_Native.snd uu____16616))
end
| uu____16631 -> begin
FStar_Syntax_Syntax.tun
end)
in (

let uu____16632 = (match (rr) with
| true -> begin
(lookup "return")
end
| uu____16633 -> begin
un_ts
end)
in (

let uu____16634 = (match (rr) with
| true -> begin
(lookup "bind")
end
| uu____16635 -> begin
un_ts
end)
in {FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = eff_t1; FStar_Syntax_Syntax.ret_wp = uu____16605; FStar_Syntax_Syntax.bind_wp = uu____16606; FStar_Syntax_Syntax.if_then_else = uu____16607; FStar_Syntax_Syntax.ite_wp = uu____16608; FStar_Syntax_Syntax.stronger = uu____16609; FStar_Syntax_Syntax.close_wp = uu____16610; FStar_Syntax_Syntax.assert_p = uu____16611; FStar_Syntax_Syntax.assume_p = uu____16612; FStar_Syntax_Syntax.null_wp = uu____16613; FStar_Syntax_Syntax.trivial = uu____16614; FStar_Syntax_Syntax.repr = uu____16615; FStar_Syntax_Syntax.return_repr = uu____16632; FStar_Syntax_Syntax.bind_repr = uu____16634; FStar_Syntax_Syntax.actions = actions1})))))))))))))
in FStar_Syntax_Syntax.Sig_new_effect (uu____16604))
in {FStar_Syntax_Syntax.sigel = uu____16603; FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = qualifiers; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})))
end)
in (

let env3 = (FStar_ToSyntax_Env.push_sigelt env0 se)
in (

let env4 = (FStar_ToSyntax_Env.push_doc env3 mname d.FStar_Parser_AST.doc)
in (

let env5 = (FStar_All.pipe_right actions_docs (FStar_List.fold_left (fun env5 uu____16659 -> (match (uu____16659) with
| (a, doc1) -> begin
(

let env6 = (

let uu____16673 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_ToSyntax_Env.push_sigelt env5 uu____16673))
in (FStar_ToSyntax_Env.push_doc env6 a.FStar_Syntax_Syntax.action_name doc1))
end)) env4))
in (

let env6 = (

let uu____16675 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____16675) with
| true -> begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_ToSyntax_Env.qualify monad_env))
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]
in (

let refl_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (FStar_ToSyntax_Env.push_sigelt env5 refl_decl))))
end
| uu____16683 -> begin
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

let uu____16706 = (desugar_binders env1 eff_binders)
in (match (uu____16706) with
| (env2, binders) -> begin
(

let uu____16725 = (

let uu____16744 = (head_and_args defn)
in (match (uu____16744) with
| (head1, args) -> begin
(

let lid = (match (head1.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
l
end
| uu____16789 -> begin
(

let uu____16790 = (

let uu____16791 = (

let uu____16796 = (

let uu____16797 = (

let uu____16798 = (FStar_Parser_AST.term_to_string head1)
in (Prims.strcat uu____16798 " not found"))
in (Prims.strcat "Effect " uu____16797))
in ((uu____16796), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____16791))
in (FStar_Exn.raise uu____16790))
end)
in (

let ed = (FStar_ToSyntax_Env.fail_or env2 (FStar_ToSyntax_Env.try_lookup_effect_defn env2) lid)
in (

let uu____16800 = (match ((FStar_List.rev args)) with
| ((last_arg, uu____16830))::args_rev -> begin
(

let uu____16842 = (

let uu____16843 = (unparen last_arg)
in uu____16843.FStar_Parser_AST.tm)
in (match (uu____16842) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| uu____16871 -> begin
(([]), (args))
end))
end
| uu____16880 -> begin
(([]), (args))
end)
in (match (uu____16800) with
| (cattributes, args1) -> begin
(

let uu____16931 = (desugar_args env2 args1)
in (

let uu____16940 = (desugar_attributes env2 cattributes)
in ((lid), (ed), (uu____16931), (uu____16940))))
end))))
end))
in (match (uu____16725) with
| (ed_lid, ed, args, cattributes) -> begin
(

let binders1 = (FStar_Syntax_Subst.close_binders binders)
in (

let sub1 = (fun uu____16999 -> (match (uu____16999) with
| (uu____17012, x) -> begin
(

let uu____17018 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (uu____17018) with
| (edb, x1) -> begin
((match ((Prims.op_disEquality (FStar_List.length args) (FStar_List.length edb))) with
| true -> begin
(FStar_Exn.raise (FStar_Errors.Error ((("Unexpected number of arguments to effect constructor"), (defn.FStar_Parser_AST.range)))))
end
| uu____17042 -> begin
()
end);
(

let s = (FStar_Syntax_Util.subst_of_list edb args)
in (

let uu____17044 = (

let uu____17045 = (FStar_Syntax_Subst.subst s x1)
in (FStar_Syntax_Subst.close binders1 uu____17045))
in (([]), (uu____17044))));
)
end))
end))
in (

let mname = (FStar_ToSyntax_Env.qualify env0 eff_name)
in (

let ed1 = (

let uu____17050 = (

let uu____17051 = (sub1 (([]), (ed.FStar_Syntax_Syntax.signature)))
in (FStar_Pervasives_Native.snd uu____17051))
in (

let uu____17062 = (sub1 ed.FStar_Syntax_Syntax.ret_wp)
in (

let uu____17063 = (sub1 ed.FStar_Syntax_Syntax.bind_wp)
in (

let uu____17064 = (sub1 ed.FStar_Syntax_Syntax.if_then_else)
in (

let uu____17065 = (sub1 ed.FStar_Syntax_Syntax.ite_wp)
in (

let uu____17066 = (sub1 ed.FStar_Syntax_Syntax.stronger)
in (

let uu____17067 = (sub1 ed.FStar_Syntax_Syntax.close_wp)
in (

let uu____17068 = (sub1 ed.FStar_Syntax_Syntax.assert_p)
in (

let uu____17069 = (sub1 ed.FStar_Syntax_Syntax.assume_p)
in (

let uu____17070 = (sub1 ed.FStar_Syntax_Syntax.null_wp)
in (

let uu____17071 = (sub1 ed.FStar_Syntax_Syntax.trivial)
in (

let uu____17072 = (

let uu____17073 = (sub1 (([]), (ed.FStar_Syntax_Syntax.repr)))
in (FStar_Pervasives_Native.snd uu____17073))
in (

let uu____17084 = (sub1 ed.FStar_Syntax_Syntax.return_repr)
in (

let uu____17085 = (sub1 ed.FStar_Syntax_Syntax.bind_repr)
in (

let uu____17086 = (FStar_List.map (fun action -> (

let uu____17094 = (FStar_ToSyntax_Env.qualify env2 action.FStar_Syntax_Syntax.action_unqualified_name)
in (

let uu____17095 = (

let uu____17096 = (sub1 (([]), (action.FStar_Syntax_Syntax.action_defn)))
in (FStar_Pervasives_Native.snd uu____17096))
in (

let uu____17107 = (

let uu____17108 = (sub1 (([]), (action.FStar_Syntax_Syntax.action_typ)))
in (FStar_Pervasives_Native.snd uu____17108))
in {FStar_Syntax_Syntax.action_name = uu____17094; FStar_Syntax_Syntax.action_unqualified_name = action.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_params = action.FStar_Syntax_Syntax.action_params; FStar_Syntax_Syntax.action_defn = uu____17095; FStar_Syntax_Syntax.action_typ = uu____17107})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.cattributes = cattributes; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders1; FStar_Syntax_Syntax.signature = uu____17050; FStar_Syntax_Syntax.ret_wp = uu____17062; FStar_Syntax_Syntax.bind_wp = uu____17063; FStar_Syntax_Syntax.if_then_else = uu____17064; FStar_Syntax_Syntax.ite_wp = uu____17065; FStar_Syntax_Syntax.stronger = uu____17066; FStar_Syntax_Syntax.close_wp = uu____17067; FStar_Syntax_Syntax.assert_p = uu____17068; FStar_Syntax_Syntax.assume_p = uu____17069; FStar_Syntax_Syntax.null_wp = uu____17070; FStar_Syntax_Syntax.trivial = uu____17071; FStar_Syntax_Syntax.repr = uu____17072; FStar_Syntax_Syntax.return_repr = uu____17084; FStar_Syntax_Syntax.bind_repr = uu____17085; FStar_Syntax_Syntax.actions = uu____17086})))))))))))))))
in (

let se = (

let for_free = (

let uu____17121 = (

let uu____17122 = (

let uu____17129 = (FStar_Syntax_Util.arrow_formals ed1.FStar_Syntax_Syntax.signature)
in (FStar_Pervasives_Native.fst uu____17129))
in (FStar_List.length uu____17122))
in (Prims.op_Equality uu____17121 (Prims.parse_int "1")))
in (

let uu____17158 = (

let uu____17161 = (trans_qual1 (FStar_Pervasives_Native.Some (mname)))
in (FStar_List.map uu____17161 quals))
in {FStar_Syntax_Syntax.sigel = (match (for_free) with
| true -> begin
FStar_Syntax_Syntax.Sig_new_effect_for_free (ed1)
end
| uu____17164 -> begin
FStar_Syntax_Syntax.Sig_new_effect (ed1)
end); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = uu____17158; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}))
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

let uu____17181 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_ToSyntax_Env.push_sigelt env5 uu____17181))
in (FStar_ToSyntax_Env.push_doc env6 a.FStar_Syntax_Syntax.action_name doc1)))) env4))
in (

let env6 = (

let uu____17183 = (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable))
in (match (uu____17183) with
| true -> begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_ToSyntax_Env.qualify monad_env))
in (

let quals1 = (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]
in (

let refl_decl = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = quals1; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in (FStar_ToSyntax_Env.push_sigelt env5 refl_decl))))
end
| uu____17193 -> begin
env5
end))
in (

let env7 = (FStar_ToSyntax_Env.push_doc env6 mname d.FStar_Parser_AST.doc)
in ((env7), ((se)::[])))))))))))))
end))
end)))))
and mk_comment_attr : FStar_Parser_AST.decl  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax = (fun d -> (

let uu____17198 = (match (d.FStar_Parser_AST.doc) with
| FStar_Pervasives_Native.None -> begin
((""), ([]))
end
| FStar_Pervasives_Native.Some (fsdoc) -> begin
fsdoc
end)
in (match (uu____17198) with
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
| FStar_Pervasives_Native.Some (uu____17249) -> begin
(

let uu____17250 = (

let uu____17251 = (FStar_Parser_ToDocument.signature_to_document d)
in (FStar_Pprint.pretty_string 0.950000 (Prims.parse_int "80") uu____17251))
in (Prims.strcat "\n  " uu____17250))
end
| uu____17252 -> begin
""
end)
in (

let other = (FStar_List.filter_map (fun uu____17265 -> (match (uu____17265) with
| (k, v1) -> begin
(match (((Prims.op_disEquality k "summary") && (Prims.op_disEquality k "type"))) with
| true -> begin
FStar_Pervasives_Native.Some ((Prims.strcat k (Prims.strcat ": " v1)))
end
| uu____17276 -> begin
FStar_Pervasives_Native.None
end)
end)) kv)
in (

let other1 = (match ((Prims.op_disEquality other [])) with
| true -> begin
(Prims.strcat (FStar_String.concat "\n" other) "\n")
end
| uu____17280 -> begin
""
end)
in (

let str = (Prims.strcat summary (Prims.strcat pp (Prims.strcat other1 text)))
in (

let fv = (

let uu____17283 = (FStar_Ident.lid_of_str "FStar.Pervasives.Comment")
in (FStar_Syntax_Syntax.fvar uu____17283 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in (

let arg = (FStar_Syntax_Util.exp_string str)
in (

let uu____17285 = (

let uu____17294 = (FStar_Syntax_Syntax.as_arg arg)
in (uu____17294)::[])
in (FStar_Syntax_Util.mk_app fv uu____17285)))))))))
end)))
and desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (

let uu____17301 = (desugar_decl_noattrs env d)
in (match (uu____17301) with
| (env1, sigelts) -> begin
(

let attrs = d.FStar_Parser_AST.attrs
in (

let attrs1 = (FStar_List.map (desugar_term env1) attrs)
in (

let attrs2 = (

let uu____17321 = (mk_comment_attr d)
in (uu____17321)::attrs1)
in (

let uu____17326 = (FStar_List.map (fun sigelt -> (

let uu___269_17332 = sigelt
in {FStar_Syntax_Syntax.sigel = uu___269_17332.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___269_17332.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___269_17332.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___269_17332.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = attrs2})) sigelts)
in ((env1), (uu____17326))))))
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
| uu____17355 -> begin
()
end);
((env), ((se)::[]));
))
end
| FStar_Parser_AST.Fsdoc (uu____17358) -> begin
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

let uu____17374 = (FStar_ToSyntax_Env.push_module_abbrev env x l)
in ((uu____17374), ([])))
end
| FStar_Parser_AST.Tycon (is_effect, tcs) -> begin
(

let quals = (match (is_effect) with
| true -> begin
(FStar_Parser_AST.Effect_qual)::d.FStar_Parser_AST.quals
end
| uu____17400 -> begin
d.FStar_Parser_AST.quals
end)
in (

let tcs1 = (FStar_List.map (fun uu____17413 -> (match (uu____17413) with
| (x, uu____17421) -> begin
x
end)) tcs)
in (

let uu____17426 = (FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals)
in (desugar_tycon env d uu____17426 tcs1))))
end
| FStar_Parser_AST.TopLevelLet (isrec, lets) -> begin
(

let quals = d.FStar_Parser_AST.quals
in (

let expand_toplevel_pattern = ((Prims.op_Equality isrec FStar_Parser_AST.NoLetQualifier) && (match (lets) with
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatOp (uu____17448); FStar_Parser_AST.prange = uu____17449}, uu____17450))::[] -> begin
false
end
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____17459); FStar_Parser_AST.prange = uu____17460}, uu____17461))::[] -> begin
false
end
| (({FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (uu____17476); FStar_Parser_AST.prange = uu____17477}, uu____17478); FStar_Parser_AST.prange = uu____17479}, uu____17480))::[] -> begin
false
end
| ((p, uu____17496))::[] -> begin
(

let uu____17505 = (is_app_pattern p)
in (not (uu____17505)))
end
| uu____17506 -> begin
false
end))
in (match ((not (expand_toplevel_pattern))) with
| true -> begin
(

let as_inner_let = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)
in (

let ds_lets = (desugar_term_maybe_top true env as_inner_let)
in (

let uu____17525 = (

let uu____17526 = (FStar_All.pipe_left FStar_Syntax_Subst.compress ds_lets)
in uu____17526.FStar_Syntax_Syntax.n)
in (match (uu____17525) with
| FStar_Syntax_Syntax.Tm_let (lbs, uu____17534) -> begin
(

let fvs = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals1 = (match (quals) with
| (uu____17567)::uu____17568 -> begin
(FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals)
end
| uu____17571 -> begin
(FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.collect (fun uu___244_17584 -> (match (uu___244_17584) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (uu____17587); FStar_Syntax_Syntax.lbunivs = uu____17588; FStar_Syntax_Syntax.lbtyp = uu____17589; FStar_Syntax_Syntax.lbeff = uu____17590; FStar_Syntax_Syntax.lbdef = uu____17591} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = uu____17599; FStar_Syntax_Syntax.lbtyp = uu____17600; FStar_Syntax_Syntax.lbeff = uu____17601; FStar_Syntax_Syntax.lbdef = uu____17602} -> begin
(FStar_ToSyntax_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals2 = (

let uu____17612 = (FStar_All.pipe_right lets (FStar_Util.for_some (fun uu____17626 -> (match (uu____17626) with
| (uu____17631, t) -> begin
(Prims.op_Equality t.FStar_Parser_AST.level FStar_Parser_AST.Formula)
end))))
in (match (uu____17612) with
| true -> begin
(FStar_Syntax_Syntax.Logic)::quals1
end
| uu____17635 -> begin
quals1
end))
in (

let lbs1 = (

let uu____17643 = (FStar_All.pipe_right quals2 (FStar_List.contains FStar_Syntax_Syntax.Abstract))
in (match (uu____17643) with
| true -> begin
(

let uu____17652 = (FStar_All.pipe_right (FStar_Pervasives_Native.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu___270_17666 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let uu___271_17668 = fv
in {FStar_Syntax_Syntax.fv_name = uu___271_17668.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = uu___271_17668.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = uu___270_17666.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = uu___270_17666.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = uu___270_17666.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = uu___270_17666.FStar_Syntax_Syntax.lbdef})))))
in (((FStar_Pervasives_Native.fst lbs)), (uu____17652)))
end
| uu____17673 -> begin
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
| uu____17700 -> begin
(failwith "Desugaring a let did not produce a let")
end))))
end
| uu____17705 -> begin
(

let uu____17706 = (match (lets) with
| ((pat, body))::[] -> begin
((pat), (body))
end
| uu____17725 -> begin
(failwith "expand_toplevel_pattern should only allow single definition lets")
end)
in (match (uu____17706) with
| (pat, body) -> begin
(

let fresh_toplevel_name = (FStar_Ident.gen FStar_Range.dummyRange)
in (

let fresh_pat = (

let var_pat = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((fresh_toplevel_name), (FStar_Pervasives_Native.None)))) FStar_Range.dummyRange)
in (match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (pat1, ty) -> begin
(

let uu___272_17749 = pat1
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed (((var_pat), (ty))); FStar_Parser_AST.prange = uu___272_17749.FStar_Parser_AST.prange})
end
| uu____17750 -> begin
var_pat
end))
in (

let main_let = (desugar_decl env (

let uu___273_17757 = d
in {FStar_Parser_AST.d = FStar_Parser_AST.TopLevelLet (((isrec), ((((fresh_pat), (body)))::[]))); FStar_Parser_AST.drange = uu___273_17757.FStar_Parser_AST.drange; FStar_Parser_AST.doc = uu___273_17757.FStar_Parser_AST.doc; FStar_Parser_AST.quals = (FStar_Parser_AST.Private)::d.FStar_Parser_AST.quals; FStar_Parser_AST.attrs = uu___273_17757.FStar_Parser_AST.attrs}))
in (

let build_projection = (fun uu____17789 id -> (match (uu____17789) with
| (env1, ses) -> begin
(

let main = (

let uu____17810 = (

let uu____17811 = (FStar_Ident.lid_of_ids ((fresh_toplevel_name)::[]))
in FStar_Parser_AST.Var (uu____17811))
in (FStar_Parser_AST.mk_term uu____17810 FStar_Range.dummyRange FStar_Parser_AST.Expr))
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

let uu____17861 = (desugar_decl env1 id_decl)
in (match (uu____17861) with
| (env2, ses') -> begin
((env2), ((FStar_List.append ses ses')))
end))))))))
end))
in (

let bvs = (

let uu____17879 = (gather_pattern_bound_vars pat)
in (FStar_All.pipe_right uu____17879 FStar_Util.set_elements))
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

let uu____17910 = (close_fun env t)
in (desugar_term env uu____17910))
in (

let quals1 = (

let uu____17914 = ((FStar_ToSyntax_Env.iface env) && (FStar_ToSyntax_Env.admitted_iface env))
in (match (uu____17914) with
| true -> begin
(FStar_Parser_AST.Assumption)::quals
end
| uu____17917 -> begin
quals
end))
in (

let lid = (FStar_ToSyntax_Env.qualify env id)
in (

let se = (

let uu____17920 = (FStar_List.map (trans_qual1 FStar_Pervasives_Native.None) quals1)
in {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (((lid), ([]), (t1))); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = uu____17920; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []})
in (

let env1 = (FStar_ToSyntax_Env.push_sigelt env se)
in (

let env2 = (FStar_ToSyntax_Env.push_doc env1 lid d.FStar_Parser_AST.doc)
in ((env2), ((se)::[])))))))))
end
| FStar_Parser_AST.Exception (id, FStar_Pervasives_Native.None) -> begin
(

let uu____17932 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) FStar_Parser_Const.exn_lid)
in (match (uu____17932) with
| (t, uu____17946) -> begin
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

let uu____17980 = (

let uu____17987 = (FStar_Syntax_Syntax.null_binder t)
in (uu____17987)::[])
in (

let uu____17988 = (

let uu____17991 = (

let uu____17992 = (FStar_ToSyntax_Env.fail_or env (FStar_ToSyntax_Env.try_lookup_lid env) FStar_Parser_Const.exn_lid)
in (FStar_Pervasives_Native.fst uu____17992))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total uu____17991))
in (FStar_Syntax_Util.arrow uu____17980 uu____17988)))
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

let uu____18054 = (FStar_ToSyntax_Env.try_lookup_effect_name env l1)
in (match (uu____18054) with
| FStar_Pervasives_Native.None -> begin
(

let uu____18057 = (

let uu____18058 = (

let uu____18063 = (

let uu____18064 = (

let uu____18065 = (FStar_Syntax_Print.lid_to_string l1)
in (Prims.strcat uu____18065 " not found"))
in (Prims.strcat "Effect name " uu____18064))
in ((uu____18063), (d.FStar_Parser_AST.drange)))
in FStar_Errors.Error (uu____18058))
in (FStar_Exn.raise uu____18057))
end
| FStar_Pervasives_Native.Some (l2) -> begin
l2
end)))
in (

let src = (lookup l.FStar_Parser_AST.msource)
in (

let dst = (lookup l.FStar_Parser_AST.mdest)
in (

let uu____18069 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(

let uu____18111 = (

let uu____18120 = (

let uu____18127 = (desugar_term env t)
in (([]), (uu____18127)))
in FStar_Pervasives_Native.Some (uu____18120))
in ((uu____18111), (FStar_Pervasives_Native.None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(

let uu____18160 = (

let uu____18169 = (

let uu____18176 = (desugar_term env wp)
in (([]), (uu____18176)))
in FStar_Pervasives_Native.Some (uu____18169))
in (

let uu____18185 = (

let uu____18194 = (

let uu____18201 = (desugar_term env t)
in (([]), (uu____18201)))
in FStar_Pervasives_Native.Some (uu____18194))
in ((uu____18160), (uu____18185))))
end
| FStar_Parser_AST.LiftForFree (t) -> begin
(

let uu____18227 = (

let uu____18236 = (

let uu____18243 = (desugar_term env t)
in (([]), (uu____18243)))
in FStar_Pervasives_Native.Some (uu____18236))
in ((FStar_Pervasives_Native.None), (uu____18227)))
end)
in (match (uu____18069) with
| (lift_wp, lift) -> begin
(

let se = {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_sub_effect ({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift}); FStar_Syntax_Syntax.sigrng = d.FStar_Parser_AST.drange; FStar_Syntax_Syntax.sigquals = []; FStar_Syntax_Syntax.sigmeta = FStar_Syntax_Syntax.default_sigmeta; FStar_Syntax_Syntax.sigattrs = []}
in ((env), ((se)::[])))
end)))))
end)))


let desugar_decls : env_t  ->  FStar_Parser_AST.decl Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env decls -> (

let uu____18333 = (FStar_List.fold_left (fun uu____18353 d -> (match (uu____18353) with
| (env1, sigelts) -> begin
(

let uu____18373 = (desugar_decl env1 d)
in (match (uu____18373) with
| (env2, se) -> begin
((env2), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls)
in (match (uu____18333) with
| (env1, sigelts) -> begin
(

let rec forward = (fun acc uu___246_18414 -> (match (uu___246_18414) with
| (se1)::(se2)::sigelts1 -> begin
(match (((se1.FStar_Syntax_Syntax.sigel), (se2.FStar_Syntax_Syntax.sigel))) with
| (FStar_Syntax_Syntax.Sig_declare_typ (uu____18428), FStar_Syntax_Syntax.Sig_let (uu____18429)) -> begin
(

let uu____18442 = (

let uu____18445 = (

let uu___274_18446 = se2
in (

let uu____18447 = (

let uu____18450 = (FStar_List.filter (fun uu___245_18464 -> (match (uu___245_18464) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____18468; FStar_Syntax_Syntax.vars = uu____18469}, uu____18470); FStar_Syntax_Syntax.pos = uu____18471; FStar_Syntax_Syntax.vars = uu____18472} when (

let uu____18495 = (

let uu____18496 = (FStar_Syntax_Syntax.lid_of_fv fv)
in (FStar_Ident.string_of_lid uu____18496))
in (Prims.op_Equality uu____18495 "FStar.Pervasives.Comment")) -> begin
true
end
| uu____18497 -> begin
false
end)) se1.FStar_Syntax_Syntax.sigattrs)
in (FStar_List.append uu____18450 se2.FStar_Syntax_Syntax.sigattrs))
in {FStar_Syntax_Syntax.sigel = uu___274_18446.FStar_Syntax_Syntax.sigel; FStar_Syntax_Syntax.sigrng = uu___274_18446.FStar_Syntax_Syntax.sigrng; FStar_Syntax_Syntax.sigquals = uu___274_18446.FStar_Syntax_Syntax.sigquals; FStar_Syntax_Syntax.sigmeta = uu___274_18446.FStar_Syntax_Syntax.sigmeta; FStar_Syntax_Syntax.sigattrs = uu____18447}))
in (uu____18445)::(se1)::acc)
in (forward uu____18442 sigelts1))
end
| uu____18502 -> begin
(forward ((se1)::acc) ((se2)::sigelts1))
end)
end
| sigelts1 -> begin
(FStar_List.rev_append acc sigelts1)
end))
in (

let uu____18510 = (forward [] sigelts)
in ((env1), (uu____18510))))
end)))


let open_prims_all : (FStar_Parser_AST.decoration Prims.list  ->  FStar_Parser_AST.decl) Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Parser_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Parser_Const.all_lid)) FStar_Range.dummyRange))::[]


let desugar_modul_common : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let env1 = (match (((curmod), (m))) with
| (FStar_Pervasives_Native.None, uu____18564) -> begin
env
end
| (FStar_Pervasives_Native.Some ({FStar_Syntax_Syntax.name = prev_lid; FStar_Syntax_Syntax.declarations = uu____18568; FStar_Syntax_Syntax.exports = uu____18569; FStar_Syntax_Syntax.is_interface = uu____18570}), FStar_Parser_AST.Module (current_lid, uu____18572)) when ((FStar_Ident.lid_equals prev_lid current_lid) && (FStar_Options.interactive ())) -> begin
env
end
| (FStar_Pervasives_Native.Some (prev_mod), uu____18580) -> begin
(FStar_ToSyntax_Env.finish_module_or_interface env prev_mod)
end)
in (

let uu____18583 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(

let uu____18619 = (FStar_ToSyntax_Env.prepare_module_or_interface true admitted env1 mname FStar_ToSyntax_Env.default_mii)
in ((uu____18619), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(

let uu____18636 = (FStar_ToSyntax_Env.prepare_module_or_interface false false env1 mname FStar_ToSyntax_Env.default_mii)
in ((uu____18636), (mname), (decls), (false)))
end)
in (match (uu____18583) with
| ((env2, pop_when_done), mname, decls, intf) -> begin
(

let uu____18666 = (desugar_decls env2 decls)
in (match (uu____18666) with
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

let uu____18724 = ((FStar_Options.interactive ()) && (

let uu____18726 = (

let uu____18727 = (

let uu____18728 = (FStar_Options.file_list ())
in (FStar_List.hd uu____18728))
in (FStar_Util.get_file_extension uu____18727))
in (FStar_List.mem uu____18726 (("fsti")::("fsi")::[]))))
in (match (uu____18724) with
| true -> begin
(as_interface m)
end
| uu____18731 -> begin
m
end))
in (

let uu____18732 = (desugar_modul_common curmod env m1)
in (match (uu____18732) with
| (x, y, pop_when_done) -> begin
((match (pop_when_done) with
| true -> begin
(

let uu____18747 = (FStar_ToSyntax_Env.pop ())
in ())
end
| uu____18748 -> begin
()
end);
((x), (y));
)
end))))


let desugar_modul : FStar_ToSyntax_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (

let uu____18765 = (desugar_modul_common FStar_Pervasives_Native.None env m)
in (match (uu____18765) with
| (env1, modul, pop_when_done) -> begin
(

let env2 = (FStar_ToSyntax_Env.finish_module_or_interface env1 modul)
in ((

let uu____18781 = (FStar_Options.dump_module modul.FStar_Syntax_Syntax.name.FStar_Ident.str)
in (match (uu____18781) with
| true -> begin
(

let uu____18782 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" uu____18782))
end
| uu____18783 -> begin
()
end));
(

let uu____18784 = (match (pop_when_done) with
| true -> begin
(FStar_ToSyntax_Env.export_interface modul.FStar_Syntax_Syntax.name env2)
end
| uu____18785 -> begin
env2
end)
in ((uu____18784), (modul)));
))
end)))


let ast_modul_to_modul : FStar_Parser_AST.modul  ->  FStar_Syntax_Syntax.modul FStar_ToSyntax_Env.withenv = (fun modul env -> (

let uu____18799 = (desugar_modul env modul)
in (match (uu____18799) with
| (env1, modul1) -> begin
((modul1), (env1))
end)))


let decls_to_sigelts : FStar_Parser_AST.decl Prims.list  ->  FStar_Syntax_Syntax.sigelts FStar_ToSyntax_Env.withenv = (fun decls env -> (

let uu____18827 = (desugar_decls env decls)
in (match (uu____18827) with
| (env1, sigelts) -> begin
((sigelts), (env1))
end)))


let partial_ast_modul_to_modul : FStar_Syntax_Syntax.modul FStar_Pervasives_Native.option  ->  FStar_Parser_AST.modul  ->  FStar_Syntax_Syntax.modul FStar_ToSyntax_Env.withenv = (fun modul a_modul env -> (

let uu____18867 = (desugar_partial_modul modul env a_modul)
in (match (uu____18867) with
| (env1, modul1) -> begin
((modul1), (env1))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_ToSyntax_Env.module_inclusion_info  ->  Prims.unit FStar_ToSyntax_Env.withenv = (fun m mii en -> (

let uu____18895 = (FStar_ToSyntax_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name mii)
in (match (uu____18895) with
| (en1, pop_when_done) -> begin
(

let en2 = (

let uu____18907 = (FStar_ToSyntax_Env.set_current_module en1 m.FStar_Syntax_Syntax.name)
in (FStar_List.fold_left FStar_ToSyntax_Env.push_sigelt uu____18907 m.FStar_Syntax_Syntax.exports))
in (

let env = (FStar_ToSyntax_Env.finish en2 m)
in (

let uu____18909 = (match (pop_when_done) with
| true -> begin
(FStar_ToSyntax_Env.export_interface m.FStar_Syntax_Syntax.name env)
end
| uu____18910 -> begin
env
end)
in ((()), (uu____18909)))))
end)))




