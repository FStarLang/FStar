
open Prims

let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _65_1 -> (match (_65_1) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Syntax_Syntax.Equality)
end
| _65_32 -> begin
None
end))


let trans_qual : FStar_Range.range  ->  FStar_Ident.lident Prims.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun r maybe_effect_id _65_2 -> (match (_65_2) with
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
| FStar_Parser_AST.Irreducible -> begin
FStar_Syntax_Syntax.Irreducible
end
| FStar_Parser_AST.Logic -> begin
FStar_Syntax_Syntax.Logic
end
| FStar_Parser_AST.TotalEffect -> begin
FStar_Syntax_Syntax.TotalEffect
end
| FStar_Parser_AST.Effect -> begin
FStar_Syntax_Syntax.Effect
end
| FStar_Parser_AST.New -> begin
FStar_Syntax_Syntax.New
end
| FStar_Parser_AST.Abstract -> begin
FStar_Syntax_Syntax.Abstract
end
| FStar_Parser_AST.Opaque -> begin
(

let _65_47 = (FStar_TypeChecker_Errors.warn r "The \'opaque\' qualifier is deprecated since its use was strangely schizophrenic. There were two overloaded uses: (1) Given \'opaque val f : t\', the behavior was to exclude the definition of \'f\' to the SMT solver. This corresponds roughly to the new \'irreducible\' qualifier. (2) Given \'opaque type t = t\'\', the behavior was to provide the definition of \'t\' to the SMT solver, but not to inline it, unless absolutely required for unification. This corresponds roughly to the behavior of \'unfoldable\' (which is currently the default).")
in FStar_Syntax_Syntax.Visible_default)
end
| FStar_Parser_AST.Reflectable -> begin
(match (maybe_effect_id) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Qualifier reflect only supported on effects"), (r)))))
end
| Some (effect_id) -> begin
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
(Prims.raise (FStar_Syntax_Syntax.Error ((("The \'default\' qualifier on effects is no longer supported"), (r)))))
end
| (FStar_Parser_AST.Inline) | (FStar_Parser_AST.Visible) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unsupported qualifier"), (r)))))
end))


let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun _65_3 -> (match (_65_3) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end))


let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _65_4 -> (match (_65_4) with
| FStar_Parser_AST.Hash -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| _65_67 -> begin
None
end))


let arg_withimp_e = (fun imp t -> ((t), ((as_imp imp))))


let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
((t), (Some (FStar_Syntax_Syntax.imp_tag)))
end
| _65_74 -> begin
((t), (None))
end))


let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_65_78) -> begin
true
end
| _65_81 -> begin
false
end)))))


let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _65_86 -> begin
t
end))


let tm_type_z : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _160_25 = (let _160_24 = (FStar_Ident.lid_of_path (("Type0")::[]) r)
in FStar_Parser_AST.Name (_160_24))
in (FStar_Parser_AST.mk_term _160_25 r FStar_Parser_AST.Kind)))


let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _160_29 = (let _160_28 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_160_28))
in (FStar_Parser_AST.mk_term _160_29 r FStar_Parser_AST.Kind)))


let rec is_comp_type : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> (match (t.FStar_Parser_AST.tm) with
| (FStar_Parser_AST.Name (l)) | (FStar_Parser_AST.Construct (l, _)) -> begin
(let _160_34 = (FStar_Parser_Env.try_lookup_effect_name env l)
in (FStar_All.pipe_right _160_34 FStar_Option.isSome))
end
| FStar_Parser_AST.App (head, _65_99, _65_101) -> begin
(is_comp_type env head)
end
| (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) | (FStar_Parser_AST.LetOpen (_, t)) -> begin
(is_comp_type env t)
end
| _65_115 -> begin
false
end))


let unit_ty : FStar_Parser_AST.term = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.unit_lid)) FStar_Range.dummyRange FStar_Parser_AST.Type)


let compile_op : Prims.int  ->  Prims.string  ->  Prims.string = (fun arity s -> (

let name_of_char = (fun _65_5 -> (match (_65_5) with
| '&' -> begin
"Amp"
end
| '@' -> begin
"At"
end
| '+' -> begin
"Plus"
end
| '-' when (arity = (Prims.parse_int "1")) -> begin
"Minus"
end
| '-' -> begin
"Subtraction"
end
| '/' -> begin
"Slash"
end
| '<' -> begin
"Less"
end
| '=' -> begin
"Equals"
end
| '>' -> begin
"Greater"
end
| '_' -> begin
"Underscore"
end
| '|' -> begin
"Bar"
end
| '!' -> begin
"Bang"
end
| '^' -> begin
"Hat"
end
| '%' -> begin
"Percent"
end
| '*' -> begin
"Star"
end
| '?' -> begin
"Question"
end
| ':' -> begin
"Colon"
end
| _65_137 -> begin
"UNKNOWN"
end))
in (

let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _160_45 = (let _160_43 = (FStar_Util.char_at s i)
in (name_of_char _160_43))
in (let _160_44 = (aux (i + (Prims.parse_int "1")))
in (_160_45)::_160_44))
end)
in (match (s) with
| ".[]<-" -> begin
"op_String_Assignment"
end
| ".()<-" -> begin
"op_Array_Assignment"
end
| ".[]" -> begin
"op_String_Access"
end
| ".()" -> begin
"op_Array_Access"
end
| _65_146 -> begin
(let _160_47 = (let _160_46 = (aux (Prims.parse_int "0"))
in (FStar_String.concat "_" _160_46))
in (Prims.strcat "op_" _160_47))
end))))


let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _160_57 = (let _160_56 = (let _160_55 = (let _160_54 = (compile_op n s)
in ((_160_54), (r)))
in (FStar_Ident.mk_ident _160_55))
in (_160_56)::[])
in (FStar_All.pipe_right _160_57 FStar_Ident.lid_of_ids)))


let op_as_term : FStar_Parser_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.term Prims.option = (fun env arity rng s -> (

let r = (fun l dd -> (let _160_71 = (let _160_70 = (FStar_Syntax_Syntax.lid_as_fv (FStar_Ident.set_lid_range l rng) dd None)
in (FStar_All.pipe_right _160_70 FStar_Syntax_Syntax.fv_to_tm))
in Some (_160_71)))
in (

let fallback = (fun _65_158 -> (match (()) with
| () -> begin
(match (s) with
| "=" -> begin
(r FStar_Syntax_Const.op_Eq FStar_Syntax_Syntax.Delta_equational)
end
| ":=" -> begin
(r FStar_Syntax_Const.write_lid FStar_Syntax_Syntax.Delta_equational)
end
| "<" -> begin
(r FStar_Syntax_Const.op_LT FStar_Syntax_Syntax.Delta_equational)
end
| "<=" -> begin
(r FStar_Syntax_Const.op_LTE FStar_Syntax_Syntax.Delta_equational)
end
| ">" -> begin
(r FStar_Syntax_Const.op_GT FStar_Syntax_Syntax.Delta_equational)
end
| ">=" -> begin
(r FStar_Syntax_Const.op_GTE FStar_Syntax_Syntax.Delta_equational)
end
| "&&" -> begin
(r FStar_Syntax_Const.op_And FStar_Syntax_Syntax.Delta_equational)
end
| "||" -> begin
(r FStar_Syntax_Const.op_Or FStar_Syntax_Syntax.Delta_equational)
end
| "+" -> begin
(r FStar_Syntax_Const.op_Addition FStar_Syntax_Syntax.Delta_equational)
end
| "-" when (arity = (Prims.parse_int "1")) -> begin
(r FStar_Syntax_Const.op_Minus FStar_Syntax_Syntax.Delta_equational)
end
| "-" -> begin
(r FStar_Syntax_Const.op_Subtraction FStar_Syntax_Syntax.Delta_equational)
end
| "/" -> begin
(r FStar_Syntax_Const.op_Division FStar_Syntax_Syntax.Delta_equational)
end
| "%" -> begin
(r FStar_Syntax_Const.op_Modulus FStar_Syntax_Syntax.Delta_equational)
end
| "!" -> begin
(r FStar_Syntax_Const.read_lid FStar_Syntax_Syntax.Delta_equational)
end
| "@" -> begin
(r FStar_Syntax_Const.list_append_lid FStar_Syntax_Syntax.Delta_equational)
end
| "^" -> begin
(r FStar_Syntax_Const.strcat_lid FStar_Syntax_Syntax.Delta_equational)
end
| "|>" -> begin
(r FStar_Syntax_Const.pipe_right_lid FStar_Syntax_Syntax.Delta_equational)
end
| "<|" -> begin
(r FStar_Syntax_Const.pipe_left_lid FStar_Syntax_Syntax.Delta_equational)
end
| "<>" -> begin
(r FStar_Syntax_Const.op_notEq FStar_Syntax_Syntax.Delta_equational)
end
| "~" -> begin
(r FStar_Syntax_Const.not_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "2"))))
end
| "==" -> begin
(r FStar_Syntax_Const.eq2_lid FStar_Syntax_Syntax.Delta_constant)
end
| "<<" -> begin
(r FStar_Syntax_Const.precedes_lid FStar_Syntax_Syntax.Delta_constant)
end
| "/\\" -> begin
(r FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))))
end
| "\\/" -> begin
(r FStar_Syntax_Const.or_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))))
end
| "==>" -> begin
(r FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))))
end
| "<==>" -> begin
(r FStar_Syntax_Const.iff_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "2"))))
end
| _65_186 -> begin
None
end)
end))
in (match ((let _160_74 = (compile_op_lid arity s rng)
in (FStar_Parser_Env.try_lookup_lid env _160_74))) with
| Some (t) -> begin
Some ((Prims.fst t))
end
| _65_190 -> begin
(fallback ())
end))))


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _160_81 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _160_81)))


let rec free_type_vars_b : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_65_199) -> begin
((env), ([]))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let _65_206 = (FStar_Parser_Env.push_bv env x)
in (match (_65_206) with
| (env, _65_205) -> begin
((env), ((x)::[]))
end))
end
| FStar_Parser_AST.Annotated (_65_208, term) -> begin
(let _160_88 = (free_type_vars env term)
in ((env), (_160_88)))
end
| FStar_Parser_AST.TAnnotated (id, _65_214) -> begin
(

let _65_220 = (FStar_Parser_Env.push_bv env id)
in (match (_65_220) with
| (env, _65_219) -> begin
((env), ([]))
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _160_89 = (free_type_vars env t)
in ((env), (_160_89)))
end))
and free_type_vars : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _160_92 = (unparen t)
in _160_92.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (_65_226) -> begin
(FStar_All.failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_Env.try_lookup_id env a)) with
| None -> begin
(a)::[]
end
| _65_232 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Projector (_)) | (FStar_Parser_AST.Discrim (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Assign (_, t)) | (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_65_272, ts) -> begin
(FStar_List.collect (fun _65_279 -> (match (_65_279) with
| (t, _65_278) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_65_281, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _65_288) -> begin
(let _160_95 = (free_type_vars env t1)
in (let _160_94 = (free_type_vars env t2)
in (FStar_List.append _160_95 _160_94)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(

let _65_297 = (free_type_vars_b env b)
in (match (_65_297) with
| (env, f) -> begin
(let _160_96 = (free_type_vars env t)
in (FStar_List.append f _160_96))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(

let _65_313 = (FStar_List.fold_left (fun _65_306 binder -> (match (_65_306) with
| (env, free) -> begin
(

let _65_310 = (free_type_vars_b env binder)
in (match (_65_310) with
| (env, f) -> begin
((env), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (_65_313) with
| (env, free) -> begin
(let _160_99 = (free_type_vars env body)
in (FStar_List.append free _160_99))
end))
end
| FStar_Parser_AST.Project (t, _65_316) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Attributes (cattributes) -> begin
(FStar_List.collect (free_type_vars env) cattributes)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
[]
end))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (

let rec aux = (fun args t -> (match ((let _160_106 = (unparen t)
in _160_106.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| _65_365 -> begin
((t), (args))
end))
in (aux [] t)))


let close : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _160_111 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _160_111))
in if ((FStar_List.length ftv) = (Prims.parse_int "0")) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _160_115 = (let _160_114 = (let _160_113 = (tm_type x.FStar_Ident.idRange)
in ((x), (_160_113)))
in FStar_Parser_AST.TAnnotated (_160_114))
in (FStar_Parser_AST.mk_binder _160_115 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))


let close_fun : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _160_120 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _160_120))
in if ((FStar_List.length ftv) = (Prims.parse_int "0")) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _160_124 = (let _160_123 = (let _160_122 = (tm_type x.FStar_Ident.idRange)
in ((x), (_160_122)))
in FStar_Parser_AST.TAnnotated (_160_123))
in (FStar_Parser_AST.mk_binder _160_124 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let t = (match ((let _160_125 = (unparen t)
in _160_125.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_65_378) -> begin
t
end
| _65_381 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end)
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result)))
end))


let rec uncurry : FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term) = (fun bs t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (binders, t) -> begin
(uncurry (FStar_List.append bs binders) t)
end
| _65_391 -> begin
((bs), (t))
end))


let rec is_var_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatWild) | (FStar_Parser_AST.PatTvar (_, _)) | (FStar_Parser_AST.PatVar (_, _)) -> begin
true
end
| FStar_Parser_AST.PatAscribed (p, _65_408) -> begin
(is_var_pattern p)
end
| _65_412 -> begin
false
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _65_416) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_65_422); FStar_Parser_AST.prange = _65_420}, _65_426) -> begin
true
end
| _65_430 -> begin
false
end))


let replace_unit_pattern : FStar_Parser_AST.pattern  ->  FStar_Parser_AST.pattern = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatConst (FStar_Const.Const_unit) -> begin
(FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatAscribed ((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)), (unit_ty)))) p.FStar_Parser_AST.prange)
end
| _65_435 -> begin
p
end))


let rec destruct_app_pattern : FStar_Parser_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _65_447 = (destruct_app_pattern env is_top_level p)
in (match (_65_447) with
| (name, args, _65_446) -> begin
((name), (args), (Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _65_452); FStar_Parser_AST.prange = _65_449}, args) when is_top_level -> begin
(let _160_143 = (let _160_142 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_160_142))
in ((_160_143), (args), (None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _65_463); FStar_Parser_AST.prange = _65_460}, args) -> begin
((FStar_Util.Inl (id)), (args), (None))
end
| _65_471 -> begin
(FStar_All.failwith "Not an app pattern")
end))


type bnd =
| LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * FStar_Syntax_Syntax.term)


let is_LocalBinder = (fun _discr_ -> (match (_discr_) with
| LocalBinder (_) -> begin
true
end
| _ -> begin
false
end))


let is_LetBinder = (fun _discr_ -> (match (_discr_) with
| LetBinder (_) -> begin
true
end
| _ -> begin
false
end))


let ___LocalBinder____0 = (fun projectee -> (match (projectee) with
| LocalBinder (_65_474) -> begin
_65_474
end))


let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_65_477) -> begin
_65_477
end))


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun _65_6 -> (match (_65_6) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| _65_484 -> begin
(FStar_All.failwith "Impossible")
end))


let as_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_Parser_Env.env) = (fun env imp _65_7 -> (match (_65_7) with
| (None, k) -> begin
(let _160_180 = (FStar_Syntax_Syntax.null_binder k)
in ((_160_180), (env)))
end
| (Some (a), k) -> begin
(

let _65_497 = (FStar_Parser_Env.push_bv env a)
in (match (_65_497) with
| (env, a) -> begin
(((((

let _65_498 = a
in {FStar_Syntax_Syntax.ppname = _65_498.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_498.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), ((trans_aqual imp)))), (env))
end))
end))


type env_t =
FStar_Parser_Env.env


type lenv_t =
FStar_Syntax_Syntax.bv Prims.list


let mk_lb : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.letbinding = (fun _65_503 -> (match (_65_503) with
| (n, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))


let no_annot_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t None))


let mk_ref_read = (fun tm -> (

let tm' = (let _160_193 = (let _160_192 = (let _160_188 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _160_188))
in (let _160_191 = (let _160_190 = (let _160_189 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (_160_189)))
in (_160_190)::[])
in ((_160_192), (_160_191))))
in FStar_Syntax_Syntax.Tm_app (_160_193))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_alloc = (fun tm -> (

let tm' = (let _160_200 = (let _160_199 = (let _160_195 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _160_195))
in (let _160_198 = (let _160_197 = (let _160_196 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (_160_196)))
in (_160_197)::[])
in ((_160_199), (_160_198))))
in FStar_Syntax_Syntax.Tm_app (_160_200))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_assign = (fun t1 t2 pos -> (

let tm = (let _160_212 = (let _160_211 = (let _160_204 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _160_204))
in (let _160_210 = (let _160_209 = (let _160_205 = (FStar_Syntax_Syntax.as_implicit false)
in ((t1), (_160_205)))
in (let _160_208 = (let _160_207 = (let _160_206 = (FStar_Syntax_Syntax.as_implicit false)
in ((t2), (_160_206)))
in (_160_207)::[])
in (_160_209)::_160_208))
in ((_160_211), (_160_210))))
in FStar_Syntax_Syntax.Tm_app (_160_212))
in (FStar_Syntax_Syntax.mk tm None pos)))


let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun _65_8 -> (match (_65_8) with
| ("repr") | ("post") | ("pre") | ("wp") -> begin
true
end
| _65_520 -> begin
false
end))


let rec desugar_data_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat) = (fun env p is_mut -> (

let check_linear_pattern_variables = (fun p -> (

let rec pat_vars = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_dot_term (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_constant (_)) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (_65_540, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out _65_548 -> (match (_65_548) with
| (p, _65_547) -> begin
(let _160_271 = (pat_vars p)
in (FStar_Util.set_union out _160_271))
end)) FStar_Syntax_Syntax.no_names))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let xs = (pat_vars hd)
in if (not ((FStar_Util.for_all (fun p -> (

let ys = (pat_vars p)
in ((FStar_Util.set_is_subset_of xs ys) && (FStar_Util.set_is_subset_of ys xs)))) tl))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Disjunctive pattern binds different variables in each case"), (p.FStar_Syntax_Syntax.p)))))
end else begin
xs
end)
end))
in (pat_vars p)))
in (

let _65_571 = (match (((is_mut), (p.FStar_Parser_AST.pat))) with
| ((false, _)) | ((true, FStar_Parser_AST.PatVar (_))) -> begin
()
end
| (true, _65_569) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("let-mutable is for variables only"), (p.FStar_Parser_AST.prange)))))
end)
in (

let push_bv_maybe_mut = if is_mut then begin
FStar_Parser_Env.push_bv_mutable
end else begin
FStar_Parser_Env.push_bv
end
in (

let resolvex = (fun l e x -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText))))) with
| Some (y) -> begin
((l), (e), (y))
end
| _65_582 -> begin
(

let _65_585 = (push_bv_maybe_mut e x)
in (match (_65_585) with
| (e, x) -> begin
(((x)::l), (e), (x))
end))
end))
in (

let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun b -> (b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText))))) with
| Some (b) -> begin
((l), (e), (b))
end
| _65_594 -> begin
(

let _65_597 = (push_bv_maybe_mut e a)
in (match (_65_597) with
| (e, a) -> begin
(((a)::l), (e), (a))
end))
end))
in (

let rec aux = (fun loc env p -> (

let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Parser_AST.prange))
in (

let pos_r = (fun r q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r))
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (op) -> begin
(let _160_307 = (let _160_306 = (let _160_305 = (let _160_304 = (let _160_303 = (compile_op (Prims.parse_int "0") op)
in (FStar_Ident.id_of_text _160_303))
in ((_160_304), (None)))
in FStar_Parser_AST.PatVar (_160_305))
in {FStar_Parser_AST.pat = _160_306; FStar_Parser_AST.prange = p.FStar_Parser_AST.prange})
in (aux loc env _160_307))
end
| FStar_Parser_AST.PatOr ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.PatOr ((p)::ps) -> begin
(

let _65_621 = (aux loc env p)
in (match (_65_621) with
| (loc, env, var, p, _65_620) -> begin
(

let _65_638 = (FStar_List.fold_left (fun _65_625 p -> (match (_65_625) with
| (loc, env, ps) -> begin
(

let _65_634 = (aux loc env p)
in (match (_65_634) with
| (loc, env, _65_630, p, _65_633) -> begin
((loc), (env), ((p)::ps))
end))
end)) ((loc), (env), ([])) ps)
in (match (_65_638) with
| (loc, env, ps) -> begin
(

let pat = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in ((loc), (env), (var), (pat), (false)))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _65_649 = (aux loc env p)
in (match (_65_649) with
| (loc, env', binder, p, imp) -> begin
(

let binder = (match (binder) with
| LetBinder (_65_651) -> begin
(FStar_All.failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t = (let _160_310 = (close_fun env t)
in (desugar_term env _160_310))
in LocalBinder ((((

let _65_658 = x
in {FStar_Syntax_Syntax.ppname = _65_658.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_658.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (aq))))
end)
in ((loc), (env'), (binder), (p), (imp)))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _160_311 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env), (LocalBinder (((x), (None)))), (_160_311), (false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _160_312 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env), (LocalBinder (((x), (None)))), (_160_312), (false))))
end
| (FStar_Parser_AST.PatTvar (x, aq)) | (FStar_Parser_AST.PatVar (x, aq)) -> begin
(

let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (

let aq = (trans_aqual aq)
in (

let _65_677 = (resolvex loc env x)
in (match (_65_677) with
| (loc, env, xbv) -> begin
(let _160_313 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc), (env), (LocalBinder (((xbv), (aq)))), (_160_313), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _160_314 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), ([])))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_160_314), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _65_683}, args) -> begin
(

let _65_705 = (FStar_List.fold_right (fun arg _65_694 -> (match (_65_694) with
| (loc, env, args) -> begin
(

let _65_701 = (aux loc env arg)
in (match (_65_701) with
| (loc, env, _65_698, arg, imp) -> begin
((loc), (env), ((((arg), (imp)))::args))
end))
end)) args ((loc), (env), ([])))
in (match (_65_705) with
| (loc, env, args) -> begin
(

let l = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _160_317 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_160_317), (false)))))
end))
end
| FStar_Parser_AST.PatApp (_65_709) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let _65_729 = (FStar_List.fold_right (fun pat _65_717 -> (match (_65_717) with
| (loc, env, pats) -> begin
(

let _65_725 = (aux loc env pat)
in (match (_65_725) with
| (loc, env, _65_721, pat, _65_724) -> begin
((loc), (env), ((pat)::pats))
end))
end)) pats ((loc), (env), ([])))
in (match (_65_729) with
| (loc, env, pats) -> begin
(

let pat = (let _160_330 = (let _160_329 = (let _160_325 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _160_325))
in (let _160_328 = (let _160_327 = (let _160_326 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_160_326), ([])))
in FStar_Syntax_Syntax.Pat_cons (_160_327))
in (FStar_All.pipe_left _160_329 _160_328)))
in (FStar_List.fold_right (fun hd tl -> (

let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (let _160_324 = (let _160_323 = (let _160_322 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_160_322), ((((hd), (false)))::(((tl), (false)))::[])))
in FStar_Syntax_Syntax.Pat_cons (_160_323))
in (FStar_All.pipe_left (pos_r r) _160_324)))) pats _160_330))
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc), (env), (LocalBinder (((x), (None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(

let _65_755 = (FStar_List.fold_left (fun _65_742 p -> (match (_65_742) with
| (loc, env, pats) -> begin
(

let _65_751 = (aux loc env p)
in (match (_65_751) with
| (loc, env, _65_747, pat, _65_750) -> begin
((loc), (env), ((((pat), (false)))::pats))
end))
end)) ((loc), (env), ([])) args)
in (match (_65_755) with
| (loc, env, args) -> begin
(

let args = (FStar_List.rev args)
in (

let l = if dep then begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end else begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end
in (

let _65_761 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) l)
in (match (_65_761) with
| (constr, _65_760) -> begin
(

let l = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| _65_765 -> begin
(FStar_All.failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _160_333 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_160_333), (false)))))
end))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(

let _65_775 = (FStar_List.hd fields)
in (match (_65_775) with
| (f, _65_774) -> begin
(

let _65_779 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_65_779) with
| (record, _65_778) -> begin
(

let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _65_782 -> (match (_65_782) with
| (f, p) -> begin
(let _160_335 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.qualify_field_to_record env record) f)
in ((_160_335), (p)))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _65_787 -> (match (_65_787) with
| (f, _65_786) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _65_791 -> (match (_65_791) with
| (g, _65_790) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_65_794, p) -> begin
p
end)
end))))
in (

let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_Env.constrname)) p.FStar_Parser_AST.prange)), (args)))) p.FStar_Parser_AST.prange)
in (

let _65_806 = (aux loc env app)
in (match (_65_806) with
| (env, e, b, p, _65_805) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(let _160_344 = (let _160_343 = (let _160_342 = (

let _65_811 = fv
in (let _160_341 = (let _160_340 = (let _160_339 = (let _160_338 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_Env.typename), (_160_338)))
in FStar_Syntax_Syntax.Record_ctor (_160_339))
in Some (_160_340))
in {FStar_Syntax_Syntax.fv_name = _65_811.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = _65_811.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _160_341}))
in ((_160_342), (args)))
in FStar_Syntax_Syntax.Pat_cons (_160_343))
in (FStar_All.pipe_left pos _160_344))
end
| _65_814 -> begin
p
end)
in ((env), (e), (b), (p), (false)))
end)))))
end))
end))
end))))
in (

let _65_823 = (aux [] env p)
in (match (_65_823) with
| (_65_817, env, b, p, _65_822) -> begin
(

let _65_824 = (let _160_345 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore _160_345))
in ((env), (b), (p)))
end)))))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p is_mut -> (

let mklet = (fun x -> (let _160_354 = (let _160_353 = (let _160_352 = (FStar_Parser_Env.qualify env x)
in ((_160_352), (FStar_Syntax_Syntax.tun)))
in LetBinder (_160_353))
in ((env), (_160_354), (None))))
in if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(let _160_356 = (let _160_355 = (compile_op (Prims.parse_int "0") x)
in (FStar_Ident.id_of_text _160_355))
in (mklet _160_356))
end
| FStar_Parser_AST.PatVar (x, _65_836) -> begin
(mklet x)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _65_843); FStar_Parser_AST.prange = _65_840}, t) -> begin
(let _160_360 = (let _160_359 = (let _160_358 = (FStar_Parser_Env.qualify env x)
in (let _160_357 = (desugar_term env t)
in ((_160_358), (_160_357))))
in LetBinder (_160_359))
in ((env), (_160_360), (None)))
end
| _65_851 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end else begin
(

let _65_855 = (desugar_data_pat env p is_mut)
in (match (_65_855) with
| (env, binder, p) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| _65_863 -> begin
Some (p)
end)
in ((env), (binder), (p)))
end))
end))
and desugar_binding_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun _65_867 env pat -> (

let _65_875 = (desugar_data_pat env pat false)
in (match (_65_875) with
| (env, _65_873, pat) -> begin
((env), (pat))
end)))
and desugar_match_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let _65_880 = env
in {FStar_Parser_Env.curmodule = _65_880.FStar_Parser_Env.curmodule; FStar_Parser_Env.curmonad = _65_880.FStar_Parser_Env.curmonad; FStar_Parser_Env.modules = _65_880.FStar_Parser_Env.modules; FStar_Parser_Env.scope_mods = _65_880.FStar_Parser_Env.scope_mods; FStar_Parser_Env.sigaccum = _65_880.FStar_Parser_Env.sigaccum; FStar_Parser_Env.sigmap = _65_880.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _65_880.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _65_880.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _65_880.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let _65_885 = env
in {FStar_Parser_Env.curmodule = _65_885.FStar_Parser_Env.curmodule; FStar_Parser_Env.curmonad = _65_885.FStar_Parser_Env.curmonad; FStar_Parser_Env.modules = _65_885.FStar_Parser_Env.modules; FStar_Parser_Env.scope_mods = _65_885.FStar_Parser_Env.scope_mods; FStar_Parser_Env.sigaccum = _65_885.FStar_Parser_Env.sigaccum; FStar_Parser_Env.sigmap = _65_885.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _65_885.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _65_885.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _65_885.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_machine_integer : FStar_Parser_Env.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env repr _65_892 range -> (match (_65_892) with
| (signedness, width) -> begin
(

let lid = (Prims.strcat "FStar." (Prims.strcat (match (signedness) with
| FStar_Const.Unsigned -> begin
"U"
end
| FStar_Const.Signed -> begin
""
end) (Prims.strcat "Int" (Prims.strcat (match (width) with
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
end) (Prims.strcat "." (Prims.strcat (match (signedness) with
| FStar_Const.Unsigned -> begin
"u"
end
| FStar_Const.Signed -> begin
""
end) "int_to_t"))))))
in (

let lid = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text lid) range)
in (

let lid = (match ((FStar_Parser_Env.try_lookup_lid env lid)) with
| Some (lid) -> begin
(Prims.fst lid)
end
| None -> begin
(let _160_376 = (FStar_Util.format1 "%s not in scope\n" (FStar_Ident.text_of_lid lid))
in (FStar_All.failwith _160_376))
end)
in (

let repr = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (None))))) None range)
in (let _160_381 = (let _160_380 = (let _160_379 = (let _160_378 = (let _160_377 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr), (_160_377)))
in (_160_378)::[])
in ((lid), (_160_379)))
in FStar_Syntax_Syntax.Tm_app (_160_380))
in (FStar_Syntax_Syntax.mk _160_381 None range))))))
end))
and desugar_name : (FStar_Syntax_Syntax.term'  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env_t  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.term = (fun mk setpos env l -> (

let _65_915 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) l)
in (match (_65_915) with
| (tm, mut) -> begin
(

let tm = (setpos tm)
in if mut then begin
(let _160_394 = (let _160_393 = (let _160_392 = (mk_ref_read tm)
in ((_160_392), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval))))
in FStar_Syntax_Syntax.Tm_meta (_160_393))
in (FStar_All.pipe_left mk _160_394))
end else begin
tm
end)
end)))
and desugar_attributes : FStar_Parser_Env.env  ->  FStar_Parser_AST.term Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun env cattributes -> (

let desugar_attribute = (fun t -> (match ((let _160_399 = (unparen t)
in _160_399.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Var ({FStar_Ident.ns = _65_927; FStar_Ident.ident = _65_925; FStar_Ident.nsstr = _65_923; FStar_Ident.str = "cps"}) -> begin
FStar_Syntax_Syntax.CPS
end
| _65_931 -> begin
(let _160_403 = (let _160_402 = (let _160_401 = (let _160_400 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "Unknown attribute " _160_400))
in ((_160_401), (t.FStar_Parser_AST.range)))
in FStar_Syntax_Syntax.Error (_160_402))
in (Prims.raise _160_403))
end))
in (FStar_List.map desugar_attribute cattributes)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (

let mk = (fun e -> (FStar_Syntax_Syntax.mk e None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let _65_939 = e
in {FStar_Syntax_Syntax.n = _65_939.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _65_939.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _65_939.FStar_Syntax_Syntax.vars}))
in (match ((let _160_411 = (unparen top)
in _160_411.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (_65_943) -> begin
(desugar_formula env top)
end
| FStar_Parser_AST.Requires (t, lopt) -> begin
(desugar_formula env t)
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(desugar_formula env t)
end
| FStar_Parser_AST.Attributes (ts) -> begin
(FStar_All.failwith "Attributes should not be desugared by desugar_term_maybe_top")
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (i, Some (size))) -> begin
(desugar_machine_integer env i size top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Const (c) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (c)))
end
| FStar_Parser_AST.Op ("=!=", args) -> begin
(desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Op ((("~"), (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Op ((("=="), (args)))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))::[])))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op ("*", (_65_971)::(_65_969)::[]) when (let _160_412 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right _160_412 FStar_Option.isNone)) -> begin
(

let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", (t1)::(t2)::[]) -> begin
(let _160_415 = (flatten t1)
in (FStar_List.append _160_415 ((t2)::[])))
end
| _65_984 -> begin
(t)::[]
end))
in (

let targs = (let _160_419 = (let _160_416 = (unparen top)
in (flatten _160_416))
in (FStar_All.pipe_right _160_419 (FStar_List.map (fun t -> (let _160_418 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg _160_418))))))
in (

let _65_990 = (let _160_420 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) _160_420))
in (match (_65_990) with
| (tup, _65_989) -> begin
(mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _160_422 = (let _160_421 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) a)
in (Prims.fst _160_421))
in (FStar_All.pipe_left setpos _160_422))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Unexpected or unbound operator: " s)), (top.FStar_Parser_AST.range)))))
end
| Some (op) -> begin
if ((FStar_List.length args) > (Prims.parse_int "0")) then begin
(

let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _160_424 = (desugar_term env t)
in ((_160_424), (None))))))
in (mk (FStar_Syntax_Syntax.Tm_app (((op), (args))))))
end else begin
op
end
end)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _65_1008; FStar_Ident.ident = _65_1006; FStar_Ident.nsstr = _65_1004; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _65_1017; FStar_Ident.ident = _65_1015; FStar_Ident.nsstr = _65_1013; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _65_1026; FStar_Ident.ident = _65_1024; FStar_Ident.nsstr = _65_1022; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _65_1035; FStar_Ident.ident = _65_1033; FStar_Ident.nsstr = _65_1031; FStar_Ident.str = "True"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant None)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _65_1044; FStar_Ident.ident = _65_1042; FStar_Ident.nsstr = _65_1040; FStar_Ident.str = "False"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant None)
end
| FStar_Parser_AST.Projector (eff_name, {FStar_Ident.idText = txt; FStar_Ident.idRange = _65_1049}) when ((is_special_effect_combinator txt) && (FStar_Parser_Env.is_effect_name env eff_name)) -> begin
(match ((FStar_Parser_Env.try_lookup_effect_defn env eff_name)) with
| Some (ed) -> begin
(let _160_425 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" txt))) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.fvar _160_425 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None))
end
| None -> begin
(FStar_All.failwith "immpossible special_effect_combinator")
end)
end
| FStar_Parser_AST.Assign (ident, t2) -> begin
(

let t2 = (desugar_term env t2)
in (

let _65_1064 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) ident)
in (match (_65_1064) with
| (t1, mut) -> begin
(

let _65_1065 = if (not (mut)) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Can only assign to mutable values"), (top.FStar_Parser_AST.range)))))
end else begin
()
end
in (mk_ref_assign t1 t2 top.FStar_Parser_AST.range))
end)))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(desugar_name mk setpos env l)
end
| FStar_Parser_AST.Projector (l, i) -> begin
(

let found = ((let _160_426 = (FStar_Parser_Env.try_lookup_datacon env l)
in (FStar_Option.isSome _160_426)) || (let _160_427 = (FStar_Parser_Env.try_lookup_effect_defn env l)
in (FStar_Option.isSome _160_427)))
in if found then begin
(let _160_428 = (FStar_Syntax_Util.mk_field_projector_name_from_ident l i)
in (desugar_name mk setpos env _160_428))
end else begin
(let _160_431 = (let _160_430 = (let _160_429 = (FStar_Util.format1 "Data constructor or effect %s not found" l.FStar_Ident.str)
in ((_160_429), (top.FStar_Parser_AST.range)))
in FStar_Syntax_Syntax.Error (_160_430))
in (Prims.raise _160_431))
end)
end
| FStar_Parser_AST.Discrim (lid) -> begin
(match ((FStar_Parser_Env.try_lookup_datacon env lid)) with
| None -> begin
(let _160_434 = (let _160_433 = (let _160_432 = (FStar_Util.format1 "Data constructor %s not found" lid.FStar_Ident.str)
in ((_160_432), (top.FStar_Parser_AST.range)))
in FStar_Syntax_Syntax.Error (_160_433))
in (Prims.raise _160_434))
end
| _65_1079 -> begin
(

let lid' = (FStar_Syntax_Util.mk_discriminator lid)
in (desugar_name mk setpos env lid'))
end)
end
| FStar_Parser_AST.Construct (l, args) -> begin
(match ((FStar_Parser_Env.try_lookup_datacon env l)) with
| Some (head) -> begin
(

let _65_1089 = (let _160_435 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in ((_160_435), (true)))
in (match (_65_1089) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| _65_1092 -> begin
(

let args = (FStar_List.map (fun _65_1095 -> (match (_65_1095) with
| (t, imp) -> begin
(

let te = (desugar_term env t)
in (arg_withimp_e imp te))
end)) args)
in (

let app = (mk (FStar_Syntax_Syntax.Tm_app (((head), (args)))))
in if is_data then begin
(mk (FStar_Syntax_Syntax.Tm_meta (((app), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end else begin
app
end))
end)
end))
end
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Constructor " (Prims.strcat l.FStar_Ident.str " not found"))), (top.FStar_Parser_AST.range)))))
end)
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let _65_1124 = (FStar_List.fold_left (fun _65_1107 b -> (match (_65_1107) with
| (env, tparams, typs) -> begin
(

let _65_1111 = (desugar_binder env b)
in (match (_65_1111) with
| (xopt, t) -> begin
(

let _65_1117 = (match (xopt) with
| None -> begin
(let _160_439 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env), (_160_439)))
end
| Some (x) -> begin
(FStar_Parser_Env.push_bv env x)
end)
in (match (_65_1117) with
| (env, x) -> begin
(let _160_443 = (let _160_442 = (let _160_441 = (let _160_440 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _160_440))
in (_160_441)::[])
in (FStar_List.append typs _160_442))
in ((env), ((FStar_List.append tparams (((((

let _65_1118 = x
in {FStar_Syntax_Syntax.ppname = _65_1118.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_1118.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (None)))::[]))), (_160_443)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_65_1124) with
| (env, _65_1122, targs) -> begin
(

let _65_1128 = (let _160_444 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) _160_444))
in (match (_65_1128) with
| (tup, _65_1127) -> begin
(FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let _65_1135 = (uncurry binders t)
in (match (_65_1135) with
| (bs, t) -> begin
(

let rec aux = (fun env bs _65_9 -> (match (_65_9) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (let _160_451 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos _160_451)))
end
| (hd)::tl -> begin
(

let mlenv = (FStar_Parser_Env.default_ml env)
in (

let bb = (desugar_binder mlenv hd)
in (

let _65_1149 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_65_1149) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_binder env b)) with
| (None, _65_1156) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(

let _65_1164 = (as_binder env None b)
in (match (_65_1164) with
| ((x, _65_1161), env) -> begin
(

let f = (desugar_formula env f)
in (let _160_452 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos _160_452)))
end))
end)
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let binders = (FStar_All.pipe_right binders (FStar_List.map replace_unit_pattern))
in (

let _65_1185 = (FStar_List.fold_left (fun _65_1173 pat -> (match (_65_1173) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (_65_1176, t) -> begin
(let _160_456 = (let _160_455 = (free_type_vars env t)
in (FStar_List.append _160_455 ftvs))
in ((env), (_160_456)))
end
| _65_1181 -> begin
((env), (ftvs))
end)
end)) ((env), ([])) binders)
in (match (_65_1185) with
| (_65_1183, ftv) -> begin
(

let ftv = (sort_ftv ftv)
in (

let binders = (let _160_458 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append _160_458 binders))
in (

let rec aux = (fun env bs sc_pat_opt _65_10 -> (match (_65_10) with
| [] -> begin
(

let body = (desugar_term env body)
in (

let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(

let body = (let _160_468 = (let _160_467 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right _160_467 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close _160_468 body))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (None), (body)))::[])))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (let _160_469 = (no_annot_abs (FStar_List.rev bs) body)
in (setpos _160_469))))
end
| (p)::rest -> begin
(

let _65_1209 = (desugar_binding_pat env p)
in (match (_65_1209) with
| (env, b, pat) -> begin
(

let _65_1260 = (match (b) with
| LetBinder (_65_1211) -> begin
(FStar_All.failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt = (match (((pat), (sc_pat_opt))) with
| (None, _65_1219) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _160_471 = (let _160_470 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_160_470), (p)))
in Some (_160_471))
end
| (Some (p), Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (_65_1233), _65_1236) -> begin
(

let tup2 = (let _160_472 = (FStar_Syntax_Util.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _160_472 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (let _160_480 = (let _160_479 = (let _160_478 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (let _160_477 = (let _160_476 = (FStar_Syntax_Syntax.as_arg sc)
in (let _160_475 = (let _160_474 = (let _160_473 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _160_473))
in (_160_474)::[])
in (_160_476)::_160_475))
in ((_160_478), (_160_477))))
in FStar_Syntax_Syntax.Tm_app (_160_479))
in (FStar_Syntax_Syntax.mk _160_480 None top.FStar_Parser_AST.range))
in (

let p = (let _160_481 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p), (false)))::[])))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _160_481))
in Some (((sc), (p))))))
end
| (FStar_Syntax_Syntax.Tm_app (_65_1242, args), FStar_Syntax_Syntax.Pat_cons (_65_1247, pats)) -> begin
(

let tupn = (let _160_482 = (FStar_Syntax_Util.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _160_482 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (let _160_489 = (let _160_488 = (let _160_487 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (let _160_486 = (let _160_485 = (let _160_484 = (let _160_483 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _160_483))
in (_160_484)::[])
in (FStar_List.append args _160_485))
in ((_160_487), (_160_486))))
in FStar_Syntax_Syntax.Tm_app (_160_488))
in (mk _160_489))
in (

let p = (let _160_490 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p), (false)))::[])))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _160_490))
in Some (((sc), (p))))))
end
| _65_1256 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt)))
end)
in (match (_65_1260) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end)))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = rng; FStar_Parser_AST.level = _65_1262}, phi, _65_1269) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(

let phi = (desugar_formula env phi)
in (

let a = (FStar_Ident.set_lid_range a rng)
in (let _160_498 = (let _160_497 = (let _160_496 = (FStar_Syntax_Syntax.fvar a FStar_Syntax_Syntax.Delta_equational None)
in (let _160_495 = (let _160_494 = (FStar_Syntax_Syntax.as_arg phi)
in (let _160_493 = (let _160_492 = (let _160_491 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _160_491))
in (_160_492)::[])
in (_160_494)::_160_493))
in ((_160_496), (_160_495))))
in FStar_Syntax_Syntax.Tm_app (_160_497))
in (mk _160_498))))
end
| FStar_Parser_AST.App (_65_1275) -> begin
(

let rec aux = (fun args e -> (match ((let _160_503 = (unparen e)
in _160_503.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(

let arg = (let _160_504 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _160_504))
in (aux ((arg)::args) e))
end
| _65_1287 -> begin
(

let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app (((head), (args))))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _160_507 = (let _160_506 = (let _160_505 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((_160_505), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))
in FStar_Syntax_Syntax.Tm_meta (_160_506))
in (mk _160_507))
end
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(

let env = (FStar_Parser_Env.push_namespace env lid)
in (desugar_term_maybe_top top_level env e))
end
| FStar_Parser_AST.Let (qual, ((pat, _snd))::_tl, body) -> begin
(

let is_rec = (qual = FStar_Parser_AST.Rec)
in (

let ds_let_rec_or_app = (fun _65_1309 -> (match (()) with
| () -> begin
(

let bindings = (((pat), (_snd)))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _65_1313 -> (match (_65_1313) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _160_511 = (destruct_app_pattern env top_level p)
in ((_160_511), (def)))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _160_512 = (destruct_app_pattern env top_level p)
in ((_160_512), (def)))
end
| _65_1319 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _65_1324); FStar_Parser_AST.prange = _65_1321}, t) -> begin
if top_level then begin
(let _160_515 = (let _160_514 = (let _160_513 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_160_513))
in ((_160_514), ([]), (Some (t))))
in ((_160_515), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (Some (t)))), (def))
end
end
| FStar_Parser_AST.PatVar (id, _65_1333) -> begin
if top_level then begin
(let _160_518 = (let _160_517 = (let _160_516 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_160_516))
in ((_160_517), ([]), (None)))
in ((_160_518), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (None))), (def))
end
end
| _65_1337 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end
end))))
in (

let _65_1366 = (FStar_List.fold_left (fun _65_1342 _65_1351 -> (match (((_65_1342), (_65_1351))) with
| ((env, fnames, rec_bindings), ((f, _65_1345, _65_1347), _65_1350)) -> begin
(

let _65_1362 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let _65_1356 = (FStar_Parser_Env.push_bv env x)
in (match (_65_1356) with
| (env, xx) -> begin
(let _160_522 = (let _160_521 = (FStar_Syntax_Syntax.mk_binder xx)
in (_160_521)::rec_bindings)
in ((env), (FStar_Util.Inl (xx)), (_160_522)))
end))
end
| FStar_Util.Inr (l) -> begin
(let _160_523 = (FStar_Parser_Env.push_top_level_rec_binding env l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in ((_160_523), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (_65_1362) with
| (env, lbname, rec_bindings) -> begin
((env), ((lbname)::fnames), (rec_bindings))
end))
end)) ((env), ([]), ([])) funs)
in (match (_65_1366) with
| (env', fnames, rec_bindings) -> begin
(

let fnames = (FStar_List.rev fnames)
in (

let desugar_one_def = (fun env lbname _65_1377 -> (match (_65_1377) with
| ((_65_1372, args, result_t), def) -> begin
(

let args = (FStar_All.pipe_right args (FStar_List.map replace_unit_pattern))
in (

let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(

let _65_1386 = if (is_comp_type env t) then begin
(match ((FStar_All.pipe_right args (FStar_List.tryFind (fun x -> (not ((is_var_pattern x))))))) with
| None -> begin
()
end
| Some (p) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable"), (p.FStar_Parser_AST.prange)))))
end)
end else begin
()
end
in (let _160_531 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t)))) _160_531 FStar_Parser_AST.Expr)))
end)
in (

let def = (match (args) with
| [] -> begin
def
end
| _65_1391 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.un_curry_abs args def) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
end)
in (

let body = (desugar_term env def)
in (

let lbname = (match (lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl (x)
end
| FStar_Util.Inr (l) -> begin
(let _160_533 = (let _160_532 = (FStar_Syntax_Util.incr_delta_qualifier body)
in (FStar_Syntax_Syntax.lid_as_fv l _160_532 None))
in FStar_Util.Inr (_160_533))
end)
in (

let body = if is_rec then begin
(FStar_Syntax_Subst.close rec_bindings body)
end else begin
body
end
in (mk_lb ((lbname), (FStar_Syntax_Syntax.tun), (body)))))))))
end))
in (

let lbs = (FStar_List.map2 (desugar_one_def (if is_rec then begin
env'
end else begin
env
end)) fnames funs)
in (

let body = (desugar_term env' body)
in (let _160_536 = (let _160_535 = (let _160_534 = (FStar_Syntax_Subst.close rec_bindings body)
in ((((is_rec), (lbs))), (_160_534)))
in FStar_Syntax_Syntax.Tm_let (_160_535))
in (FStar_All.pipe_left mk _160_536))))))
end))))
end))
in (

let ds_non_rec = (fun pat t1 t2 -> (

let t1 = (desugar_term env t1)
in (

let is_mutable = (qual = FStar_Parser_AST.Mutable)
in (

let t1 = if is_mutable then begin
(mk_ref_alloc t1)
end else begin
t1
end
in (

let _65_1412 = (desugar_binding_pat_maybe_top top_level env pat is_mutable)
in (match (_65_1412) with
| (env, binder, pat) -> begin
(

let tm = (match (binder) with
| LetBinder (l, t) -> begin
(

let body = (desugar_term env t2)
in (

let fv = (let _160_543 = (FStar_Syntax_Util.incr_delta_qualifier t1)
in (FStar_Syntax_Syntax.lid_as_fv l _160_543 None))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((((false), (({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]))), (body)))))))
end
| LocalBinder (x, _65_1421) -> begin
(

let body = (desugar_term env t2)
in (

let body = (match (pat) with
| (None) | (Some ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (_); FStar_Syntax_Syntax.ty = _; FStar_Syntax_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _160_548 = (let _160_547 = (let _160_546 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _160_545 = (let _160_544 = (FStar_Syntax_Util.branch ((pat), (None), (body)))
in (_160_544)::[])
in ((_160_546), (_160_545))))
in FStar_Syntax_Syntax.Tm_match (_160_547))
in (FStar_Syntax_Syntax.mk _160_548 None body.FStar_Syntax_Syntax.pos))
end)
in (let _160_553 = (let _160_552 = (let _160_551 = (let _160_550 = (let _160_549 = (FStar_Syntax_Syntax.mk_binder x)
in (_160_549)::[])
in (FStar_Syntax_Subst.close _160_550 body))
in ((((false), (((mk_lb ((FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t1))))::[]))), (_160_551)))
in FStar_Syntax_Syntax.Tm_let (_160_552))
in (FStar_All.pipe_left mk _160_553))))
end)
in if is_mutable then begin
(FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((tm), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc))))))
end else begin
tm
end)
end))))))
in if (is_rec || (is_app_pattern pat)) then begin
(ds_let_rec_or_app ())
end else begin
(ds_non_rec pat _snd body)
end)))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (let _160_564 = (let _160_563 = (let _160_562 = (desugar_term env t1)
in (let _160_561 = (let _160_560 = (let _160_555 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (let _160_554 = (desugar_term env t2)
in ((_160_555), (None), (_160_554))))
in (let _160_559 = (let _160_558 = (let _160_557 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (let _160_556 = (desugar_term env t3)
in ((_160_557), (None), (_160_556))))
in (_160_558)::[])
in (_160_560)::_160_559))
in ((_160_562), (_160_561))))
in FStar_Syntax_Syntax.Tm_match (_160_563))
in (mk _160_564)))
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(

let r = top.FStar_Parser_AST.range
in (

let handler = (FStar_Parser_AST.mk_function branches r r)
in (

let body = (FStar_Parser_AST.mk_function (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatConst (FStar_Const.Const_unit)) r)), (None), (e)))::[]) r r)
in (

let a1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (FStar_Syntax_Const.try_with_lid)) r top.FStar_Parser_AST.level)), (body), (FStar_Parser_AST.Nothing)))) r top.FStar_Parser_AST.level)
in (

let a2 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((a1), (handler), (FStar_Parser_AST.Nothing)))) r top.FStar_Parser_AST.level)
in (desugar_term env a2))))))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(

let desugar_branch = (fun _65_1462 -> (match (_65_1462) with
| (pat, wopt, b) -> begin
(

let _65_1465 = (desugar_match_pat env pat)
in (match (_65_1465) with
| (env, pat) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _160_567 = (desugar_term env e)
in Some (_160_567))
end)
in (

let b = (desugar_term env b)
in (FStar_Syntax_Util.branch ((pat), (wopt), (b)))))
end))
end))
in (let _160_571 = (let _160_570 = (let _160_569 = (desugar_term env e)
in (let _160_568 = (FStar_List.map desugar_branch branches)
in ((_160_569), (_160_568))))
in FStar_Syntax_Syntax.Tm_match (_160_570))
in (FStar_All.pipe_left mk _160_571)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(

let env = (FStar_Parser_Env.default_ml env)
in (

let c = (desugar_comp t.FStar_Parser_AST.range true env t)
in (

let annot = if (FStar_Syntax_Util.is_ml_comp c) then begin
FStar_Util.Inl ((FStar_Syntax_Util.comp_result c))
end else begin
FStar_Util.Inr (c)
end
in (let _160_574 = (let _160_573 = (let _160_572 = (desugar_term env e)
in ((_160_572), (annot), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (_160_573))
in (FStar_All.pipe_left mk _160_574)))))
end
| FStar_Parser_AST.Record (_65_1479, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let _65_1490 = (FStar_List.hd fields)
in (match (_65_1490) with
| (f, _65_1489) -> begin
(

let _65_1494 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_65_1494) with
| (record, _65_1493) -> begin
(

let fields' = (FStar_All.pipe_right fields (FStar_List.map (fun _65_1497 -> (match (_65_1497) with
| (f, e) -> begin
(let _160_576 = (FStar_Syntax_Util.mk_field_projector_name_from_ident record.FStar_Parser_Env.constrname f.FStar_Ident.ident)
in ((_160_576), (e)))
end))))
in (

let get_field = (fun xopt f -> (

let found = (FStar_All.pipe_right fields' (FStar_Util.find_opt (fun _65_1505 -> (match (_65_1505) with
| (g, _65_1504) -> begin
(FStar_Ident.lid_equals f g)
end))))
in (match (found) with
| Some (_65_1508, e) -> begin
((f), (e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _160_584 = (let _160_583 = (let _160_582 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in ((_160_582), (top.FStar_Parser_AST.range)))
in FStar_Syntax_Syntax.Error (_160_583))
in (Prims.raise _160_584))
end
| Some (x) -> begin
((f), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Project (((x), (f)))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end)))
in (

let recterm = (match (eopt) with
| None -> begin
(let _160_589 = (let _160_588 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _65_1520 -> (match (_65_1520) with
| (f, _65_1519) -> begin
(let _160_587 = (let _160_586 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _160_586))
in ((_160_587), (FStar_Parser_AST.Nothing)))
end))))
in ((record.FStar_Parser_Env.constrname), (_160_588)))
in FStar_Parser_AST.Construct (_160_589))
end
| Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (let _160_591 = (let _160_590 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_160_590))
in (FStar_Parser_AST.mk_term _160_591 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record = (let _160_594 = (let _160_593 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _65_1528 -> (match (_65_1528) with
| (f, _65_1527) -> begin
(get_field (Some (xterm)) f)
end))))
in ((None), (_160_593)))
in FStar_Parser_AST.Record (_160_594))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _65_1544; FStar_Syntax_Syntax.pos = _65_1542; FStar_Syntax_Syntax.vars = _65_1540}, args); FStar_Syntax_Syntax.tk = _65_1538; FStar_Syntax_Syntax.pos = _65_1536; FStar_Syntax_Syntax.vars = _65_1534}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(

let e = (let _160_601 = (let _160_600 = (let _160_599 = (let _160_598 = (let _160_597 = (let _160_596 = (let _160_595 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_Env.typename), (_160_595)))
in FStar_Syntax_Syntax.Record_ctor (_160_596))
in Some (_160_597))
in (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant _160_598))
in ((_160_599), (args)))
in FStar_Syntax_Syntax.Tm_app (_160_600))
in (FStar_All.pipe_left mk _160_601))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))))))
end
| _65_1558 -> begin
e
end))))))
end))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(

let _65_1565 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_projector_by_field_name env) f)
in (match (_65_1565) with
| (fieldname, is_rec) -> begin
(

let e = (desugar_term env e)
in (

let fn = fieldname
in (

let qual = if is_rec then begin
Some (FStar_Syntax_Syntax.Record_projector (fn))
end else begin
None
end
in (let _160_606 = (let _160_605 = (let _160_604 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range fieldname (FStar_Ident.range_of_lid f)) FStar_Syntax_Syntax.Delta_equational qual)
in (let _160_603 = (let _160_602 = (FStar_Syntax_Syntax.as_arg e)
in (_160_602)::[])
in ((_160_604), (_160_603))))
in FStar_Syntax_Syntax.Tm_app (_160_605))
in (FStar_All.pipe_left mk _160_606)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| _65_1576 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _65_1578 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Let (_65_1580, _65_1582, _65_1584) -> begin
(FStar_All.failwith "Not implemented yet")
end
| FStar_Parser_AST.QForall (_65_1588, _65_1590, _65_1592) -> begin
(FStar_All.failwith "Not implemented yet")
end
| FStar_Parser_AST.QExists (_65_1596, _65_1598, _65_1600) -> begin
(FStar_All.failwith "Not implemented yet")
end))))
and desugar_args : FStar_Parser_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun _65_1607 -> (match (_65_1607) with
| (a, imp) -> begin
(let _160_610 = (desugar_term env a)
in (arg_withimp_e imp _160_610))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r default_ok env t -> (

let fail = (fun msg -> (Prims.raise (FStar_Syntax_Syntax.Error (((msg), (r))))))
in (

let is_requires = (fun _65_1619 -> (match (_65_1619) with
| (t, _65_1618) -> begin
(match ((let _160_618 = (unparen t)
in _160_618.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Requires (_65_1621) -> begin
true
end
| _65_1624 -> begin
false
end)
end))
in (

let is_ensures = (fun _65_1629 -> (match (_65_1629) with
| (t, _65_1628) -> begin
(match ((let _160_621 = (unparen t)
in _160_621.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ensures (_65_1631) -> begin
true
end
| _65_1634 -> begin
false
end)
end))
in (

let is_app = (fun head _65_1640 -> (match (_65_1640) with
| (t, _65_1639) -> begin
(match ((let _160_626 = (unparen t)
in _160_626.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _65_1644; FStar_Parser_AST.level = _65_1642}, _65_1649, _65_1651) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| _65_1655 -> begin
false
end)
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t -> (

let _65_1661 = (head_and_args t)
in (match (_65_1661) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(

let unit_tm = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type)), (FStar_Parser_AST.Nothing))
in (

let nil_pat = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr)), (FStar_Parser_AST.Nothing))
in (

let req_true = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Requires ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.true_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Formula)), (None)))) t.FStar_Parser_AST.range FStar_Parser_AST.Type)), (FStar_Parser_AST.Nothing))
in (

let args = (match (args) with
| [] -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Not enough arguments to \'Lemma\'"), (t.FStar_Parser_AST.range)))))
end
| (ens)::[] -> begin
(unit_tm)::(req_true)::(ens)::(nil_pat)::[]
end
| (req)::(ens)::[] when ((is_requires req) && (is_ensures ens)) -> begin
(unit_tm)::(req)::(ens)::(nil_pat)::[]
end
| (ens)::(dec)::[] when ((is_ensures ens) && (is_decreases dec)) -> begin
(unit_tm)::(req_true)::(ens)::(nil_pat)::(dec)::[]
end
| (req)::(ens)::(dec)::[] when (((is_requires req) && (is_ensures ens)) && (is_app "decreases" dec)) -> begin
(unit_tm)::(req)::(ens)::(nil_pat)::(dec)::[]
end
| more -> begin
(unit_tm)::more
end)
in (

let head_and_attributes = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_name_and_attributes env) lemma)
in ((head_and_attributes), (args)))))))
end
| FStar_Parser_AST.Name (l) when (FStar_Parser_Env.is_effect_name env l) -> begin
(let _160_630 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_name_and_attributes env) l)
in ((_160_630), (args)))
end
| FStar_Parser_AST.Name (l) when ((let _160_631 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _160_631 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when ((let _160_632 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _160_632 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when ((((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) && default_ok) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)), ([]))), ((((t), (FStar_Parser_AST.Nothing)))::[]))
end
| _65_1692 when default_ok -> begin
(((((FStar_Ident.set_lid_range env.FStar_Parser_Env.default_result_effect head.FStar_Parser_AST.range)), ([]))), ((((t), (FStar_Parser_AST.Nothing)))::[]))
end
| _65_1694 -> begin
(let _160_634 = (let _160_633 = (FStar_Parser_AST.term_to_string t)
in (FStar_Util.format1 "%s is not an effect" _160_633))
in (fail _160_634))
end)
end)))
in (

let _65_1699 = (pre_process_comp_typ t)
in (match (_65_1699) with
| ((eff, cattributes), args) -> begin
(

let _65_1700 = if ((FStar_List.length args) = (Prims.parse_int "0")) then begin
(let _160_636 = (let _160_635 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" _160_635))
in (fail _160_636))
end else begin
()
end
in (

let _65_1704 = (let _160_638 = (FStar_List.hd args)
in (let _160_637 = (FStar_List.tl args)
in ((_160_638), (_160_637))))
in (match (_65_1704) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (Prims.fst result_arg))
in (

let rest = (desugar_args env rest)
in (

let _65_1729 = (FStar_All.pipe_right rest (FStar_List.partition (fun _65_1710 -> (match (_65_1710) with
| (t, _65_1709) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _65_1716; FStar_Syntax_Syntax.pos = _65_1714; FStar_Syntax_Syntax.vars = _65_1712}, (_65_1721)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| _65_1726 -> begin
false
end)
end))))
in (match (_65_1729) with
| (dec, rest) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _65_1733 -> (match (_65_1733) with
| (t, _65_1732) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_65_1735, ((arg, _65_1738))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| _65_1744 -> begin
(FStar_All.failwith "impos")
end)
end))))
in (

let no_additional_args = ((((FStar_List.length decreases_clause) = (Prims.parse_int "0")) && ((FStar_List.length rest) = (Prims.parse_int "0"))) && ((FStar_List.length cattributes) = (Prims.parse_int "0")))
in if (no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid)) then begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end else begin
if (no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid)) then begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end else begin
(

let flags = if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid) then begin
(FStar_Syntax_Syntax.LEMMA)::[]
end else begin
if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid) then begin
(FStar_Syntax_Syntax.TOTAL)::[]
end else begin
if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_ML_lid) then begin
(FStar_Syntax_Syntax.MLEFFECT)::[]
end else begin
if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid) then begin
(FStar_Syntax_Syntax.SOMETRIVIAL)::[]
end else begin
[]
end
end
end
end
in (

let flags = (FStar_List.append flags cattributes)
in (

let rest = if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid) then begin
(match (rest) with
| (req)::(ens)::((pat, aq))::[] -> begin
(

let pat = (match (pat.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
(

let nil = (FStar_Syntax_Syntax.mk_Tm_uinst pat ((FStar_Syntax_Syntax.U_succ (FStar_Syntax_Syntax.U_zero))::[]))
in (

let pattern = (let _160_641 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.mk_Tm_uinst _160_641 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app nil ((((pattern), (Some (FStar_Syntax_Syntax.imp_tag))))::[]) None pat.FStar_Syntax_Syntax.pos)))
end
| _65_1760 -> begin
pat
end)
in (let _160_645 = (let _160_644 = (let _160_643 = (let _160_642 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) None pat.FStar_Syntax_Syntax.pos)
in ((_160_642), (aq)))
in (_160_643)::[])
in (ens)::_160_644)
in (req)::_160_645))
end
| _65_1763 -> begin
rest
end)
end else begin
rest
end
in (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = []; FStar_Syntax_Syntax.effect_name = eff; FStar_Syntax_Syntax.result_typ = result_typ; FStar_Syntax_Syntax.effect_args = rest; FStar_Syntax_Syntax.flags = (FStar_List.append flags decreases_clause)}))))
end
end))
end))))
end)))
end)))))))))
and desugar_formula : env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env f -> (

let connective = (fun s -> (match (s) with
| "/\\" -> begin
Some (FStar_Syntax_Const.and_lid)
end
| "\\/" -> begin
Some (FStar_Syntax_Const.or_lid)
end
| "==>" -> begin
Some (FStar_Syntax_Const.imp_lid)
end
| "<==>" -> begin
Some (FStar_Syntax_Const.iff_lid)
end
| "~" -> begin
Some (FStar_Syntax_Const.not_lid)
end
| _65_1775 -> begin
None
end))
in (

let mk = (fun t -> (FStar_Syntax_Syntax.mk t None f.FStar_Parser_AST.range))
in (

let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let _65_1782 = t
in {FStar_Syntax_Syntax.n = _65_1782.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _65_1782.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _65_1782.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let _65_1789 = b
in {FStar_Parser_AST.b = _65_1789.FStar_Parser_AST.b; FStar_Parser_AST.brange = _65_1789.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _65_1789.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _160_680 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _160_680)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(

let _65_1803 = (FStar_Parser_Env.push_bv env a)
in (match (_65_1803) with
| (env, a) -> begin
(

let a = (

let _65_1804 = a
in {FStar_Syntax_Syntax.ppname = _65_1804.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_1804.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats = (desugar_pats env pats)
in (

let body = (desugar_formula env body)
in (

let body = (match (pats) with
| [] -> begin
body
end
| _65_1811 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta (((body), (FStar_Syntax_Syntax.Meta_pattern (pats))))))
end)
in (

let body = (let _160_683 = (let _160_682 = (let _160_681 = (FStar_Syntax_Syntax.mk_binder a)
in (_160_681)::[])
in (no_annot_abs _160_682 body))
in (FStar_All.pipe_left setpos _160_683))
in (let _160_688 = (let _160_687 = (let _160_686 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (let _160_685 = (let _160_684 = (FStar_Syntax_Syntax.as_arg body)
in (_160_684)::[])
in ((_160_686), (_160_685))))
in FStar_Syntax_Syntax.Tm_app (_160_687))
in (FStar_All.pipe_left mk _160_688)))))))
end))
end
| _65_1815 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body = (let _160_703 = (q ((rest), (pats), (body)))
in (let _160_702 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _160_703 _160_702 FStar_Parser_AST.Formula)))
in (let _160_704 = (q (((b)::[]), ([]), (body)))
in (FStar_Parser_AST.mk_term _160_704 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _65_1829 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _160_705 = (unparen f)
in _160_705.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(

let f = (desugar_formula env f)
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((l), (f.FStar_Syntax_Syntax.pos), (p)))))))))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _160_707 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _160_707)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _160_709 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _160_709)))
end
| FStar_Parser_AST.QForall ((b)::[], pats, body) -> begin
(desugar_quant FStar_Syntax_Const.forall_lid b pats body)
end
| FStar_Parser_AST.QExists ((b)::[], pats, body) -> begin
(desugar_quant FStar_Syntax_Const.exists_lid b pats body)
end
| FStar_Parser_AST.Paren (f) -> begin
(desugar_formula env f)
end
| _65_1887 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (

let _65_1911 = (FStar_List.fold_left (fun _65_1892 b -> (match (_65_1892) with
| (env, out) -> begin
(

let tk = (desugar_binder env (

let _65_1894 = b
in {FStar_Parser_AST.b = _65_1894.FStar_Parser_AST.b; FStar_Parser_AST.brange = _65_1894.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _65_1894.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(

let _65_1903 = (FStar_Parser_Env.push_bv env a)
in (match (_65_1903) with
| (env, a) -> begin
(

let a = (

let _65_1904 = a
in {FStar_Syntax_Syntax.ppname = _65_1904.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_1904.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in ((env), ((((a), ((trans_aqual b.FStar_Parser_AST.aqual))))::out)))
end))
end
| _65_1908 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (_65_1911) with
| (env, tpars) -> begin
((env), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(let _160_716 = (desugar_typ env t)
in ((Some (x)), (_160_716)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _160_717 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None x.FStar_Ident.idRange)
in ((Some (x)), (_160_717)))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _160_718 = (desugar_typ env t)
in ((None), (_160_718)))
end
| FStar_Parser_AST.Variable (x) -> begin
((Some (x)), (FStar_Syntax_Syntax.tun))
end))


let mk_data_discriminators : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  FStar_Ident.lid  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun quals env t tps k datas -> (

let quals = (FStar_All.pipe_right quals (FStar_List.filter (fun _65_11 -> (match (_65_11) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| _65_1936 -> begin
false
end))))
in (

let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_Env.iface) || env.FStar_Parser_Env.admitted_iface) then begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (

let binders = (let _160_735 = (let _160_734 = (FStar_Syntax_Util.arrow_formals k)
in (Prims.fst _160_734))
in (FStar_List.append tps _160_735))
in (

let p = (FStar_Ident.range_of_lid t)
in (

let _65_1944 = (FStar_Syntax_Util.args_of_binders binders)
in (match (_65_1944) with
| (binders, args) -> begin
(

let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _65_1948 -> (match (_65_1948) with
| (x, _65_1947) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let binders = (let _160_741 = (let _160_740 = (let _160_739 = (let _160_738 = (let _160_737 = (FStar_Syntax_Syntax.lid_as_fv t FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _160_737))
in (FStar_Syntax_Syntax.mk_Tm_app _160_738 args None p))
in (FStar_All.pipe_left FStar_Syntax_Syntax.null_binder _160_739))
in (_160_740)::[])
in (FStar_List.append imp_binders _160_741))
in (

let disc_type = (let _160_744 = (let _160_743 = (let _160_742 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _160_742))
in (FStar_Syntax_Syntax.mk_Total _160_743))
in (FStar_Syntax_Util.arrow binders _160_744))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (let _160_747 = (let _160_746 = (quals ((FStar_Syntax_Syntax.Logic)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in ((disc_name), ([]), (disc_type), (_160_746), ((FStar_Ident.range_of_lid disc_name))))
in FStar_Syntax_Syntax.Sig_declare_typ (_160_747)))))))))
end)))))))


let mk_indexed_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq refine_domain env tc lid inductive_tps imp_tps fields t -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p))
in (

let projectee = (fun ptyp -> (FStar_Syntax_Syntax.gen_bv "projectee" (Some (p)) ptyp))
in (

let tps = (FStar_List.map2 (fun _65_1972 _65_1976 -> (match (((_65_1972), (_65_1976))) with
| ((_65_1970, imp), (x, _65_1975)) -> begin
((x), (imp))
end)) inductive_tps imp_tps)
in (

let _65_2077 = (

let _65_1980 = (FStar_Syntax_Util.head_and_args t)
in (match (_65_1980) with
| (head, args0) -> begin
(

let args = (

let rec arguments = (fun tps args -> (match (((tps), (args))) with
| ([], _65_1986) -> begin
args
end
| (_65_1989, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Not enough arguments to type"), ((FStar_Ident.range_of_lid lid))))))
end
| (((_65_1994, Some (FStar_Syntax_Syntax.Implicit (_65_1996))))::tps', ((_65_2003, Some (FStar_Syntax_Syntax.Implicit (_65_2005))))::args') -> begin
(arguments tps' args')
end
| (((_65_2013, Some (FStar_Syntax_Syntax.Implicit (_65_2015))))::tps', ((_65_2023, _65_2025))::_65_2021) -> begin
(arguments tps' args)
end
| (((_65_2032, _65_2034))::_65_2030, ((a, Some (FStar_Syntax_Syntax.Implicit (_65_2041))))::_65_2038) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected implicit annotation on argument"), (a.FStar_Syntax_Syntax.pos)))))
end
| (((_65_2049, _65_2051))::tps', ((_65_2056, _65_2058))::args') -> begin
(arguments tps' args')
end))
in (arguments inductive_tps args0))
in (

let indices = (FStar_All.pipe_right args (FStar_List.map (fun _65_2063 -> (let _160_779 = (FStar_Syntax_Syntax.new_bv (Some (p)) FStar_Syntax_Syntax.tun)
in (FStar_All.pipe_right _160_779 FStar_Syntax_Syntax.mk_binder)))))
in (

let arg_typ = (let _160_784 = (let _160_780 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _160_780))
in (let _160_783 = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _65_2068 -> (match (_65_2068) with
| (x, imp) -> begin
(let _160_782 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_160_782), (imp)))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app _160_784 _160_783 None p)))
in (

let arg_binder = if (not (refine_domain)) then begin
(let _160_785 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder _160_785))
end else begin
(

let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p)) arg_typ)
in (let _160_793 = (

let _65_2072 = (projectee arg_typ)
in (let _160_792 = (let _160_791 = (let _160_790 = (let _160_789 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range disc_name p) FStar_Syntax_Syntax.Delta_equational None)
in (let _160_788 = (let _160_787 = (let _160_786 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _160_786))
in (_160_787)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _160_789 _160_788 None p)))
in (FStar_Syntax_Util.b2t _160_790))
in (FStar_Syntax_Util.refine x _160_791))
in {FStar_Syntax_Syntax.ppname = _65_2072.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_2072.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _160_792}))
in (FStar_Syntax_Syntax.mk_binder _160_793))))
end
in ((arg_binder), (indices))))))
end))
in (match (_65_2077) with
| (arg_binder, indices) -> begin
(

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder))
in (

let imp_binders = (let _160_795 = (FStar_All.pipe_right indices (FStar_List.map (fun _65_2082 -> (match (_65_2082) with
| (x, _65_2081) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (FStar_List.append imp_tps _160_795))
in (

let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (

let arg = (FStar_Syntax_Util.arg_of_non_null_binder arg_binder)
in (

let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _65_2090 -> (match (_65_2090) with
| (a, _65_2089) -> begin
(

let _65_2094 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (_65_2094) with
| (field_name, _65_2093) -> begin
(

let proj = (let _160_799 = (let _160_798 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.fv_to_tm _160_798))
in (FStar_Syntax_Syntax.mk_Tm_app _160_799 ((arg)::[]) None p))
in FStar_Syntax_Syntax.NT (((a), (proj))))
end))
end))))
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (FStar_List.append imp_tps fields)
in (let _160_838 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _65_2103 -> (match (_65_2103) with
| (x, _65_2102) -> begin
(

let _65_2107 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_65_2107) with
| (field_name, _65_2106) -> begin
(

let t = (let _160_803 = (let _160_802 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total _160_802))
in (FStar_Syntax_Util.arrow binders _160_803))
in (

let only_decl = (((let _160_804 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _160_804)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _160_806 = (let _160_805 = (FStar_Parser_Env.current_module env)
in _160_805.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _160_806)))
in (

let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (

let quals = (fun q -> if only_decl then begin
(let _160_810 = (FStar_List.filter (fun _65_12 -> (match (_65_12) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| _65_2116 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::_160_810)
end else begin
q
end)
in (

let quals = (

let iquals = (FStar_All.pipe_right iquals (FStar_List.filter (fun _65_13 -> (match (_65_13) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| _65_2121 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals)))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), ([]), (t), (quals), ((FStar_Ident.range_of_lid field_name))))
in if only_decl then begin
(decl)::[]
end else begin
(

let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _65_2129 -> (match (_65_2129) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in if ((i + ntps) = j) then begin
(let _160_814 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in ((_160_814), (b)))
end else begin
if (b && (j < ntps)) then begin
(let _160_818 = (let _160_817 = (let _160_816 = (let _160_815 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in ((_160_815), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (_160_816))
in (pos _160_817))
in ((_160_818), (b)))
end else begin
(let _160_821 = (let _160_820 = (let _160_819 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_160_819))
in (pos _160_820))
in ((_160_821), (b)))
end
end)
end))))
in (

let pat = (let _160_826 = (let _160_824 = (let _160_823 = (let _160_822 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in ((_160_822), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (_160_823))
in (FStar_All.pipe_right _160_824 pos))
in (let _160_825 = (FStar_Syntax_Syntax.bv_to_name projection)
in ((_160_826), (None), (_160_825))))
in (

let body = (let _160_830 = (let _160_829 = (let _160_828 = (let _160_827 = (FStar_Syntax_Util.branch pat)
in (_160_827)::[])
in ((arg_exp), (_160_828)))
in FStar_Syntax_Syntax.Tm_match (_160_829))
in (FStar_Syntax_Syntax.mk _160_830 None p))
in (

let imp = (no_annot_abs binders body)
in (

let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end else begin
FStar_Syntax_Syntax.Delta_equational
end
in (

let lb = (let _160_832 = (let _160_831 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (_160_831))
in {FStar_Syntax_Syntax.lbname = _160_832; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = imp})
in (

let impl = (let _160_837 = (let _160_836 = (let _160_835 = (let _160_834 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _160_834 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_160_835)::[])
in ((((false), ((lb)::[]))), (p), (_160_836), (quals)))
in FStar_Syntax_Syntax.Sig_let (_160_837))
in if no_decl then begin
(impl)::[]
end else begin
(decl)::(impl)::[]
end))))))))
end))))))
end))
end))))
in (FStar_All.pipe_right _160_838 FStar_List.flatten)))))))))
end)))))))


let mk_data_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env _65_2143 -> (match (_65_2143) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _65_2146, t, l, n, quals, _65_2152, _65_2154) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _65_14 -> (match (_65_14) with
| FStar_Syntax_Syntax.RecordConstructor (_65_2159) -> begin
true
end
| _65_2162 -> begin
false
end)))) then begin
false
end else begin
(match ((FStar_Parser_Env.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > (Prims.parse_int "1"))
end
| _65_2166 -> begin
true
end)
end
in (

let _65_2170 = (FStar_Syntax_Util.arrow_formals t)
in (match (_65_2170) with
| (formals, cod) -> begin
(match (formals) with
| [] -> begin
[]
end
| _65_2173 -> begin
(

let fv_qual = (match ((FStar_Util.find_map quals (fun _65_15 -> (match (_65_15) with
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| _65_2178 -> begin
None
end)))) with
| None -> begin
FStar_Syntax_Syntax.Data_ctor
end
| Some (q) -> begin
q
end)
in (

let iquals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract iquals) then begin
(FStar_Syntax_Syntax.Private)::iquals
end else begin
iquals
end
in (

let _65_2186 = (FStar_Util.first_N n formals)
in (match (_65_2186) with
| (tps, rest) -> begin
(mk_indexed_projectors iquals fv_qual refine_domain env l lid inductive_tps tps rest cod)
end))))
end)
end)))
end
| _65_2188 -> begin
[]
end)
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (

let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _160_863 = (FStar_Syntax_Util.incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (_160_863))
end else begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end
in (

let lb = (let _160_868 = (let _160_864 = (FStar_Syntax_Syntax.lid_as_fv lid dd None)
in FStar_Util.Inr (_160_864))
in (let _160_867 = (let _160_865 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars _160_865))
in (let _160_866 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = _160_868; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = _160_867; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _160_866})))
in FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (rng), (lids), (quals))))))


let rec desugar_tycon : FStar_Parser_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (

let tycon_id = (fun _65_16 -> (match (_65_16) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _160_882 = (let _160_881 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_160_881))
in (FStar_Parser_AST.mk_term _160_882 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| (FStar_Parser_AST.TAnnotated (a, _)) | (FStar_Parser_AST.TVariable (a)) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar (a)) a.FStar_Ident.idRange FStar_Parser_AST.Type)
end
| FStar_Parser_AST.NoName (t) -> begin
t
end))
in (

let tot = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) rng FStar_Parser_AST.Expr)
in (

let with_constructor_effect = (fun t -> (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((tot), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level))
in (

let apply_binders = (fun t binders -> (

let imp_of_aqual = (fun b -> (match (b.FStar_Parser_AST.aqual) with
| Some (FStar_Parser_AST.Implicit) -> begin
FStar_Parser_AST.Hash
end
| _65_2263 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _160_895 = (let _160_894 = (let _160_893 = (binder_to_term b)
in ((out), (_160_893), ((imp_of_aqual b))))
in FStar_Parser_AST.App (_160_894))
in (FStar_Parser_AST.mk_term _160_895 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun _65_17 -> (match (_65_17) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun _65_2278 -> (match (_65_2278) with
| (x, t, _65_2277) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Syntax_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (

let result = (let _160_901 = (let _160_900 = (let _160_899 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_160_899))
in (FStar_Parser_AST.mk_term _160_900 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _160_901 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _160_903 = (FStar_All.pipe_right fields (FStar_List.map (fun _65_2287 -> (match (_65_2287) with
| (x, _65_2284, _65_2286) -> begin
(FStar_Parser_Env.qualify env x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (Some (constrTyp)), (None), (false)))::[])))), (_160_903)))))))
end
| _65_2289 -> begin
(FStar_All.failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals _env mutuals _65_18 -> (match (_65_18) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let _65_2303 = (typars_of_binders _env binders)
in (match (_65_2303) with
| (_env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
FStar_Syntax_Util.ktype
end
| Some (k) -> begin
(desugar_term _env' k)
end)
in (

let tconstr = (let _160_914 = (let _160_913 = (let _160_912 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_160_912))
in (FStar_Parser_AST.mk_term _160_913 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _160_914 binders))
in (

let qlid = (FStar_Parser_Env.qualify _env id)
in (

let typars = (FStar_Syntax_Subst.close_binders typars)
in (

let k = (FStar_Syntax_Subst.close typars k)
in (

let se = FStar_Syntax_Syntax.Sig_inductive_typ (((qlid), ([]), (typars), (k), (mutuals), ([]), (quals), (rng)))
in (

let _env = (FStar_Parser_Env.push_top_level_rec_binding _env id FStar_Syntax_Syntax.Delta_constant)
in (

let _env2 = (FStar_Parser_Env.push_top_level_rec_binding _env' id FStar_Syntax_Syntax.Delta_constant)
in ((_env), (_env2), (se), (tconstr))))))))))
end))
end
| _65_2316 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env bs -> (

let _65_2331 = (FStar_List.fold_left (fun _65_2322 _65_2325 -> (match (((_65_2322), (_65_2325))) with
| ((env, tps), (x, imp)) -> begin
(

let _65_2328 = (FStar_Parser_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (_65_2328) with
| (env, y) -> begin
((env), ((((y), (imp)))::tps))
end))
end)) ((env), ([])) bs)
in (match (_65_2331) with
| (env, bs) -> begin
((env), ((FStar_List.rev bs)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id, bs, kopt))::[] -> begin
(

let kopt = (match (kopt) with
| None -> begin
(let _160_921 = (tm_type_z id.FStar_Ident.idRange)
in Some (_160_921))
end
| _65_2340 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id), (bs), (kopt)))
in (

let _65_2350 = (desugar_abstract_tc quals env [] tc)
in (match (_65_2350) with
| (_65_2344, _65_2346, se, _65_2349) -> begin
(

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _65_2353, typars, k, [], [], quals, rng) -> begin
(

let quals = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
quals
end else begin
(

let _65_2362 = (let _160_923 = (FStar_Range.string_of_range rng)
in (let _160_922 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" _160_923 _160_922)))
in (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals)
end
in (

let t = (match (typars) with
| [] -> begin
k
end
| _65_2367 -> begin
(let _160_926 = (let _160_925 = (let _160_924 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (_160_924)))
in FStar_Syntax_Syntax.Tm_arrow (_160_925))
in (FStar_Syntax_Syntax.mk _160_926 None rng))
end)
in FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t), (quals), (rng)))))
end
| _65_2370 -> begin
se
end)
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in ((env), ((se)::[]))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let _65_2382 = (typars_of_binders env binders)
in (match (_65_2382) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _65_19 -> (match (_65_19) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| _65_2387 -> begin
false
end)) quals) then begin
FStar_Syntax_Syntax.teff
end else begin
FStar_Syntax_Syntax.tun
end
end
| Some (k) -> begin
(desugar_term env' k)
end)
in (

let t0 = t
in (

let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _65_20 -> (match (_65_20) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| _65_2395 -> begin
false
end)))) then begin
quals
end else begin
if (t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula) then begin
(FStar_Syntax_Syntax.Logic)::quals
end else begin
quals
end
end
in (

let se = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Effect)) then begin
(

let _65_2420 = (match ((let _160_929 = (unparen t)
in _160_929.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Construct (head, args) -> begin
(

let _65_2415 = (match ((FStar_List.rev args)) with
| ((last_arg, _65_2404))::args_rev -> begin
(match ((let _160_930 = (unparen last_arg)
in _160_930.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| _65_2410 -> begin
(([]), (args))
end)
end
| _65_2412 -> begin
(([]), (args))
end)
in (match (_65_2415) with
| (cattributes, args) -> begin
(let _160_931 = (desugar_attributes env cattributes)
in (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((head), (args)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (_160_931)))
end))
end
| _65_2417 -> begin
((t), ([]))
end)
in (match (_65_2420) with
| (t, cattributes) -> begin
(

let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (

let typars = (FStar_Syntax_Subst.close_binders typars)
in (

let c = (FStar_Syntax_Subst.close_comp typars c)
in (let _160_935 = (let _160_934 = (FStar_Parser_Env.qualify env id)
in (let _160_933 = (FStar_All.pipe_right quals (FStar_List.filter (fun _65_21 -> (match (_65_21) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| _65_2427 -> begin
true
end))))
in ((_160_934), ([]), (typars), (c), (_160_933), ((FStar_List.append cattributes (FStar_Syntax_Util.comp_flags c))), (rng))))
in FStar_Syntax_Syntax.Sig_effect_abbrev (_160_935)))))
end))
end else begin
(

let t = (desugar_typ env' t)
in (

let nm = (FStar_Parser_Env.qualify env id)
in (mk_typ_abbrev nm [] typars k t ((nm)::[]) quals rng)))
end
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in ((env), ((se)::[])))))))
end))
end
| (FStar_Parser_AST.TyconRecord (_65_2433))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let _65_2439 = (tycon_record_as_variant trec)
in (match (_65_2439) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| (_65_2443)::_65_2441 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_Env.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals et tc -> (

let _65_2454 = et
in (match (_65_2454) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_65_2456) -> begin
(

let trec = tc
in (

let _65_2461 = (tycon_record_as_variant trec)
in (match (_65_2461) with
| (t, fs) -> begin
(collect_tcs ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((env), (tcs)) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let _65_2473 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_65_2473) with
| (env, _65_2470, se, tconstr) -> begin
((env), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals))))::tcs))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let _65_2485 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_65_2485) with
| (env, _65_2482, se, tconstr) -> begin
((env), ((FStar_Util.Inr (((se), (t), (quals))))::tcs))
end))
end
| _65_2487 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (

let _65_2490 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (_65_2490) with
| (env, tcs) -> begin
(

let tcs = (FStar_List.rev tcs)
in (

let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _65_23 -> (match (_65_23) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, _65_2498, _65_2500, _65_2502, _65_2504), t, quals) -> begin
(

let _65_2514 = (push_tparams env tpars)
in (match (_65_2514) with
| (env_tps, _65_2513) -> begin
(

let t = (desugar_term env_tps t)
in (let _160_945 = (let _160_944 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in (([]), (_160_944)))
in (_160_945)::[]))
end))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, _65_2522, tags, _65_2525), constrs, tconstr, quals) -> begin
(

let tycon = ((tname), (tpars), (k))
in (

let _65_2536 = (push_tparams env tpars)
in (match (_65_2536) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun _65_2540 -> (match (_65_2540) with
| (x, _65_2539) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let _65_2566 = (let _160_957 = (FStar_All.pipe_right constrs (FStar_List.map (fun _65_2547 -> (match (_65_2547) with
| (id, topt, _65_2545, of_notation) -> begin
(

let t = if of_notation then begin
(match (topt) with
| Some (t) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level None))::[]), (tconstr)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end
| None -> begin
tconstr
end)
end else begin
(match (topt) with
| None -> begin
(FStar_All.failwith "Impossible")
end
| Some (t) -> begin
t
end)
end
in (

let t = (let _160_949 = (FStar_Parser_Env.default_total env_tps)
in (let _160_948 = (close env_tps t)
in (desugar_term _160_949 _160_948)))
in (

let name = (FStar_Parser_Env.qualify env id)
in (

let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _65_22 -> (match (_65_22) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| _65_2561 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (let _160_956 = (let _160_955 = (let _160_954 = (let _160_953 = (let _160_952 = (let _160_951 = (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total _160_951))
in (FStar_Syntax_Util.arrow data_tpars _160_952))
in ((name), (univs), (_160_953), (tname), (ntps), (quals), (mutuals), (rng)))
in FStar_Syntax_Syntax.Sig_datacon (_160_954))
in ((tps), (_160_955)))
in ((name), (_160_956))))))))
end))))
in (FStar_All.pipe_left FStar_List.split _160_957))
in (match (_65_2566) with
| (constrNames, constrs) -> begin
((([]), (FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs), (tpars), (k), (mutuals), (constrNames), (tags), (rng))))))::constrs
end)))
end)))
end
| _65_2568 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (

let bundle = (let _160_959 = (let _160_958 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in ((sigelts), (quals), (_160_958), (rng)))
in FStar_Syntax_Syntax.Sig_bundle (_160_959))
in (

let env = (FStar_Parser_Env.push_sigelt env0 bundle)
in (

let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projectors quals env)))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _65_24 -> (match (_65_24) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, _65_2577, tps, k, _65_2581, constrs, quals, _65_2585) when ((FStar_List.length constrs) > (Prims.parse_int "1")) -> begin
(

let quals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract quals) then begin
(FStar_Syntax_Syntax.Private)::quals
end else begin
quals
end
in (mk_data_discriminators quals env tname tps k constrs))
end
| _65_2590 -> begin
[]
end))))
in (

let ops = (FStar_List.append discs data_ops)
in (

let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env ops)
in ((env), ((FStar_List.append ((bundle)::[]) ops))))))))))))
end)))))
end
| [] -> begin
(FStar_All.failwith "impossible")
end))))))))))


let desugar_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.binder Prims.list) = (fun env binders -> (

let _65_2614 = (FStar_List.fold_left (fun _65_2599 b -> (match (_65_2599) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| (Some (a), k) -> begin
(

let _65_2607 = (FStar_Parser_Env.push_bv env a)
in (match (_65_2607) with
| (env, a) -> begin
(let _160_968 = (let _160_967 = (FStar_Syntax_Syntax.mk_binder (

let _65_2608 = a
in {FStar_Syntax_Syntax.ppname = _65_2608.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_2608.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (_160_967)::binders)
in ((env), (_160_968)))
end))
end
| _65_2611 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end)
end)) ((env), ([])) binders)
in (match (_65_2614) with
| (env, binders) -> begin
((env), ((FStar_List.rev binders)))
end)))


let rec desugar_effect : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  Prims.bool  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_kind eff_decls actions for_free -> (

let env0 = env
in (

let monad_env = (FStar_Parser_Env.enter_monad_scope env eff_name)
in (

let _65_2628 = (desugar_binders monad_env eff_binders)
in (match (_65_2628) with
| (env, binders) -> begin
(

let eff_k = (let _160_1006 = (FStar_Parser_Env.default_total env)
in (desugar_term _160_1006 eff_kind))
in (

let _65_2639 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _65_2632 decl -> (match (_65_2632) with
| (env, out) -> begin
(

let _65_2636 = (desugar_decl env decl)
in (match (_65_2636) with
| (env, ses) -> begin
(let _160_1010 = (let _160_1009 = (FStar_List.hd ses)
in (_160_1009)::out)
in ((env), (_160_1010)))
end))
end)) ((env), ([]))))
in (match (_65_2639) with
| (env, decls) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let actions = (FStar_All.pipe_right actions (FStar_List.map (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (_65_2643, ((FStar_Parser_AST.TyconAbbrev (name, _65_2646, _65_2648, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (_65_2654, ((def, _65_2661))::((cps_type, _65_2657))::[]); FStar_Parser_AST.range = _65_2652; FStar_Parser_AST.level = _65_2650}), _65_2670))::[]) when (not (for_free)) -> begin
(let _160_1016 = (FStar_Parser_Env.qualify env name)
in (let _160_1015 = (let _160_1012 = (desugar_term env def)
in (FStar_Syntax_Subst.close binders _160_1012))
in (let _160_1014 = (let _160_1013 = (desugar_typ env cps_type)
in (FStar_Syntax_Subst.close binders _160_1013))
in {FStar_Syntax_Syntax.action_name = _160_1016; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = _160_1015; FStar_Syntax_Syntax.action_typ = _160_1014})))
end
| FStar_Parser_AST.Tycon (_65_2676, ((FStar_Parser_AST.TyconAbbrev (name, _65_2679, _65_2681, defn), _65_2686))::[]) when for_free -> begin
(let _160_1019 = (FStar_Parser_Env.qualify env name)
in (let _160_1018 = (let _160_1017 = (desugar_term env defn)
in (FStar_Syntax_Subst.close binders _160_1017))
in {FStar_Syntax_Syntax.action_name = _160_1019; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = _160_1018; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
end
| _65_2692 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples)."), (d.FStar_Parser_AST.drange)))))
end))))
in (

let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (

let lookup = (fun s -> (

let l = (FStar_Parser_Env.qualify env (FStar_Ident.mk_ident ((s), (d.FStar_Parser_AST.drange))))
in (let _160_1023 = (let _160_1022 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) _160_1022))
in (([]), (_160_1023)))))
in (

let mname = (FStar_Parser_Env.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange (Some (mname))) quals)
in (

let se = if for_free then begin
(

let dummy_tscheme = (let _160_1024 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (([]), (_160_1024)))
in (let _160_1030 = (let _160_1029 = (let _160_1028 = (let _160_1025 = (lookup "repr")
in (Prims.snd _160_1025))
in (let _160_1027 = (lookup "return")
in (let _160_1026 = (lookup "bind")
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = _160_1028; FStar_Syntax_Syntax.return_repr = _160_1027; FStar_Syntax_Syntax.bind_repr = _160_1026; FStar_Syntax_Syntax.actions = actions})))
in ((_160_1029), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (_160_1030)))
end else begin
(

let rr = ((FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) || (FStar_All.pipe_right qualifiers FStar_Syntax_Syntax.contains_reflectable))
in (

let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in (let _160_1046 = (let _160_1045 = (let _160_1044 = (lookup "return_wp")
in (let _160_1043 = (lookup "bind_wp")
in (let _160_1042 = (lookup "if_then_else")
in (let _160_1041 = (lookup "ite_wp")
in (let _160_1040 = (lookup "stronger")
in (let _160_1039 = (lookup "close_wp")
in (let _160_1038 = (lookup "assert_p")
in (let _160_1037 = (lookup "assume_p")
in (let _160_1036 = (lookup "null_wp")
in (let _160_1035 = (lookup "trivial")
in (let _160_1034 = if rr then begin
(let _160_1031 = (lookup "repr")
in (FStar_All.pipe_left Prims.snd _160_1031))
end else begin
FStar_Syntax_Syntax.tun
end
in (let _160_1033 = if rr then begin
(lookup "return")
end else begin
un_ts
end
in (let _160_1032 = if rr then begin
(lookup "bind")
end else begin
un_ts
end
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = _160_1044; FStar_Syntax_Syntax.bind_wp = _160_1043; FStar_Syntax_Syntax.if_then_else = _160_1042; FStar_Syntax_Syntax.ite_wp = _160_1041; FStar_Syntax_Syntax.stronger = _160_1040; FStar_Syntax_Syntax.close_wp = _160_1039; FStar_Syntax_Syntax.assert_p = _160_1038; FStar_Syntax_Syntax.assume_p = _160_1037; FStar_Syntax_Syntax.null_wp = _160_1036; FStar_Syntax_Syntax.trivial = _160_1035; FStar_Syntax_Syntax.repr = _160_1034; FStar_Syntax_Syntax.return_repr = _160_1033; FStar_Syntax_Syntax.bind_repr = _160_1032; FStar_Syntax_Syntax.actions = actions})))))))))))))
in ((_160_1045), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_new_effect (_160_1046))))
end
in (

let env = (FStar_Parser_Env.push_sigelt env0 se)
in (

let env = (FStar_All.pipe_right actions (FStar_List.fold_left (fun env a -> (let _160_1049 = (FStar_Syntax_Util.action_as_lb a)
in (FStar_Parser_Env.push_sigelt env _160_1049))) env))
in (

let env = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable)) then begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_Parser_Env.qualify monad_env))
in (

let refl_decl = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]), (d.FStar_Parser_AST.drange)))
in (FStar_Parser_Env.push_sigelt env refl_decl)))
end else begin
env
end
in ((env), ((se)::[]))))))))))))
end)))
end)))))
and desugar_redefine_effect : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl  ->  (FStar_Ident.lident Prims.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier)  ->  FStar_Parser_AST.qualifier Prims.list  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.eff_decl  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt)  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d trans_qual quals eff_name eff_binders defn build_sigelt -> (

let env0 = env
in (

let env = (FStar_Parser_Env.enter_monad_scope env eff_name)
in (

let _65_2723 = (desugar_binders env eff_binders)
in (match (_65_2723) with
| (env, binders) -> begin
(

let _65_2750 = (

let _65_2726 = (head_and_args defn)
in (match (_65_2726) with
| (head, args) -> begin
(

let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_defn env) l)
end
| _65_2730 -> begin
(let _160_1076 = (let _160_1075 = (let _160_1074 = (let _160_1073 = (let _160_1072 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat _160_1072 " not found"))
in (Prims.strcat "Effect " _160_1073))
in ((_160_1074), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_160_1075))
in (Prims.raise _160_1076))
end)
in (

let _65_2746 = (match ((FStar_List.rev args)) with
| ((last_arg, _65_2735))::args_rev -> begin
(match ((let _160_1077 = (unparen last_arg)
in _160_1077.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| _65_2741 -> begin
(([]), (args))
end)
end
| _65_2743 -> begin
(([]), (args))
end)
in (match (_65_2746) with
| (cattributes, args) -> begin
(let _160_1079 = (desugar_args env args)
in (let _160_1078 = (desugar_attributes env cattributes)
in ((ed), (_160_1079), (_160_1078))))
end)))
end))
in (match (_65_2750) with
| (ed, args, cattributes) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let sub = (fun _65_2756 -> (match (_65_2756) with
| (_65_2754, x) -> begin
(

let _65_2759 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (_65_2759) with
| (edb, x) -> begin
(

let _65_2760 = if ((FStar_List.length args) <> (FStar_List.length edb)) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected number of arguments to effect constructor"), (defn.FStar_Parser_AST.range)))))
end else begin
()
end
in (

let s = (FStar_Syntax_Util.subst_of_list edb args)
in (let _160_1083 = (let _160_1082 = (FStar_Syntax_Subst.subst s x)
in (FStar_Syntax_Subst.close binders _160_1082))
in (([]), (_160_1083)))))
end))
end))
in (

let mname = (FStar_Parser_Env.qualify env0 eff_name)
in (

let ed = (let _160_1108 = (let _160_1084 = (trans_qual (Some (mname)))
in (FStar_List.map _160_1084 quals))
in (let _160_1107 = (let _160_1085 = (sub (([]), (ed.FStar_Syntax_Syntax.signature)))
in (Prims.snd _160_1085))
in (let _160_1106 = (sub ed.FStar_Syntax_Syntax.ret_wp)
in (let _160_1105 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (let _160_1104 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (let _160_1103 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (let _160_1102 = (sub ed.FStar_Syntax_Syntax.stronger)
in (let _160_1101 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (let _160_1100 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (let _160_1099 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (let _160_1098 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (let _160_1097 = (sub ed.FStar_Syntax_Syntax.trivial)
in (let _160_1096 = (let _160_1086 = (sub (([]), (ed.FStar_Syntax_Syntax.repr)))
in (Prims.snd _160_1086))
in (let _160_1095 = (sub ed.FStar_Syntax_Syntax.return_repr)
in (let _160_1094 = (sub ed.FStar_Syntax_Syntax.bind_repr)
in (let _160_1093 = (FStar_List.map (fun action -> (let _160_1092 = (FStar_Parser_Env.qualify env action.FStar_Syntax_Syntax.action_unqualified_name)
in (let _160_1091 = (let _160_1088 = (sub (([]), (action.FStar_Syntax_Syntax.action_defn)))
in (Prims.snd _160_1088))
in (let _160_1090 = (let _160_1089 = (sub (([]), (action.FStar_Syntax_Syntax.action_typ)))
in (Prims.snd _160_1089))
in {FStar_Syntax_Syntax.action_name = _160_1092; FStar_Syntax_Syntax.action_unqualified_name = action.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _160_1091; FStar_Syntax_Syntax.action_typ = _160_1090})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = _160_1108; FStar_Syntax_Syntax.cattributes = cattributes; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = _160_1107; FStar_Syntax_Syntax.ret_wp = _160_1106; FStar_Syntax_Syntax.bind_wp = _160_1105; FStar_Syntax_Syntax.if_then_else = _160_1104; FStar_Syntax_Syntax.ite_wp = _160_1103; FStar_Syntax_Syntax.stronger = _160_1102; FStar_Syntax_Syntax.close_wp = _160_1101; FStar_Syntax_Syntax.assert_p = _160_1100; FStar_Syntax_Syntax.assume_p = _160_1099; FStar_Syntax_Syntax.null_wp = _160_1098; FStar_Syntax_Syntax.trivial = _160_1097; FStar_Syntax_Syntax.repr = _160_1096; FStar_Syntax_Syntax.return_repr = _160_1095; FStar_Syntax_Syntax.bind_repr = _160_1094; FStar_Syntax_Syntax.actions = _160_1093}))))))))))))))))
in (

let se = (build_sigelt ed d.FStar_Parser_AST.drange)
in (

let monad_env = env
in (

let env = (FStar_Parser_Env.push_sigelt env0 se)
in (

let env = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun env a -> (let _160_1111 = (FStar_Syntax_Util.action_as_lb a)
in (FStar_Parser_Env.push_sigelt env _160_1111))) env))
in (

let env = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable)) then begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_Parser_Env.qualify monad_env))
in (

let refl_decl = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable (mname))::[]), (d.FStar_Parser_AST.drange)))
in (FStar_Parser_Env.push_sigelt env refl_decl)))
end else begin
env
end
in ((env), ((se)::[])))))))))))
end))
end)))))
and desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (

let trans_qual = (trans_qual d.FStar_Parser_AST.drange)
in (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(

let se = FStar_Syntax_Syntax.Sig_pragma ((((trans_pragma p)), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[])))
end
| FStar_Parser_AST.Fsdoc (_65_2782) -> begin
((env), ([]))
end
| FStar_Parser_AST.TopLevelModule (id) -> begin
((env), ([]))
end
| FStar_Parser_AST.Open (lid) -> begin
(

let env = (FStar_Parser_Env.push_namespace env lid)
in ((env), ([])))
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(let _160_1116 = (FStar_Parser_Env.push_module_abbrev env x l)
in ((_160_1116), ([])))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(

let tcs = (FStar_List.map (fun _65_2800 -> (match (_65_2800) with
| (x, _65_2799) -> begin
x
end)) tcs)
in (let _160_1118 = (FStar_List.map (trans_qual None) qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _160_1118 tcs)))
end
| FStar_Parser_AST.TopLevelLet (quals, isrec, lets) -> begin
(match ((let _160_1120 = (let _160_1119 = (desugar_term_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Syntax_Subst.compress _160_1119))
in _160_1120.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let (lbs, _65_2809) -> begin
(

let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals = (match (quals) with
| (_65_2817)::_65_2815 -> begin
(FStar_List.map (trans_qual None) quals)
end
| _65_2820 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _65_25 -> (match (_65_25) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (_65_2831); FStar_Syntax_Syntax.lbunivs = _65_2829; FStar_Syntax_Syntax.lbtyp = _65_2827; FStar_Syntax_Syntax.lbeff = _65_2825; FStar_Syntax_Syntax.lbdef = _65_2823} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _65_2841; FStar_Syntax_Syntax.lbtyp = _65_2839; FStar_Syntax_Syntax.lbeff = _65_2837; FStar_Syntax_Syntax.lbdef = _65_2835} -> begin
(FStar_Parser_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals = if (FStar_All.pipe_right lets (FStar_Util.for_some (fun _65_2849 -> (match (_65_2849) with
| (_65_2847, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end)))) then begin
(FStar_Syntax_Syntax.Logic)::quals
end else begin
quals
end
in (

let lbs = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _160_1125 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _65_2853 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let _65_2855 = fv
in {FStar_Syntax_Syntax.fv_name = _65_2855.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = _65_2855.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = _65_2853.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _65_2853.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _65_2853.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _65_2853.FStar_Syntax_Syntax.lbdef})))))
in (((Prims.fst lbs)), (_160_1125)))
end else begin
lbs
end
in (

let s = (let _160_1128 = (let _160_1127 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in ((lbs), (d.FStar_Parser_AST.drange), (_160_1127), (quals)))
in FStar_Syntax_Syntax.Sig_let (_160_1128))
in (

let env = (FStar_Parser_Env.push_sigelt env s)
in ((env), ((s)::[]))))))))
end
| _65_2862 -> begin
(FStar_All.failwith "Desugaring a let did not produce a let")
end)
end
| FStar_Parser_AST.Main (t) -> begin
(

let e = (desugar_term env t)
in (

let se = FStar_Syntax_Syntax.Sig_main (((e), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[]))))
end
| FStar_Parser_AST.Assume (atag, id, t) -> begin
(

let f = (desugar_formula env t)
in (let _160_1132 = (let _160_1131 = (let _160_1130 = (let _160_1129 = (FStar_Parser_Env.qualify env id)
in ((_160_1129), (f), ((FStar_Syntax_Syntax.Assumption)::[]), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_assume (_160_1130))
in (_160_1131)::[])
in ((env), (_160_1132))))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(

let t = (let _160_1133 = (close_fun env t)
in (desugar_term env _160_1133))
in (

let quals = if (env.FStar_Parser_Env.iface && env.FStar_Parser_Env.admitted_iface) then begin
(FStar_Parser_AST.Assumption)::quals
end else begin
quals
end
in (

let se = (let _160_1136 = (let _160_1135 = (FStar_Parser_Env.qualify env id)
in (let _160_1134 = (FStar_List.map (trans_qual None) quals)
in ((_160_1135), ([]), (t), (_160_1134), (d.FStar_Parser_AST.drange))))
in FStar_Syntax_Syntax.Sig_declare_typ (_160_1136))
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in ((env), ((se)::[]))))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(

let _65_2889 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (match (_65_2889) with
| (t, _65_2888) -> begin
(

let l = (FStar_Parser_Env.qualify env id)
in (

let se = FStar_Syntax_Syntax.Sig_datacon (((l), ([]), (t), (FStar_Syntax_Const.exn_lid), ((Prims.parse_int "0")), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((FStar_Syntax_Const.exn_lid)::[]), (d.FStar_Parser_AST.drange)))
in (

let se' = FStar_Syntax_Syntax.Sig_bundle ((((se)::[]), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((l)::[]), (d.FStar_Parser_AST.drange)))
in (

let env = (FStar_Parser_Env.push_sigelt env se')
in (

let data_ops = (mk_data_projectors [] env (([]), (se)))
in (

let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (

let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in ((env), ((FStar_List.append ((se')::discs) data_ops))))))))))
end))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(

let t = (desugar_term env term)
in (

let t = (let _160_1141 = (let _160_1137 = (FStar_Syntax_Syntax.null_binder t)
in (_160_1137)::[])
in (let _160_1140 = (let _160_1139 = (let _160_1138 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (Prims.fst _160_1138))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _160_1139))
in (FStar_Syntax_Util.arrow _160_1141 _160_1140)))
in (

let l = (FStar_Parser_Env.qualify env id)
in (

let se = FStar_Syntax_Syntax.Sig_datacon (((l), ([]), (t), (FStar_Syntax_Const.exn_lid), ((Prims.parse_int "0")), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((FStar_Syntax_Const.exn_lid)::[]), (d.FStar_Parser_AST.drange)))
in (

let se' = FStar_Syntax_Syntax.Sig_bundle ((((se)::[]), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((l)::[]), (d.FStar_Parser_AST.drange)))
in (

let env = (FStar_Parser_Env.push_sigelt env se')
in (

let data_ops = (mk_data_projectors [] env (([]), (se)))
in (

let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (

let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in ((env), ((FStar_List.append ((se')::discs) data_ops))))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(

let _65_2918 = (desugar_binders env binders)
in (match (_65_2918) with
| (env_k, binders) -> begin
(

let k = (desugar_term env_k k)
in (

let name = (FStar_Parser_Env.qualify env id)
in (

let se = (mk_typ_abbrev name [] binders FStar_Syntax_Syntax.tun k ((name)::[]) [] d.FStar_Parser_AST.drange)
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in ((env), ((se)::[]))))))
end))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(desugar_redefine_effect env d trans_qual quals eff_name eff_binders defn (fun ed range -> FStar_Syntax_Syntax.Sig_new_effect (((ed), (range)))))
end
| FStar_Parser_AST.NewEffectForFree (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(desugar_redefine_effect env d trans_qual quals eff_name eff_binders defn (fun ed range -> FStar_Syntax_Syntax.Sig_new_effect_for_free (((ed), (range)))))
end
| FStar_Parser_AST.NewEffectForFree (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls, actions)) -> begin
(desugar_effect env d quals eff_name eff_binders eff_kind eff_decls actions true)
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls, actions)) -> begin
(desugar_effect env d quals eff_name eff_binders eff_kind eff_decls actions false)
end
| FStar_Parser_AST.SubEffect (l) -> begin
(

let lookup = (fun l -> (match ((FStar_Parser_Env.try_lookup_effect_name env l)) with
| None -> begin
(let _160_1152 = (let _160_1151 = (let _160_1150 = (let _160_1149 = (let _160_1148 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat _160_1148 " not found"))
in (Prims.strcat "Effect name " _160_1149))
in ((_160_1150), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_160_1151))
in (Prims.raise _160_1152))
end
| Some (l) -> begin
l
end))
in (

let src = (lookup l.FStar_Parser_AST.msource)
in (

let dst = (lookup l.FStar_Parser_AST.mdest)
in (

let _65_2982 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(let _160_1155 = (let _160_1154 = (let _160_1153 = (desugar_term env t)
in (([]), (_160_1153)))
in Some (_160_1154))
in ((_160_1155), (None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(let _160_1161 = (let _160_1157 = (let _160_1156 = (desugar_term env wp)
in (([]), (_160_1156)))
in Some (_160_1157))
in (let _160_1160 = (let _160_1159 = (let _160_1158 = (desugar_term env t)
in (([]), (_160_1158)))
in Some (_160_1159))
in ((_160_1161), (_160_1160))))
end
| FStar_Parser_AST.LiftForFree (t) -> begin
(let _160_1164 = (let _160_1163 = (let _160_1162 = (desugar_term env t)
in (([]), (_160_1162)))
in Some (_160_1163))
in ((None), (_160_1164)))
end)
in (match (_65_2982) with
| (lift_wp, lift) -> begin
(

let se = FStar_Syntax_Syntax.Sig_sub_effect ((({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift}), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[])))
end)))))
end)))


let desugar_decls : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _65_2988 d -> (match (_65_2988) with
| (env, sigelts) -> begin
(

let _65_2992 = (desugar_decl env d)
in (match (_65_2992) with
| (env, se) -> begin
((env), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls))


let open_prims_all : (FStar_Parser_AST.fsdoc Prims.option  ->  FStar_Parser_AST.decl) Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.all_lid)) FStar_Range.dummyRange))::[]


let desugar_modul_common : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod) -> begin
(FStar_Parser_Env.finish_module_or_interface env prev_mod)
end)
in (

let _65_3015 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _160_1182 = (FStar_Parser_Env.prepare_module_or_interface true admitted env mname)
in ((_160_1182), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _160_1183 = (FStar_Parser_Env.prepare_module_or_interface false false env mname)
in ((_160_1183), (mname), (decls), (false)))
end)
in (match (_65_3015) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(

let _65_3018 = (desugar_decls env decls)
in (match (_65_3018) with
| (env, sigelts) -> begin
(

let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in ((env), (modul), (pop_when_done)))
end))
end))))


let desugar_partial_modul : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (

let m = if (FStar_Options.interactive_fsi ()) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface (((mname), (decls), (true)))
end
| FStar_Parser_AST.Interface (mname, _65_3029, _65_3031) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (

let _65_3039 = (desugar_modul_common curmod env m)
in (match (_65_3039) with
| (x, y, _65_3038) -> begin
((x), (y))
end))))


let desugar_modul : FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (

let _65_3045 = (desugar_modul_common None env m)
in (match (_65_3045) with
| (env, modul, pop_when_done) -> begin
(

let env = (FStar_Parser_Env.finish_module_or_interface env modul)
in (

let _65_3047 = if (FStar_Options.dump_module modul.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _160_1194 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _160_1194))
end else begin
()
end
in (let _160_1195 = if pop_when_done then begin
(FStar_Parser_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end else begin
env
end
in ((_160_1195), (modul)))))
end)))


let desugar_file : FStar_Parser_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (

let _65_3060 = (FStar_List.fold_left (fun _65_3053 m -> (match (_65_3053) with
| (env, mods) -> begin
(

let _65_3057 = (desugar_modul env m)
in (match (_65_3057) with
| (env, m) -> begin
((env), ((m)::mods))
end))
end)) ((env), ([])) f)
in (match (_65_3060) with
| (env, mods) -> begin
((env), ((FStar_List.rev mods)))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Parser_Env.env  ->  FStar_Parser_Env.env = (fun m en -> (

let _65_3065 = (FStar_Parser_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (_65_3065) with
| (en, pop_when_done) -> begin
(

let en = (FStar_List.fold_left FStar_Parser_Env.push_sigelt (

let _65_3066 = en
in {FStar_Parser_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_Parser_Env.curmonad = _65_3066.FStar_Parser_Env.curmonad; FStar_Parser_Env.modules = _65_3066.FStar_Parser_Env.modules; FStar_Parser_Env.scope_mods = _65_3066.FStar_Parser_Env.scope_mods; FStar_Parser_Env.sigaccum = _65_3066.FStar_Parser_Env.sigaccum; FStar_Parser_Env.sigmap = _65_3066.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _65_3066.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _65_3066.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _65_3066.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = _65_3066.FStar_Parser_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (

let env = (FStar_Parser_Env.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_Env.export_interface m.FStar_Syntax_Syntax.name env)
end else begin
env
end))
end)))




