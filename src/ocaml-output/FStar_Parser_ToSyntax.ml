
open Prims

let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _66_1 -> (match (_66_1) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Syntax_Syntax.Equality)
end
| _66_34 -> begin
None
end))


let trans_qual : FStar_Range.range  ->  FStar_Ident.lident Prims.option  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun r maybe_effect_id _66_2 -> (match (_66_2) with
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

let _66_50 = (FStar_TypeChecker_Errors.warn r "The \'opaque\' qualifier is deprecated since its use was strangely schizophrenic. There were two overloaded uses: (1) Given \'opaque val f : t\', the behavior was to exclude the definition of \'f\' to the SMT solver. This corresponds roughly to the new \'irreducible\' qualifier. (2) Given \'opaque type t = t\'\', the behavior was to provide the definition of \'t\' to the SMT solver, but not to inline it, unless absolutely required for unification. This corresponds roughly to the behavior of \'unfoldable\' (which is currently the default).")
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


let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun _66_3 -> (match (_66_3) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end))


let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _66_4 -> (match (_66_4) with
| FStar_Parser_AST.Hash -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| _66_70 -> begin
None
end))


let arg_withimp_e = (fun imp t -> ((t), ((as_imp imp))))


let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
((t), (Some (FStar_Syntax_Syntax.imp_tag)))
end
| _66_77 -> begin
((t), (None))
end))


let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_66_81) -> begin
true
end
| _66_84 -> begin
false
end)))))


let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _66_89 -> begin
t
end))


let tm_type_z : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _163_25 = (let _163_24 = (FStar_Ident.lid_of_path (("Type0")::[]) r)
in FStar_Parser_AST.Name (_163_24))
in (FStar_Parser_AST.mk_term _163_25 r FStar_Parser_AST.Kind)))


let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _163_29 = (let _163_28 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_163_28))
in (FStar_Parser_AST.mk_term _163_29 r FStar_Parser_AST.Kind)))


let rec is_comp_type : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> (match (t.FStar_Parser_AST.tm) with
| (FStar_Parser_AST.Name (l)) | (FStar_Parser_AST.Construct (l, _)) -> begin
(let _163_34 = (FStar_Parser_Env.try_lookup_effect_name env l)
in (FStar_All.pipe_right _163_34 FStar_Option.isSome))
end
| FStar_Parser_AST.App (head, _66_102, _66_104) -> begin
(is_comp_type env head)
end
| (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) | (FStar_Parser_AST.LetOpen (_, t)) -> begin
(is_comp_type env t)
end
| _66_118 -> begin
false
end))


let unit_ty : FStar_Parser_AST.term = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.unit_lid)) FStar_Range.dummyRange FStar_Parser_AST.Type)


let compile_op : Prims.int  ->  Prims.string  ->  Prims.string = (fun arity s -> (

let name_of_char = (fun _66_5 -> (match (_66_5) with
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
| _66_140 -> begin
"UNKNOWN"
end))
in (

let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _163_45 = (let _163_43 = (FStar_Util.char_at s i)
in (name_of_char _163_43))
in (let _163_44 = (aux (i + (Prims.parse_int "1")))
in (_163_45)::_163_44))
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
| _66_149 -> begin
(let _163_47 = (let _163_46 = (aux (Prims.parse_int "0"))
in (FStar_String.concat "_" _163_46))
in (Prims.strcat "op_" _163_47))
end))))


let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _163_57 = (let _163_56 = (let _163_55 = (let _163_54 = (compile_op n s)
in ((_163_54), (r)))
in (FStar_Ident.mk_ident _163_55))
in (_163_56)::[])
in (FStar_All.pipe_right _163_57 FStar_Ident.lid_of_ids)))


let op_as_term : FStar_Parser_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.term Prims.option = (fun env arity rng s -> (

let r = (fun l dd -> (let _163_71 = (let _163_70 = (FStar_Syntax_Syntax.lid_as_fv (FStar_Ident.set_lid_range l rng) dd None)
in (FStar_All.pipe_right _163_70 FStar_Syntax_Syntax.fv_to_tm))
in Some (_163_71)))
in (

let fallback = (fun _66_161 -> (match (()) with
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
| _66_189 -> begin
None
end)
end))
in (match ((let _163_74 = (compile_op_lid arity s rng)
in (FStar_Parser_Env.try_lookup_lid env _163_74))) with
| Some (t) -> begin
Some ((Prims.fst t))
end
| _66_193 -> begin
(fallback ())
end))))


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _163_81 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _163_81)))


let rec free_type_vars_b : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_66_202) -> begin
((env), ([]))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let _66_209 = (FStar_Parser_Env.push_bv env x)
in (match (_66_209) with
| (env, _66_208) -> begin
((env), ((x)::[]))
end))
end
| FStar_Parser_AST.Annotated (_66_211, term) -> begin
(let _163_88 = (free_type_vars env term)
in ((env), (_163_88)))
end
| FStar_Parser_AST.TAnnotated (id, _66_217) -> begin
(

let _66_223 = (FStar_Parser_Env.push_bv env id)
in (match (_66_223) with
| (env, _66_222) -> begin
((env), ([]))
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _163_89 = (free_type_vars env t)
in ((env), (_163_89)))
end))
and free_type_vars : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _163_92 = (unparen t)
in _163_92.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (_66_229) -> begin
(FStar_All.failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_Env.try_lookup_id env a)) with
| None -> begin
(a)::[]
end
| _66_235 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Uvar (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Projector (_)) | (FStar_Parser_AST.Discrim (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Assign (_, t)) | (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_66_278, ts) -> begin
(FStar_List.collect (fun _66_285 -> (match (_66_285) with
| (t, _66_284) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_66_287, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _66_294) -> begin
(let _163_95 = (free_type_vars env t1)
in (let _163_94 = (free_type_vars env t2)
in (FStar_List.append _163_95 _163_94)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(

let _66_303 = (free_type_vars_b env b)
in (match (_66_303) with
| (env, f) -> begin
(let _163_96 = (free_type_vars env t)
in (FStar_List.append f _163_96))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(

let _66_319 = (FStar_List.fold_left (fun _66_312 binder -> (match (_66_312) with
| (env, free) -> begin
(

let _66_316 = (free_type_vars_b env binder)
in (match (_66_316) with
| (env, f) -> begin
((env), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (_66_319) with
| (env, free) -> begin
(let _163_99 = (free_type_vars env body)
in (FStar_List.append free _163_99))
end))
end
| FStar_Parser_AST.Project (t, _66_322) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Attributes (cattributes) -> begin
(FStar_List.collect (free_type_vars env) cattributes)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
[]
end))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (

let rec aux = (fun args t -> (match ((let _163_106 = (unparen t)
in _163_106.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| _66_371 -> begin
((t), (args))
end))
in (aux [] t)))


let close : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _163_111 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _163_111))
in if ((FStar_List.length ftv) = (Prims.parse_int "0")) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _163_115 = (let _163_114 = (let _163_113 = (tm_type x.FStar_Ident.idRange)
in ((x), (_163_113)))
in FStar_Parser_AST.TAnnotated (_163_114))
in (FStar_Parser_AST.mk_binder _163_115 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))


let close_fun : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _163_120 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _163_120))
in if ((FStar_List.length ftv) = (Prims.parse_int "0")) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _163_124 = (let _163_123 = (let _163_122 = (tm_type x.FStar_Ident.idRange)
in ((x), (_163_122)))
in FStar_Parser_AST.TAnnotated (_163_123))
in (FStar_Parser_AST.mk_binder _163_124 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let t = (match ((let _163_125 = (unparen t)
in _163_125.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_66_384) -> begin
t
end
| _66_387 -> begin
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
| _66_397 -> begin
((bs), (t))
end))


let rec is_var_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatWild) | (FStar_Parser_AST.PatTvar (_, _)) | (FStar_Parser_AST.PatVar (_, _)) -> begin
true
end
| FStar_Parser_AST.PatAscribed (p, _66_414) -> begin
(is_var_pattern p)
end
| _66_418 -> begin
false
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _66_422) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_66_428); FStar_Parser_AST.prange = _66_426}, _66_432) -> begin
true
end
| _66_436 -> begin
false
end))


let replace_unit_pattern : FStar_Parser_AST.pattern  ->  FStar_Parser_AST.pattern = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatConst (FStar_Const.Const_unit) -> begin
(FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatAscribed ((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)), (unit_ty)))) p.FStar_Parser_AST.prange)
end
| _66_441 -> begin
p
end))


let rec destruct_app_pattern : FStar_Parser_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _66_453 = (destruct_app_pattern env is_top_level p)
in (match (_66_453) with
| (name, args, _66_452) -> begin
((name), (args), (Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _66_458); FStar_Parser_AST.prange = _66_455}, args) when is_top_level -> begin
(let _163_143 = (let _163_142 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_163_142))
in ((_163_143), (args), (None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _66_469); FStar_Parser_AST.prange = _66_466}, args) -> begin
((FStar_Util.Inl (id)), (args), (None))
end
| _66_477 -> begin
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
| LocalBinder (_66_480) -> begin
_66_480
end))


let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_66_483) -> begin
_66_483
end))


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun _66_6 -> (match (_66_6) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| _66_490 -> begin
(FStar_All.failwith "Impossible")
end))


let as_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_Parser_Env.env) = (fun env imp _66_7 -> (match (_66_7) with
| (None, k) -> begin
(let _163_180 = (FStar_Syntax_Syntax.null_binder k)
in ((_163_180), (env)))
end
| (Some (a), k) -> begin
(

let _66_503 = (FStar_Parser_Env.push_bv env a)
in (match (_66_503) with
| (env, a) -> begin
(((((

let _66_504 = a
in {FStar_Syntax_Syntax.ppname = _66_504.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_504.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), ((trans_aqual imp)))), (env))
end))
end))


type env_t =
FStar_Parser_Env.env


type lenv_t =
FStar_Syntax_Syntax.bv Prims.list


let mk_lb : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.letbinding = (fun _66_509 -> (match (_66_509) with
| (n, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))


let no_annot_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t None))


let mk_ref_read = (fun tm -> (

let tm' = (let _163_193 = (let _163_192 = (let _163_188 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _163_188))
in (let _163_191 = (let _163_190 = (let _163_189 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (_163_189)))
in (_163_190)::[])
in ((_163_192), (_163_191))))
in FStar_Syntax_Syntax.Tm_app (_163_193))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_alloc = (fun tm -> (

let tm' = (let _163_200 = (let _163_199 = (let _163_195 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _163_195))
in (let _163_198 = (let _163_197 = (let _163_196 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (_163_196)))
in (_163_197)::[])
in ((_163_199), (_163_198))))
in FStar_Syntax_Syntax.Tm_app (_163_200))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_assign = (fun t1 t2 pos -> (

let tm = (let _163_212 = (let _163_211 = (let _163_204 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _163_204))
in (let _163_210 = (let _163_209 = (let _163_205 = (FStar_Syntax_Syntax.as_implicit false)
in ((t1), (_163_205)))
in (let _163_208 = (let _163_207 = (let _163_206 = (FStar_Syntax_Syntax.as_implicit false)
in ((t2), (_163_206)))
in (_163_207)::[])
in (_163_209)::_163_208))
in ((_163_211), (_163_210))))
in FStar_Syntax_Syntax.Tm_app (_163_212))
in (FStar_Syntax_Syntax.mk tm None pos)))


let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun _66_8 -> (match (_66_8) with
| ("repr") | ("post") | ("pre") | ("wp") -> begin
true
end
| _66_526 -> begin
false
end))


let rec sum_to_universe : FStar_Syntax_Syntax.universe  ->  Prims.int  ->  FStar_Syntax_Syntax.universe = (fun u n -> if (n = (Prims.parse_int "0")) then begin
u
end else begin
(let _163_219 = (sum_to_universe u (n - (Prims.parse_int "1")))
in FStar_Syntax_Syntax.U_succ (_163_219))
end)


let int_to_universe : Prims.int  ->  FStar_Syntax_Syntax.universe = (fun n -> (sum_to_universe FStar_Syntax_Syntax.U_zero n))


let rec desugar_maybe_non_constant_universe : FStar_Parser_AST.term  ->  (Prims.int, FStar_Syntax_Syntax.universe) FStar_Util.either = (fun t -> (match ((let _163_224 = (unparen t)
in _163_224.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(let _163_225 = (FStar_TypeChecker_Env.new_u_univ ())
in FStar_Util.Inr (_163_225))
end
| FStar_Parser_AST.Uvar (u) -> begin
FStar_Util.Inr (FStar_Syntax_Syntax.U_name (u))
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (repr, _66_536)) -> begin
(

let n = (FStar_Util.int_of_string repr)
in (

let _66_541 = if (n < (Prims.parse_int "0")) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Negative universe constant  are not supported : " repr)), (t.FStar_Parser_AST.range)))))
end else begin
()
end
in FStar_Util.Inl (n)))
end
| FStar_Parser_AST.Op (op_plus, (t1)::(t2)::[]) -> begin
(

let _66_549 = ()
in (

let u1 = (desugar_maybe_non_constant_universe t1)
in (

let u2 = (desugar_maybe_non_constant_universe t2)
in (match (((u1), (u2))) with
| (FStar_Util.Inl (n1), FStar_Util.Inl (n2)) -> begin
FStar_Util.Inl ((n1 + n2))
end
| ((FStar_Util.Inl (n), FStar_Util.Inr (u))) | ((FStar_Util.Inr (u), FStar_Util.Inl (n))) -> begin
(let _163_226 = (sum_to_universe u n)
in FStar_Util.Inr (_163_226))
end
| (FStar_Util.Inr (u1), FStar_Util.Inr (u2)) -> begin
(let _163_230 = (let _163_229 = (let _163_228 = (let _163_227 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "This universe might contain a sum of two universe variables " _163_227))
in ((_163_228), (t.FStar_Parser_AST.range)))
in FStar_Syntax_Syntax.Error (_163_229))
in (Prims.raise _163_230))
end))))
end
| FStar_Parser_AST.App (_66_572) -> begin
(

let rec aux = (fun t univargs -> (match ((let _163_235 = (unparen t)
in _163_235.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, targ, _66_580) -> begin
(

let uarg = (desugar_maybe_non_constant_universe targ)
in (aux t ((uarg)::univargs)))
end
| FStar_Parser_AST.Var (max_lid) -> begin
(

let _66_586 = ()
in if (FStar_List.existsb (fun _66_9 -> (match (_66_9) with
| FStar_Util.Inr (_66_590) -> begin
true
end
| _66_593 -> begin
false
end)) univargs) then begin
(let _163_239 = (let _163_238 = (FStar_List.map (fun _66_10 -> (match (_66_10) with
| FStar_Util.Inl (n) -> begin
(int_to_universe n)
end
| FStar_Util.Inr (u) -> begin
u
end)) univargs)
in FStar_Syntax_Syntax.U_max (_163_238))
in FStar_Util.Inr (_163_239))
end else begin
(

let nargs = (FStar_List.map (fun _66_11 -> (match (_66_11) with
| FStar_Util.Inl (n) -> begin
n
end
| FStar_Util.Inr (_66_603) -> begin
(FStar_All.failwith "impossible")
end)) univargs)
in (let _163_243 = (FStar_List.fold_left (fun m n -> if (m > n) then begin
m
end else begin
n
end) (Prims.parse_int "0") nargs)
in FStar_Util.Inl (_163_243)))
end)
end
| _66_609 -> begin
(let _163_248 = (let _163_247 = (let _163_246 = (let _163_245 = (let _163_244 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat _163_244 " in universe context"))
in (Prims.strcat "Unexpected term " _163_245))
in ((_163_246), (t.FStar_Parser_AST.range)))
in FStar_Syntax_Syntax.Error (_163_247))
in (Prims.raise _163_248))
end))
in (aux t []))
end
| _66_611 -> begin
(let _163_253 = (let _163_252 = (let _163_251 = (let _163_250 = (let _163_249 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat _163_249 " in universe context"))
in (Prims.strcat "Unexpected term " _163_250))
in ((_163_251), (t.FStar_Parser_AST.range)))
in FStar_Syntax_Syntax.Error (_163_252))
in (Prims.raise _163_253))
end))


let rec desugar_universe : FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.universe = (fun t -> (

let u = (desugar_maybe_non_constant_universe t)
in (match (u) with
| FStar_Util.Inl (n) -> begin
(int_to_universe n)
end
| FStar_Util.Inr (u) -> begin
u
end)))


let check_fields = (fun env fields rg -> (

let _66_624 = (FStar_List.hd fields)
in (match (_66_624) with
| (f, _66_623) -> begin
(

let record = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (

let check_field = (fun _66_630 -> (match (_66_630) with
| (f', _66_629) -> begin
if (FStar_Parser_Env.belongs_to_record env f' record) then begin
()
end else begin
(

let msg = (FStar_Util.format3 "Field %s belongs to record type %s, whereas field %s does not" f.FStar_Ident.str record.FStar_Parser_Env.typename.FStar_Ident.str f'.FStar_Ident.str)
in (Prims.raise (FStar_Syntax_Syntax.Error (((msg), (rg))))))
end
end))
in (

let _66_632 = (let _163_261 = (FStar_List.tl fields)
in (FStar_List.iter check_field _163_261))
in (match (()) with
| () -> begin
record
end))))
end)))


let rec desugar_data_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat) = (fun env p is_mut -> (

let check_linear_pattern_variables = (fun p -> (

let rec pat_vars = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_dot_term (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_constant (_)) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (_66_652, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out _66_660 -> (match (_66_660) with
| (p, _66_659) -> begin
(let _163_318 = (pat_vars p)
in (FStar_Util.set_union out _163_318))
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

let _66_683 = (match (((is_mut), (p.FStar_Parser_AST.pat))) with
| ((false, _)) | ((true, FStar_Parser_AST.PatVar (_))) -> begin
()
end
| (true, _66_681) -> begin
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
| _66_694 -> begin
(

let _66_697 = (push_bv_maybe_mut e x)
in (match (_66_697) with
| (e, x) -> begin
(((x)::l), (e), (x))
end))
end))
in (

let rec aux = (fun loc env p -> (

let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Parser_AST.prange))
in (

let pos_r = (fun r q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r))
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (op) -> begin
(let _163_347 = (let _163_346 = (let _163_345 = (let _163_344 = (let _163_343 = (compile_op (Prims.parse_int "0") op)
in (FStar_Ident.id_of_text _163_343))
in ((_163_344), (None)))
in FStar_Parser_AST.PatVar (_163_345))
in {FStar_Parser_AST.pat = _163_346; FStar_Parser_AST.prange = p.FStar_Parser_AST.prange})
in (aux loc env _163_347))
end
| FStar_Parser_AST.PatOr ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.PatOr ((p)::ps) -> begin
(

let _66_721 = (aux loc env p)
in (match (_66_721) with
| (loc, env, var, p, _66_720) -> begin
(

let _66_738 = (FStar_List.fold_left (fun _66_725 p -> (match (_66_725) with
| (loc, env, ps) -> begin
(

let _66_734 = (aux loc env p)
in (match (_66_734) with
| (loc, env, _66_730, p, _66_733) -> begin
((loc), (env), ((p)::ps))
end))
end)) ((loc), (env), ([])) ps)
in (match (_66_738) with
| (loc, env, ps) -> begin
(

let pat = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in ((loc), (env), (var), (pat), (false)))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _66_749 = (aux loc env p)
in (match (_66_749) with
| (loc, env', binder, p, imp) -> begin
(

let binder = (match (binder) with
| LetBinder (_66_751) -> begin
(FStar_All.failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t = (let _163_350 = (close_fun env t)
in (desugar_term env _163_350))
in LocalBinder ((((

let _66_758 = x
in {FStar_Syntax_Syntax.ppname = _66_758.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_758.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (aq))))
end)
in ((loc), (env'), (binder), (p), (imp)))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _163_351 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env), (LocalBinder (((x), (None)))), (_163_351), (false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _163_352 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env), (LocalBinder (((x), (None)))), (_163_352), (false))))
end
| (FStar_Parser_AST.PatTvar (x, aq)) | (FStar_Parser_AST.PatVar (x, aq)) -> begin
(

let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (

let aq = (trans_aqual aq)
in (

let _66_777 = (resolvex loc env x)
in (match (_66_777) with
| (loc, env, xbv) -> begin
(let _163_353 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc), (env), (LocalBinder (((xbv), (aq)))), (_163_353), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _163_354 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), ([])))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_163_354), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _66_783}, args) -> begin
(

let _66_805 = (FStar_List.fold_right (fun arg _66_794 -> (match (_66_794) with
| (loc, env, args) -> begin
(

let _66_801 = (aux loc env arg)
in (match (_66_801) with
| (loc, env, _66_798, arg, imp) -> begin
((loc), (env), ((((arg), (imp)))::args))
end))
end)) args ((loc), (env), ([])))
in (match (_66_805) with
| (loc, env, args) -> begin
(

let l = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _163_357 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_163_357), (false)))))
end))
end
| FStar_Parser_AST.PatApp (_66_809) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let _66_829 = (FStar_List.fold_right (fun pat _66_817 -> (match (_66_817) with
| (loc, env, pats) -> begin
(

let _66_825 = (aux loc env pat)
in (match (_66_825) with
| (loc, env, _66_821, pat, _66_824) -> begin
((loc), (env), ((pat)::pats))
end))
end)) pats ((loc), (env), ([])))
in (match (_66_829) with
| (loc, env, pats) -> begin
(

let pat = (let _163_370 = (let _163_369 = (let _163_365 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _163_365))
in (let _163_368 = (let _163_367 = (let _163_366 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_163_366), ([])))
in FStar_Syntax_Syntax.Pat_cons (_163_367))
in (FStar_All.pipe_left _163_369 _163_368)))
in (FStar_List.fold_right (fun hd tl -> (

let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (let _163_364 = (let _163_363 = (let _163_362 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_163_362), ((((hd), (false)))::(((tl), (false)))::[])))
in FStar_Syntax_Syntax.Pat_cons (_163_363))
in (FStar_All.pipe_left (pos_r r) _163_364)))) pats _163_370))
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc), (env), (LocalBinder (((x), (None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(

let _66_855 = (FStar_List.fold_left (fun _66_842 p -> (match (_66_842) with
| (loc, env, pats) -> begin
(

let _66_851 = (aux loc env p)
in (match (_66_851) with
| (loc, env, _66_847, pat, _66_850) -> begin
((loc), (env), ((((pat), (false)))::pats))
end))
end)) ((loc), (env), ([])) args)
in (match (_66_855) with
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

let _66_861 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) l)
in (match (_66_861) with
| (constr, _66_860) -> begin
(

let l = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| _66_865 -> begin
(FStar_All.failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _163_373 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_163_373), (false)))))
end))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(

let record = (check_fields env fields p.FStar_Parser_AST.prange)
in (

let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _66_875 -> (match (_66_875) with
| (f, p) -> begin
((f.FStar_Ident.ident), (p))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _66_880 -> (match (_66_880) with
| (f, _66_879) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _66_884 -> (match (_66_884) with
| (g, _66_883) -> begin
(f.FStar_Ident.idText = g.FStar_Ident.idText)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_66_887, p) -> begin
p
end)
end))))
in (

let app = (let _163_381 = (let _163_380 = (let _163_379 = (let _163_378 = (let _163_377 = (FStar_Ident.lid_of_ids (FStar_List.append record.FStar_Parser_Env.typename.FStar_Ident.ns ((record.FStar_Parser_Env.constrname)::[])))
in FStar_Parser_AST.PatName (_163_377))
in (FStar_Parser_AST.mk_pattern _163_378 p.FStar_Parser_AST.prange))
in ((_163_379), (args)))
in FStar_Parser_AST.PatApp (_163_380))
in (FStar_Parser_AST.mk_pattern _163_381 p.FStar_Parser_AST.prange))
in (

let _66_899 = (aux loc env app)
in (match (_66_899) with
| (env, e, b, p, _66_898) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(let _163_388 = (let _163_387 = (let _163_386 = (

let _66_904 = fv
in (let _163_385 = (let _163_384 = (let _163_383 = (let _163_382 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_Env.typename), (_163_382)))
in FStar_Syntax_Syntax.Record_ctor (_163_383))
in Some (_163_384))
in {FStar_Syntax_Syntax.fv_name = _66_904.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = _66_904.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _163_385}))
in ((_163_386), (args)))
in FStar_Syntax_Syntax.Pat_cons (_163_387))
in (FStar_All.pipe_left pos _163_388))
end
| _66_907 -> begin
p
end)
in ((env), (e), (b), (p), (false)))
end))))))
end))))
in (

let _66_916 = (aux [] env p)
in (match (_66_916) with
| (_66_910, env, b, p, _66_915) -> begin
(

let _66_917 = (let _163_389 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore _163_389))
in ((env), (b), (p)))
end))))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p is_mut -> (

let mklet = (fun x -> (let _163_398 = (let _163_397 = (let _163_396 = (FStar_Parser_Env.qualify env x)
in ((_163_396), (FStar_Syntax_Syntax.tun)))
in LetBinder (_163_397))
in ((env), (_163_398), (None))))
in if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(let _163_400 = (let _163_399 = (compile_op (Prims.parse_int "0") x)
in (FStar_Ident.id_of_text _163_399))
in (mklet _163_400))
end
| FStar_Parser_AST.PatVar (x, _66_929) -> begin
(mklet x)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _66_936); FStar_Parser_AST.prange = _66_933}, t) -> begin
(let _163_404 = (let _163_403 = (let _163_402 = (FStar_Parser_Env.qualify env x)
in (let _163_401 = (desugar_term env t)
in ((_163_402), (_163_401))))
in LetBinder (_163_403))
in ((env), (_163_404), (None)))
end
| _66_944 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end else begin
(

let _66_948 = (desugar_data_pat env p is_mut)
in (match (_66_948) with
| (env, binder, p) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| _66_956 -> begin
Some (p)
end)
in ((env), (binder), (p)))
end))
end))
and desugar_binding_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun _66_960 env pat -> (

let _66_968 = (desugar_data_pat env pat false)
in (match (_66_968) with
| (env, _66_966, pat) -> begin
((env), (pat))
end)))
and desugar_match_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let _66_973 = env
in {FStar_Parser_Env.curmodule = _66_973.FStar_Parser_Env.curmodule; FStar_Parser_Env.curmonad = _66_973.FStar_Parser_Env.curmonad; FStar_Parser_Env.modules = _66_973.FStar_Parser_Env.modules; FStar_Parser_Env.scope_mods = _66_973.FStar_Parser_Env.scope_mods; FStar_Parser_Env.sigaccum = _66_973.FStar_Parser_Env.sigaccum; FStar_Parser_Env.sigmap = _66_973.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _66_973.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _66_973.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _66_973.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let _66_978 = env
in {FStar_Parser_Env.curmodule = _66_978.FStar_Parser_Env.curmodule; FStar_Parser_Env.curmonad = _66_978.FStar_Parser_Env.curmonad; FStar_Parser_Env.modules = _66_978.FStar_Parser_Env.modules; FStar_Parser_Env.scope_mods = _66_978.FStar_Parser_Env.scope_mods; FStar_Parser_Env.sigaccum = _66_978.FStar_Parser_Env.sigaccum; FStar_Parser_Env.sigmap = _66_978.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _66_978.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _66_978.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _66_978.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_machine_integer : FStar_Parser_Env.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env repr _66_985 range -> (match (_66_985) with
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
(let _163_420 = (FStar_Util.format1 "%s not in scope\n" (FStar_Ident.text_of_lid lid))
in (FStar_All.failwith _163_420))
end)
in (

let repr = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (None))))) None range)
in (let _163_425 = (let _163_424 = (let _163_423 = (let _163_422 = (let _163_421 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr), (_163_421)))
in (_163_422)::[])
in ((lid), (_163_423)))
in FStar_Syntax_Syntax.Tm_app (_163_424))
in (FStar_Syntax_Syntax.mk _163_425 None range))))))
end))
and desugar_name : (FStar_Syntax_Syntax.term'  ->  FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax)  ->  env_t  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.term = (fun mk setpos env l -> (

let _66_1008 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) l)
in (match (_66_1008) with
| (tm, mut) -> begin
(

let tm = (setpos tm)
in if mut then begin
(let _163_438 = (let _163_437 = (let _163_436 = (mk_ref_read tm)
in ((_163_436), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval))))
in FStar_Syntax_Syntax.Tm_meta (_163_437))
in (FStar_All.pipe_left mk _163_438))
end else begin
tm
end)
end)))
and desugar_attributes : FStar_Parser_Env.env  ->  FStar_Parser_AST.term Prims.list  ->  FStar_Syntax_Syntax.cflags Prims.list = (fun env cattributes -> (

let desugar_attribute = (fun t -> (match ((let _163_443 = (unparen t)
in _163_443.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Var ({FStar_Ident.ns = _66_1020; FStar_Ident.ident = _66_1018; FStar_Ident.nsstr = _66_1016; FStar_Ident.str = "cps"}) -> begin
FStar_Syntax_Syntax.CPS
end
| _66_1024 -> begin
(let _163_447 = (let _163_446 = (let _163_445 = (let _163_444 = (FStar_Parser_AST.term_to_string t)
in (Prims.strcat "Unknown attribute " _163_444))
in ((_163_445), (t.FStar_Parser_AST.range)))
in FStar_Syntax_Syntax.Error (_163_446))
in (Prims.raise _163_447))
end))
in (FStar_List.map desugar_attribute cattributes)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (

let mk = (fun e -> (FStar_Syntax_Syntax.mk e None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let _66_1032 = e
in {FStar_Syntax_Syntax.n = _66_1032.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _66_1032.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _66_1032.FStar_Syntax_Syntax.vars}))
in (match ((let _163_455 = (unparen top)
in _163_455.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (_66_1036) -> begin
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
| FStar_Parser_AST.Op ("*", (_66_1064)::(_66_1062)::[]) when (let _163_456 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right _163_456 FStar_Option.isNone)) -> begin
(

let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", (t1)::(t2)::[]) -> begin
(let _163_459 = (flatten t1)
in (FStar_List.append _163_459 ((t2)::[])))
end
| _66_1077 -> begin
(t)::[]
end))
in (

let targs = (let _163_463 = (let _163_460 = (unparen top)
in (flatten _163_460))
in (FStar_All.pipe_right _163_463 (FStar_List.map (fun t -> (let _163_462 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg _163_462))))))
in (

let _66_1083 = (let _163_464 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) _163_464))
in (match (_66_1083) with
| (tup, _66_1082) -> begin
(mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _163_466 = (let _163_465 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) a)
in (Prims.fst _163_465))
in (FStar_All.pipe_left setpos _163_466))
end
| FStar_Parser_AST.Uvar (u) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Unexpected universe variable " (Prims.strcat (FStar_Ident.text_of_id u) " in non-universe context"))), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Unexpected or unbound operator: " s)), (top.FStar_Parser_AST.range)))))
end
| Some (op) -> begin
if ((FStar_List.length args) > (Prims.parse_int "0")) then begin
(

let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _163_468 = (desugar_term env t)
in ((_163_468), (None))))))
in (mk (FStar_Syntax_Syntax.Tm_app (((op), (args))))))
end else begin
op
end
end)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _66_1103; FStar_Ident.ident = _66_1101; FStar_Ident.nsstr = _66_1099; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _66_1112; FStar_Ident.ident = _66_1110; FStar_Ident.nsstr = _66_1108; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Construct ({FStar_Ident.ns = _66_1121; FStar_Ident.ident = _66_1119; FStar_Ident.nsstr = _66_1117; FStar_Ident.str = "Type"}, ((t, FStar_Parser_AST.UnivApp))::[]) -> begin
(let _163_470 = (let _163_469 = (desugar_universe t)
in FStar_Syntax_Syntax.Tm_type (_163_469))
in (mk _163_470))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _66_1135; FStar_Ident.ident = _66_1133; FStar_Ident.nsstr = _66_1131; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _66_1144; FStar_Ident.ident = _66_1142; FStar_Ident.nsstr = _66_1140; FStar_Ident.str = "True"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant None)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _66_1153; FStar_Ident.ident = _66_1151; FStar_Ident.nsstr = _66_1149; FStar_Ident.str = "False"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant None)
end
| FStar_Parser_AST.Projector (eff_name, {FStar_Ident.idText = txt; FStar_Ident.idRange = _66_1158}) when ((is_special_effect_combinator txt) && (FStar_Parser_Env.is_effect_name env eff_name)) -> begin
(match ((FStar_Parser_Env.try_lookup_effect_defn env eff_name)) with
| Some (ed) -> begin
(let _163_471 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" txt))) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.fvar _163_471 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None))
end
| None -> begin
(FStar_All.failwith "immpossible special_effect_combinator")
end)
end
| FStar_Parser_AST.Assign (ident, t2) -> begin
(

let t2 = (desugar_term env t2)
in (

let _66_1173 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) ident)
in (match (_66_1173) with
| (t1, mut) -> begin
(

let _66_1174 = if (not (mut)) then begin
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

let found = ((let _163_472 = (FStar_Parser_Env.try_lookup_datacon env l)
in (FStar_Option.isSome _163_472)) || (let _163_473 = (FStar_Parser_Env.try_lookup_effect_defn env l)
in (FStar_Option.isSome _163_473)))
in if found then begin
(let _163_474 = (FStar_Syntax_Util.mk_field_projector_name_from_ident l i)
in (desugar_name mk setpos env _163_474))
end else begin
(let _163_477 = (let _163_476 = (let _163_475 = (FStar_Util.format1 "Data constructor or effect %s not found" l.FStar_Ident.str)
in ((_163_475), (top.FStar_Parser_AST.range)))
in FStar_Syntax_Syntax.Error (_163_476))
in (Prims.raise _163_477))
end)
end
| FStar_Parser_AST.Discrim (lid) -> begin
(match ((FStar_Parser_Env.try_lookup_datacon env lid)) with
| None -> begin
(let _163_480 = (let _163_479 = (let _163_478 = (FStar_Util.format1 "Data constructor %s not found" lid.FStar_Ident.str)
in ((_163_478), (top.FStar_Parser_AST.range)))
in FStar_Syntax_Syntax.Error (_163_479))
in (Prims.raise _163_480))
end
| _66_1188 -> begin
(

let lid' = (FStar_Syntax_Util.mk_discriminator lid)
in (desugar_name mk setpos env lid'))
end)
end
| FStar_Parser_AST.Construct (l, args) -> begin
(match ((FStar_Parser_Env.try_lookup_datacon env l)) with
| Some (head) -> begin
(

let _66_1198 = (let _163_481 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in ((_163_481), (true)))
in (match (_66_1198) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| _66_1201 -> begin
(

let args = (FStar_List.map (fun _66_1204 -> (match (_66_1204) with
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

let _66_1233 = (FStar_List.fold_left (fun _66_1216 b -> (match (_66_1216) with
| (env, tparams, typs) -> begin
(

let _66_1220 = (desugar_binder env b)
in (match (_66_1220) with
| (xopt, t) -> begin
(

let _66_1226 = (match (xopt) with
| None -> begin
(let _163_485 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env), (_163_485)))
end
| Some (x) -> begin
(FStar_Parser_Env.push_bv env x)
end)
in (match (_66_1226) with
| (env, x) -> begin
(let _163_489 = (let _163_488 = (let _163_487 = (let _163_486 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _163_486))
in (_163_487)::[])
in (FStar_List.append typs _163_488))
in ((env), ((FStar_List.append tparams (((((

let _66_1227 = x
in {FStar_Syntax_Syntax.ppname = _66_1227.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_1227.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (None)))::[]))), (_163_489)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_66_1233) with
| (env, _66_1231, targs) -> begin
(

let _66_1237 = (let _163_490 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) _163_490))
in (match (_66_1237) with
| (tup, _66_1236) -> begin
(FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let _66_1244 = (uncurry binders t)
in (match (_66_1244) with
| (bs, t) -> begin
(

let rec aux = (fun env bs _66_12 -> (match (_66_12) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (let _163_497 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos _163_497)))
end
| (hd)::tl -> begin
(

let mlenv = (FStar_Parser_Env.default_ml env)
in (

let bb = (desugar_binder mlenv hd)
in (

let _66_1258 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_66_1258) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_binder env b)) with
| (None, _66_1265) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(

let _66_1273 = (as_binder env None b)
in (match (_66_1273) with
| ((x, _66_1270), env) -> begin
(

let f = (desugar_formula env f)
in (let _163_498 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos _163_498)))
end))
end)
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let binders = (FStar_All.pipe_right binders (FStar_List.map replace_unit_pattern))
in (

let _66_1294 = (FStar_List.fold_left (fun _66_1282 pat -> (match (_66_1282) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (_66_1285, t) -> begin
(let _163_502 = (let _163_501 = (free_type_vars env t)
in (FStar_List.append _163_501 ftvs))
in ((env), (_163_502)))
end
| _66_1290 -> begin
((env), (ftvs))
end)
end)) ((env), ([])) binders)
in (match (_66_1294) with
| (_66_1292, ftv) -> begin
(

let ftv = (sort_ftv ftv)
in (

let binders = (let _163_504 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append _163_504 binders))
in (

let rec aux = (fun env bs sc_pat_opt _66_13 -> (match (_66_13) with
| [] -> begin
(

let body = (desugar_term env body)
in (

let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(

let body = (let _163_514 = (let _163_513 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right _163_513 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close _163_514 body))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (None), (body)))::[])))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (let _163_515 = (no_annot_abs (FStar_List.rev bs) body)
in (setpos _163_515))))
end
| (p)::rest -> begin
(

let _66_1318 = (desugar_binding_pat env p)
in (match (_66_1318) with
| (env, b, pat) -> begin
(

let _66_1369 = (match (b) with
| LetBinder (_66_1320) -> begin
(FStar_All.failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt = (match (((pat), (sc_pat_opt))) with
| (None, _66_1328) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _163_517 = (let _163_516 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_163_516), (p)))
in Some (_163_517))
end
| (Some (p), Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (_66_1342), _66_1345) -> begin
(

let tup2 = (let _163_518 = (FStar_Syntax_Util.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _163_518 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (let _163_526 = (let _163_525 = (let _163_524 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (let _163_523 = (let _163_522 = (FStar_Syntax_Syntax.as_arg sc)
in (let _163_521 = (let _163_520 = (let _163_519 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _163_519))
in (_163_520)::[])
in (_163_522)::_163_521))
in ((_163_524), (_163_523))))
in FStar_Syntax_Syntax.Tm_app (_163_525))
in (FStar_Syntax_Syntax.mk _163_526 None top.FStar_Parser_AST.range))
in (

let p = (let _163_527 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p), (false)))::[])))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _163_527))
in Some (((sc), (p))))))
end
| (FStar_Syntax_Syntax.Tm_app (_66_1351, args), FStar_Syntax_Syntax.Pat_cons (_66_1356, pats)) -> begin
(

let tupn = (let _163_528 = (FStar_Syntax_Util.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _163_528 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (let _163_535 = (let _163_534 = (let _163_533 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (let _163_532 = (let _163_531 = (let _163_530 = (let _163_529 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _163_529))
in (_163_530)::[])
in (FStar_List.append args _163_531))
in ((_163_533), (_163_532))))
in FStar_Syntax_Syntax.Tm_app (_163_534))
in (mk _163_535))
in (

let p = (let _163_536 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p), (false)))::[])))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _163_536))
in Some (((sc), (p))))))
end
| _66_1365 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt)))
end)
in (match (_66_1369) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end)))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = rng; FStar_Parser_AST.level = _66_1371}, phi, _66_1378) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(

let phi = (desugar_formula env phi)
in (

let a = (FStar_Ident.set_lid_range a rng)
in (let _163_544 = (let _163_543 = (let _163_542 = (FStar_Syntax_Syntax.fvar a FStar_Syntax_Syntax.Delta_equational None)
in (let _163_541 = (let _163_540 = (FStar_Syntax_Syntax.as_arg phi)
in (let _163_539 = (let _163_538 = (let _163_537 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _163_537))
in (_163_538)::[])
in (_163_540)::_163_539))
in ((_163_542), (_163_541))))
in FStar_Syntax_Syntax.Tm_app (_163_543))
in (mk _163_544))))
end
| FStar_Parser_AST.App (_66_1384, _66_1386, FStar_Parser_AST.UnivApp) -> begin
(

let rec aux = (fun universes e -> (match ((let _163_549 = (unparen e)
in _163_549.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, FStar_Parser_AST.UnivApp) -> begin
(

let univ_arg = (desugar_universe t)
in (aux ((univ_arg)::universes) e))
end
| _66_1400 -> begin
(

let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_uinst (((head), (universes))))))
end))
in (aux [] top))
end
| FStar_Parser_AST.App (_66_1403) -> begin
(

let rec aux = (fun args e -> (match ((let _163_554 = (unparen e)
in _163_554.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) when (imp <> FStar_Parser_AST.UnivApp) -> begin
(

let arg = (let _163_555 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _163_555))
in (aux ((arg)::args) e))
end
| _66_1415 -> begin
(

let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app (((head), (args))))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _163_558 = (let _163_557 = (let _163_556 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((_163_556), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))
in FStar_Syntax_Syntax.Tm_meta (_163_557))
in (mk _163_558))
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

let ds_let_rec_or_app = (fun _66_1437 -> (match (()) with
| () -> begin
(

let bindings = (((pat), (_snd)))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _66_1441 -> (match (_66_1441) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _163_562 = (destruct_app_pattern env top_level p)
in ((_163_562), (def)))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _163_563 = (destruct_app_pattern env top_level p)
in ((_163_563), (def)))
end
| _66_1447 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _66_1452); FStar_Parser_AST.prange = _66_1449}, t) -> begin
if top_level then begin
(let _163_566 = (let _163_565 = (let _163_564 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_163_564))
in ((_163_565), ([]), (Some (t))))
in ((_163_566), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (Some (t)))), (def))
end
end
| FStar_Parser_AST.PatVar (id, _66_1461) -> begin
if top_level then begin
(let _163_569 = (let _163_568 = (let _163_567 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_163_567))
in ((_163_568), ([]), (None)))
in ((_163_569), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (None))), (def))
end
end
| _66_1465 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end
end))))
in (

let _66_1494 = (FStar_List.fold_left (fun _66_1470 _66_1479 -> (match (((_66_1470), (_66_1479))) with
| ((env, fnames, rec_bindings), ((f, _66_1473, _66_1475), _66_1478)) -> begin
(

let _66_1490 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let _66_1484 = (FStar_Parser_Env.push_bv env x)
in (match (_66_1484) with
| (env, xx) -> begin
(let _163_573 = (let _163_572 = (FStar_Syntax_Syntax.mk_binder xx)
in (_163_572)::rec_bindings)
in ((env), (FStar_Util.Inl (xx)), (_163_573)))
end))
end
| FStar_Util.Inr (l) -> begin
(let _163_574 = (FStar_Parser_Env.push_top_level_rec_binding env l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in ((_163_574), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (_66_1490) with
| (env, lbname, rec_bindings) -> begin
((env), ((lbname)::fnames), (rec_bindings))
end))
end)) ((env), ([]), ([])) funs)
in (match (_66_1494) with
| (env', fnames, rec_bindings) -> begin
(

let fnames = (FStar_List.rev fnames)
in (

let desugar_one_def = (fun env lbname _66_1505 -> (match (_66_1505) with
| ((_66_1500, args, result_t), def) -> begin
(

let args = (FStar_All.pipe_right args (FStar_List.map replace_unit_pattern))
in (

let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(

let _66_1514 = if (is_comp_type env t) then begin
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
in (let _163_582 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t)))) _163_582 FStar_Parser_AST.Expr)))
end)
in (

let def = (match (args) with
| [] -> begin
def
end
| _66_1519 -> begin
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
(let _163_584 = (let _163_583 = (FStar_Syntax_Util.incr_delta_qualifier body)
in (FStar_Syntax_Syntax.lid_as_fv l _163_583 None))
in FStar_Util.Inr (_163_584))
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
in (let _163_587 = (let _163_586 = (let _163_585 = (FStar_Syntax_Subst.close rec_bindings body)
in ((((is_rec), (lbs))), (_163_585)))
in FStar_Syntax_Syntax.Tm_let (_163_586))
in (FStar_All.pipe_left mk _163_587))))))
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

let _66_1540 = (desugar_binding_pat_maybe_top top_level env pat is_mutable)
in (match (_66_1540) with
| (env, binder, pat) -> begin
(

let tm = (match (binder) with
| LetBinder (l, t) -> begin
(

let body = (desugar_term env t2)
in (

let fv = (let _163_594 = (FStar_Syntax_Util.incr_delta_qualifier t1)
in (FStar_Syntax_Syntax.lid_as_fv l _163_594 None))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((((false), (({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]))), (body)))))))
end
| LocalBinder (x, _66_1549) -> begin
(

let body = (desugar_term env t2)
in (

let body = (match (pat) with
| (None) | (Some ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (_); FStar_Syntax_Syntax.ty = _; FStar_Syntax_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _163_599 = (let _163_598 = (let _163_597 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _163_596 = (let _163_595 = (FStar_Syntax_Util.branch ((pat), (None), (body)))
in (_163_595)::[])
in ((_163_597), (_163_596))))
in FStar_Syntax_Syntax.Tm_match (_163_598))
in (FStar_Syntax_Syntax.mk _163_599 None body.FStar_Syntax_Syntax.pos))
end)
in (let _163_604 = (let _163_603 = (let _163_602 = (let _163_601 = (let _163_600 = (FStar_Syntax_Syntax.mk_binder x)
in (_163_600)::[])
in (FStar_Syntax_Subst.close _163_601 body))
in ((((false), (((mk_lb ((FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t1))))::[]))), (_163_602)))
in FStar_Syntax_Syntax.Tm_let (_163_603))
in (FStar_All.pipe_left mk _163_604))))
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
in (let _163_615 = (let _163_614 = (let _163_613 = (desugar_term env t1)
in (let _163_612 = (let _163_611 = (let _163_606 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (let _163_605 = (desugar_term env t2)
in ((_163_606), (None), (_163_605))))
in (let _163_610 = (let _163_609 = (let _163_608 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (let _163_607 = (desugar_term env t3)
in ((_163_608), (None), (_163_607))))
in (_163_609)::[])
in (_163_611)::_163_610))
in ((_163_613), (_163_612))))
in FStar_Syntax_Syntax.Tm_match (_163_614))
in (mk _163_615)))
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

let desugar_branch = (fun _66_1590 -> (match (_66_1590) with
| (pat, wopt, b) -> begin
(

let _66_1593 = (desugar_match_pat env pat)
in (match (_66_1593) with
| (env, pat) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _163_618 = (desugar_term env e)
in Some (_163_618))
end)
in (

let b = (desugar_term env b)
in (FStar_Syntax_Util.branch ((pat), (wopt), (b)))))
end))
end))
in (let _163_622 = (let _163_621 = (let _163_620 = (desugar_term env e)
in (let _163_619 = (FStar_List.map desugar_branch branches)
in ((_163_620), (_163_619))))
in FStar_Syntax_Syntax.Tm_match (_163_621))
in (FStar_All.pipe_left mk _163_622)))
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
in (let _163_625 = (let _163_624 = (let _163_623 = (desugar_term env e)
in ((_163_623), (annot), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (_163_624))
in (FStar_All.pipe_left mk _163_625)))))
end
| FStar_Parser_AST.Record (_66_1607, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let record = (check_fields env fields top.FStar_Parser_AST.range)
in (

let user_ns = (

let _66_1619 = (FStar_List.hd fields)
in (match (_66_1619) with
| (f, _66_1618) -> begin
f.FStar_Ident.ns
end))
in (

let get_field = (fun xopt f -> (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _66_1627 -> (match (_66_1627) with
| (g, _66_1626) -> begin
(f.FStar_Ident.idText = g.FStar_Ident.ident.FStar_Ident.idText)
end))))
in (

let fn = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((f)::[])))
in (match (found) with
| Some (_66_1631, e) -> begin
((fn), (e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _163_633 = (let _163_632 = (let _163_631 = (FStar_Util.format2 "Field %s of record type %s is missing" f.FStar_Ident.idText record.FStar_Parser_Env.typename.FStar_Ident.str)
in ((_163_631), (top.FStar_Parser_AST.range)))
in FStar_Syntax_Syntax.Error (_163_632))
in (Prims.raise _163_633))
end
| Some (x) -> begin
((fn), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Project (((x), (fn)))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end))))
in (

let user_constrname = (FStar_Ident.lid_of_ids (FStar_List.append user_ns ((record.FStar_Parser_Env.constrname)::[])))
in (

let recterm = (match (eopt) with
| None -> begin
(let _163_638 = (let _163_637 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _66_1644 -> (match (_66_1644) with
| (f, _66_1643) -> begin
(let _163_636 = (let _163_635 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _163_635))
in ((_163_636), (FStar_Parser_AST.Nothing)))
end))))
in ((user_constrname), (_163_637)))
in FStar_Parser_AST.Construct (_163_638))
end
| Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (let _163_640 = (let _163_639 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_163_639))
in (FStar_Parser_AST.mk_term _163_640 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record = (let _163_643 = (let _163_642 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _66_1652 -> (match (_66_1652) with
| (f, _66_1651) -> begin
(get_field (Some (xterm)) f)
end))))
in ((None), (_163_642)))
in FStar_Parser_AST.Record (_163_643))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _66_1668; FStar_Syntax_Syntax.pos = _66_1666; FStar_Syntax_Syntax.vars = _66_1664}, args); FStar_Syntax_Syntax.tk = _66_1662; FStar_Syntax_Syntax.pos = _66_1660; FStar_Syntax_Syntax.vars = _66_1658}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(

let e = (let _163_650 = (let _163_649 = (let _163_648 = (let _163_647 = (let _163_646 = (let _163_645 = (let _163_644 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_Env.typename), (_163_644)))
in FStar_Syntax_Syntax.Record_ctor (_163_645))
in Some (_163_646))
in (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant _163_647))
in ((_163_648), (args)))
in FStar_Syntax_Syntax.Tm_app (_163_649))
in (FStar_All.pipe_left mk _163_650))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))))))
end
| _66_1682 -> begin
e
end))))))))
end
| FStar_Parser_AST.Project (e, f) -> begin
(

let _66_1689 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_dc_by_field_name env) f)
in (match (_66_1689) with
| (constrname, is_rec) -> begin
(

let e = (desugar_term env e)
in (

let projname = (FStar_Syntax_Util.mk_field_projector_name_from_ident constrname f.FStar_Ident.ident)
in (

let qual = if is_rec then begin
Some (FStar_Syntax_Syntax.Record_projector (((constrname), (f.FStar_Ident.ident))))
end else begin
None
end
in (let _163_655 = (let _163_654 = (let _163_653 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range projname (FStar_Ident.range_of_lid f)) FStar_Syntax_Syntax.Delta_equational qual)
in (let _163_652 = (let _163_651 = (FStar_Syntax_Syntax.as_arg e)
in (_163_651)::[])
in ((_163_653), (_163_652))))
in FStar_Syntax_Syntax.Tm_app (_163_654))
in (FStar_All.pipe_left mk _163_655)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| _66_1700 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _66_1702 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Let (_66_1704, _66_1706, _66_1708) -> begin
(FStar_All.failwith "Not implemented yet")
end
| FStar_Parser_AST.QForall (_66_1712, _66_1714, _66_1716) -> begin
(FStar_All.failwith "Not implemented yet")
end
| FStar_Parser_AST.QExists (_66_1720, _66_1722, _66_1724) -> begin
(FStar_All.failwith "Not implemented yet")
end))))
and desugar_args : FStar_Parser_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun _66_1731 -> (match (_66_1731) with
| (a, imp) -> begin
(let _163_659 = (desugar_term env a)
in (arg_withimp_e imp _163_659))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r default_ok env t -> (

let fail = (fun msg -> (Prims.raise (FStar_Syntax_Syntax.Error (((msg), (r))))))
in (

let is_requires = (fun _66_1743 -> (match (_66_1743) with
| (t, _66_1742) -> begin
(match ((let _163_667 = (unparen t)
in _163_667.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Requires (_66_1745) -> begin
true
end
| _66_1748 -> begin
false
end)
end))
in (

let is_ensures = (fun _66_1753 -> (match (_66_1753) with
| (t, _66_1752) -> begin
(match ((let _163_670 = (unparen t)
in _163_670.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ensures (_66_1755) -> begin
true
end
| _66_1758 -> begin
false
end)
end))
in (

let is_app = (fun head _66_1764 -> (match (_66_1764) with
| (t, _66_1763) -> begin
(match ((let _163_675 = (unparen t)
in _163_675.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _66_1768; FStar_Parser_AST.level = _66_1766}, _66_1773, _66_1775) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| _66_1779 -> begin
false
end)
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t -> (

let _66_1785 = (head_and_args t)
in (match (_66_1785) with
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
(let _163_679 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_name_and_attributes env) l)
in ((_163_679), (args)))
end
| FStar_Parser_AST.Name (l) when ((let _163_680 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _163_680 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when ((let _163_681 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _163_681 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)), ([]))), (args))
end
| FStar_Parser_AST.Name (l) when ((((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) && default_ok) -> begin
(((((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)), ([]))), ((((t), (FStar_Parser_AST.Nothing)))::[]))
end
| _66_1816 when default_ok -> begin
(((((FStar_Ident.set_lid_range env.FStar_Parser_Env.default_result_effect head.FStar_Parser_AST.range)), ([]))), ((((t), (FStar_Parser_AST.Nothing)))::[]))
end
| _66_1818 -> begin
(let _163_683 = (let _163_682 = (FStar_Parser_AST.term_to_string t)
in (FStar_Util.format1 "%s is not an effect" _163_682))
in (fail _163_683))
end)
end)))
in (

let _66_1823 = (pre_process_comp_typ t)
in (match (_66_1823) with
| ((eff, cattributes), args) -> begin
(

let _66_1824 = if ((FStar_List.length args) = (Prims.parse_int "0")) then begin
(let _163_685 = (let _163_684 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" _163_684))
in (fail _163_685))
end else begin
()
end
in (

let _66_1828 = (let _163_687 = (FStar_List.hd args)
in (let _163_686 = (FStar_List.tl args)
in ((_163_687), (_163_686))))
in (match (_66_1828) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (Prims.fst result_arg))
in (

let rest = (desugar_args env rest)
in (

let _66_1853 = (FStar_All.pipe_right rest (FStar_List.partition (fun _66_1834 -> (match (_66_1834) with
| (t, _66_1833) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _66_1840; FStar_Syntax_Syntax.pos = _66_1838; FStar_Syntax_Syntax.vars = _66_1836}, (_66_1845)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| _66_1850 -> begin
false
end)
end))))
in (match (_66_1853) with
| (dec, rest) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _66_1857 -> (match (_66_1857) with
| (t, _66_1856) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_66_1859, ((arg, _66_1862))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| _66_1868 -> begin
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

let pattern = (let _163_690 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.mk_Tm_uinst _163_690 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app nil ((((pattern), (Some (FStar_Syntax_Syntax.imp_tag))))::[]) None pat.FStar_Syntax_Syntax.pos)))
end
| _66_1884 -> begin
pat
end)
in (let _163_694 = (let _163_693 = (let _163_692 = (let _163_691 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) None pat.FStar_Syntax_Syntax.pos)
in ((_163_691), (aq)))
in (_163_692)::[])
in (ens)::_163_693)
in (req)::_163_694))
end
| _66_1887 -> begin
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
| _66_1899 -> begin
None
end))
in (

let mk = (fun t -> (FStar_Syntax_Syntax.mk t None f.FStar_Parser_AST.range))
in (

let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let _66_1906 = t
in {FStar_Syntax_Syntax.n = _66_1906.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _66_1906.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _66_1906.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let _66_1913 = b
in {FStar_Parser_AST.b = _66_1913.FStar_Parser_AST.b; FStar_Parser_AST.brange = _66_1913.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _66_1913.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _163_729 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _163_729)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(

let _66_1927 = (FStar_Parser_Env.push_bv env a)
in (match (_66_1927) with
| (env, a) -> begin
(

let a = (

let _66_1928 = a
in {FStar_Syntax_Syntax.ppname = _66_1928.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_1928.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats = (desugar_pats env pats)
in (

let body = (desugar_formula env body)
in (

let body = (match (pats) with
| [] -> begin
body
end
| _66_1935 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta (((body), (FStar_Syntax_Syntax.Meta_pattern (pats))))))
end)
in (

let body = (let _163_732 = (let _163_731 = (let _163_730 = (FStar_Syntax_Syntax.mk_binder a)
in (_163_730)::[])
in (no_annot_abs _163_731 body))
in (FStar_All.pipe_left setpos _163_732))
in (let _163_737 = (let _163_736 = (let _163_735 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (let _163_734 = (let _163_733 = (FStar_Syntax_Syntax.as_arg body)
in (_163_733)::[])
in ((_163_735), (_163_734))))
in FStar_Syntax_Syntax.Tm_app (_163_736))
in (FStar_All.pipe_left mk _163_737)))))))
end))
end
| _66_1939 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body = (let _163_752 = (q ((rest), (pats), (body)))
in (let _163_751 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _163_752 _163_751 FStar_Parser_AST.Formula)))
in (let _163_753 = (q (((b)::[]), ([]), (body)))
in (FStar_Parser_AST.mk_term _163_753 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _66_1953 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _163_754 = (unparen f)
in _163_754.FStar_Parser_AST.tm)) with
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
in (let _163_756 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _163_756)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _163_758 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _163_758)))
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
| _66_2011 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (

let _66_2035 = (FStar_List.fold_left (fun _66_2016 b -> (match (_66_2016) with
| (env, out) -> begin
(

let tk = (desugar_binder env (

let _66_2018 = b
in {FStar_Parser_AST.b = _66_2018.FStar_Parser_AST.b; FStar_Parser_AST.brange = _66_2018.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _66_2018.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(

let _66_2027 = (FStar_Parser_Env.push_bv env a)
in (match (_66_2027) with
| (env, a) -> begin
(

let a = (

let _66_2028 = a
in {FStar_Syntax_Syntax.ppname = _66_2028.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_2028.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in ((env), ((((a), ((trans_aqual b.FStar_Parser_AST.aqual))))::out)))
end))
end
| _66_2032 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (_66_2035) with
| (env, tpars) -> begin
((env), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(let _163_765 = (desugar_typ env t)
in ((Some (x)), (_163_765)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _163_766 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None x.FStar_Ident.idRange)
in ((Some (x)), (_163_766)))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _163_767 = (desugar_typ env t)
in ((None), (_163_767)))
end
| FStar_Parser_AST.Variable (x) -> begin
((Some (x)), (FStar_Syntax_Syntax.tun))
end))


let mk_data_discriminators = (fun quals env t tps k datas -> (

let quals = (FStar_All.pipe_right quals (FStar_List.filter (fun _66_14 -> (match (_66_14) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| _66_2060 -> begin
false
end))))
in (

let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_Env.iface) || env.FStar_Parser_Env.admitted_iface) then begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (let _163_779 = (let _163_778 = (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in ((disc_name), ([]), (FStar_Syntax_Syntax.tun), (_163_778), ((FStar_Ident.range_of_lid disc_name))))
in FStar_Syntax_Syntax.Sig_declare_typ (_163_779)))))))))


let mk_indexed_projector_names : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  FStar_Parser_Env.env  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq env lid fields -> (

let p = (FStar_Ident.range_of_lid lid)
in (let _163_807 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _66_2076 -> (match (_66_2076) with
| (x, _66_2075) -> begin
(

let _66_2080 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_66_2080) with
| (field_name, _66_2079) -> begin
(

let only_decl = (((let _163_792 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _163_792)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _163_794 = (let _163_793 = (FStar_Parser_Env.current_module env)
in _163_793.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _163_794)))
in (

let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (

let quals = (fun q -> if only_decl then begin
(let _163_798 = (FStar_List.filter (fun _66_15 -> (match (_66_15) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| _66_2088 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::_163_798)
end else begin
q
end)
in (

let quals = (

let iquals = (FStar_All.pipe_right iquals (FStar_List.filter (fun _66_16 -> (match (_66_16) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| _66_2093 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.OnlyName)::(FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals)))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), ([]), (FStar_Syntax_Syntax.tun), (quals), ((FStar_Ident.range_of_lid field_name))))
in if only_decl then begin
(decl)::[]
end else begin
(

let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end else begin
FStar_Syntax_Syntax.Delta_equational
end
in (

let lb = (let _163_801 = (let _163_800 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (_163_800))
in {FStar_Syntax_Syntax.lbname = _163_801; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = FStar_Syntax_Syntax.tun})
in (

let impl = (let _163_806 = (let _163_805 = (let _163_804 = (let _163_803 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _163_803 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_163_804)::[])
in ((((false), ((lb)::[]))), (p), (_163_805), (quals)))
in FStar_Syntax_Syntax.Sig_let (_163_806))
in if no_decl then begin
(impl)::[]
end else begin
(decl)::(impl)::[]
end)))
end)))))
end))
end))))
in (FStar_All.pipe_right _163_807 FStar_List.flatten))))


let mk_data_projector_names = (fun iquals env _66_2105 -> (match (_66_2105) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _66_2108, t, _66_2111, n, quals, _66_2115, _66_2117) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let _66_2123 = (FStar_Syntax_Util.arrow_formals t)
in (match (_66_2123) with
| (formals, _66_2122) -> begin
(match (formals) with
| [] -> begin
[]
end
| _66_2126 -> begin
(

let filter_records = (fun _66_17 -> (match (_66_17) with
| FStar_Syntax_Syntax.RecordConstructor (_66_2129, fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| _66_2134 -> begin
None
end))
in (

let fv_qual = (match ((FStar_Util.find_map quals filter_records)) with
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

let _66_2144 = (FStar_Util.first_N n formals)
in (match (_66_2144) with
| (_66_2142, rest) -> begin
(mk_indexed_projector_names iquals fv_qual env lid rest)
end)))))
end)
end))
end
| _66_2146 -> begin
[]
end)
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (

let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _163_829 = (FStar_Syntax_Util.incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (_163_829))
end else begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end
in (

let lb = (let _163_834 = (let _163_830 = (FStar_Syntax_Syntax.lid_as_fv lid dd None)
in FStar_Util.Inr (_163_830))
in (let _163_833 = (let _163_831 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars _163_831))
in (let _163_832 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = _163_834; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = _163_833; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _163_832})))
in FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (rng), (lids), (quals))))))


let rec desugar_tycon : FStar_Parser_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (

let tycon_id = (fun _66_18 -> (match (_66_18) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _163_848 = (let _163_847 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_163_847))
in (FStar_Parser_AST.mk_term _163_848 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
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
| _66_2221 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _163_861 = (let _163_860 = (let _163_859 = (binder_to_term b)
in ((out), (_163_859), ((imp_of_aqual b))))
in FStar_Parser_AST.App (_163_860))
in (FStar_Parser_AST.mk_term _163_861 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun _66_19 -> (match (_66_19) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun _66_2236 -> (match (_66_2236) with
| (x, t, _66_2235) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Syntax_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (

let result = (let _163_867 = (let _163_866 = (let _163_865 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_163_865))
in (FStar_Parser_AST.mk_term _163_866 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _163_867 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _163_869 = (FStar_All.pipe_right fields (FStar_List.map (fun _66_2245 -> (match (_66_2245) with
| (x, _66_2242, _66_2244) -> begin
(FStar_Syntax_Util.unmangle_field_name x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (Some (constrTyp)), (None), (false)))::[])))), (_163_869)))))))
end
| _66_2247 -> begin
(FStar_All.failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals _env mutuals _66_20 -> (match (_66_20) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let _66_2261 = (typars_of_binders _env binders)
in (match (_66_2261) with
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

let tconstr = (let _163_880 = (let _163_879 = (let _163_878 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_163_878))
in (FStar_Parser_AST.mk_term _163_879 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _163_880 binders))
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
| _66_2274 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env bs -> (

let _66_2289 = (FStar_List.fold_left (fun _66_2280 _66_2283 -> (match (((_66_2280), (_66_2283))) with
| ((env, tps), (x, imp)) -> begin
(

let _66_2286 = (FStar_Parser_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (_66_2286) with
| (env, y) -> begin
((env), ((((y), (imp)))::tps))
end))
end)) ((env), ([])) bs)
in (match (_66_2289) with
| (env, bs) -> begin
((env), ((FStar_List.rev bs)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id, bs, kopt))::[] -> begin
(

let kopt = (match (kopt) with
| None -> begin
(let _163_887 = (tm_type_z id.FStar_Ident.idRange)
in Some (_163_887))
end
| _66_2298 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id), (bs), (kopt)))
in (

let _66_2308 = (desugar_abstract_tc quals env [] tc)
in (match (_66_2308) with
| (_66_2302, _66_2304, se, _66_2307) -> begin
(

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _66_2311, typars, k, [], [], quals, rng) -> begin
(

let quals = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
quals
end else begin
(

let _66_2320 = (let _163_889 = (FStar_Range.string_of_range rng)
in (let _163_888 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" _163_889 _163_888)))
in (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals)
end
in (

let t = (match (typars) with
| [] -> begin
k
end
| _66_2325 -> begin
(let _163_892 = (let _163_891 = (let _163_890 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (_163_890)))
in FStar_Syntax_Syntax.Tm_arrow (_163_891))
in (FStar_Syntax_Syntax.mk _163_892 None rng))
end)
in FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t), (quals), (rng)))))
end
| _66_2328 -> begin
se
end)
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in ((env), ((se)::[]))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let _66_2340 = (typars_of_binders env binders)
in (match (_66_2340) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _66_21 -> (match (_66_21) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| _66_2345 -> begin
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

let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _66_22 -> (match (_66_22) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| _66_2353 -> begin
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

let _66_2378 = (match ((let _163_895 = (unparen t)
in _163_895.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Construct (head, args) -> begin
(

let _66_2373 = (match ((FStar_List.rev args)) with
| ((last_arg, _66_2362))::args_rev -> begin
(match ((let _163_896 = (unparen last_arg)
in _163_896.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| _66_2368 -> begin
(([]), (args))
end)
end
| _66_2370 -> begin
(([]), (args))
end)
in (match (_66_2373) with
| (cattributes, args) -> begin
(let _163_897 = (desugar_attributes env cattributes)
in (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct (((head), (args)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (_163_897)))
end))
end
| _66_2375 -> begin
((t), ([]))
end)
in (match (_66_2378) with
| (t, cattributes) -> begin
(

let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (

let typars = (FStar_Syntax_Subst.close_binders typars)
in (

let c = (FStar_Syntax_Subst.close_comp typars c)
in (let _163_901 = (let _163_900 = (FStar_Parser_Env.qualify env id)
in (let _163_899 = (FStar_All.pipe_right quals (FStar_List.filter (fun _66_23 -> (match (_66_23) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| _66_2385 -> begin
true
end))))
in ((_163_900), ([]), (typars), (c), (_163_899), ((FStar_List.append cattributes (FStar_Syntax_Util.comp_flags c))), (rng))))
in FStar_Syntax_Syntax.Sig_effect_abbrev (_163_901)))))
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
| (FStar_Parser_AST.TyconRecord (_66_2391))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let _66_2397 = (tycon_record_as_variant trec)
in (match (_66_2397) with
| (t, fs) -> begin
(let _163_906 = (let _163_905 = (let _163_904 = (let _163_903 = (let _163_902 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.ids_of_lid _163_902))
in ((_163_903), (fs)))
in FStar_Syntax_Syntax.RecordType (_163_904))
in (_163_905)::quals)
in (desugar_tycon env rng _163_906 ((t)::[])))
end)))
end
| (_66_2401)::_66_2399 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_Env.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals et tc -> (

let _66_2412 = et
in (match (_66_2412) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_66_2414) -> begin
(

let trec = tc
in (

let _66_2419 = (tycon_record_as_variant trec)
in (match (_66_2419) with
| (t, fs) -> begin
(let _163_918 = (let _163_917 = (let _163_916 = (let _163_915 = (let _163_914 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.ids_of_lid _163_914))
in ((_163_915), (fs)))
in FStar_Syntax_Syntax.RecordType (_163_916))
in (_163_917)::quals)
in (collect_tcs _163_918 ((env), (tcs)) t))
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let _66_2431 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_66_2431) with
| (env, _66_2428, se, tconstr) -> begin
((env), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals))))::tcs))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let _66_2443 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_66_2443) with
| (env, _66_2440, se, tconstr) -> begin
((env), ((FStar_Util.Inr (((se), (t), (quals))))::tcs))
end))
end
| _66_2445 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (

let _66_2448 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (_66_2448) with
| (env, tcs) -> begin
(

let tcs = (FStar_List.rev tcs)
in (

let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _66_25 -> (match (_66_25) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, _66_2456, _66_2458, _66_2460, _66_2462), t, quals) -> begin
(

let _66_2472 = (push_tparams env tpars)
in (match (_66_2472) with
| (env_tps, _66_2471) -> begin
(

let t = (desugar_term env_tps t)
in (let _163_921 = (let _163_920 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in (([]), (_163_920)))
in (_163_921)::[]))
end))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, _66_2480, tags, _66_2483), constrs, tconstr, quals) -> begin
(

let tycon = ((tname), (tpars), (k))
in (

let _66_2494 = (push_tparams env tpars)
in (match (_66_2494) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun _66_2498 -> (match (_66_2498) with
| (x, _66_2497) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let _66_2524 = (let _163_933 = (FStar_All.pipe_right constrs (FStar_List.map (fun _66_2505 -> (match (_66_2505) with
| (id, topt, _66_2503, of_notation) -> begin
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

let t = (let _163_925 = (FStar_Parser_Env.default_total env_tps)
in (let _163_924 = (close env_tps t)
in (desugar_term _163_925 _163_924)))
in (

let name = (FStar_Parser_Env.qualify env id)
in (

let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _66_24 -> (match (_66_24) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| _66_2519 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (let _163_932 = (let _163_931 = (let _163_930 = (let _163_929 = (let _163_928 = (let _163_927 = (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total _163_927))
in (FStar_Syntax_Util.arrow data_tpars _163_928))
in ((name), (univs), (_163_929), (tname), (ntps), (quals), (mutuals), (rng)))
in FStar_Syntax_Syntax.Sig_datacon (_163_930))
in ((tps), (_163_931)))
in ((name), (_163_932))))))))
end))))
in (FStar_All.pipe_left FStar_List.split _163_933))
in (match (_66_2524) with
| (constrNames, constrs) -> begin
((([]), (FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs), (tpars), (k), (mutuals), (constrNames), (tags), (rng))))))::constrs
end)))
end)))
end
| _66_2526 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (

let bundle = (let _163_935 = (let _163_934 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in ((sigelts), (quals), (_163_934), (rng)))
in FStar_Syntax_Syntax.Sig_bundle (_163_935))
in (

let env = (FStar_Parser_Env.push_sigelt env0 bundle)
in (

let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projector_names quals env)))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _66_26 -> (match (_66_26) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, _66_2535, tps, k, _66_2539, constrs, quals, _66_2543) when ((FStar_List.length constrs) > (Prims.parse_int "1")) -> begin
(

let quals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract quals) then begin
(FStar_Syntax_Syntax.Private)::quals
end else begin
quals
end
in (mk_data_discriminators quals env tname tps k constrs))
end
| _66_2548 -> begin
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

let _66_2572 = (FStar_List.fold_left (fun _66_2557 b -> (match (_66_2557) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| (Some (a), k) -> begin
(

let _66_2565 = (FStar_Parser_Env.push_bv env a)
in (match (_66_2565) with
| (env, a) -> begin
(let _163_944 = (let _163_943 = (FStar_Syntax_Syntax.mk_binder (

let _66_2566 = a
in {FStar_Syntax_Syntax.ppname = _66_2566.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _66_2566.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (_163_943)::binders)
in ((env), (_163_944)))
end))
end
| _66_2569 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end)
end)) ((env), ([])) binders)
in (match (_66_2572) with
| (env, binders) -> begin
((env), ((FStar_List.rev binders)))
end)))


let rec desugar_effect : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  Prims.bool  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_kind eff_decls actions for_free -> (

let env0 = env
in (

let monad_env = (FStar_Parser_Env.enter_monad_scope env eff_name)
in (

let _66_2586 = (desugar_binders monad_env eff_binders)
in (match (_66_2586) with
| (env, binders) -> begin
(

let eff_k = (let _163_982 = (FStar_Parser_Env.default_total env)
in (desugar_term _163_982 eff_kind))
in (

let _66_2597 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _66_2590 decl -> (match (_66_2590) with
| (env, out) -> begin
(

let _66_2594 = (desugar_decl env decl)
in (match (_66_2594) with
| (env, ses) -> begin
(let _163_986 = (let _163_985 = (FStar_List.hd ses)
in (_163_985)::out)
in ((env), (_163_986)))
end))
end)) ((env), ([]))))
in (match (_66_2597) with
| (env, decls) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let actions = (FStar_All.pipe_right actions (FStar_List.map (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (_66_2601, ((FStar_Parser_AST.TyconAbbrev (name, _66_2604, _66_2606, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (_66_2612, ((def, _66_2619))::((cps_type, _66_2615))::[]); FStar_Parser_AST.range = _66_2610; FStar_Parser_AST.level = _66_2608}), _66_2628))::[]) when (not (for_free)) -> begin
(let _163_992 = (FStar_Parser_Env.qualify env name)
in (let _163_991 = (let _163_988 = (desugar_term env def)
in (FStar_Syntax_Subst.close binders _163_988))
in (let _163_990 = (let _163_989 = (desugar_typ env cps_type)
in (FStar_Syntax_Subst.close binders _163_989))
in {FStar_Syntax_Syntax.action_name = _163_992; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = _163_991; FStar_Syntax_Syntax.action_typ = _163_990})))
end
| FStar_Parser_AST.Tycon (_66_2634, ((FStar_Parser_AST.TyconAbbrev (name, _66_2637, _66_2639, defn), _66_2644))::[]) when for_free -> begin
(let _163_995 = (FStar_Parser_Env.qualify env name)
in (let _163_994 = (let _163_993 = (desugar_term env defn)
in (FStar_Syntax_Subst.close binders _163_993))
in {FStar_Syntax_Syntax.action_name = _163_995; FStar_Syntax_Syntax.action_unqualified_name = name; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = _163_994; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
end
| _66_2650 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples)."), (d.FStar_Parser_AST.drange)))))
end))))
in (

let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (

let lookup = (fun s -> (

let l = (FStar_Parser_Env.qualify env (FStar_Ident.mk_ident ((s), (d.FStar_Parser_AST.drange))))
in (let _163_999 = (let _163_998 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) _163_998))
in (([]), (_163_999)))))
in (

let mname = (FStar_Parser_Env.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange (Some (mname))) quals)
in (

let se = if for_free then begin
(

let dummy_tscheme = (let _163_1000 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (([]), (_163_1000)))
in (let _163_1006 = (let _163_1005 = (let _163_1004 = (let _163_1001 = (lookup "repr")
in (Prims.snd _163_1001))
in (let _163_1003 = (lookup "return")
in (let _163_1002 = (lookup "bind")
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = _163_1004; FStar_Syntax_Syntax.return_repr = _163_1003; FStar_Syntax_Syntax.bind_repr = _163_1002; FStar_Syntax_Syntax.actions = actions})))
in ((_163_1005), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (_163_1006)))
end else begin
(

let rr = ((FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) || (FStar_All.pipe_right qualifiers FStar_Syntax_Syntax.contains_reflectable))
in (

let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in (let _163_1022 = (let _163_1021 = (let _163_1020 = (lookup "return_wp")
in (let _163_1019 = (lookup "bind_wp")
in (let _163_1018 = (lookup "if_then_else")
in (let _163_1017 = (lookup "ite_wp")
in (let _163_1016 = (lookup "stronger")
in (let _163_1015 = (lookup "close_wp")
in (let _163_1014 = (lookup "assert_p")
in (let _163_1013 = (lookup "assume_p")
in (let _163_1012 = (lookup "null_wp")
in (let _163_1011 = (lookup "trivial")
in (let _163_1010 = if rr then begin
(let _163_1007 = (lookup "repr")
in (FStar_All.pipe_left Prims.snd _163_1007))
end else begin
FStar_Syntax_Syntax.tun
end
in (let _163_1009 = if rr then begin
(lookup "return")
end else begin
un_ts
end
in (let _163_1008 = if rr then begin
(lookup "bind")
end else begin
un_ts
end
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.cattributes = []; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = _163_1020; FStar_Syntax_Syntax.bind_wp = _163_1019; FStar_Syntax_Syntax.if_then_else = _163_1018; FStar_Syntax_Syntax.ite_wp = _163_1017; FStar_Syntax_Syntax.stronger = _163_1016; FStar_Syntax_Syntax.close_wp = _163_1015; FStar_Syntax_Syntax.assert_p = _163_1014; FStar_Syntax_Syntax.assume_p = _163_1013; FStar_Syntax_Syntax.null_wp = _163_1012; FStar_Syntax_Syntax.trivial = _163_1011; FStar_Syntax_Syntax.repr = _163_1010; FStar_Syntax_Syntax.return_repr = _163_1009; FStar_Syntax_Syntax.bind_repr = _163_1008; FStar_Syntax_Syntax.actions = actions})))))))))))))
in ((_163_1021), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_new_effect (_163_1022))))
end
in (

let env = (FStar_Parser_Env.push_sigelt env0 se)
in (

let env = (FStar_All.pipe_right actions (FStar_List.fold_left (fun env a -> (let _163_1025 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_Parser_Env.push_sigelt env _163_1025))) env))
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

let _66_2681 = (desugar_binders env eff_binders)
in (match (_66_2681) with
| (env, binders) -> begin
(

let _66_2708 = (

let _66_2684 = (head_and_args defn)
in (match (_66_2684) with
| (head, args) -> begin
(

let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_defn env) l)
end
| _66_2688 -> begin
(let _163_1052 = (let _163_1051 = (let _163_1050 = (let _163_1049 = (let _163_1048 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat _163_1048 " not found"))
in (Prims.strcat "Effect " _163_1049))
in ((_163_1050), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_163_1051))
in (Prims.raise _163_1052))
end)
in (

let _66_2704 = (match ((FStar_List.rev args)) with
| ((last_arg, _66_2693))::args_rev -> begin
(match ((let _163_1053 = (unparen last_arg)
in _163_1053.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Attributes (ts) -> begin
((ts), ((FStar_List.rev args_rev)))
end
| _66_2699 -> begin
(([]), (args))
end)
end
| _66_2701 -> begin
(([]), (args))
end)
in (match (_66_2704) with
| (cattributes, args) -> begin
(let _163_1055 = (desugar_args env args)
in (let _163_1054 = (desugar_attributes env cattributes)
in ((ed), (_163_1055), (_163_1054))))
end)))
end))
in (match (_66_2708) with
| (ed, args, cattributes) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let sub = (fun _66_2714 -> (match (_66_2714) with
| (_66_2712, x) -> begin
(

let _66_2717 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (_66_2717) with
| (edb, x) -> begin
(

let _66_2718 = if ((FStar_List.length args) <> (FStar_List.length edb)) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected number of arguments to effect constructor"), (defn.FStar_Parser_AST.range)))))
end else begin
()
end
in (

let s = (FStar_Syntax_Util.subst_of_list edb args)
in (let _163_1059 = (let _163_1058 = (FStar_Syntax_Subst.subst s x)
in (FStar_Syntax_Subst.close binders _163_1058))
in (([]), (_163_1059)))))
end))
end))
in (

let mname = (FStar_Parser_Env.qualify env0 eff_name)
in (

let ed = (let _163_1084 = (let _163_1060 = (trans_qual (Some (mname)))
in (FStar_List.map _163_1060 quals))
in (let _163_1083 = (let _163_1061 = (sub (([]), (ed.FStar_Syntax_Syntax.signature)))
in (Prims.snd _163_1061))
in (let _163_1082 = (sub ed.FStar_Syntax_Syntax.ret_wp)
in (let _163_1081 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (let _163_1080 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (let _163_1079 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (let _163_1078 = (sub ed.FStar_Syntax_Syntax.stronger)
in (let _163_1077 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (let _163_1076 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (let _163_1075 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (let _163_1074 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (let _163_1073 = (sub ed.FStar_Syntax_Syntax.trivial)
in (let _163_1072 = (let _163_1062 = (sub (([]), (ed.FStar_Syntax_Syntax.repr)))
in (Prims.snd _163_1062))
in (let _163_1071 = (sub ed.FStar_Syntax_Syntax.return_repr)
in (let _163_1070 = (sub ed.FStar_Syntax_Syntax.bind_repr)
in (let _163_1069 = (FStar_List.map (fun action -> (let _163_1068 = (FStar_Parser_Env.qualify env action.FStar_Syntax_Syntax.action_unqualified_name)
in (let _163_1067 = (let _163_1064 = (sub (([]), (action.FStar_Syntax_Syntax.action_defn)))
in (Prims.snd _163_1064))
in (let _163_1066 = (let _163_1065 = (sub (([]), (action.FStar_Syntax_Syntax.action_typ)))
in (Prims.snd _163_1065))
in {FStar_Syntax_Syntax.action_name = _163_1068; FStar_Syntax_Syntax.action_unqualified_name = action.FStar_Syntax_Syntax.action_unqualified_name; FStar_Syntax_Syntax.action_univs = action.FStar_Syntax_Syntax.action_univs; FStar_Syntax_Syntax.action_defn = _163_1067; FStar_Syntax_Syntax.action_typ = _163_1066})))) ed.FStar_Syntax_Syntax.actions)
in {FStar_Syntax_Syntax.qualifiers = _163_1084; FStar_Syntax_Syntax.cattributes = cattributes; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = _163_1083; FStar_Syntax_Syntax.ret_wp = _163_1082; FStar_Syntax_Syntax.bind_wp = _163_1081; FStar_Syntax_Syntax.if_then_else = _163_1080; FStar_Syntax_Syntax.ite_wp = _163_1079; FStar_Syntax_Syntax.stronger = _163_1078; FStar_Syntax_Syntax.close_wp = _163_1077; FStar_Syntax_Syntax.assert_p = _163_1076; FStar_Syntax_Syntax.assume_p = _163_1075; FStar_Syntax_Syntax.null_wp = _163_1074; FStar_Syntax_Syntax.trivial = _163_1073; FStar_Syntax_Syntax.repr = _163_1072; FStar_Syntax_Syntax.return_repr = _163_1071; FStar_Syntax_Syntax.bind_repr = _163_1070; FStar_Syntax_Syntax.actions = _163_1069}))))))))))))))))
in (

let se = (build_sigelt ed d.FStar_Parser_AST.drange)
in (

let monad_env = env
in (

let env = (FStar_Parser_Env.push_sigelt env0 se)
in (

let env = (FStar_All.pipe_right ed.FStar_Syntax_Syntax.actions (FStar_List.fold_left (fun env a -> (let _163_1087 = (FStar_Syntax_Util.action_as_lb mname a)
in (FStar_Parser_Env.push_sigelt env _163_1087))) env))
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
| FStar_Parser_AST.Fsdoc (_66_2740) -> begin
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
(let _163_1092 = (FStar_Parser_Env.push_module_abbrev env x l)
in ((_163_1092), ([])))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(

let tcs = (FStar_List.map (fun _66_2758 -> (match (_66_2758) with
| (x, _66_2757) -> begin
x
end)) tcs)
in (let _163_1094 = (FStar_List.map (trans_qual None) qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _163_1094 tcs)))
end
| FStar_Parser_AST.TopLevelLet (quals, isrec, lets) -> begin
(match ((let _163_1096 = (let _163_1095 = (desugar_term_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Syntax_Subst.compress _163_1095))
in _163_1096.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let (lbs, _66_2767) -> begin
(

let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals = (match (quals) with
| (_66_2775)::_66_2773 -> begin
(FStar_List.map (trans_qual None) quals)
end
| _66_2778 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _66_27 -> (match (_66_27) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (_66_2789); FStar_Syntax_Syntax.lbunivs = _66_2787; FStar_Syntax_Syntax.lbtyp = _66_2785; FStar_Syntax_Syntax.lbeff = _66_2783; FStar_Syntax_Syntax.lbdef = _66_2781} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _66_2799; FStar_Syntax_Syntax.lbtyp = _66_2797; FStar_Syntax_Syntax.lbeff = _66_2795; FStar_Syntax_Syntax.lbdef = _66_2793} -> begin
(FStar_Parser_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals = if (FStar_All.pipe_right lets (FStar_Util.for_some (fun _66_2807 -> (match (_66_2807) with
| (_66_2805, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end)))) then begin
(FStar_Syntax_Syntax.Logic)::quals
end else begin
quals
end
in (

let lbs = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _163_1101 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _66_2811 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let _66_2813 = fv
in {FStar_Syntax_Syntax.fv_name = _66_2813.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = _66_2813.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = _66_2811.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _66_2811.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _66_2811.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _66_2811.FStar_Syntax_Syntax.lbdef})))))
in (((Prims.fst lbs)), (_163_1101)))
end else begin
lbs
end
in (

let s = (let _163_1104 = (let _163_1103 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in ((lbs), (d.FStar_Parser_AST.drange), (_163_1103), (quals)))
in FStar_Syntax_Syntax.Sig_let (_163_1104))
in (

let env = (FStar_Parser_Env.push_sigelt env s)
in ((env), ((s)::[]))))))))
end
| _66_2820 -> begin
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
in (let _163_1108 = (let _163_1107 = (let _163_1106 = (let _163_1105 = (FStar_Parser_Env.qualify env id)
in ((_163_1105), (f), ((FStar_Syntax_Syntax.Assumption)::[]), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_assume (_163_1106))
in (_163_1107)::[])
in ((env), (_163_1108))))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(

let t = (let _163_1109 = (close_fun env t)
in (desugar_term env _163_1109))
in (

let quals = if (env.FStar_Parser_Env.iface && env.FStar_Parser_Env.admitted_iface) then begin
(FStar_Parser_AST.Assumption)::quals
end else begin
quals
end
in (

let se = (let _163_1112 = (let _163_1111 = (FStar_Parser_Env.qualify env id)
in (let _163_1110 = (FStar_List.map (trans_qual None) quals)
in ((_163_1111), ([]), (t), (_163_1110), (d.FStar_Parser_AST.drange))))
in FStar_Syntax_Syntax.Sig_declare_typ (_163_1112))
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in ((env), ((se)::[]))))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(

let _66_2847 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (match (_66_2847) with
| (t, _66_2846) -> begin
(

let l = (FStar_Parser_Env.qualify env id)
in (

let se = FStar_Syntax_Syntax.Sig_datacon (((l), ([]), (t), (FStar_Syntax_Const.exn_lid), ((Prims.parse_int "0")), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((FStar_Syntax_Const.exn_lid)::[]), (d.FStar_Parser_AST.drange)))
in (

let se' = FStar_Syntax_Syntax.Sig_bundle ((((se)::[]), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((l)::[]), (d.FStar_Parser_AST.drange)))
in (

let env = (FStar_Parser_Env.push_sigelt env se')
in (

let data_ops = (mk_data_projector_names [] env (([]), (se)))
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

let t = (let _163_1117 = (let _163_1113 = (FStar_Syntax_Syntax.null_binder t)
in (_163_1113)::[])
in (let _163_1116 = (let _163_1115 = (let _163_1114 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (Prims.fst _163_1114))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _163_1115))
in (FStar_Syntax_Util.arrow _163_1117 _163_1116)))
in (

let l = (FStar_Parser_Env.qualify env id)
in (

let se = FStar_Syntax_Syntax.Sig_datacon (((l), ([]), (t), (FStar_Syntax_Const.exn_lid), ((Prims.parse_int "0")), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((FStar_Syntax_Const.exn_lid)::[]), (d.FStar_Parser_AST.drange)))
in (

let se' = FStar_Syntax_Syntax.Sig_bundle ((((se)::[]), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((l)::[]), (d.FStar_Parser_AST.drange)))
in (

let env = (FStar_Parser_Env.push_sigelt env se')
in (

let data_ops = (mk_data_projector_names [] env (([]), (se)))
in (

let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (

let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in ((env), ((FStar_List.append ((se')::discs) data_ops))))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(

let _66_2876 = (desugar_binders env binders)
in (match (_66_2876) with
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
(let _163_1128 = (let _163_1127 = (let _163_1126 = (let _163_1125 = (let _163_1124 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat _163_1124 " not found"))
in (Prims.strcat "Effect name " _163_1125))
in ((_163_1126), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_163_1127))
in (Prims.raise _163_1128))
end
| Some (l) -> begin
l
end))
in (

let src = (lookup l.FStar_Parser_AST.msource)
in (

let dst = (lookup l.FStar_Parser_AST.mdest)
in (

let _66_2940 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(let _163_1131 = (let _163_1130 = (let _163_1129 = (desugar_term env t)
in (([]), (_163_1129)))
in Some (_163_1130))
in ((_163_1131), (None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(let _163_1137 = (let _163_1133 = (let _163_1132 = (desugar_term env wp)
in (([]), (_163_1132)))
in Some (_163_1133))
in (let _163_1136 = (let _163_1135 = (let _163_1134 = (desugar_term env t)
in (([]), (_163_1134)))
in Some (_163_1135))
in ((_163_1137), (_163_1136))))
end
| FStar_Parser_AST.LiftForFree (t) -> begin
(let _163_1140 = (let _163_1139 = (let _163_1138 = (desugar_term env t)
in (([]), (_163_1138)))
in Some (_163_1139))
in ((None), (_163_1140)))
end)
in (match (_66_2940) with
| (lift_wp, lift) -> begin
(

let se = FStar_Syntax_Syntax.Sig_sub_effect ((({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift}), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[])))
end)))))
end)))


let desugar_decls : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _66_2946 d -> (match (_66_2946) with
| (env, sigelts) -> begin
(

let _66_2950 = (desugar_decl env d)
in (match (_66_2950) with
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

let _66_2973 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _163_1158 = (FStar_Parser_Env.prepare_module_or_interface true admitted env mname)
in ((_163_1158), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _163_1159 = (FStar_Parser_Env.prepare_module_or_interface false false env mname)
in ((_163_1159), (mname), (decls), (false)))
end)
in (match (_66_2973) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(

let _66_2976 = (desugar_decls env decls)
in (match (_66_2976) with
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
| FStar_Parser_AST.Interface (mname, _66_2987, _66_2989) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (

let _66_2997 = (desugar_modul_common curmod env m)
in (match (_66_2997) with
| (x, y, _66_2996) -> begin
((x), (y))
end))))


let desugar_modul : FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (

let _66_3003 = (desugar_modul_common None env m)
in (match (_66_3003) with
| (env, modul, pop_when_done) -> begin
(

let env = (FStar_Parser_Env.finish_module_or_interface env modul)
in (

let _66_3005 = if (FStar_Options.dump_module modul.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _163_1170 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _163_1170))
end else begin
()
end
in (let _163_1171 = if pop_when_done then begin
(FStar_Parser_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end else begin
env
end
in ((_163_1171), (modul)))))
end)))


let desugar_file : FStar_Parser_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (

let _66_3018 = (FStar_List.fold_left (fun _66_3011 m -> (match (_66_3011) with
| (env, mods) -> begin
(

let _66_3015 = (desugar_modul env m)
in (match (_66_3015) with
| (env, m) -> begin
((env), ((m)::mods))
end))
end)) ((env), ([])) f)
in (match (_66_3018) with
| (env, mods) -> begin
((env), ((FStar_List.rev mods)))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Parser_Env.env  ->  FStar_Parser_Env.env = (fun m en -> (

let _66_3023 = (FStar_Parser_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (_66_3023) with
| (en, pop_when_done) -> begin
(

let en = (FStar_List.fold_left FStar_Parser_Env.push_sigelt (

let _66_3024 = en
in {FStar_Parser_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_Parser_Env.curmonad = _66_3024.FStar_Parser_Env.curmonad; FStar_Parser_Env.modules = _66_3024.FStar_Parser_Env.modules; FStar_Parser_Env.scope_mods = _66_3024.FStar_Parser_Env.scope_mods; FStar_Parser_Env.sigaccum = _66_3024.FStar_Parser_Env.sigaccum; FStar_Parser_Env.sigmap = _66_3024.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _66_3024.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _66_3024.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _66_3024.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = _66_3024.FStar_Parser_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (

let env = (FStar_Parser_Env.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_Env.export_interface m.FStar_Syntax_Syntax.name env)
end else begin
env
end))
end)))




