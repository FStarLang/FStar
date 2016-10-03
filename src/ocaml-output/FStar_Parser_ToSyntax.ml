
open Prims

let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _65_1 -> (match (_65_1) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Syntax_Syntax.Equality)
end
| _65_29 -> begin
None
end))


let trans_qual : FStar_Range.range  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun r _65_2 -> (match (_65_2) with
| FStar_Parser_AST.Private -> begin
FStar_Syntax_Syntax.Private
end
| FStar_Parser_AST.Assumption -> begin
FStar_Syntax_Syntax.Assumption
end
| FStar_Parser_AST.Inline -> begin
FStar_Syntax_Syntax.Inline
end
| FStar_Parser_AST.Unfoldable -> begin
FStar_Syntax_Syntax.Unfoldable
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

let _65_43 = (FStar_TypeChecker_Errors.warn r "The \'opaque\' qualifier is deprecated since its use was strangely schizophrenic. There were two overloaded uses: (1) Given \'opaque val f : t\', the behavior was to exclude the definition of \'f\' to the SMT solver. This corresponds roughly to the new \'irreducible\' qualifier. (2) Given \'opaque type t = t\'\', the behavior was to provide the definition of \'t\' to the SMT solver, but not to inline it, unless absolutely required for unification. This corresponds roughly to the behavior of \'unfoldable\' (which is currently the default).")
in FStar_Syntax_Syntax.Unfoldable)
end
| FStar_Parser_AST.Reflectable -> begin
FStar_Syntax_Syntax.Reflectable
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
| _65_58 -> begin
None
end))


let arg_withimp_e = (fun imp t -> ((t), ((as_imp imp))))


let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
((t), (Some (FStar_Syntax_Syntax.imp_tag)))
end
| _65_65 -> begin
((t), (None))
end))


let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_65_69) -> begin
true
end
| _65_72 -> begin
false
end)))))


let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _65_77 -> begin
t
end))


let tm_type_z : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _159_23 = (let _159_22 = (FStar_Ident.lid_of_path (("Type0")::[]) r)
in FStar_Parser_AST.Name (_159_22))
in (FStar_Parser_AST.mk_term _159_23 r FStar_Parser_AST.Kind)))


let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _159_27 = (let _159_26 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_159_26))
in (FStar_Parser_AST.mk_term _159_27 r FStar_Parser_AST.Kind)))


let rec is_comp_type : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> (match (t.FStar_Parser_AST.tm) with
| (FStar_Parser_AST.Name (l)) | (FStar_Parser_AST.Construct (l, _)) -> begin
(let _159_32 = (FStar_Parser_Env.try_lookup_effect_name env l)
in (FStar_All.pipe_right _159_32 FStar_Option.isSome))
end
| FStar_Parser_AST.App (head, _65_90, _65_92) -> begin
(is_comp_type env head)
end
| (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) | (FStar_Parser_AST.LetOpen (_, t)) -> begin
(is_comp_type env t)
end
| _65_106 -> begin
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
| _65_128 -> begin
"UNKNOWN"
end))
in (

let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _159_43 = (let _159_41 = (FStar_Util.char_at s i)
in (name_of_char _159_41))
in (let _159_42 = (aux (i + (Prims.parse_int "1")))
in (_159_43)::_159_42))
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
| _65_137 -> begin
(let _159_45 = (let _159_44 = (aux (Prims.parse_int "0"))
in (FStar_String.concat "_" _159_44))
in (Prims.strcat "op_" _159_45))
end))))


let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _159_55 = (let _159_54 = (let _159_53 = (let _159_52 = (compile_op n s)
in ((_159_52), (r)))
in (FStar_Ident.mk_ident _159_53))
in (_159_54)::[])
in (FStar_All.pipe_right _159_55 FStar_Ident.lid_of_ids)))


let op_as_term : FStar_Parser_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.term Prims.option = (fun env arity rng s -> (

let r = (fun l dd -> (let _159_70 = (let _159_69 = (let _159_68 = (FStar_Ident.set_lid_range l rng)
in (FStar_Syntax_Syntax.lid_as_fv _159_68 dd None))
in (FStar_All.pipe_right _159_69 FStar_Syntax_Syntax.fv_to_tm))
in Some (_159_70)))
in (

let fallback = (fun _65_149 -> (match (()) with
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
(r FStar_Syntax_Const.not_lid (FStar_Syntax_Syntax.Delta_unfoldable ((Prims.parse_int "2"))))
end
| "==" -> begin
(r FStar_Syntax_Const.eq2_lid FStar_Syntax_Syntax.Delta_constant)
end
| "<<" -> begin
(r FStar_Syntax_Const.precedes_lid FStar_Syntax_Syntax.Delta_constant)
end
| "/\\" -> begin
(r FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_unfoldable ((Prims.parse_int "1"))))
end
| "\\/" -> begin
(r FStar_Syntax_Const.or_lid (FStar_Syntax_Syntax.Delta_unfoldable ((Prims.parse_int "1"))))
end
| "==>" -> begin
(r FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_unfoldable ((Prims.parse_int "1"))))
end
| "<==>" -> begin
(r FStar_Syntax_Const.iff_lid (FStar_Syntax_Syntax.Delta_unfoldable ((Prims.parse_int "2"))))
end
| _65_177 -> begin
None
end)
end))
in (match ((let _159_73 = (compile_op_lid arity s rng)
in (FStar_Parser_Env.try_lookup_lid env _159_73))) with
| Some (t) -> begin
Some ((Prims.fst t))
end
| _65_181 -> begin
(fallback ())
end))))


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _159_80 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _159_80)))


let rec free_type_vars_b : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_65_190) -> begin
((env), ([]))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let _65_197 = (FStar_Parser_Env.push_bv env x)
in (match (_65_197) with
| (env, _65_196) -> begin
((env), ((x)::[]))
end))
end
| FStar_Parser_AST.Annotated (_65_199, term) -> begin
(let _159_87 = (free_type_vars env term)
in ((env), (_159_87)))
end
| FStar_Parser_AST.TAnnotated (id, _65_205) -> begin
(

let _65_211 = (FStar_Parser_Env.push_bv env id)
in (match (_65_211) with
| (env, _65_210) -> begin
((env), ([]))
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _159_88 = (free_type_vars env t)
in ((env), (_159_88)))
end))
and free_type_vars : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _159_91 = (unparen t)
in _159_91.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (_65_217) -> begin
(FStar_All.failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_Env.try_lookup_id env a)) with
| None -> begin
(a)::[]
end
| _65_223 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Assign (_, t)) | (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_65_257, ts) -> begin
(FStar_List.collect (fun _65_264 -> (match (_65_264) with
| (t, _65_263) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_65_266, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _65_273) -> begin
(let _159_94 = (free_type_vars env t1)
in (let _159_93 = (free_type_vars env t2)
in (FStar_List.append _159_94 _159_93)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(

let _65_282 = (free_type_vars_b env b)
in (match (_65_282) with
| (env, f) -> begin
(let _159_95 = (free_type_vars env t)
in (FStar_List.append f _159_95))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(

let _65_298 = (FStar_List.fold_left (fun _65_291 binder -> (match (_65_291) with
| (env, free) -> begin
(

let _65_295 = (free_type_vars_b env binder)
in (match (_65_295) with
| (env, f) -> begin
((env), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (_65_298) with
| (env, free) -> begin
(let _159_98 = (free_type_vars env body)
in (FStar_List.append free _159_98))
end))
end
| FStar_Parser_AST.Project (t, _65_301) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
[]
end))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (

let rec aux = (fun args t -> (match ((let _159_105 = (unparen t)
in _159_105.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| _65_348 -> begin
((t), (args))
end))
in (aux [] t)))


let close : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _159_110 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _159_110))
in if ((FStar_List.length ftv) = (Prims.parse_int "0")) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _159_114 = (let _159_113 = (let _159_112 = (tm_type x.FStar_Ident.idRange)
in ((x), (_159_112)))
in FStar_Parser_AST.TAnnotated (_159_113))
in (FStar_Parser_AST.mk_binder _159_114 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))


let close_fun : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _159_119 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _159_119))
in if ((FStar_List.length ftv) = (Prims.parse_int "0")) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _159_123 = (let _159_122 = (let _159_121 = (tm_type x.FStar_Ident.idRange)
in ((x), (_159_121)))
in FStar_Parser_AST.TAnnotated (_159_122))
in (FStar_Parser_AST.mk_binder _159_123 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let t = (match ((let _159_124 = (unparen t)
in _159_124.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_65_361) -> begin
t
end
| _65_364 -> begin
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
| _65_374 -> begin
((bs), (t))
end))


let rec is_var_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatWild) | (FStar_Parser_AST.PatTvar (_, _)) | (FStar_Parser_AST.PatVar (_, _)) -> begin
true
end
| FStar_Parser_AST.PatAscribed (p, _65_391) -> begin
(is_var_pattern p)
end
| _65_395 -> begin
false
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _65_399) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_65_405); FStar_Parser_AST.prange = _65_403}, _65_409) -> begin
true
end
| _65_413 -> begin
false
end))


let replace_unit_pattern : FStar_Parser_AST.pattern  ->  FStar_Parser_AST.pattern = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatConst (FStar_Const.Const_unit) -> begin
(FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatAscribed ((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)), (unit_ty)))) p.FStar_Parser_AST.prange)
end
| _65_418 -> begin
p
end))


let rec destruct_app_pattern : FStar_Parser_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _65_430 = (destruct_app_pattern env is_top_level p)
in (match (_65_430) with
| (name, args, _65_429) -> begin
((name), (args), (Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _65_435); FStar_Parser_AST.prange = _65_432}, args) when is_top_level -> begin
(let _159_142 = (let _159_141 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_159_141))
in ((_159_142), (args), (None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _65_446); FStar_Parser_AST.prange = _65_443}, args) -> begin
((FStar_Util.Inl (id)), (args), (None))
end
| _65_454 -> begin
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
| LocalBinder (_65_457) -> begin
_65_457
end))


let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_65_460) -> begin
_65_460
end))


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun _65_6 -> (match (_65_6) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| _65_467 -> begin
(FStar_All.failwith "Impossible")
end))


let as_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_Parser_Env.env) = (fun env imp _65_7 -> (match (_65_7) with
| (None, k) -> begin
(let _159_179 = (FStar_Syntax_Syntax.null_binder k)
in ((_159_179), (env)))
end
| (Some (a), k) -> begin
(

let _65_480 = (FStar_Parser_Env.push_bv env a)
in (match (_65_480) with
| (env, a) -> begin
(((((

let _65_481 = a
in {FStar_Syntax_Syntax.ppname = _65_481.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_481.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), ((trans_aqual imp)))), (env))
end))
end))


type env_t =
FStar_Parser_Env.env


type lenv_t =
FStar_Syntax_Syntax.bv Prims.list


let mk_lb : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.letbinding = (fun _65_486 -> (match (_65_486) with
| (n, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))


let no_annot_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t None))


let mk_ref_read = (fun tm -> (

let tm' = (let _159_192 = (let _159_191 = (let _159_187 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _159_187))
in (let _159_190 = (let _159_189 = (let _159_188 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (_159_188)))
in (_159_189)::[])
in ((_159_191), (_159_190))))
in FStar_Syntax_Syntax.Tm_app (_159_192))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_alloc = (fun tm -> (

let tm' = (let _159_199 = (let _159_198 = (let _159_194 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _159_194))
in (let _159_197 = (let _159_196 = (let _159_195 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (_159_195)))
in (_159_196)::[])
in ((_159_198), (_159_197))))
in FStar_Syntax_Syntax.Tm_app (_159_199))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_assign = (fun t1 t2 pos -> (

let tm = (let _159_211 = (let _159_210 = (let _159_203 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _159_203))
in (let _159_209 = (let _159_208 = (let _159_204 = (FStar_Syntax_Syntax.as_implicit false)
in ((t1), (_159_204)))
in (let _159_207 = (let _159_206 = (let _159_205 = (FStar_Syntax_Syntax.as_implicit false)
in ((t2), (_159_205)))
in (_159_206)::[])
in (_159_208)::_159_207))
in ((_159_210), (_159_209))))
in FStar_Syntax_Syntax.Tm_app (_159_211))
in (FStar_Syntax_Syntax.mk tm None pos)))


let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun _65_8 -> (match (_65_8) with
| ("repr") | ("post") | ("pre") | ("wp") -> begin
true
end
| _65_503 -> begin
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
| FStar_Syntax_Syntax.Pat_cons (_65_523, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out _65_531 -> (match (_65_531) with
| (p, _65_530) -> begin
(let _159_260 = (pat_vars p)
in (FStar_Util.set_union out _159_260))
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

let _65_554 = (match (((is_mut), (p.FStar_Parser_AST.pat))) with
| ((false, _)) | ((true, FStar_Parser_AST.PatVar (_))) -> begin
()
end
| (true, _65_552) -> begin
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
| _65_565 -> begin
(

let _65_568 = (push_bv_maybe_mut e x)
in (match (_65_568) with
| (e, x) -> begin
(((x)::l), (e), (x))
end))
end))
in (

let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun b -> (b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText))))) with
| Some (b) -> begin
((l), (e), (b))
end
| _65_577 -> begin
(

let _65_580 = (push_bv_maybe_mut e a)
in (match (_65_580) with
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
(let _159_296 = (let _159_295 = (let _159_294 = (let _159_293 = (let _159_292 = (compile_op (Prims.parse_int "0") op)
in (FStar_Ident.id_of_text _159_292))
in ((_159_293), (None)))
in FStar_Parser_AST.PatVar (_159_294))
in {FStar_Parser_AST.pat = _159_295; FStar_Parser_AST.prange = p.FStar_Parser_AST.prange})
in (aux loc env _159_296))
end
| FStar_Parser_AST.PatOr ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.PatOr ((p)::ps) -> begin
(

let _65_604 = (aux loc env p)
in (match (_65_604) with
| (loc, env, var, p, _65_603) -> begin
(

let _65_621 = (FStar_List.fold_left (fun _65_608 p -> (match (_65_608) with
| (loc, env, ps) -> begin
(

let _65_617 = (aux loc env p)
in (match (_65_617) with
| (loc, env, _65_613, p, _65_616) -> begin
((loc), (env), ((p)::ps))
end))
end)) ((loc), (env), ([])) ps)
in (match (_65_621) with
| (loc, env, ps) -> begin
(

let pat = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in ((loc), (env), (var), (pat), (false)))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _65_632 = (aux loc env p)
in (match (_65_632) with
| (loc, env', binder, p, imp) -> begin
(

let binder = (match (binder) with
| LetBinder (_65_634) -> begin
(FStar_All.failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t = (let _159_299 = (close_fun env t)
in (desugar_term env _159_299))
in LocalBinder ((((

let _65_641 = x
in {FStar_Syntax_Syntax.ppname = _65_641.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_641.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (aq))))
end)
in ((loc), (env'), (binder), (p), (imp)))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _159_300 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env), (LocalBinder (((x), (None)))), (_159_300), (false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _159_301 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env), (LocalBinder (((x), (None)))), (_159_301), (false))))
end
| (FStar_Parser_AST.PatTvar (x, aq)) | (FStar_Parser_AST.PatVar (x, aq)) -> begin
(

let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (

let aq = (trans_aqual aq)
in (

let _65_660 = (resolvex loc env x)
in (match (_65_660) with
| (loc, env, xbv) -> begin
(let _159_302 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc), (env), (LocalBinder (((xbv), (aq)))), (_159_302), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _159_303 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), ([])))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_159_303), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _65_666}, args) -> begin
(

let _65_688 = (FStar_List.fold_right (fun arg _65_677 -> (match (_65_677) with
| (loc, env, args) -> begin
(

let _65_684 = (aux loc env arg)
in (match (_65_684) with
| (loc, env, _65_681, arg, imp) -> begin
((loc), (env), ((((arg), (imp)))::args))
end))
end)) args ((loc), (env), ([])))
in (match (_65_688) with
| (loc, env, args) -> begin
(

let l = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _159_306 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_159_306), (false)))))
end))
end
| FStar_Parser_AST.PatApp (_65_692) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let _65_712 = (FStar_List.fold_right (fun pat _65_700 -> (match (_65_700) with
| (loc, env, pats) -> begin
(

let _65_708 = (aux loc env pat)
in (match (_65_708) with
| (loc, env, _65_704, pat, _65_707) -> begin
((loc), (env), ((pat)::pats))
end))
end)) pats ((loc), (env), ([])))
in (match (_65_712) with
| (loc, env, pats) -> begin
(

let pat = (let _159_319 = (let _159_318 = (let _159_314 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _159_314))
in (let _159_317 = (let _159_316 = (let _159_315 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_159_315), ([])))
in FStar_Syntax_Syntax.Pat_cons (_159_316))
in (FStar_All.pipe_left _159_318 _159_317)))
in (FStar_List.fold_right (fun hd tl -> (

let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (let _159_313 = (let _159_312 = (let _159_311 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_159_311), ((((hd), (false)))::(((tl), (false)))::[])))
in FStar_Syntax_Syntax.Pat_cons (_159_312))
in (FStar_All.pipe_left (pos_r r) _159_313)))) pats _159_319))
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc), (env), (LocalBinder (((x), (None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(

let _65_738 = (FStar_List.fold_left (fun _65_725 p -> (match (_65_725) with
| (loc, env, pats) -> begin
(

let _65_734 = (aux loc env p)
in (match (_65_734) with
| (loc, env, _65_730, pat, _65_733) -> begin
((loc), (env), ((((pat), (false)))::pats))
end))
end)) ((loc), (env), ([])) args)
in (match (_65_738) with
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

let _65_744 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) l)
in (match (_65_744) with
| (constr, _65_743) -> begin
(

let l = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| _65_748 -> begin
(FStar_All.failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _159_322 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_159_322), (false)))))
end))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(

let _65_758 = (FStar_List.hd fields)
in (match (_65_758) with
| (f, _65_757) -> begin
(

let _65_762 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_65_762) with
| (record, _65_761) -> begin
(

let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _65_765 -> (match (_65_765) with
| (f, p) -> begin
(let _159_324 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.qualify_field_to_record env record) f)
in ((_159_324), (p)))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _65_770 -> (match (_65_770) with
| (f, _65_769) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _65_774 -> (match (_65_774) with
| (g, _65_773) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_65_777, p) -> begin
p
end)
end))))
in (

let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_Env.constrname)) p.FStar_Parser_AST.prange)), (args)))) p.FStar_Parser_AST.prange)
in (

let _65_789 = (aux loc env app)
in (match (_65_789) with
| (env, e, b, p, _65_788) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(let _159_333 = (let _159_332 = (let _159_331 = (

let _65_794 = fv
in (let _159_330 = (let _159_329 = (let _159_328 = (let _159_327 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_Env.typename), (_159_327)))
in FStar_Syntax_Syntax.Record_ctor (_159_328))
in Some (_159_329))
in {FStar_Syntax_Syntax.fv_name = _65_794.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = _65_794.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _159_330}))
in ((_159_331), (args)))
in FStar_Syntax_Syntax.Pat_cons (_159_332))
in (FStar_All.pipe_left pos _159_333))
end
| _65_797 -> begin
p
end)
in ((env), (e), (b), (p), (false)))
end)))))
end))
end))
end))))
in (

let _65_806 = (aux [] env p)
in (match (_65_806) with
| (_65_800, env, b, p, _65_805) -> begin
(

let _65_807 = (let _159_334 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore _159_334))
in ((env), (b), (p)))
end)))))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p is_mut -> (

let mklet = (fun x -> (let _159_343 = (let _159_342 = (let _159_341 = (FStar_Parser_Env.qualify env x)
in ((_159_341), (FStar_Syntax_Syntax.tun)))
in LetBinder (_159_342))
in ((env), (_159_343), (None))))
in if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(let _159_345 = (let _159_344 = (compile_op (Prims.parse_int "0") x)
in (FStar_Ident.id_of_text _159_344))
in (mklet _159_345))
end
| FStar_Parser_AST.PatVar (x, _65_819) -> begin
(mklet x)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _65_826); FStar_Parser_AST.prange = _65_823}, t) -> begin
(let _159_349 = (let _159_348 = (let _159_347 = (FStar_Parser_Env.qualify env x)
in (let _159_346 = (desugar_term env t)
in ((_159_347), (_159_346))))
in LetBinder (_159_348))
in ((env), (_159_349), (None)))
end
| _65_834 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end else begin
(

let _65_838 = (desugar_data_pat env p is_mut)
in (match (_65_838) with
| (env, binder, p) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| _65_846 -> begin
Some (p)
end)
in ((env), (binder), (p)))
end))
end))
and desugar_binding_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun _65_850 env pat -> (

let _65_858 = (desugar_data_pat env pat false)
in (match (_65_858) with
| (env, _65_856, pat) -> begin
((env), (pat))
end)))
and desugar_match_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let _65_863 = env
in {FStar_Parser_Env.curmodule = _65_863.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _65_863.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _65_863.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _65_863.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _65_863.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _65_863.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _65_863.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _65_863.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _65_863.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _65_863.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _65_863.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let _65_868 = env
in {FStar_Parser_Env.curmodule = _65_868.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _65_868.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _65_868.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _65_868.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _65_868.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _65_868.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _65_868.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _65_868.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _65_868.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _65_868.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _65_868.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_machine_integer : FStar_Parser_Env.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env repr _65_875 range -> (match (_65_875) with
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
(let _159_365 = (FStar_Util.format1 "%s not in scope\n" (FStar_Ident.text_of_lid lid))
in (FStar_All.failwith _159_365))
end)
in (

let repr = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (None))))) None range)
in (let _159_370 = (let _159_369 = (let _159_368 = (let _159_367 = (let _159_366 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr), (_159_366)))
in (_159_367)::[])
in ((lid), (_159_368)))
in FStar_Syntax_Syntax.Tm_app (_159_369))
in (FStar_Syntax_Syntax.mk _159_370 None range))))))
end))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (

let mk = (fun e -> (FStar_Syntax_Syntax.mk e None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let _65_899 = e
in {FStar_Syntax_Syntax.n = _65_899.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _65_899.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _65_899.FStar_Syntax_Syntax.vars}))
in (match ((let _159_378 = (unparen top)
in _159_378.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (_65_903) -> begin
(desugar_formula env top)
end
| FStar_Parser_AST.Requires (t, lopt) -> begin
(desugar_formula env t)
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(desugar_formula env t)
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
| FStar_Parser_AST.Op ("*", (_65_929)::(_65_927)::[]) when (let _159_379 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right _159_379 FStar_Option.isNone)) -> begin
(

let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", (t1)::(t2)::[]) -> begin
(let _159_382 = (flatten t1)
in (FStar_List.append _159_382 ((t2)::[])))
end
| _65_942 -> begin
(t)::[]
end))
in (

let targs = (let _159_386 = (let _159_383 = (unparen top)
in (flatten _159_383))
in (FStar_All.pipe_right _159_386 (FStar_List.map (fun t -> (let _159_385 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg _159_385))))))
in (

let _65_948 = (let _159_387 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) _159_387))
in (match (_65_948) with
| (tup, _65_947) -> begin
(mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _159_389 = (let _159_388 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) a)
in (Prims.fst _159_388))
in (FStar_All.pipe_left setpos _159_389))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Unexpected or unbound operator: " s)), (top.FStar_Parser_AST.range)))))
end
| Some (op) -> begin
if ((FStar_List.length args) > (Prims.parse_int "0")) then begin
(

let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _159_391 = (desugar_term env t)
in ((_159_391), (None))))))
in (mk (FStar_Syntax_Syntax.Tm_app (((op), (args))))))
end else begin
op
end
end)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _65_966; FStar_Ident.ident = _65_964; FStar_Ident.nsstr = _65_962; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _65_975; FStar_Ident.ident = _65_973; FStar_Ident.nsstr = _65_971; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _65_984; FStar_Ident.ident = _65_982; FStar_Ident.nsstr = _65_980; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _65_993; FStar_Ident.ident = _65_991; FStar_Ident.nsstr = _65_989; FStar_Ident.str = "True"}) -> begin
(let _159_392 = (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _159_392 FStar_Syntax_Syntax.Delta_constant None))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _65_1002; FStar_Ident.ident = _65_1000; FStar_Ident.nsstr = _65_998; FStar_Ident.str = "False"}) -> begin
(let _159_393 = (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _159_393 FStar_Syntax_Syntax.Delta_constant None))
end
| FStar_Parser_AST.Var ({FStar_Ident.ns = (eff)::rest; FStar_Ident.ident = {FStar_Ident.idText = txt; FStar_Ident.idRange = _65_1010}; FStar_Ident.nsstr = _65_1008; FStar_Ident.str = _65_1006}) when ((is_special_effect_combinator txt) && (let _159_394 = (FStar_Ident.lid_of_ids ((eff)::rest))
in (FStar_Parser_Env.is_effect_name env _159_394))) -> begin
(match ((let _159_395 = (FStar_Ident.lid_of_ids ((eff)::rest))
in (FStar_Parser_Env.try_lookup_effect_defn env _159_395))) with
| Some (ed) -> begin
(let _159_396 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" txt))) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.fvar _159_396 (FStar_Syntax_Syntax.Delta_unfoldable ((Prims.parse_int "1"))) None))
end
| None -> begin
(FStar_All.failwith "immpossible special_effect_combinator")
end)
end
| FStar_Parser_AST.Assign (ident, t2) -> begin
(

let t2 = (desugar_term env t2)
in (

let _65_1028 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) ident)
in (match (_65_1028) with
| (t1, mut) -> begin
(

let _65_1029 = if (not (mut)) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Can only assign to mutable values"), (top.FStar_Parser_AST.range)))))
end else begin
()
end
in (mk_ref_assign t1 t2 top.FStar_Parser_AST.range))
end)))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(

let _65_1036 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) l)
in (match (_65_1036) with
| (tm, mut) -> begin
(

let tm = (setpos tm)
in if mut then begin
(let _159_399 = (let _159_398 = (let _159_397 = (mk_ref_read tm)
in ((_159_397), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval))))
in FStar_Syntax_Syntax.Tm_meta (_159_398))
in (FStar_All.pipe_left mk _159_399))
end else begin
tm
end)
end))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(match ((FStar_Parser_Env.try_lookup_datacon env l)) with
| Some (head) -> begin
(

let _65_1046 = (let _159_400 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in ((_159_400), (true)))
in (match (_65_1046) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| _65_1049 -> begin
(

let args = (FStar_List.map (fun _65_1052 -> (match (_65_1052) with
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
(

let l = (FStar_Parser_Env.expand_module_abbrev env l)
in (

let env = (FStar_Parser_Env.push_namespace env l)
in (match (args) with
| ((e, _65_1061))::[] -> begin
(desugar_term_maybe_top top_level env e)
end
| _65_1065 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("The Foo.Bar (...) local open takes exactly one argument"), (top.FStar_Parser_AST.range)))))
end)))
end)
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let _65_1090 = (FStar_List.fold_left (fun _65_1073 b -> (match (_65_1073) with
| (env, tparams, typs) -> begin
(

let _65_1077 = (desugar_binder env b)
in (match (_65_1077) with
| (xopt, t) -> begin
(

let _65_1083 = (match (xopt) with
| None -> begin
(let _159_404 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env), (_159_404)))
end
| Some (x) -> begin
(FStar_Parser_Env.push_bv env x)
end)
in (match (_65_1083) with
| (env, x) -> begin
(let _159_408 = (let _159_407 = (let _159_406 = (let _159_405 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _159_405))
in (_159_406)::[])
in (FStar_List.append typs _159_407))
in ((env), ((FStar_List.append tparams (((((

let _65_1084 = x
in {FStar_Syntax_Syntax.ppname = _65_1084.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_1084.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (None)))::[]))), (_159_408)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_65_1090) with
| (env, _65_1088, targs) -> begin
(

let _65_1094 = (let _159_409 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) _159_409))
in (match (_65_1094) with
| (tup, _65_1093) -> begin
(FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let _65_1101 = (uncurry binders t)
in (match (_65_1101) with
| (bs, t) -> begin
(

let rec aux = (fun env bs _65_9 -> (match (_65_9) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (let _159_416 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos _159_416)))
end
| (hd)::tl -> begin
(

let mlenv = (FStar_Parser_Env.default_ml env)
in (

let bb = (desugar_binder mlenv hd)
in (

let _65_1115 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_65_1115) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_binder env b)) with
| (None, _65_1122) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(

let _65_1130 = (as_binder env None b)
in (match (_65_1130) with
| ((x, _65_1127), env) -> begin
(

let f = (desugar_formula env f)
in (let _159_417 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos _159_417)))
end))
end)
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let binders = (FStar_All.pipe_right binders (FStar_List.map replace_unit_pattern))
in (

let _65_1151 = (FStar_List.fold_left (fun _65_1139 pat -> (match (_65_1139) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (_65_1142, t) -> begin
(let _159_421 = (let _159_420 = (free_type_vars env t)
in (FStar_List.append _159_420 ftvs))
in ((env), (_159_421)))
end
| _65_1147 -> begin
((env), (ftvs))
end)
end)) ((env), ([])) binders)
in (match (_65_1151) with
| (_65_1149, ftv) -> begin
(

let ftv = (sort_ftv ftv)
in (

let binders = (let _159_423 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append _159_423 binders))
in (

let rec aux = (fun env bs sc_pat_opt _65_10 -> (match (_65_10) with
| [] -> begin
(

let body = (desugar_term env body)
in (

let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(

let body = (let _159_433 = (let _159_432 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right _159_432 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close _159_433 body))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (None), (body)))::[])))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (let _159_434 = (no_annot_abs (FStar_List.rev bs) body)
in (setpos _159_434))))
end
| (p)::rest -> begin
(

let _65_1175 = (desugar_binding_pat env p)
in (match (_65_1175) with
| (env, b, pat) -> begin
(

let _65_1226 = (match (b) with
| LetBinder (_65_1177) -> begin
(FStar_All.failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt = (match (((pat), (sc_pat_opt))) with
| (None, _65_1185) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _159_436 = (let _159_435 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_159_435), (p)))
in Some (_159_436))
end
| (Some (p), Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (_65_1199), _65_1202) -> begin
(

let tup2 = (let _159_437 = (FStar_Syntax_Util.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _159_437 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (let _159_445 = (let _159_444 = (let _159_443 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (let _159_442 = (let _159_441 = (FStar_Syntax_Syntax.as_arg sc)
in (let _159_440 = (let _159_439 = (let _159_438 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _159_438))
in (_159_439)::[])
in (_159_441)::_159_440))
in ((_159_443), (_159_442))))
in FStar_Syntax_Syntax.Tm_app (_159_444))
in (FStar_Syntax_Syntax.mk _159_445 None top.FStar_Parser_AST.range))
in (

let p = (let _159_446 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p), (false)))::[])))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _159_446))
in Some (((sc), (p))))))
end
| (FStar_Syntax_Syntax.Tm_app (_65_1208, args), FStar_Syntax_Syntax.Pat_cons (_65_1213, pats)) -> begin
(

let tupn = (let _159_447 = (FStar_Syntax_Util.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _159_447 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (let _159_454 = (let _159_453 = (let _159_452 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (let _159_451 = (let _159_450 = (let _159_449 = (let _159_448 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _159_448))
in (_159_449)::[])
in (FStar_List.append args _159_450))
in ((_159_452), (_159_451))))
in FStar_Syntax_Syntax.Tm_app (_159_453))
in (mk _159_454))
in (

let p = (let _159_455 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p), (false)))::[])))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _159_455))
in Some (((sc), (p))))))
end
| _65_1222 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt)))
end)
in (match (_65_1226) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end)))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _65_1230; FStar_Parser_AST.level = _65_1228}, phi, _65_1236) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(

let phi = (desugar_formula env phi)
in (let _159_463 = (let _159_462 = (let _159_461 = (FStar_Syntax_Syntax.fvar a FStar_Syntax_Syntax.Delta_equational None)
in (let _159_460 = (let _159_459 = (FStar_Syntax_Syntax.as_arg phi)
in (let _159_458 = (let _159_457 = (let _159_456 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _159_456))
in (_159_457)::[])
in (_159_459)::_159_458))
in ((_159_461), (_159_460))))
in FStar_Syntax_Syntax.Tm_app (_159_462))
in (mk _159_463)))
end
| FStar_Parser_AST.App (_65_1241) -> begin
(

let rec aux = (fun args e -> (match ((let _159_468 = (unparen e)
in _159_468.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(

let arg = (let _159_469 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _159_469))
in (aux ((arg)::args) e))
end
| _65_1253 -> begin
(

let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app (((head), (args))))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _159_472 = (let _159_471 = (let _159_470 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((_159_470), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))
in FStar_Syntax_Syntax.Tm_meta (_159_471))
in (mk _159_472))
end
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(

let lid = (FStar_Parser_Env.expand_module_abbrev env lid)
in (

let env = (FStar_Parser_Env.push_namespace env lid)
in (desugar_term_maybe_top top_level env e)))
end
| FStar_Parser_AST.Let (qual, ((pat, _snd))::_tl, body) -> begin
(

let is_rec = (qual = FStar_Parser_AST.Rec)
in (

let ds_let_rec_or_app = (fun _65_1276 -> (match (()) with
| () -> begin
(

let bindings = (((pat), (_snd)))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _65_1280 -> (match (_65_1280) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _159_476 = (destruct_app_pattern env top_level p)
in ((_159_476), (def)))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _159_477 = (destruct_app_pattern env top_level p)
in ((_159_477), (def)))
end
| _65_1286 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _65_1291); FStar_Parser_AST.prange = _65_1288}, t) -> begin
if top_level then begin
(let _159_480 = (let _159_479 = (let _159_478 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_159_478))
in ((_159_479), ([]), (Some (t))))
in ((_159_480), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (Some (t)))), (def))
end
end
| FStar_Parser_AST.PatVar (id, _65_1300) -> begin
if top_level then begin
(let _159_483 = (let _159_482 = (let _159_481 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_159_481))
in ((_159_482), ([]), (None)))
in ((_159_483), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (None))), (def))
end
end
| _65_1304 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end
end))))
in (

let _65_1333 = (FStar_List.fold_left (fun _65_1309 _65_1318 -> (match (((_65_1309), (_65_1318))) with
| ((env, fnames, rec_bindings), ((f, _65_1312, _65_1314), _65_1317)) -> begin
(

let _65_1329 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let _65_1323 = (FStar_Parser_Env.push_bv env x)
in (match (_65_1323) with
| (env, xx) -> begin
(let _159_487 = (let _159_486 = (FStar_Syntax_Syntax.mk_binder xx)
in (_159_486)::rec_bindings)
in ((env), (FStar_Util.Inl (xx)), (_159_487)))
end))
end
| FStar_Util.Inr (l) -> begin
(let _159_488 = (FStar_Parser_Env.push_top_level_rec_binding env l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in ((_159_488), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (_65_1329) with
| (env, lbname, rec_bindings) -> begin
((env), ((lbname)::fnames), (rec_bindings))
end))
end)) ((env), ([]), ([])) funs)
in (match (_65_1333) with
| (env', fnames, rec_bindings) -> begin
(

let fnames = (FStar_List.rev fnames)
in (

let desugar_one_def = (fun env lbname _65_1344 -> (match (_65_1344) with
| ((_65_1339, args, result_t), def) -> begin
(

let args = (FStar_All.pipe_right args (FStar_List.map replace_unit_pattern))
in (

let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(

let _65_1353 = if (is_comp_type env t) then begin
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
in (let _159_496 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t)))) _159_496 FStar_Parser_AST.Expr)))
end)
in (

let def = (match (args) with
| [] -> begin
def
end
| _65_1358 -> begin
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
(let _159_498 = (let _159_497 = (FStar_Syntax_Util.incr_delta_qualifier body)
in (FStar_Syntax_Syntax.lid_as_fv l _159_497 None))
in FStar_Util.Inr (_159_498))
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
in (let _159_501 = (let _159_500 = (let _159_499 = (FStar_Syntax_Subst.close rec_bindings body)
in ((((is_rec), (lbs))), (_159_499)))
in FStar_Syntax_Syntax.Tm_let (_159_500))
in (FStar_All.pipe_left mk _159_501))))))
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

let _65_1379 = (desugar_binding_pat_maybe_top top_level env pat is_mutable)
in (match (_65_1379) with
| (env, binder, pat) -> begin
(

let tm = (match (binder) with
| LetBinder (l, t) -> begin
(

let body = (desugar_term env t2)
in (

let fv = (let _159_508 = (FStar_Syntax_Util.incr_delta_qualifier t1)
in (FStar_Syntax_Syntax.lid_as_fv l _159_508 None))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((((false), (({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]))), (body)))))))
end
| LocalBinder (x, _65_1388) -> begin
(

let body = (desugar_term env t2)
in (

let body = (match (pat) with
| (None) | (Some ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (_); FStar_Syntax_Syntax.ty = _; FStar_Syntax_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _159_513 = (let _159_512 = (let _159_511 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _159_510 = (let _159_509 = (FStar_Syntax_Util.branch ((pat), (None), (body)))
in (_159_509)::[])
in ((_159_511), (_159_510))))
in FStar_Syntax_Syntax.Tm_match (_159_512))
in (FStar_Syntax_Syntax.mk _159_513 None body.FStar_Syntax_Syntax.pos))
end)
in (let _159_518 = (let _159_517 = (let _159_516 = (let _159_515 = (let _159_514 = (FStar_Syntax_Syntax.mk_binder x)
in (_159_514)::[])
in (FStar_Syntax_Subst.close _159_515 body))
in ((((false), (((mk_lb ((FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t1))))::[]))), (_159_516)))
in FStar_Syntax_Syntax.Tm_let (_159_517))
in (FStar_All.pipe_left mk _159_518))))
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
in (let _159_529 = (let _159_528 = (let _159_527 = (desugar_term env t1)
in (let _159_526 = (let _159_525 = (let _159_520 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (let _159_519 = (desugar_term env t2)
in ((_159_520), (None), (_159_519))))
in (let _159_524 = (let _159_523 = (let _159_522 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (let _159_521 = (desugar_term env t3)
in ((_159_522), (None), (_159_521))))
in (_159_523)::[])
in (_159_525)::_159_524))
in ((_159_527), (_159_526))))
in FStar_Syntax_Syntax.Tm_match (_159_528))
in (mk _159_529)))
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

let desugar_branch = (fun _65_1429 -> (match (_65_1429) with
| (pat, wopt, b) -> begin
(

let _65_1432 = (desugar_match_pat env pat)
in (match (_65_1432) with
| (env, pat) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _159_532 = (desugar_term env e)
in Some (_159_532))
end)
in (

let b = (desugar_term env b)
in (FStar_Syntax_Util.branch ((pat), (wopt), (b)))))
end))
end))
in (let _159_536 = (let _159_535 = (let _159_534 = (desugar_term env e)
in (let _159_533 = (FStar_List.map desugar_branch branches)
in ((_159_534), (_159_533))))
in FStar_Syntax_Syntax.Tm_match (_159_535))
in (FStar_All.pipe_left mk _159_536)))
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
in (let _159_539 = (let _159_538 = (let _159_537 = (desugar_term env e)
in ((_159_537), (annot), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (_159_538))
in (FStar_All.pipe_left mk _159_539)))))
end
| FStar_Parser_AST.Record (_65_1446, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let _65_1457 = (FStar_List.hd fields)
in (match (_65_1457) with
| (f, _65_1456) -> begin
(

let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (

let _65_1463 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_65_1463) with
| (record, _65_1462) -> begin
(

let get_field = (fun xopt f -> (

let fn = f.FStar_Ident.ident
in (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _65_1471 -> (match (_65_1471) with
| (g, _65_1470) -> begin
(

let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_65_1475, e) -> begin
(let _159_547 = (qfn fn)
in ((_159_547), (e)))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _159_550 = (let _159_549 = (let _159_548 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in ((_159_548), (top.FStar_Parser_AST.range)))
in FStar_Syntax_Syntax.Error (_159_549))
in (Prims.raise _159_550))
end
| Some (x) -> begin
(let _159_551 = (qfn fn)
in ((_159_551), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Project (((x), (f)))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level))))
end)
end))))
in (

let recterm = (match (eopt) with
| None -> begin
(let _159_556 = (let _159_555 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _65_1487 -> (match (_65_1487) with
| (f, _65_1486) -> begin
(let _159_554 = (let _159_553 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _159_553))
in ((_159_554), (FStar_Parser_AST.Nothing)))
end))))
in ((record.FStar_Parser_Env.constrname), (_159_555)))
in FStar_Parser_AST.Construct (_159_556))
end
| Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (let _159_558 = (let _159_557 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_159_557))
in (FStar_Parser_AST.mk_term _159_558 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record = (let _159_561 = (let _159_560 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _65_1495 -> (match (_65_1495) with
| (f, _65_1494) -> begin
(get_field (Some (xterm)) f)
end))))
in ((None), (_159_560)))
in FStar_Parser_AST.Record (_159_561))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _65_1511; FStar_Syntax_Syntax.pos = _65_1509; FStar_Syntax_Syntax.vars = _65_1507}, args); FStar_Syntax_Syntax.tk = _65_1505; FStar_Syntax_Syntax.pos = _65_1503; FStar_Syntax_Syntax.vars = _65_1501}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(

let e = (let _159_569 = (let _159_568 = (let _159_567 = (let _159_566 = (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos)
in (let _159_565 = (let _159_564 = (let _159_563 = (let _159_562 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_Env.typename), (_159_562)))
in FStar_Syntax_Syntax.Record_ctor (_159_563))
in Some (_159_564))
in (FStar_Syntax_Syntax.fvar _159_566 FStar_Syntax_Syntax.Delta_constant _159_565)))
in ((_159_567), (args)))
in FStar_Syntax_Syntax.Tm_app (_159_568))
in (FStar_All.pipe_left mk _159_569))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))))))
end
| _65_1525 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(

let _65_1532 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_projector_by_field_name env) f)
in (match (_65_1532) with
| (fieldname, is_rec) -> begin
(

let e = (desugar_term env e)
in (

let fn = (

let _65_1537 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_65_1537) with
| (ns, _65_1536) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (

let qual = if is_rec then begin
Some (FStar_Syntax_Syntax.Record_projector (fn))
end else begin
None
end
in (let _159_575 = (let _159_574 = (let _159_573 = (let _159_570 = (FStar_Ident.set_lid_range fieldname (FStar_Ident.range_of_lid f))
in (FStar_Syntax_Syntax.fvar _159_570 FStar_Syntax_Syntax.Delta_equational qual))
in (let _159_572 = (let _159_571 = (FStar_Syntax_Syntax.as_arg e)
in (_159_571)::[])
in ((_159_573), (_159_572))))
in FStar_Syntax_Syntax.Tm_app (_159_574))
in (FStar_All.pipe_left mk _159_575)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| _65_1547 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _65_1549 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Let (_65_1551, _65_1553, _65_1555) -> begin
(FStar_All.failwith "Not implemented yet")
end
| FStar_Parser_AST.QForall (_65_1559, _65_1561, _65_1563) -> begin
(FStar_All.failwith "Not implemented yet")
end
| FStar_Parser_AST.QExists (_65_1567, _65_1569, _65_1571) -> begin
(FStar_All.failwith "Not implemented yet")
end))))
and desugar_args : FStar_Parser_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun _65_1578 -> (match (_65_1578) with
| (a, imp) -> begin
(let _159_579 = (desugar_term env a)
in (arg_withimp_e imp _159_579))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r default_ok env t -> (

let fail = (fun msg -> (Prims.raise (FStar_Syntax_Syntax.Error (((msg), (r))))))
in (

let is_requires = (fun _65_1590 -> (match (_65_1590) with
| (t, _65_1589) -> begin
(match ((let _159_587 = (unparen t)
in _159_587.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Requires (_65_1592) -> begin
true
end
| _65_1595 -> begin
false
end)
end))
in (

let is_ensures = (fun _65_1600 -> (match (_65_1600) with
| (t, _65_1599) -> begin
(match ((let _159_590 = (unparen t)
in _159_590.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ensures (_65_1602) -> begin
true
end
| _65_1605 -> begin
false
end)
end))
in (

let is_app = (fun head _65_1611 -> (match (_65_1611) with
| (t, _65_1610) -> begin
(match ((let _159_595 = (unparen t)
in _159_595.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _65_1615; FStar_Parser_AST.level = _65_1613}, _65_1620, _65_1622) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| _65_1626 -> begin
false
end)
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t -> (

let _65_1632 = (head_and_args t)
in (match (_65_1632) with
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

let head = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_name env) lemma)
in ((head), (args)))))))
end
| FStar_Parser_AST.Name (l) when (FStar_Parser_Env.is_effect_name env l) -> begin
(let _159_599 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_name env) l)
in ((_159_599), (args)))
end
| FStar_Parser_AST.Name (l) when ((let _159_600 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _159_600 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(let _159_601 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in ((_159_601), (args)))
end
| FStar_Parser_AST.Name (l) when ((let _159_602 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _159_602 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(let _159_603 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)
in ((_159_603), (args)))
end
| FStar_Parser_AST.Name (l) when ((((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) && default_ok) -> begin
(let _159_604 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in ((_159_604), ((((t), (FStar_Parser_AST.Nothing)))::[])))
end
| _65_1663 when default_ok -> begin
(let _159_605 = (FStar_Ident.set_lid_range env.FStar_Parser_Env.default_result_effect head.FStar_Parser_AST.range)
in ((_159_605), ((((t), (FStar_Parser_AST.Nothing)))::[])))
end
| _65_1665 -> begin
(let _159_607 = (let _159_606 = (FStar_Parser_AST.term_to_string t)
in (FStar_Util.format1 "%s is not an effect" _159_606))
in (fail _159_607))
end)
end)))
in (

let _65_1668 = (pre_process_comp_typ t)
in (match (_65_1668) with
| (eff, args) -> begin
(

let _65_1669 = if ((FStar_List.length args) = (Prims.parse_int "0")) then begin
(let _159_609 = (let _159_608 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" _159_608))
in (fail _159_609))
end else begin
()
end
in (

let _65_1673 = (let _159_611 = (FStar_List.hd args)
in (let _159_610 = (FStar_List.tl args)
in ((_159_611), (_159_610))))
in (match (_65_1673) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (Prims.fst result_arg))
in (

let rest = (desugar_args env rest)
in (

let _65_1698 = (FStar_All.pipe_right rest (FStar_List.partition (fun _65_1679 -> (match (_65_1679) with
| (t, _65_1678) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _65_1685; FStar_Syntax_Syntax.pos = _65_1683; FStar_Syntax_Syntax.vars = _65_1681}, (_65_1690)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| _65_1695 -> begin
false
end)
end))))
in (match (_65_1698) with
| (dec, rest) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _65_1702 -> (match (_65_1702) with
| (t, _65_1701) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_65_1704, ((arg, _65_1707))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| _65_1713 -> begin
(FStar_All.failwith "impos")
end)
end))))
in (

let no_additional_args = (((FStar_List.length decreases_clause) = (Prims.parse_int "0")) && ((FStar_List.length rest) = (Prims.parse_int "0")))
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

let rest = if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid) then begin
(match (rest) with
| (req)::(ens)::((pat, aq))::[] -> begin
(

let pat = (match (pat.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
(

let nil = (FStar_Syntax_Syntax.mk_Tm_uinst pat ((FStar_Syntax_Syntax.U_succ (FStar_Syntax_Syntax.U_zero))::[]))
in (

let pattern = (let _159_615 = (let _159_614 = (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _159_614 FStar_Syntax_Syntax.Delta_constant None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _159_615 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app nil ((((pattern), (Some (FStar_Syntax_Syntax.imp_tag))))::[]) None pat.FStar_Syntax_Syntax.pos)))
end
| _65_1728 -> begin
pat
end)
in (let _159_619 = (let _159_618 = (let _159_617 = (let _159_616 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) None pat.FStar_Syntax_Syntax.pos)
in ((_159_616), (aq)))
in (_159_617)::[])
in (ens)::_159_618)
in (req)::_159_619))
end
| _65_1731 -> begin
rest
end)
end else begin
rest
end
in (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = []; FStar_Syntax_Syntax.effect_name = eff; FStar_Syntax_Syntax.result_typ = result_typ; FStar_Syntax_Syntax.effect_args = rest; FStar_Syntax_Syntax.flags = (FStar_List.append flags decreases_clause)})))
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
| _65_1743 -> begin
None
end))
in (

let mk = (fun t -> (FStar_Syntax_Syntax.mk t None f.FStar_Parser_AST.range))
in (

let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let _65_1750 = t
in {FStar_Syntax_Syntax.n = _65_1750.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _65_1750.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _65_1750.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let _65_1757 = b
in {FStar_Parser_AST.b = _65_1757.FStar_Parser_AST.b; FStar_Parser_AST.brange = _65_1757.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _65_1757.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _159_654 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _159_654)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(

let _65_1771 = (FStar_Parser_Env.push_bv env a)
in (match (_65_1771) with
| (env, a) -> begin
(

let a = (

let _65_1772 = a
in {FStar_Syntax_Syntax.ppname = _65_1772.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_1772.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats = (desugar_pats env pats)
in (

let body = (desugar_formula env body)
in (

let body = (match (pats) with
| [] -> begin
body
end
| _65_1779 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta (((body), (FStar_Syntax_Syntax.Meta_pattern (pats))))))
end)
in (

let body = (let _159_657 = (let _159_656 = (let _159_655 = (FStar_Syntax_Syntax.mk_binder a)
in (_159_655)::[])
in (no_annot_abs _159_656 body))
in (FStar_All.pipe_left setpos _159_657))
in (let _159_663 = (let _159_662 = (let _159_661 = (let _159_658 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Syntax_Syntax.fvar _159_658 (FStar_Syntax_Syntax.Delta_unfoldable ((Prims.parse_int "1"))) None))
in (let _159_660 = (let _159_659 = (FStar_Syntax_Syntax.as_arg body)
in (_159_659)::[])
in ((_159_661), (_159_660))))
in FStar_Syntax_Syntax.Tm_app (_159_662))
in (FStar_All.pipe_left mk _159_663)))))))
end))
end
| _65_1783 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body = (let _159_678 = (q ((rest), (pats), (body)))
in (let _159_677 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _159_678 _159_677 FStar_Parser_AST.Formula)))
in (let _159_679 = (q (((b)::[]), ([]), (body)))
in (FStar_Parser_AST.mk_term _159_679 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _65_1797 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _159_680 = (unparen f)
in _159_680.FStar_Parser_AST.tm)) with
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
in (let _159_682 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _159_682)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _159_684 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _159_684)))
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
| _65_1855 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (

let _65_1879 = (FStar_List.fold_left (fun _65_1860 b -> (match (_65_1860) with
| (env, out) -> begin
(

let tk = (desugar_binder env (

let _65_1862 = b
in {FStar_Parser_AST.b = _65_1862.FStar_Parser_AST.b; FStar_Parser_AST.brange = _65_1862.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _65_1862.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(

let _65_1871 = (FStar_Parser_Env.push_bv env a)
in (match (_65_1871) with
| (env, a) -> begin
(

let a = (

let _65_1872 = a
in {FStar_Syntax_Syntax.ppname = _65_1872.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_1872.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in ((env), ((((a), ((trans_aqual b.FStar_Parser_AST.aqual))))::out)))
end))
end
| _65_1876 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (_65_1879) with
| (env, tpars) -> begin
((env), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(let _159_691 = (desugar_typ env t)
in ((Some (x)), (_159_691)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _159_692 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None x.FStar_Ident.idRange)
in ((Some (x)), (_159_692)))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _159_693 = (desugar_typ env t)
in ((None), (_159_693)))
end
| FStar_Parser_AST.Variable (x) -> begin
((Some (x)), (FStar_Syntax_Syntax.tun))
end))


let mk_data_discriminators : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  FStar_Ident.lid  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun quals env t tps k datas -> (

let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_Env.iface) || env.FStar_Parser_Env.admitted_iface) then begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (

let binders = (let _159_709 = (let _159_708 = (FStar_Syntax_Util.arrow_formals k)
in (Prims.fst _159_708))
in (FStar_List.append tps _159_709))
in (

let p = (FStar_Ident.range_of_lid t)
in (

let _65_1906 = (FStar_Syntax_Util.args_of_binders binders)
in (match (_65_1906) with
| (binders, args) -> begin
(

let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _65_1910 -> (match (_65_1910) with
| (x, _65_1909) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let binders = (let _159_715 = (let _159_714 = (let _159_713 = (let _159_712 = (let _159_711 = (FStar_Syntax_Syntax.lid_as_fv t FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _159_711))
in (FStar_Syntax_Syntax.mk_Tm_app _159_712 args None p))
in (FStar_All.pipe_left FStar_Syntax_Syntax.null_binder _159_713))
in (_159_714)::[])
in (FStar_List.append imp_binders _159_715))
in (

let disc_type = (let _159_718 = (let _159_717 = (let _159_716 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _159_716))
in (FStar_Syntax_Syntax.mk_Total _159_717))
in (FStar_Syntax_Util.arrow binders _159_718))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (let _159_721 = (let _159_720 = (quals ((FStar_Syntax_Syntax.Logic)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in ((disc_name), ([]), (disc_type), (_159_720), ((FStar_Ident.range_of_lid disc_name))))
in FStar_Syntax_Syntax.Sig_declare_typ (_159_721)))))))))
end))))))


let mk_indexed_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq refine_domain env tc lid inductive_tps imp_tps fields t -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p))
in (

let projectee = (fun ptyp -> (FStar_Syntax_Syntax.gen_bv "projectee" (Some (p)) ptyp))
in (

let tps = (FStar_List.map2 (fun _65_1934 _65_1938 -> (match (((_65_1934), (_65_1938))) with
| ((_65_1932, imp), (x, _65_1937)) -> begin
((x), (imp))
end)) inductive_tps imp_tps)
in (

let _65_2039 = (

let _65_1942 = (FStar_Syntax_Util.head_and_args t)
in (match (_65_1942) with
| (head, args0) -> begin
(

let args = (

let rec arguments = (fun tps args -> (match (((tps), (args))) with
| ([], _65_1948) -> begin
args
end
| (_65_1951, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Not enough arguments to type"), ((FStar_Ident.range_of_lid lid))))))
end
| (((_65_1956, Some (FStar_Syntax_Syntax.Implicit (_65_1958))))::tps', ((_65_1965, Some (FStar_Syntax_Syntax.Implicit (_65_1967))))::args') -> begin
(arguments tps' args')
end
| (((_65_1975, Some (FStar_Syntax_Syntax.Implicit (_65_1977))))::tps', ((_65_1985, _65_1987))::_65_1983) -> begin
(arguments tps' args)
end
| (((_65_1994, _65_1996))::_65_1992, ((a, Some (FStar_Syntax_Syntax.Implicit (_65_2003))))::_65_2000) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected implicit annotation on argument"), (a.FStar_Syntax_Syntax.pos)))))
end
| (((_65_2011, _65_2013))::tps', ((_65_2018, _65_2020))::args') -> begin
(arguments tps' args')
end))
in (arguments inductive_tps args0))
in (

let indices = (FStar_All.pipe_right args (FStar_List.map (fun _65_2025 -> (let _159_753 = (FStar_Syntax_Syntax.new_bv (Some (p)) FStar_Syntax_Syntax.tun)
in (FStar_All.pipe_right _159_753 FStar_Syntax_Syntax.mk_binder)))))
in (

let arg_typ = (let _159_758 = (let _159_754 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _159_754))
in (let _159_757 = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _65_2030 -> (match (_65_2030) with
| (x, imp) -> begin
(let _159_756 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_159_756), (imp)))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app _159_758 _159_757 None p)))
in (

let arg_binder = if (not (refine_domain)) then begin
(let _159_759 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder _159_759))
end else begin
(

let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p)) arg_typ)
in (let _159_768 = (

let _65_2034 = (projectee arg_typ)
in (let _159_767 = (let _159_766 = (let _159_765 = (let _159_764 = (let _159_760 = (FStar_Ident.set_lid_range disc_name p)
in (FStar_Syntax_Syntax.fvar _159_760 FStar_Syntax_Syntax.Delta_equational None))
in (let _159_763 = (let _159_762 = (let _159_761 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _159_761))
in (_159_762)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _159_764 _159_763 None p)))
in (FStar_Syntax_Util.b2t _159_765))
in (FStar_Syntax_Util.refine x _159_766))
in {FStar_Syntax_Syntax.ppname = _65_2034.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_2034.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _159_767}))
in (FStar_Syntax_Syntax.mk_binder _159_768))))
end
in ((arg_binder), (indices))))))
end))
in (match (_65_2039) with
| (arg_binder, indices) -> begin
(

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder))
in (

let imp_binders = (let _159_770 = (FStar_All.pipe_right indices (FStar_List.map (fun _65_2044 -> (match (_65_2044) with
| (x, _65_2043) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (FStar_List.append imp_tps _159_770))
in (

let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (

let arg = (FStar_Syntax_Util.arg_of_non_null_binder arg_binder)
in (

let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _65_2052 -> (match (_65_2052) with
| (a, _65_2051) -> begin
(

let _65_2056 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (_65_2056) with
| (field_name, _65_2055) -> begin
(

let proj = (let _159_774 = (let _159_773 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.fv_to_tm _159_773))
in (FStar_Syntax_Syntax.mk_Tm_app _159_774 ((arg)::[]) None p))
in FStar_Syntax_Syntax.NT (((a), (proj))))
end))
end))))
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (FStar_List.append imp_tps fields)
in (let _159_810 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _65_2065 -> (match (_65_2065) with
| (x, _65_2064) -> begin
(

let _65_2069 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_65_2069) with
| (field_name, _65_2068) -> begin
(

let t = (let _159_778 = (let _159_777 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total _159_777))
in (FStar_Syntax_Util.arrow binders _159_778))
in (

let only_decl = (((let _159_779 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _159_779)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _159_781 = (let _159_780 = (FStar_Parser_Env.current_module env)
in _159_780.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _159_781)))
in (

let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (

let quals = (fun q -> if only_decl then begin
(FStar_Syntax_Syntax.Assumption)::q
end else begin
q
end)
in (

let quals = (quals ((FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), ([]), (t), (quals), ((FStar_Ident.range_of_lid field_name))))
in if only_decl then begin
(decl)::[]
end else begin
(

let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _65_2081 -> (match (_65_2081) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in if ((i + ntps) = j) then begin
(let _159_786 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in ((_159_786), (b)))
end else begin
if (b && (j < ntps)) then begin
(let _159_790 = (let _159_789 = (let _159_788 = (let _159_787 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in ((_159_787), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (_159_788))
in (pos _159_789))
in ((_159_790), (b)))
end else begin
(let _159_793 = (let _159_792 = (let _159_791 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_159_791))
in (pos _159_792))
in ((_159_793), (b)))
end
end)
end))))
in (

let pat = (let _159_798 = (let _159_796 = (let _159_795 = (let _159_794 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in ((_159_794), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (_159_795))
in (FStar_All.pipe_right _159_796 pos))
in (let _159_797 = (FStar_Syntax_Syntax.bv_to_name projection)
in ((_159_798), (None), (_159_797))))
in (

let body = (let _159_802 = (let _159_801 = (let _159_800 = (let _159_799 = (FStar_Syntax_Util.branch pat)
in (_159_799)::[])
in ((arg_exp), (_159_800)))
in FStar_Syntax_Syntax.Tm_match (_159_801))
in (FStar_Syntax_Syntax.mk _159_802 None p))
in (

let imp = (no_annot_abs binders body)
in (

let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end else begin
FStar_Syntax_Syntax.Delta_equational
end
in (

let lb = (let _159_804 = (let _159_803 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (_159_803))
in {FStar_Syntax_Syntax.lbname = _159_804; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = imp})
in (

let impl = (let _159_809 = (let _159_808 = (let _159_807 = (let _159_806 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _159_806 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_159_807)::[])
in ((((false), ((lb)::[]))), (p), (_159_808), (quals)))
in FStar_Syntax_Syntax.Sig_let (_159_809))
in if no_decl then begin
(impl)::[]
end else begin
(decl)::(impl)::[]
end))))))))
end))))))
end))
end))))
in (FStar_All.pipe_right _159_810 FStar_List.flatten)))))))))
end)))))))


let mk_data_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env _65_2095 -> (match (_65_2095) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _65_2098, t, l, n, quals, _65_2104, _65_2106) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _65_11 -> (match (_65_11) with
| FStar_Syntax_Syntax.RecordConstructor (_65_2111) -> begin
true
end
| _65_2114 -> begin
false
end)))) then begin
false
end else begin
(match ((FStar_Parser_Env.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > (Prims.parse_int "1"))
end
| _65_2118 -> begin
true
end)
end
in (

let _65_2122 = (FStar_Syntax_Util.arrow_formals t)
in (match (_65_2122) with
| (formals, cod) -> begin
(match (formals) with
| [] -> begin
[]
end
| _65_2125 -> begin
(

let fv_qual = (match ((FStar_Util.find_map quals (fun _65_12 -> (match (_65_12) with
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| _65_2130 -> begin
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

let _65_2138 = (FStar_Util.first_N n formals)
in (match (_65_2138) with
| (tps, rest) -> begin
(mk_indexed_projectors iquals fv_qual refine_domain env l lid inductive_tps tps rest cod)
end))))
end)
end)))
end
| _65_2140 -> begin
[]
end)
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (

let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _159_835 = (FStar_Syntax_Util.incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (_159_835))
end else begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end
in (

let lb = (let _159_840 = (let _159_836 = (FStar_Syntax_Syntax.lid_as_fv lid dd None)
in FStar_Util.Inr (_159_836))
in (let _159_839 = (let _159_837 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars _159_837))
in (let _159_838 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = _159_840; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = _159_839; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _159_838})))
in FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (rng), (lids), (quals))))))


let rec desugar_tycon : FStar_Parser_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (

let tycon_id = (fun _65_13 -> (match (_65_13) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _159_854 = (let _159_853 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_159_853))
in (FStar_Parser_AST.mk_term _159_854 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
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
| _65_2215 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _159_867 = (let _159_866 = (let _159_865 = (binder_to_term b)
in ((out), (_159_865), ((imp_of_aqual b))))
in FStar_Parser_AST.App (_159_866))
in (FStar_Parser_AST.mk_term _159_867 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun _65_14 -> (match (_65_14) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun _65_2230 -> (match (_65_2230) with
| (x, t, _65_2229) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Syntax_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (

let result = (let _159_873 = (let _159_872 = (let _159_871 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_159_871))
in (FStar_Parser_AST.mk_term _159_872 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _159_873 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _159_875 = (FStar_All.pipe_right fields (FStar_List.map (fun _65_2239 -> (match (_65_2239) with
| (x, _65_2236, _65_2238) -> begin
(FStar_Parser_Env.qualify env x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (Some (constrTyp)), (None), (false)))::[])))), (_159_875)))))))
end
| _65_2241 -> begin
(FStar_All.failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals _env mutuals _65_15 -> (match (_65_15) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let _65_2255 = (typars_of_binders _env binders)
in (match (_65_2255) with
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

let tconstr = (let _159_886 = (let _159_885 = (let _159_884 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_159_884))
in (FStar_Parser_AST.mk_term _159_885 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _159_886 binders))
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
| _65_2268 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env bs -> (

let _65_2283 = (FStar_List.fold_left (fun _65_2274 _65_2277 -> (match (((_65_2274), (_65_2277))) with
| ((env, tps), (x, imp)) -> begin
(

let _65_2280 = (FStar_Parser_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (_65_2280) with
| (env, y) -> begin
((env), ((((y), (imp)))::tps))
end))
end)) ((env), ([])) bs)
in (match (_65_2283) with
| (env, bs) -> begin
((env), ((FStar_List.rev bs)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id, bs, kopt))::[] -> begin
(

let kopt = (match (kopt) with
| None -> begin
(let _159_893 = (tm_type_z id.FStar_Ident.idRange)
in Some (_159_893))
end
| _65_2292 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id), (bs), (kopt)))
in (

let _65_2302 = (desugar_abstract_tc quals env [] tc)
in (match (_65_2302) with
| (_65_2296, _65_2298, se, _65_2301) -> begin
(

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _65_2305, typars, k, [], [], quals, rng) -> begin
(

let quals = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
quals
end else begin
(

let _65_2314 = (let _159_895 = (FStar_Range.string_of_range rng)
in (let _159_894 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" _159_895 _159_894)))
in (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals)
end
in (

let t = (match (typars) with
| [] -> begin
k
end
| _65_2319 -> begin
(let _159_898 = (let _159_897 = (let _159_896 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (_159_896)))
in FStar_Syntax_Syntax.Tm_arrow (_159_897))
in (FStar_Syntax_Syntax.mk _159_898 None rng))
end)
in FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t), (quals), (rng)))))
end
| _65_2322 -> begin
se
end)
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in ((env), ((se)::[]))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let _65_2334 = (typars_of_binders env binders)
in (match (_65_2334) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _65_16 -> (match (_65_16) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| _65_2339 -> begin
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

let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _65_17 -> (match (_65_17) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| _65_2347 -> begin
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

let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (

let typars = (FStar_Syntax_Subst.close_binders typars)
in (

let c = (FStar_Syntax_Subst.close_comp typars c)
in (let _159_904 = (let _159_903 = (FStar_Parser_Env.qualify env id)
in (let _159_902 = (FStar_All.pipe_right quals (FStar_List.filter (fun _65_18 -> (match (_65_18) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| _65_2355 -> begin
true
end))))
in ((_159_903), ([]), (typars), (c), (_159_902), (rng))))
in FStar_Syntax_Syntax.Sig_effect_abbrev (_159_904)))))
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
| (FStar_Parser_AST.TyconRecord (_65_2361))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let _65_2367 = (tycon_record_as_variant trec)
in (match (_65_2367) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| (_65_2371)::_65_2369 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_Env.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals et tc -> (

let _65_2382 = et
in (match (_65_2382) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_65_2384) -> begin
(

let trec = tc
in (

let _65_2389 = (tycon_record_as_variant trec)
in (match (_65_2389) with
| (t, fs) -> begin
(collect_tcs ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((env), (tcs)) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let _65_2401 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_65_2401) with
| (env, _65_2398, se, tconstr) -> begin
((env), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals))))::tcs))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let _65_2413 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_65_2413) with
| (env, _65_2410, se, tconstr) -> begin
((env), ((FStar_Util.Inr (((se), (t), (quals))))::tcs))
end))
end
| _65_2415 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (

let _65_2418 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (_65_2418) with
| (env, tcs) -> begin
(

let tcs = (FStar_List.rev tcs)
in (

let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _65_20 -> (match (_65_20) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, _65_2426, _65_2428, _65_2430, _65_2432), t, quals) -> begin
(

let _65_2442 = (push_tparams env tpars)
in (match (_65_2442) with
| (env_tps, _65_2441) -> begin
(

let t = (desugar_term env_tps t)
in (let _159_914 = (let _159_913 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in (([]), (_159_913)))
in (_159_914)::[]))
end))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, _65_2450, tags, _65_2453), constrs, tconstr, quals) -> begin
(

let tycon = ((tname), (tpars), (k))
in (

let _65_2464 = (push_tparams env tpars)
in (match (_65_2464) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun _65_2468 -> (match (_65_2468) with
| (x, _65_2467) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let _65_2494 = (let _159_926 = (FStar_All.pipe_right constrs (FStar_List.map (fun _65_2475 -> (match (_65_2475) with
| (id, topt, _65_2473, of_notation) -> begin
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

let t = (let _159_918 = (FStar_Parser_Env.default_total env_tps)
in (let _159_917 = (close env_tps t)
in (desugar_term _159_918 _159_917)))
in (

let name = (FStar_Parser_Env.qualify env id)
in (

let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _65_19 -> (match (_65_19) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| _65_2489 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (let _159_925 = (let _159_924 = (let _159_923 = (let _159_922 = (let _159_921 = (let _159_920 = (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total _159_920))
in (FStar_Syntax_Util.arrow data_tpars _159_921))
in ((name), (univs), (_159_922), (tname), (ntps), (quals), (mutuals), (rng)))
in FStar_Syntax_Syntax.Sig_datacon (_159_923))
in ((tps), (_159_924)))
in ((name), (_159_925))))))))
end))))
in (FStar_All.pipe_left FStar_List.split _159_926))
in (match (_65_2494) with
| (constrNames, constrs) -> begin
((([]), (FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs), (tpars), (k), (mutuals), (constrNames), (tags), (rng))))))::constrs
end)))
end)))
end
| _65_2496 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (

let bundle = (let _159_928 = (let _159_927 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in ((sigelts), (quals), (_159_927), (rng)))
in FStar_Syntax_Syntax.Sig_bundle (_159_928))
in (

let env = (FStar_Parser_Env.push_sigelt env0 bundle)
in (

let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projectors quals env)))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _65_21 -> (match (_65_21) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, _65_2505, tps, k, _65_2509, constrs, quals, _65_2513) when ((FStar_List.length constrs) > (Prims.parse_int "1")) -> begin
(

let quals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract quals) then begin
(FStar_Syntax_Syntax.Private)::quals
end else begin
quals
end
in (mk_data_discriminators quals env tname tps k constrs))
end
| _65_2518 -> begin
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

let _65_2542 = (FStar_List.fold_left (fun _65_2527 b -> (match (_65_2527) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| (Some (a), k) -> begin
(

let _65_2535 = (FStar_Parser_Env.push_bv env a)
in (match (_65_2535) with
| (env, a) -> begin
(let _159_937 = (let _159_936 = (FStar_Syntax_Syntax.mk_binder (

let _65_2536 = a
in {FStar_Syntax_Syntax.ppname = _65_2536.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_2536.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (_159_936)::binders)
in ((env), (_159_937)))
end))
end
| _65_2539 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end)
end)) ((env), ([])) binders)
in (match (_65_2542) with
| (env, binders) -> begin
((env), ((FStar_List.rev binders)))
end)))


let rec desugar_effect : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  Prims.bool  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_kind eff_decls actions for_free -> (

let env0 = env
in (

let monad_env = (FStar_Parser_Env.enter_monad_scope env eff_name)
in (

let _65_2556 = (desugar_binders monad_env eff_binders)
in (match (_65_2556) with
| (env, binders) -> begin
(

let eff_k = (let _159_958 = (FStar_Parser_Env.default_total env)
in (desugar_term _159_958 eff_kind))
in (

let _65_2567 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _65_2560 decl -> (match (_65_2560) with
| (env, out) -> begin
(

let _65_2564 = (desugar_decl env decl)
in (match (_65_2564) with
| (env, ses) -> begin
(let _159_962 = (let _159_961 = (FStar_List.hd ses)
in (_159_961)::out)
in ((env), (_159_962)))
end))
end)) ((env), ([]))))
in (match (_65_2567) with
| (env, decls) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let actions = (FStar_All.pipe_right actions (FStar_List.map (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (_65_2571, ((FStar_Parser_AST.TyconAbbrev (name, _65_2574, _65_2576, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (_65_2582, ((def, _65_2589))::((cps_type, _65_2585))::[]); FStar_Parser_AST.range = _65_2580; FStar_Parser_AST.level = _65_2578}), _65_2598))::[]) when (not (for_free)) -> begin
(let _159_968 = (FStar_Parser_Env.qualify env name)
in (let _159_967 = (let _159_964 = (desugar_term env def)
in (FStar_Syntax_Subst.close binders _159_964))
in (let _159_966 = (let _159_965 = (desugar_typ env cps_type)
in (FStar_Syntax_Subst.close binders _159_965))
in {FStar_Syntax_Syntax.action_name = _159_968; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = _159_967; FStar_Syntax_Syntax.action_typ = _159_966})))
end
| FStar_Parser_AST.Tycon (_65_2604, ((FStar_Parser_AST.TyconAbbrev (name, _65_2607, _65_2609, defn), _65_2614))::[]) when for_free -> begin
(let _159_971 = (FStar_Parser_Env.qualify env name)
in (let _159_970 = (let _159_969 = (desugar_term env defn)
in (FStar_Syntax_Subst.close binders _159_969))
in {FStar_Syntax_Syntax.action_name = _159_971; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = _159_970; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
end
| _65_2620 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples)."), (d.FStar_Parser_AST.drange)))))
end))))
in (

let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (

let lookup = (fun s -> (

let l = (FStar_Parser_Env.qualify env (FStar_Ident.mk_ident ((s), (d.FStar_Parser_AST.drange))))
in (let _159_975 = (let _159_974 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) _159_974))
in (([]), (_159_975)))))
in (

let mname = (FStar_Parser_Env.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange) quals)
in (

let se = if for_free then begin
(

let dummy_tscheme = (let _159_976 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (([]), (_159_976)))
in (let _159_982 = (let _159_981 = (let _159_980 = (let _159_977 = (lookup "repr")
in (Prims.snd _159_977))
in (let _159_979 = (lookup "return")
in (let _159_978 = (lookup "bind")
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = _159_980; FStar_Syntax_Syntax.return_repr = _159_979; FStar_Syntax_Syntax.bind_repr = _159_978; FStar_Syntax_Syntax.actions = actions})))
in ((_159_981), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (_159_982)))
end else begin
(

let rr = ((FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) || (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable)))
in (

let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in (let _159_998 = (let _159_997 = (let _159_996 = (lookup "return_wp")
in (let _159_995 = (lookup "bind_wp")
in (let _159_994 = (lookup "if_then_else")
in (let _159_993 = (lookup "ite_wp")
in (let _159_992 = (lookup "stronger")
in (let _159_991 = (lookup "close_wp")
in (let _159_990 = (lookup "assert_p")
in (let _159_989 = (lookup "assume_p")
in (let _159_988 = (lookup "null_wp")
in (let _159_987 = (lookup "trivial")
in (let _159_986 = if rr then begin
(let _159_983 = (lookup "repr")
in (FStar_All.pipe_left Prims.snd _159_983))
end else begin
FStar_Syntax_Syntax.tun
end
in (let _159_985 = if rr then begin
(lookup "return")
end else begin
un_ts
end
in (let _159_984 = if rr then begin
(lookup "bind")
end else begin
un_ts
end
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = _159_996; FStar_Syntax_Syntax.bind_wp = _159_995; FStar_Syntax_Syntax.if_then_else = _159_994; FStar_Syntax_Syntax.ite_wp = _159_993; FStar_Syntax_Syntax.stronger = _159_992; FStar_Syntax_Syntax.close_wp = _159_991; FStar_Syntax_Syntax.assert_p = _159_990; FStar_Syntax_Syntax.assume_p = _159_989; FStar_Syntax_Syntax.null_wp = _159_988; FStar_Syntax_Syntax.trivial = _159_987; FStar_Syntax_Syntax.repr = _159_986; FStar_Syntax_Syntax.return_repr = _159_985; FStar_Syntax_Syntax.bind_repr = _159_984; FStar_Syntax_Syntax.actions = actions})))))))))))))
in ((_159_997), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_new_effect (_159_998))))
end
in (

let env = (FStar_Parser_Env.push_sigelt env0 se)
in (

let env = (FStar_All.pipe_right actions (FStar_List.fold_left (fun env a -> (let _159_1001 = (FStar_Syntax_Util.action_as_lb a)
in (FStar_Parser_Env.push_sigelt env _159_1001))) env))
in (

let env = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable)) then begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_Parser_Env.qualify monad_env))
in (

let refl_decl = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable)::[]), (d.FStar_Parser_AST.drange)))
in (FStar_Parser_Env.push_sigelt env refl_decl)))
end else begin
env
end
in ((env), ((se)::[]))))))))))))
end)))
end)))))
and desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (

let trans_qual = (trans_qual d.FStar_Parser_AST.drange)
in (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(

let se = FStar_Syntax_Syntax.Sig_pragma ((((trans_pragma p)), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[])))
end
| FStar_Parser_AST.Fsdoc (_65_2646) -> begin
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
(let _159_1005 = (FStar_Parser_Env.push_module_abbrev env x l)
in ((_159_1005), ([])))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(

let tcs = (FStar_List.map (fun _65_2664 -> (match (_65_2664) with
| (x, _65_2663) -> begin
x
end)) tcs)
in (let _159_1007 = (FStar_List.map trans_qual qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _159_1007 tcs)))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _159_1009 = (let _159_1008 = (desugar_term_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Syntax_Subst.compress _159_1008))
in _159_1009.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let (lbs, _65_2673) -> begin
(

let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals = (match (quals) with
| (_65_2681)::_65_2679 -> begin
(FStar_List.map trans_qual quals)
end
| _65_2684 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _65_22 -> (match (_65_22) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (_65_2695); FStar_Syntax_Syntax.lbunivs = _65_2693; FStar_Syntax_Syntax.lbtyp = _65_2691; FStar_Syntax_Syntax.lbeff = _65_2689; FStar_Syntax_Syntax.lbdef = _65_2687} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _65_2705; FStar_Syntax_Syntax.lbtyp = _65_2703; FStar_Syntax_Syntax.lbeff = _65_2701; FStar_Syntax_Syntax.lbdef = _65_2699} -> begin
(FStar_Parser_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals = if (FStar_All.pipe_right lets (FStar_Util.for_some (fun _65_2713 -> (match (_65_2713) with
| (_65_2711, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end)))) then begin
(FStar_Syntax_Syntax.Logic)::quals
end else begin
quals
end
in (

let lbs = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _159_1014 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _65_2717 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let _65_2719 = fv
in {FStar_Syntax_Syntax.fv_name = _65_2719.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = _65_2719.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = _65_2717.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _65_2717.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _65_2717.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _65_2717.FStar_Syntax_Syntax.lbdef})))))
in (((Prims.fst lbs)), (_159_1014)))
end else begin
lbs
end
in (

let s = (let _159_1017 = (let _159_1016 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in ((lbs), (d.FStar_Parser_AST.drange), (_159_1016), (quals)))
in FStar_Syntax_Syntax.Sig_let (_159_1017))
in (

let env = (FStar_Parser_Env.push_sigelt env s)
in ((env), ((s)::[]))))))))
end
| _65_2726 -> begin
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
in (let _159_1021 = (let _159_1020 = (let _159_1019 = (let _159_1018 = (FStar_Parser_Env.qualify env id)
in ((_159_1018), (f), ((FStar_Syntax_Syntax.Assumption)::[]), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_assume (_159_1019))
in (_159_1020)::[])
in ((env), (_159_1021))))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(

let t = (let _159_1022 = (close_fun env t)
in (desugar_term env _159_1022))
in (

let quals = if (env.FStar_Parser_Env.iface && env.FStar_Parser_Env.admitted_iface) then begin
(FStar_Parser_AST.Assumption)::quals
end else begin
quals
end
in (

let se = (let _159_1025 = (let _159_1024 = (FStar_Parser_Env.qualify env id)
in (let _159_1023 = (FStar_List.map trans_qual quals)
in ((_159_1024), ([]), (t), (_159_1023), (d.FStar_Parser_AST.drange))))
in FStar_Syntax_Syntax.Sig_declare_typ (_159_1025))
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in ((env), ((se)::[]))))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(

let _65_2753 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (match (_65_2753) with
| (t, _65_2752) -> begin
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

let t = (let _159_1030 = (let _159_1026 = (FStar_Syntax_Syntax.null_binder t)
in (_159_1026)::[])
in (let _159_1029 = (let _159_1028 = (let _159_1027 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (Prims.fst _159_1027))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _159_1028))
in (FStar_Syntax_Util.arrow _159_1030 _159_1029)))
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

let _65_2782 = (desugar_binders env binders)
in (match (_65_2782) with
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
(

let env0 = env
in (

let _65_2798 = (desugar_binders env eff_binders)
in (match (_65_2798) with
| (env, binders) -> begin
(

let _65_2809 = (

let _65_2801 = (head_and_args defn)
in (match (_65_2801) with
| (head, args) -> begin
(

let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_defn env) l)
end
| _65_2805 -> begin
(let _159_1035 = (let _159_1034 = (let _159_1033 = (let _159_1032 = (let _159_1031 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat _159_1031 " not found"))
in (Prims.strcat "Effect " _159_1032))
in ((_159_1033), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_159_1034))
in (Prims.raise _159_1035))
end)
in (let _159_1036 = (desugar_args env args)
in ((ed), (_159_1036))))
end))
in (match (_65_2809) with
| (ed, args) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let sub = (fun _65_2815 -> (match (_65_2815) with
| (_65_2813, x) -> begin
(

let _65_2818 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (_65_2818) with
| (edb, x) -> begin
(

let _65_2819 = if ((FStar_List.length args) <> (FStar_List.length edb)) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected number of arguments to effect constructor"), (defn.FStar_Parser_AST.range)))))
end else begin
()
end
in (

let s = (FStar_Syntax_Util.subst_of_list edb args)
in (let _159_1040 = (let _159_1039 = (FStar_Syntax_Subst.subst s x)
in (FStar_Syntax_Subst.close binders _159_1039))
in (([]), (_159_1040)))))
end))
end))
in (

let ed = (let _159_1054 = (FStar_List.map trans_qual quals)
in (let _159_1053 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _159_1052 = (let _159_1041 = (sub (([]), (ed.FStar_Syntax_Syntax.signature)))
in (Prims.snd _159_1041))
in (let _159_1051 = (sub ed.FStar_Syntax_Syntax.ret_wp)
in (let _159_1050 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (let _159_1049 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (let _159_1048 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (let _159_1047 = (sub ed.FStar_Syntax_Syntax.stronger)
in (let _159_1046 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (let _159_1045 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (let _159_1044 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (let _159_1043 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (let _159_1042 = (sub ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _159_1054; FStar_Syntax_Syntax.mname = _159_1053; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = _159_1052; FStar_Syntax_Syntax.ret_wp = _159_1051; FStar_Syntax_Syntax.bind_wp = _159_1050; FStar_Syntax_Syntax.if_then_else = _159_1049; FStar_Syntax_Syntax.ite_wp = _159_1048; FStar_Syntax_Syntax.stronger = _159_1047; FStar_Syntax_Syntax.close_wp = _159_1046; FStar_Syntax_Syntax.assert_p = _159_1045; FStar_Syntax_Syntax.assume_p = _159_1044; FStar_Syntax_Syntax.null_wp = _159_1043; FStar_Syntax_Syntax.trivial = _159_1042; FStar_Syntax_Syntax.repr = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.return_repr = (([]), (FStar_Syntax_Syntax.tun)); FStar_Syntax_Syntax.bind_repr = (([]), (FStar_Syntax_Syntax.tun)); FStar_Syntax_Syntax.actions = []})))))))))))))
in (

let se = FStar_Syntax_Syntax.Sig_new_effect (((ed), (d.FStar_Parser_AST.drange)))
in (

let env = (FStar_Parser_Env.push_sigelt env0 se)
in ((env), ((se)::[])))))))
end))
end)))
end
| FStar_Parser_AST.NewEffectForFree (_65_2826, FStar_Parser_AST.RedefineEffect (_65_2828)) -> begin
(FStar_All.failwith "impossible")
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
(let _159_1061 = (let _159_1060 = (let _159_1059 = (let _159_1058 = (let _159_1057 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat _159_1057 " not found"))
in (Prims.strcat "Effect name " _159_1058))
in ((_159_1059), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_159_1060))
in (Prims.raise _159_1061))
end
| Some (l) -> begin
l
end))
in (

let src = (lookup l.FStar_Parser_AST.msource)
in (

let dst = (lookup l.FStar_Parser_AST.mdest)
in (

let _65_2869 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(let _159_1063 = (let _159_1062 = (desugar_term env t)
in (([]), (_159_1062)))
in ((_159_1063), (None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(let _159_1068 = (let _159_1064 = (desugar_term env wp)
in (([]), (_159_1064)))
in (let _159_1067 = (let _159_1066 = (let _159_1065 = (desugar_term env t)
in (([]), (_159_1065)))
in Some (_159_1066))
in ((_159_1068), (_159_1067))))
end)
in (match (_65_2869) with
| (lift_wp, lift) -> begin
(

let se = FStar_Syntax_Syntax.Sig_sub_effect ((({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift}), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[])))
end)))))
end)))


let desugar_decls : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _65_2875 d -> (match (_65_2875) with
| (env, sigelts) -> begin
(

let _65_2879 = (desugar_decl env d)
in (match (_65_2879) with
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

let _65_2902 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _159_1086 = (FStar_Parser_Env.prepare_module_or_interface true admitted env mname)
in ((_159_1086), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _159_1087 = (FStar_Parser_Env.prepare_module_or_interface false false env mname)
in ((_159_1087), (mname), (decls), (false)))
end)
in (match (_65_2902) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(

let _65_2905 = (desugar_decls env decls)
in (match (_65_2905) with
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
| FStar_Parser_AST.Interface (mname, _65_2916, _65_2918) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (

let _65_2926 = (desugar_modul_common curmod env m)
in (match (_65_2926) with
| (x, y, _65_2925) -> begin
((x), (y))
end))))


let desugar_modul : FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (

let _65_2932 = (desugar_modul_common None env m)
in (match (_65_2932) with
| (env, modul, pop_when_done) -> begin
(

let env = (FStar_Parser_Env.finish_module_or_interface env modul)
in (

let _65_2934 = if (FStar_Options.dump_module modul.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _159_1098 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _159_1098))
end else begin
()
end
in (let _159_1099 = if pop_when_done then begin
(FStar_Parser_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end else begin
env
end
in ((_159_1099), (modul)))))
end)))


let desugar_file : FStar_Parser_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (

let _65_2947 = (FStar_List.fold_left (fun _65_2940 m -> (match (_65_2940) with
| (env, mods) -> begin
(

let _65_2944 = (desugar_modul env m)
in (match (_65_2944) with
| (env, m) -> begin
((env), ((m)::mods))
end))
end)) ((env), ([])) f)
in (match (_65_2947) with
| (env, mods) -> begin
((env), ((FStar_List.rev mods)))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Parser_Env.env  ->  FStar_Parser_Env.env = (fun m en -> (

let _65_2952 = (FStar_Parser_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (_65_2952) with
| (en, pop_when_done) -> begin
(

let en = (FStar_List.fold_left FStar_Parser_Env.push_sigelt (

let _65_2953 = en
in {FStar_Parser_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_Parser_Env.modules = _65_2953.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _65_2953.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _65_2953.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _65_2953.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _65_2953.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _65_2953.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _65_2953.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _65_2953.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _65_2953.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _65_2953.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = _65_2953.FStar_Parser_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (

let env = (FStar_Parser_Env.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_Env.export_interface m.FStar_Syntax_Syntax.name env)
end else begin
env
end))
end)))




