
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
| _65_101 -> begin
"UNKNOWN"
end))
in (

let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _159_38 = (let _159_36 = (FStar_Util.char_at s i)
in (name_of_char _159_36))
in (let _159_37 = (aux (i + (Prims.parse_int "1")))
in (_159_38)::_159_37))
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
| _65_110 -> begin
(let _159_40 = (let _159_39 = (aux (Prims.parse_int "0"))
in (FStar_String.concat "_" _159_39))
in (Prims.strcat "op_" _159_40))
end))))


let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _159_50 = (let _159_49 = (let _159_48 = (let _159_47 = (compile_op n s)
in ((_159_47), (r)))
in (FStar_Ident.mk_ident _159_48))
in (_159_49)::[])
in (FStar_All.pipe_right _159_50 FStar_Ident.lid_of_ids)))


let op_as_term : FStar_Parser_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.term Prims.option = (fun env arity rng s -> (

let r = (fun l dd -> (let _159_65 = (let _159_64 = (let _159_63 = (FStar_Ident.set_lid_range l rng)
in (FStar_Syntax_Syntax.lid_as_fv _159_63 dd None))
in (FStar_All.pipe_right _159_64 FStar_Syntax_Syntax.fv_to_tm))
in Some (_159_65)))
in (

let fallback = (fun _65_122 -> (match (()) with
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
| _65_150 -> begin
None
end)
end))
in (match ((let _159_68 = (compile_op_lid arity s rng)
in (FStar_Parser_Env.try_lookup_lid env _159_68))) with
| Some (t) -> begin
Some ((Prims.fst t))
end
| _65_154 -> begin
(fallback ())
end))))


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _159_75 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _159_75)))


let rec free_type_vars_b : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_65_163) -> begin
((env), ([]))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let _65_170 = (FStar_Parser_Env.push_bv env x)
in (match (_65_170) with
| (env, _65_169) -> begin
((env), ((x)::[]))
end))
end
| FStar_Parser_AST.Annotated (_65_172, term) -> begin
(let _159_82 = (free_type_vars env term)
in ((env), (_159_82)))
end
| FStar_Parser_AST.TAnnotated (id, _65_178) -> begin
(

let _65_184 = (FStar_Parser_Env.push_bv env id)
in (match (_65_184) with
| (env, _65_183) -> begin
((env), ([]))
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _159_83 = (free_type_vars env t)
in ((env), (_159_83)))
end))
and free_type_vars : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _159_86 = (unparen t)
in _159_86.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (_65_190) -> begin
(FStar_All.failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_Env.try_lookup_id env a)) with
| None -> begin
(a)::[]
end
| _65_196 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Assign (_, t)) | (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_65_230, ts) -> begin
(FStar_List.collect (fun _65_237 -> (match (_65_237) with
| (t, _65_236) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_65_239, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _65_246) -> begin
(let _159_89 = (free_type_vars env t1)
in (let _159_88 = (free_type_vars env t2)
in (FStar_List.append _159_89 _159_88)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(

let _65_255 = (free_type_vars_b env b)
in (match (_65_255) with
| (env, f) -> begin
(let _159_90 = (free_type_vars env t)
in (FStar_List.append f _159_90))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(

let _65_271 = (FStar_List.fold_left (fun _65_264 binder -> (match (_65_264) with
| (env, free) -> begin
(

let _65_268 = (free_type_vars_b env binder)
in (match (_65_268) with
| (env, f) -> begin
((env), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (_65_271) with
| (env, free) -> begin
(let _159_93 = (free_type_vars env body)
in (FStar_List.append free _159_93))
end))
end
| FStar_Parser_AST.Project (t, _65_274) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
[]
end))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (

let rec aux = (fun args t -> (match ((let _159_100 = (unparen t)
in _159_100.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| _65_321 -> begin
((t), (args))
end))
in (aux [] t)))


let close : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _159_105 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _159_105))
in if ((FStar_List.length ftv) = (Prims.parse_int "0")) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _159_109 = (let _159_108 = (let _159_107 = (tm_type x.FStar_Ident.idRange)
in ((x), (_159_107)))
in FStar_Parser_AST.TAnnotated (_159_108))
in (FStar_Parser_AST.mk_binder _159_109 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))


let close_fun : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _159_114 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _159_114))
in if ((FStar_List.length ftv) = (Prims.parse_int "0")) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _159_118 = (let _159_117 = (let _159_116 = (tm_type x.FStar_Ident.idRange)
in ((x), (_159_116)))
in FStar_Parser_AST.TAnnotated (_159_117))
in (FStar_Parser_AST.mk_binder _159_118 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let t = (match ((let _159_119 = (unparen t)
in _159_119.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_65_334) -> begin
t
end
| _65_337 -> begin
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
| _65_347 -> begin
((bs), (t))
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _65_351) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_65_357); FStar_Parser_AST.prange = _65_355}, _65_361) -> begin
true
end
| _65_365 -> begin
false
end))


let rec destruct_app_pattern : FStar_Parser_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _65_377 = (destruct_app_pattern env is_top_level p)
in (match (_65_377) with
| (name, args, _65_376) -> begin
((name), (args), (Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _65_382); FStar_Parser_AST.prange = _65_379}, args) when is_top_level -> begin
(let _159_133 = (let _159_132 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_159_132))
in ((_159_133), (args), (None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _65_393); FStar_Parser_AST.prange = _65_390}, args) -> begin
((FStar_Util.Inl (id)), (args), (None))
end
| _65_401 -> begin
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
| LocalBinder (_65_404) -> begin
_65_404
end))


let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_65_407) -> begin
_65_407
end))


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun _65_6 -> (match (_65_6) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| _65_414 -> begin
(FStar_All.failwith "Impossible")
end))


let as_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_Parser_Env.env) = (fun env imp _65_7 -> (match (_65_7) with
| (None, k) -> begin
(let _159_170 = (FStar_Syntax_Syntax.null_binder k)
in ((_159_170), (env)))
end
| (Some (a), k) -> begin
(

let _65_427 = (FStar_Parser_Env.push_bv env a)
in (match (_65_427) with
| (env, a) -> begin
(((((

let _65_428 = a
in {FStar_Syntax_Syntax.ppname = _65_428.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_428.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), ((trans_aqual imp)))), (env))
end))
end))


type env_t =
FStar_Parser_Env.env


type lenv_t =
FStar_Syntax_Syntax.bv Prims.list


let mk_lb : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.letbinding = (fun _65_433 -> (match (_65_433) with
| (n, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))


let no_annot_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t None))


let mk_ref_read = (fun tm -> (

let tm' = (let _159_183 = (let _159_182 = (let _159_178 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _159_178))
in (let _159_181 = (let _159_180 = (let _159_179 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (_159_179)))
in (_159_180)::[])
in ((_159_182), (_159_181))))
in FStar_Syntax_Syntax.Tm_app (_159_183))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_alloc = (fun tm -> (

let tm' = (let _159_190 = (let _159_189 = (let _159_185 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _159_185))
in (let _159_188 = (let _159_187 = (let _159_186 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (_159_186)))
in (_159_187)::[])
in ((_159_189), (_159_188))))
in FStar_Syntax_Syntax.Tm_app (_159_190))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_assign = (fun t1 t2 pos -> (

let tm = (let _159_202 = (let _159_201 = (let _159_194 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _159_194))
in (let _159_200 = (let _159_199 = (let _159_195 = (FStar_Syntax_Syntax.as_implicit false)
in ((t1), (_159_195)))
in (let _159_198 = (let _159_197 = (let _159_196 = (FStar_Syntax_Syntax.as_implicit false)
in ((t2), (_159_196)))
in (_159_197)::[])
in (_159_199)::_159_198))
in ((_159_201), (_159_200))))
in FStar_Syntax_Syntax.Tm_app (_159_202))
in (FStar_Syntax_Syntax.mk tm None pos)))


let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun _65_8 -> (match (_65_8) with
| ("repr") | ("post") | ("pre") | ("wp") -> begin
true
end
| _65_450 -> begin
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
| FStar_Syntax_Syntax.Pat_cons (_65_470, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out _65_478 -> (match (_65_478) with
| (p, _65_477) -> begin
(let _159_251 = (pat_vars p)
in (FStar_Util.set_union out _159_251))
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

let _65_501 = (match (((is_mut), (p.FStar_Parser_AST.pat))) with
| ((false, _)) | ((true, FStar_Parser_AST.PatVar (_))) -> begin
()
end
| (true, _65_499) -> begin
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
| _65_512 -> begin
(

let _65_515 = (push_bv_maybe_mut e x)
in (match (_65_515) with
| (e, x) -> begin
(((x)::l), (e), (x))
end))
end))
in (

let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun b -> (b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText))))) with
| Some (b) -> begin
((l), (e), (b))
end
| _65_524 -> begin
(

let _65_527 = (push_bv_maybe_mut e a)
in (match (_65_527) with
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
(let _159_287 = (let _159_286 = (let _159_285 = (let _159_284 = (let _159_283 = (compile_op (Prims.parse_int "0") op)
in (FStar_Ident.id_of_text _159_283))
in ((_159_284), (None)))
in FStar_Parser_AST.PatVar (_159_285))
in {FStar_Parser_AST.pat = _159_286; FStar_Parser_AST.prange = p.FStar_Parser_AST.prange})
in (aux loc env _159_287))
end
| FStar_Parser_AST.PatOr ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.PatOr ((p)::ps) -> begin
(

let _65_551 = (aux loc env p)
in (match (_65_551) with
| (loc, env, var, p, _65_550) -> begin
(

let _65_568 = (FStar_List.fold_left (fun _65_555 p -> (match (_65_555) with
| (loc, env, ps) -> begin
(

let _65_564 = (aux loc env p)
in (match (_65_564) with
| (loc, env, _65_560, p, _65_563) -> begin
((loc), (env), ((p)::ps))
end))
end)) ((loc), (env), ([])) ps)
in (match (_65_568) with
| (loc, env, ps) -> begin
(

let pat = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in ((loc), (env), (var), (pat), (false)))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _65_579 = (aux loc env p)
in (match (_65_579) with
| (loc, env', binder, p, imp) -> begin
(

let binder = (match (binder) with
| LetBinder (_65_581) -> begin
(FStar_All.failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t = (let _159_290 = (close_fun env t)
in (desugar_term env _159_290))
in LocalBinder ((((

let _65_588 = x
in {FStar_Syntax_Syntax.ppname = _65_588.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_588.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (aq))))
end)
in ((loc), (env'), (binder), (p), (imp)))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _159_291 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env), (LocalBinder (((x), (None)))), (_159_291), (false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _159_292 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env), (LocalBinder (((x), (None)))), (_159_292), (false))))
end
| (FStar_Parser_AST.PatTvar (x, aq)) | (FStar_Parser_AST.PatVar (x, aq)) -> begin
(

let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (

let aq = (trans_aqual aq)
in (

let _65_607 = (resolvex loc env x)
in (match (_65_607) with
| (loc, env, xbv) -> begin
(let _159_293 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc), (env), (LocalBinder (((xbv), (aq)))), (_159_293), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _159_294 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), ([])))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_159_294), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _65_613}, args) -> begin
(

let _65_635 = (FStar_List.fold_right (fun arg _65_624 -> (match (_65_624) with
| (loc, env, args) -> begin
(

let _65_631 = (aux loc env arg)
in (match (_65_631) with
| (loc, env, _65_628, arg, imp) -> begin
((loc), (env), ((((arg), (imp)))::args))
end))
end)) args ((loc), (env), ([])))
in (match (_65_635) with
| (loc, env, args) -> begin
(

let l = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _159_297 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_159_297), (false)))))
end))
end
| FStar_Parser_AST.PatApp (_65_639) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let _65_659 = (FStar_List.fold_right (fun pat _65_647 -> (match (_65_647) with
| (loc, env, pats) -> begin
(

let _65_655 = (aux loc env pat)
in (match (_65_655) with
| (loc, env, _65_651, pat, _65_654) -> begin
((loc), (env), ((pat)::pats))
end))
end)) pats ((loc), (env), ([])))
in (match (_65_659) with
| (loc, env, pats) -> begin
(

let pat = (let _159_310 = (let _159_309 = (let _159_305 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _159_305))
in (let _159_308 = (let _159_307 = (let _159_306 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_159_306), ([])))
in FStar_Syntax_Syntax.Pat_cons (_159_307))
in (FStar_All.pipe_left _159_309 _159_308)))
in (FStar_List.fold_right (fun hd tl -> (

let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (let _159_304 = (let _159_303 = (let _159_302 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_159_302), ((((hd), (false)))::(((tl), (false)))::[])))
in FStar_Syntax_Syntax.Pat_cons (_159_303))
in (FStar_All.pipe_left (pos_r r) _159_304)))) pats _159_310))
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc), (env), (LocalBinder (((x), (None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(

let _65_685 = (FStar_List.fold_left (fun _65_672 p -> (match (_65_672) with
| (loc, env, pats) -> begin
(

let _65_681 = (aux loc env p)
in (match (_65_681) with
| (loc, env, _65_677, pat, _65_680) -> begin
((loc), (env), ((((pat), (false)))::pats))
end))
end)) ((loc), (env), ([])) args)
in (match (_65_685) with
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

let _65_691 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) l)
in (match (_65_691) with
| (constr, _65_690) -> begin
(

let l = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| _65_695 -> begin
(FStar_All.failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _159_313 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_159_313), (false)))))
end))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(

let _65_705 = (FStar_List.hd fields)
in (match (_65_705) with
| (f, _65_704) -> begin
(

let _65_709 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_65_709) with
| (record, _65_708) -> begin
(

let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _65_712 -> (match (_65_712) with
| (f, p) -> begin
(let _159_315 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.qualify_field_to_record env record) f)
in ((_159_315), (p)))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _65_717 -> (match (_65_717) with
| (f, _65_716) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _65_721 -> (match (_65_721) with
| (g, _65_720) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_65_724, p) -> begin
p
end)
end))))
in (

let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_Env.constrname)) p.FStar_Parser_AST.prange)), (args)))) p.FStar_Parser_AST.prange)
in (

let _65_736 = (aux loc env app)
in (match (_65_736) with
| (env, e, b, p, _65_735) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(let _159_324 = (let _159_323 = (let _159_322 = (

let _65_741 = fv
in (let _159_321 = (let _159_320 = (let _159_319 = (let _159_318 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_Env.typename), (_159_318)))
in FStar_Syntax_Syntax.Record_ctor (_159_319))
in Some (_159_320))
in {FStar_Syntax_Syntax.fv_name = _65_741.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = _65_741.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _159_321}))
in ((_159_322), (args)))
in FStar_Syntax_Syntax.Pat_cons (_159_323))
in (FStar_All.pipe_left pos _159_324))
end
| _65_744 -> begin
p
end)
in ((env), (e), (b), (p), (false)))
end)))))
end))
end))
end))))
in (

let _65_753 = (aux [] env p)
in (match (_65_753) with
| (_65_747, env, b, p, _65_752) -> begin
(

let _65_754 = (let _159_325 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore _159_325))
in ((env), (b), (p)))
end)))))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p is_mut -> (

let mklet = (fun x -> (let _159_334 = (let _159_333 = (let _159_332 = (FStar_Parser_Env.qualify env x)
in ((_159_332), (FStar_Syntax_Syntax.tun)))
in LetBinder (_159_333))
in ((env), (_159_334), (None))))
in if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(let _159_336 = (let _159_335 = (compile_op (Prims.parse_int "0") x)
in (FStar_Ident.id_of_text _159_335))
in (mklet _159_336))
end
| FStar_Parser_AST.PatVar (x, _65_766) -> begin
(mklet x)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _65_773); FStar_Parser_AST.prange = _65_770}, t) -> begin
(let _159_340 = (let _159_339 = (let _159_338 = (FStar_Parser_Env.qualify env x)
in (let _159_337 = (desugar_term env t)
in ((_159_338), (_159_337))))
in LetBinder (_159_339))
in ((env), (_159_340), (None)))
end
| _65_781 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end else begin
(

let _65_785 = (desugar_data_pat env p is_mut)
in (match (_65_785) with
| (env, binder, p) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| _65_793 -> begin
Some (p)
end)
in ((env), (binder), (p)))
end))
end))
and desugar_binding_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun _65_797 env pat -> (

let _65_805 = (desugar_data_pat env pat false)
in (match (_65_805) with
| (env, _65_803, pat) -> begin
((env), (pat))
end)))
and desugar_match_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let _65_810 = env
in {FStar_Parser_Env.curmodule = _65_810.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _65_810.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _65_810.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _65_810.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _65_810.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _65_810.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _65_810.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _65_810.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _65_810.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _65_810.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _65_810.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let _65_815 = env
in {FStar_Parser_Env.curmodule = _65_815.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _65_815.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _65_815.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _65_815.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _65_815.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _65_815.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _65_815.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _65_815.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _65_815.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _65_815.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _65_815.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_machine_integer : FStar_Parser_Env.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env repr _65_822 range -> (match (_65_822) with
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
(let _159_356 = (FStar_Util.format1 "%s not in scope\n" (FStar_Ident.text_of_lid lid))
in (FStar_All.failwith _159_356))
end)
in (

let repr = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (None))))) None range)
in (let _159_361 = (let _159_360 = (let _159_359 = (let _159_358 = (let _159_357 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr), (_159_357)))
in (_159_358)::[])
in ((lid), (_159_359)))
in FStar_Syntax_Syntax.Tm_app (_159_360))
in (FStar_Syntax_Syntax.mk _159_361 None range))))))
end))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (

let mk = (fun e -> (FStar_Syntax_Syntax.mk e None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let _65_846 = e
in {FStar_Syntax_Syntax.n = _65_846.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _65_846.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _65_846.FStar_Syntax_Syntax.vars}))
in (match ((let _159_369 = (unparen top)
in _159_369.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (_65_850) -> begin
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
| FStar_Parser_AST.Op ("*", (_65_876)::(_65_874)::[]) when (let _159_370 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right _159_370 FStar_Option.isNone)) -> begin
(

let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", (t1)::(t2)::[]) -> begin
(let _159_373 = (flatten t1)
in (FStar_List.append _159_373 ((t2)::[])))
end
| _65_889 -> begin
(t)::[]
end))
in (

let targs = (let _159_377 = (let _159_374 = (unparen top)
in (flatten _159_374))
in (FStar_All.pipe_right _159_377 (FStar_List.map (fun t -> (let _159_376 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg _159_376))))))
in (

let _65_895 = (let _159_378 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) _159_378))
in (match (_65_895) with
| (tup, _65_894) -> begin
(mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _159_380 = (let _159_379 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) a)
in (Prims.fst _159_379))
in (FStar_All.pipe_left setpos _159_380))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Unexpected or unbound operator: " s)), (top.FStar_Parser_AST.range)))))
end
| Some (op) -> begin
if ((FStar_List.length args) > (Prims.parse_int "0")) then begin
(

let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _159_382 = (desugar_term env t)
in ((_159_382), (None))))))
in (mk (FStar_Syntax_Syntax.Tm_app (((op), (args))))))
end else begin
op
end
end)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _65_913; FStar_Ident.ident = _65_911; FStar_Ident.nsstr = _65_909; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _65_922; FStar_Ident.ident = _65_920; FStar_Ident.nsstr = _65_918; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _65_931; FStar_Ident.ident = _65_929; FStar_Ident.nsstr = _65_927; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _65_940; FStar_Ident.ident = _65_938; FStar_Ident.nsstr = _65_936; FStar_Ident.str = "True"}) -> begin
(let _159_383 = (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _159_383 FStar_Syntax_Syntax.Delta_constant None))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _65_949; FStar_Ident.ident = _65_947; FStar_Ident.nsstr = _65_945; FStar_Ident.str = "False"}) -> begin
(let _159_384 = (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _159_384 FStar_Syntax_Syntax.Delta_constant None))
end
| FStar_Parser_AST.Var ({FStar_Ident.ns = (eff)::rest; FStar_Ident.ident = {FStar_Ident.idText = txt; FStar_Ident.idRange = _65_957}; FStar_Ident.nsstr = _65_955; FStar_Ident.str = _65_953}) when ((is_special_effect_combinator txt) && (let _159_385 = (FStar_Ident.lid_of_ids ((eff)::rest))
in (FStar_Parser_Env.is_effect_name env _159_385))) -> begin
(match ((let _159_386 = (FStar_Ident.lid_of_ids ((eff)::rest))
in (FStar_Parser_Env.try_lookup_effect_defn env _159_386))) with
| Some (ed) -> begin
(let _159_387 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" txt))) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.fvar _159_387 (FStar_Syntax_Syntax.Delta_unfoldable ((Prims.parse_int "1"))) None))
end
| None -> begin
(FStar_All.failwith "immpossible special_effect_combinator")
end)
end
| FStar_Parser_AST.Assign (ident, t2) -> begin
(

let t2 = (desugar_term env t2)
in (

let _65_975 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) ident)
in (match (_65_975) with
| (t1, mut) -> begin
(

let _65_976 = if (not (mut)) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Can only assign to mutable values"), (top.FStar_Parser_AST.range)))))
end else begin
()
end
in (mk_ref_assign t1 t2 top.FStar_Parser_AST.range))
end)))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(

let _65_983 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) l)
in (match (_65_983) with
| (tm, mut) -> begin
(

let tm = (setpos tm)
in if mut then begin
(let _159_390 = (let _159_389 = (let _159_388 = (mk_ref_read tm)
in ((_159_388), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval))))
in FStar_Syntax_Syntax.Tm_meta (_159_389))
in (FStar_All.pipe_left mk _159_390))
end else begin
tm
end)
end))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(match ((FStar_Parser_Env.try_lookup_datacon env l)) with
| Some (head) -> begin
(

let _65_993 = (let _159_391 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in ((_159_391), (true)))
in (match (_65_993) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| _65_996 -> begin
(

let args = (FStar_List.map (fun _65_999 -> (match (_65_999) with
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
| ((e, _65_1008))::[] -> begin
(desugar_term_maybe_top top_level env e)
end
| _65_1012 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("The Foo.Bar (...) local open takes exactly one argument"), (top.FStar_Parser_AST.range)))))
end)))
end)
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let _65_1037 = (FStar_List.fold_left (fun _65_1020 b -> (match (_65_1020) with
| (env, tparams, typs) -> begin
(

let _65_1024 = (desugar_binder env b)
in (match (_65_1024) with
| (xopt, t) -> begin
(

let _65_1030 = (match (xopt) with
| None -> begin
(let _159_395 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env), (_159_395)))
end
| Some (x) -> begin
(FStar_Parser_Env.push_bv env x)
end)
in (match (_65_1030) with
| (env, x) -> begin
(let _159_399 = (let _159_398 = (let _159_397 = (let _159_396 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _159_396))
in (_159_397)::[])
in (FStar_List.append typs _159_398))
in ((env), ((FStar_List.append tparams (((((

let _65_1031 = x
in {FStar_Syntax_Syntax.ppname = _65_1031.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_1031.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (None)))::[]))), (_159_399)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_65_1037) with
| (env, _65_1035, targs) -> begin
(

let _65_1041 = (let _159_400 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) _159_400))
in (match (_65_1041) with
| (tup, _65_1040) -> begin
(FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let _65_1048 = (uncurry binders t)
in (match (_65_1048) with
| (bs, t) -> begin
(

let rec aux = (fun env bs _65_9 -> (match (_65_9) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (let _159_407 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos _159_407)))
end
| (hd)::tl -> begin
(

let mlenv = (FStar_Parser_Env.default_ml env)
in (

let bb = (desugar_binder mlenv hd)
in (

let _65_1062 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_65_1062) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_binder env b)) with
| (None, _65_1069) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(

let _65_1077 = (as_binder env None b)
in (match (_65_1077) with
| ((x, _65_1074), env) -> begin
(

let f = (desugar_formula env f)
in (let _159_408 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos _159_408)))
end))
end)
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let _65_1097 = (FStar_List.fold_left (fun _65_1085 pat -> (match (_65_1085) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (_65_1088, t) -> begin
(let _159_412 = (let _159_411 = (free_type_vars env t)
in (FStar_List.append _159_411 ftvs))
in ((env), (_159_412)))
end
| _65_1093 -> begin
((env), (ftvs))
end)
end)) ((env), ([])) binders)
in (match (_65_1097) with
| (_65_1095, ftv) -> begin
(

let ftv = (sort_ftv ftv)
in (

let binders = (let _159_414 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append _159_414 binders))
in (

let rec aux = (fun env bs sc_pat_opt _65_10 -> (match (_65_10) with
| [] -> begin
(

let body = (desugar_term env body)
in (

let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(

let body = (let _159_424 = (let _159_423 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right _159_423 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close _159_424 body))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (None), (body)))::[])))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (let _159_425 = (no_annot_abs (FStar_List.rev bs) body)
in (setpos _159_425))))
end
| (p)::rest -> begin
(

let _65_1121 = (desugar_binding_pat env p)
in (match (_65_1121) with
| (env, b, pat) -> begin
(

let _65_1172 = (match (b) with
| LetBinder (_65_1123) -> begin
(FStar_All.failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt = (match (((pat), (sc_pat_opt))) with
| (None, _65_1131) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _159_427 = (let _159_426 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_159_426), (p)))
in Some (_159_427))
end
| (Some (p), Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (_65_1145), _65_1148) -> begin
(

let tup2 = (let _159_428 = (FStar_Syntax_Util.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _159_428 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (let _159_436 = (let _159_435 = (let _159_434 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (let _159_433 = (let _159_432 = (FStar_Syntax_Syntax.as_arg sc)
in (let _159_431 = (let _159_430 = (let _159_429 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _159_429))
in (_159_430)::[])
in (_159_432)::_159_431))
in ((_159_434), (_159_433))))
in FStar_Syntax_Syntax.Tm_app (_159_435))
in (FStar_Syntax_Syntax.mk _159_436 None top.FStar_Parser_AST.range))
in (

let p = (let _159_437 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p), (false)))::[])))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _159_437))
in Some (((sc), (p))))))
end
| (FStar_Syntax_Syntax.Tm_app (_65_1154, args), FStar_Syntax_Syntax.Pat_cons (_65_1159, pats)) -> begin
(

let tupn = (let _159_438 = (FStar_Syntax_Util.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _159_438 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (let _159_445 = (let _159_444 = (let _159_443 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (let _159_442 = (let _159_441 = (let _159_440 = (let _159_439 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _159_439))
in (_159_440)::[])
in (FStar_List.append args _159_441))
in ((_159_443), (_159_442))))
in FStar_Syntax_Syntax.Tm_app (_159_444))
in (mk _159_445))
in (

let p = (let _159_446 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p), (false)))::[])))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _159_446))
in Some (((sc), (p))))))
end
| _65_1168 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt)))
end)
in (match (_65_1172) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _65_1176; FStar_Parser_AST.level = _65_1174}, phi, _65_1182) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(

let phi = (desugar_formula env phi)
in (let _159_454 = (let _159_453 = (let _159_452 = (FStar_Syntax_Syntax.fvar a FStar_Syntax_Syntax.Delta_equational None)
in (let _159_451 = (let _159_450 = (FStar_Syntax_Syntax.as_arg phi)
in (let _159_449 = (let _159_448 = (let _159_447 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _159_447))
in (_159_448)::[])
in (_159_450)::_159_449))
in ((_159_452), (_159_451))))
in FStar_Syntax_Syntax.Tm_app (_159_453))
in (mk _159_454)))
end
| FStar_Parser_AST.App (_65_1187) -> begin
(

let rec aux = (fun args e -> (match ((let _159_459 = (unparen e)
in _159_459.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(

let arg = (let _159_460 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _159_460))
in (aux ((arg)::args) e))
end
| _65_1199 -> begin
(

let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app (((head), (args))))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _159_463 = (let _159_462 = (let _159_461 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((_159_461), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))
in FStar_Syntax_Syntax.Tm_meta (_159_462))
in (mk _159_463))
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

let ds_let_rec_or_app = (fun _65_1222 -> (match (()) with
| () -> begin
(

let bindings = (((pat), (_snd)))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _65_1226 -> (match (_65_1226) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _159_467 = (destruct_app_pattern env top_level p)
in ((_159_467), (def)))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _159_468 = (destruct_app_pattern env top_level p)
in ((_159_468), (def)))
end
| _65_1232 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _65_1237); FStar_Parser_AST.prange = _65_1234}, t) -> begin
if top_level then begin
(let _159_471 = (let _159_470 = (let _159_469 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_159_469))
in ((_159_470), ([]), (Some (t))))
in ((_159_471), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (Some (t)))), (def))
end
end
| FStar_Parser_AST.PatVar (id, _65_1246) -> begin
if top_level then begin
(let _159_474 = (let _159_473 = (let _159_472 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_159_472))
in ((_159_473), ([]), (None)))
in ((_159_474), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (None))), (def))
end
end
| _65_1250 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end
end))))
in (

let _65_1279 = (FStar_List.fold_left (fun _65_1255 _65_1264 -> (match (((_65_1255), (_65_1264))) with
| ((env, fnames, rec_bindings), ((f, _65_1258, _65_1260), _65_1263)) -> begin
(

let _65_1275 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let _65_1269 = (FStar_Parser_Env.push_bv env x)
in (match (_65_1269) with
| (env, xx) -> begin
(let _159_478 = (let _159_477 = (FStar_Syntax_Syntax.mk_binder xx)
in (_159_477)::rec_bindings)
in ((env), (FStar_Util.Inl (xx)), (_159_478)))
end))
end
| FStar_Util.Inr (l) -> begin
(let _159_479 = (FStar_Parser_Env.push_top_level_rec_binding env l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in ((_159_479), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (_65_1275) with
| (env, lbname, rec_bindings) -> begin
((env), ((lbname)::fnames), (rec_bindings))
end))
end)) ((env), ([]), ([])) funs)
in (match (_65_1279) with
| (env', fnames, rec_bindings) -> begin
(

let fnames = (FStar_List.rev fnames)
in (

let desugar_one_def = (fun env lbname _65_1290 -> (match (_65_1290) with
| ((_65_1285, args, result_t), def) -> begin
(

let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _159_486 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t)))) _159_486 FStar_Parser_AST.Expr))
end)
in (

let def = (match (args) with
| [] -> begin
def
end
| _65_1297 -> begin
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
(let _159_488 = (let _159_487 = (FStar_Syntax_Util.incr_delta_qualifier body)
in (FStar_Syntax_Syntax.lid_as_fv l _159_487 None))
in FStar_Util.Inr (_159_488))
end)
in (

let body = if is_rec then begin
(FStar_Syntax_Subst.close rec_bindings body)
end else begin
body
end
in (mk_lb ((lbname), (FStar_Syntax_Syntax.tun), (body))))))))
end))
in (

let lbs = (FStar_List.map2 (desugar_one_def (if is_rec then begin
env'
end else begin
env
end)) fnames funs)
in (

let body = (desugar_term env' body)
in (let _159_491 = (let _159_490 = (let _159_489 = (FStar_Syntax_Subst.close rec_bindings body)
in ((((is_rec), (lbs))), (_159_489)))
in FStar_Syntax_Syntax.Tm_let (_159_490))
in (FStar_All.pipe_left mk _159_491))))))
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

let _65_1318 = (desugar_binding_pat_maybe_top top_level env pat is_mutable)
in (match (_65_1318) with
| (env, binder, pat) -> begin
(

let tm = (match (binder) with
| LetBinder (l, t) -> begin
(

let body = (desugar_term env t2)
in (

let fv = (let _159_498 = (FStar_Syntax_Util.incr_delta_qualifier t1)
in (FStar_Syntax_Syntax.lid_as_fv l _159_498 None))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((((false), (({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]))), (body)))))))
end
| LocalBinder (x, _65_1327) -> begin
(

let body = (desugar_term env t2)
in (

let body = (match (pat) with
| (None) | (Some ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (_); FStar_Syntax_Syntax.ty = _; FStar_Syntax_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _159_503 = (let _159_502 = (let _159_501 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _159_500 = (let _159_499 = (FStar_Syntax_Util.branch ((pat), (None), (body)))
in (_159_499)::[])
in ((_159_501), (_159_500))))
in FStar_Syntax_Syntax.Tm_match (_159_502))
in (FStar_Syntax_Syntax.mk _159_503 None body.FStar_Syntax_Syntax.pos))
end)
in (let _159_508 = (let _159_507 = (let _159_506 = (let _159_505 = (let _159_504 = (FStar_Syntax_Syntax.mk_binder x)
in (_159_504)::[])
in (FStar_Syntax_Subst.close _159_505 body))
in ((((false), (((mk_lb ((FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t1))))::[]))), (_159_506)))
in FStar_Syntax_Syntax.Tm_let (_159_507))
in (FStar_All.pipe_left mk _159_508))))
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
in (let _159_519 = (let _159_518 = (let _159_517 = (desugar_term env t1)
in (let _159_516 = (let _159_515 = (let _159_510 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (let _159_509 = (desugar_term env t2)
in ((_159_510), (None), (_159_509))))
in (let _159_514 = (let _159_513 = (let _159_512 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (let _159_511 = (desugar_term env t3)
in ((_159_512), (None), (_159_511))))
in (_159_513)::[])
in (_159_515)::_159_514))
in ((_159_517), (_159_516))))
in FStar_Syntax_Syntax.Tm_match (_159_518))
in (mk _159_519)))
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

let desugar_branch = (fun _65_1368 -> (match (_65_1368) with
| (pat, wopt, b) -> begin
(

let _65_1371 = (desugar_match_pat env pat)
in (match (_65_1371) with
| (env, pat) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _159_522 = (desugar_term env e)
in Some (_159_522))
end)
in (

let b = (desugar_term env b)
in (FStar_Syntax_Util.branch ((pat), (wopt), (b)))))
end))
end))
in (let _159_526 = (let _159_525 = (let _159_524 = (desugar_term env e)
in (let _159_523 = (FStar_List.map desugar_branch branches)
in ((_159_524), (_159_523))))
in FStar_Syntax_Syntax.Tm_match (_159_525))
in (FStar_All.pipe_left mk _159_526)))
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
in (let _159_529 = (let _159_528 = (let _159_527 = (desugar_term env e)
in ((_159_527), (annot), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (_159_528))
in (FStar_All.pipe_left mk _159_529)))))
end
| FStar_Parser_AST.Record (_65_1385, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let _65_1396 = (FStar_List.hd fields)
in (match (_65_1396) with
| (f, _65_1395) -> begin
(

let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (

let _65_1402 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_65_1402) with
| (record, _65_1401) -> begin
(

let get_field = (fun xopt f -> (

let fn = f.FStar_Ident.ident
in (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _65_1410 -> (match (_65_1410) with
| (g, _65_1409) -> begin
(

let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_65_1414, e) -> begin
(let _159_537 = (qfn fn)
in ((_159_537), (e)))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _159_540 = (let _159_539 = (let _159_538 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in ((_159_538), (top.FStar_Parser_AST.range)))
in FStar_Syntax_Syntax.Error (_159_539))
in (Prims.raise _159_540))
end
| Some (x) -> begin
(let _159_541 = (qfn fn)
in ((_159_541), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Project (((x), (f)))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level))))
end)
end))))
in (

let recterm = (match (eopt) with
| None -> begin
(let _159_546 = (let _159_545 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _65_1426 -> (match (_65_1426) with
| (f, _65_1425) -> begin
(let _159_544 = (let _159_543 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _159_543))
in ((_159_544), (FStar_Parser_AST.Nothing)))
end))))
in ((record.FStar_Parser_Env.constrname), (_159_545)))
in FStar_Parser_AST.Construct (_159_546))
end
| Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (let _159_548 = (let _159_547 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_159_547))
in (FStar_Parser_AST.mk_term _159_548 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record = (let _159_551 = (let _159_550 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _65_1434 -> (match (_65_1434) with
| (f, _65_1433) -> begin
(get_field (Some (xterm)) f)
end))))
in ((None), (_159_550)))
in FStar_Parser_AST.Record (_159_551))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _65_1450; FStar_Syntax_Syntax.pos = _65_1448; FStar_Syntax_Syntax.vars = _65_1446}, args); FStar_Syntax_Syntax.tk = _65_1444; FStar_Syntax_Syntax.pos = _65_1442; FStar_Syntax_Syntax.vars = _65_1440}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(

let e = (let _159_559 = (let _159_558 = (let _159_557 = (let _159_556 = (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos)
in (let _159_555 = (let _159_554 = (let _159_553 = (let _159_552 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_Env.typename), (_159_552)))
in FStar_Syntax_Syntax.Record_ctor (_159_553))
in Some (_159_554))
in (FStar_Syntax_Syntax.fvar _159_556 FStar_Syntax_Syntax.Delta_constant _159_555)))
in ((_159_557), (args)))
in FStar_Syntax_Syntax.Tm_app (_159_558))
in (FStar_All.pipe_left mk _159_559))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))))))
end
| _65_1464 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(

let _65_1471 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_projector_by_field_name env) f)
in (match (_65_1471) with
| (fieldname, is_rec) -> begin
(

let e = (desugar_term env e)
in (

let fn = (

let _65_1476 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_65_1476) with
| (ns, _65_1475) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (

let qual = if is_rec then begin
Some (FStar_Syntax_Syntax.Record_projector (fn))
end else begin
None
end
in (let _159_565 = (let _159_564 = (let _159_563 = (let _159_560 = (FStar_Ident.set_lid_range fieldname (FStar_Ident.range_of_lid f))
in (FStar_Syntax_Syntax.fvar _159_560 FStar_Syntax_Syntax.Delta_equational qual))
in (let _159_562 = (let _159_561 = (FStar_Syntax_Syntax.as_arg e)
in (_159_561)::[])
in ((_159_563), (_159_562))))
in FStar_Syntax_Syntax.Tm_app (_159_564))
in (FStar_All.pipe_left mk _159_565)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| _65_1486 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _65_1488 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_args : FStar_Parser_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun _65_1493 -> (match (_65_1493) with
| (a, imp) -> begin
(let _159_569 = (desugar_term env a)
in (arg_withimp_e imp _159_569))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r default_ok env t -> (

let fail = (fun msg -> (Prims.raise (FStar_Syntax_Syntax.Error (((msg), (r))))))
in (

let is_requires = (fun _65_1505 -> (match (_65_1505) with
| (t, _65_1504) -> begin
(match ((let _159_577 = (unparen t)
in _159_577.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Requires (_65_1507) -> begin
true
end
| _65_1510 -> begin
false
end)
end))
in (

let is_ensures = (fun _65_1515 -> (match (_65_1515) with
| (t, _65_1514) -> begin
(match ((let _159_580 = (unparen t)
in _159_580.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ensures (_65_1517) -> begin
true
end
| _65_1520 -> begin
false
end)
end))
in (

let is_app = (fun head _65_1526 -> (match (_65_1526) with
| (t, _65_1525) -> begin
(match ((let _159_585 = (unparen t)
in _159_585.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _65_1530; FStar_Parser_AST.level = _65_1528}, _65_1535, _65_1537) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| _65_1541 -> begin
false
end)
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t -> (

let _65_1547 = (head_and_args t)
in (match (_65_1547) with
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
(let _159_589 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_name env) l)
in ((_159_589), (args)))
end
| FStar_Parser_AST.Name (l) when ((let _159_590 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _159_590 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(let _159_591 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in ((_159_591), (args)))
end
| FStar_Parser_AST.Name (l) when ((let _159_592 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _159_592 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(let _159_593 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)
in ((_159_593), (args)))
end
| FStar_Parser_AST.Name (l) when ((((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) && default_ok) -> begin
(let _159_594 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in ((_159_594), ((((t), (FStar_Parser_AST.Nothing)))::[])))
end
| _65_1578 when default_ok -> begin
(let _159_595 = (FStar_Ident.set_lid_range env.FStar_Parser_Env.default_result_effect head.FStar_Parser_AST.range)
in ((_159_595), ((((t), (FStar_Parser_AST.Nothing)))::[])))
end
| _65_1580 -> begin
(let _159_597 = (let _159_596 = (FStar_Parser_AST.term_to_string t)
in (FStar_Util.format1 "%s is not an effect" _159_596))
in (fail _159_597))
end)
end)))
in (

let _65_1583 = (pre_process_comp_typ t)
in (match (_65_1583) with
| (eff, args) -> begin
(

let _65_1584 = if ((FStar_List.length args) = (Prims.parse_int "0")) then begin
(let _159_599 = (let _159_598 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" _159_598))
in (fail _159_599))
end else begin
()
end
in (

let _65_1588 = (let _159_601 = (FStar_List.hd args)
in (let _159_600 = (FStar_List.tl args)
in ((_159_601), (_159_600))))
in (match (_65_1588) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (Prims.fst result_arg))
in (

let rest = (desugar_args env rest)
in (

let _65_1613 = (FStar_All.pipe_right rest (FStar_List.partition (fun _65_1594 -> (match (_65_1594) with
| (t, _65_1593) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _65_1600; FStar_Syntax_Syntax.pos = _65_1598; FStar_Syntax_Syntax.vars = _65_1596}, (_65_1605)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| _65_1610 -> begin
false
end)
end))))
in (match (_65_1613) with
| (dec, rest) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _65_1617 -> (match (_65_1617) with
| (t, _65_1616) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_65_1619, ((arg, _65_1622))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| _65_1628 -> begin
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

let pattern = (let _159_605 = (let _159_604 = (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _159_604 FStar_Syntax_Syntax.Delta_constant None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _159_605 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app nil ((((pattern), (Some (FStar_Syntax_Syntax.imp_tag))))::[]) None pat.FStar_Syntax_Syntax.pos)))
end
| _65_1643 -> begin
pat
end)
in (let _159_609 = (let _159_608 = (let _159_607 = (let _159_606 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) None pat.FStar_Syntax_Syntax.pos)
in ((_159_606), (aq)))
in (_159_607)::[])
in (ens)::_159_608)
in (req)::_159_609))
end
| _65_1646 -> begin
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
| _65_1658 -> begin
None
end))
in (

let mk = (fun t -> (FStar_Syntax_Syntax.mk t None f.FStar_Parser_AST.range))
in (

let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let _65_1665 = t
in {FStar_Syntax_Syntax.n = _65_1665.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _65_1665.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _65_1665.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let _65_1672 = b
in {FStar_Parser_AST.b = _65_1672.FStar_Parser_AST.b; FStar_Parser_AST.brange = _65_1672.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _65_1672.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _159_644 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _159_644)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(

let _65_1686 = (FStar_Parser_Env.push_bv env a)
in (match (_65_1686) with
| (env, a) -> begin
(

let a = (

let _65_1687 = a
in {FStar_Syntax_Syntax.ppname = _65_1687.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_1687.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats = (desugar_pats env pats)
in (

let body = (desugar_formula env body)
in (

let body = (match (pats) with
| [] -> begin
body
end
| _65_1694 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta (((body), (FStar_Syntax_Syntax.Meta_pattern (pats))))))
end)
in (

let body = (let _159_647 = (let _159_646 = (let _159_645 = (FStar_Syntax_Syntax.mk_binder a)
in (_159_645)::[])
in (no_annot_abs _159_646 body))
in (FStar_All.pipe_left setpos _159_647))
in (let _159_653 = (let _159_652 = (let _159_651 = (let _159_648 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Syntax_Syntax.fvar _159_648 (FStar_Syntax_Syntax.Delta_unfoldable ((Prims.parse_int "1"))) None))
in (let _159_650 = (let _159_649 = (FStar_Syntax_Syntax.as_arg body)
in (_159_649)::[])
in ((_159_651), (_159_650))))
in FStar_Syntax_Syntax.Tm_app (_159_652))
in (FStar_All.pipe_left mk _159_653)))))))
end))
end
| _65_1698 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body = (let _159_668 = (q ((rest), (pats), (body)))
in (let _159_667 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _159_668 _159_667 FStar_Parser_AST.Formula)))
in (let _159_669 = (q (((b)::[]), ([]), (body)))
in (FStar_Parser_AST.mk_term _159_669 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _65_1712 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _159_670 = (unparen f)
in _159_670.FStar_Parser_AST.tm)) with
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
in (let _159_672 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _159_672)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _159_674 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _159_674)))
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
| _65_1770 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (

let _65_1794 = (FStar_List.fold_left (fun _65_1775 b -> (match (_65_1775) with
| (env, out) -> begin
(

let tk = (desugar_binder env (

let _65_1777 = b
in {FStar_Parser_AST.b = _65_1777.FStar_Parser_AST.b; FStar_Parser_AST.brange = _65_1777.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _65_1777.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(

let _65_1786 = (FStar_Parser_Env.push_bv env a)
in (match (_65_1786) with
| (env, a) -> begin
(

let a = (

let _65_1787 = a
in {FStar_Syntax_Syntax.ppname = _65_1787.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_1787.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in ((env), ((((a), ((trans_aqual b.FStar_Parser_AST.aqual))))::out)))
end))
end
| _65_1791 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (_65_1794) with
| (env, tpars) -> begin
((env), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(let _159_681 = (desugar_typ env t)
in ((Some (x)), (_159_681)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _159_682 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None x.FStar_Ident.idRange)
in ((Some (x)), (_159_682)))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _159_683 = (desugar_typ env t)
in ((None), (_159_683)))
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

let binders = (let _159_699 = (let _159_698 = (FStar_Syntax_Util.arrow_formals k)
in (Prims.fst _159_698))
in (FStar_List.append tps _159_699))
in (

let p = (FStar_Ident.range_of_lid t)
in (

let _65_1821 = (FStar_Syntax_Util.args_of_binders binders)
in (match (_65_1821) with
| (binders, args) -> begin
(

let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _65_1825 -> (match (_65_1825) with
| (x, _65_1824) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let binders = (let _159_705 = (let _159_704 = (let _159_703 = (let _159_702 = (let _159_701 = (FStar_Syntax_Syntax.lid_as_fv t FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _159_701))
in (FStar_Syntax_Syntax.mk_Tm_app _159_702 args None p))
in (FStar_All.pipe_left FStar_Syntax_Syntax.null_binder _159_703))
in (_159_704)::[])
in (FStar_List.append imp_binders _159_705))
in (

let disc_type = (let _159_708 = (let _159_707 = (let _159_706 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _159_706))
in (FStar_Syntax_Syntax.mk_Total _159_707))
in (FStar_Syntax_Util.arrow binders _159_708))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (let _159_711 = (let _159_710 = (quals ((FStar_Syntax_Syntax.Logic)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in ((disc_name), ([]), (disc_type), (_159_710), ((FStar_Ident.range_of_lid disc_name))))
in FStar_Syntax_Syntax.Sig_declare_typ (_159_711)))))))))
end))))))


let mk_indexed_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq refine_domain env tc lid inductive_tps imp_tps fields t -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p))
in (

let projectee = (fun ptyp -> (FStar_Syntax_Syntax.gen_bv "projectee" (Some (p)) ptyp))
in (

let tps = (FStar_List.map2 (fun _65_1849 _65_1853 -> (match (((_65_1849), (_65_1853))) with
| ((_65_1847, imp), (x, _65_1852)) -> begin
((x), (imp))
end)) inductive_tps imp_tps)
in (

let _65_1954 = (

let _65_1857 = (FStar_Syntax_Util.head_and_args t)
in (match (_65_1857) with
| (head, args0) -> begin
(

let args = (

let rec arguments = (fun tps args -> (match (((tps), (args))) with
| ([], _65_1863) -> begin
args
end
| (_65_1866, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Not enough arguments to type"), ((FStar_Ident.range_of_lid lid))))))
end
| (((_65_1871, Some (FStar_Syntax_Syntax.Implicit (_65_1873))))::tps', ((_65_1880, Some (FStar_Syntax_Syntax.Implicit (_65_1882))))::args') -> begin
(arguments tps' args')
end
| (((_65_1890, Some (FStar_Syntax_Syntax.Implicit (_65_1892))))::tps', ((_65_1900, _65_1902))::_65_1898) -> begin
(arguments tps' args)
end
| (((_65_1909, _65_1911))::_65_1907, ((a, Some (FStar_Syntax_Syntax.Implicit (_65_1918))))::_65_1915) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected implicit annotation on argument"), (a.FStar_Syntax_Syntax.pos)))))
end
| (((_65_1926, _65_1928))::tps', ((_65_1933, _65_1935))::args') -> begin
(arguments tps' args')
end))
in (arguments inductive_tps args0))
in (

let indices = (FStar_All.pipe_right args (FStar_List.map (fun _65_1940 -> (let _159_743 = (FStar_Syntax_Syntax.new_bv (Some (p)) FStar_Syntax_Syntax.tun)
in (FStar_All.pipe_right _159_743 FStar_Syntax_Syntax.mk_binder)))))
in (

let arg_typ = (let _159_748 = (let _159_744 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _159_744))
in (let _159_747 = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _65_1945 -> (match (_65_1945) with
| (x, imp) -> begin
(let _159_746 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_159_746), (imp)))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app _159_748 _159_747 None p)))
in (

let arg_binder = if (not (refine_domain)) then begin
(let _159_749 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder _159_749))
end else begin
(

let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p)) arg_typ)
in (let _159_758 = (

let _65_1949 = (projectee arg_typ)
in (let _159_757 = (let _159_756 = (let _159_755 = (let _159_754 = (let _159_750 = (FStar_Ident.set_lid_range disc_name p)
in (FStar_Syntax_Syntax.fvar _159_750 FStar_Syntax_Syntax.Delta_equational None))
in (let _159_753 = (let _159_752 = (let _159_751 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _159_751))
in (_159_752)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _159_754 _159_753 None p)))
in (FStar_Syntax_Util.b2t _159_755))
in (FStar_Syntax_Util.refine x _159_756))
in {FStar_Syntax_Syntax.ppname = _65_1949.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_1949.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _159_757}))
in (FStar_Syntax_Syntax.mk_binder _159_758))))
end
in ((arg_binder), (indices))))))
end))
in (match (_65_1954) with
| (arg_binder, indices) -> begin
(

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder))
in (

let imp_binders = (let _159_760 = (FStar_All.pipe_right indices (FStar_List.map (fun _65_1959 -> (match (_65_1959) with
| (x, _65_1958) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (FStar_List.append imp_tps _159_760))
in (

let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (

let arg = (FStar_Syntax_Util.arg_of_non_null_binder arg_binder)
in (

let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _65_1967 -> (match (_65_1967) with
| (a, _65_1966) -> begin
(

let _65_1971 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (_65_1971) with
| (field_name, _65_1970) -> begin
(

let proj = (let _159_764 = (let _159_763 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.fv_to_tm _159_763))
in (FStar_Syntax_Syntax.mk_Tm_app _159_764 ((arg)::[]) None p))
in FStar_Syntax_Syntax.NT (((a), (proj))))
end))
end))))
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (FStar_List.append imp_tps fields)
in (let _159_800 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _65_1980 -> (match (_65_1980) with
| (x, _65_1979) -> begin
(

let _65_1984 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_65_1984) with
| (field_name, _65_1983) -> begin
(

let t = (let _159_768 = (let _159_767 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total _159_767))
in (FStar_Syntax_Util.arrow binders _159_768))
in (

let only_decl = (((let _159_769 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _159_769)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _159_771 = (let _159_770 = (FStar_Parser_Env.current_module env)
in _159_770.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _159_771)))
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

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _65_1996 -> (match (_65_1996) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in if ((i + ntps) = j) then begin
(let _159_776 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in ((_159_776), (b)))
end else begin
if (b && (j < ntps)) then begin
(let _159_780 = (let _159_779 = (let _159_778 = (let _159_777 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in ((_159_777), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (_159_778))
in (pos _159_779))
in ((_159_780), (b)))
end else begin
(let _159_783 = (let _159_782 = (let _159_781 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_159_781))
in (pos _159_782))
in ((_159_783), (b)))
end
end)
end))))
in (

let pat = (let _159_788 = (let _159_786 = (let _159_785 = (let _159_784 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in ((_159_784), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (_159_785))
in (FStar_All.pipe_right _159_786 pos))
in (let _159_787 = (FStar_Syntax_Syntax.bv_to_name projection)
in ((_159_788), (None), (_159_787))))
in (

let body = (let _159_792 = (let _159_791 = (let _159_790 = (let _159_789 = (FStar_Syntax_Util.branch pat)
in (_159_789)::[])
in ((arg_exp), (_159_790)))
in FStar_Syntax_Syntax.Tm_match (_159_791))
in (FStar_Syntax_Syntax.mk _159_792 None p))
in (

let imp = (no_annot_abs binders body)
in (

let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end else begin
FStar_Syntax_Syntax.Delta_equational
end
in (

let lb = (let _159_794 = (let _159_793 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (_159_793))
in {FStar_Syntax_Syntax.lbname = _159_794; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = imp})
in (

let impl = (let _159_799 = (let _159_798 = (let _159_797 = (let _159_796 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _159_796 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_159_797)::[])
in ((((false), ((lb)::[]))), (p), (_159_798), (quals)))
in FStar_Syntax_Syntax.Sig_let (_159_799))
in if no_decl then begin
(impl)::[]
end else begin
(decl)::(impl)::[]
end))))))))
end))))))
end))
end))))
in (FStar_All.pipe_right _159_800 FStar_List.flatten)))))))))
end)))))))


let mk_data_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env _65_2010 -> (match (_65_2010) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _65_2013, t, l, n, quals, _65_2019, _65_2021) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _65_11 -> (match (_65_11) with
| FStar_Syntax_Syntax.RecordConstructor (_65_2026) -> begin
true
end
| _65_2029 -> begin
false
end)))) then begin
false
end else begin
(match ((FStar_Parser_Env.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > (Prims.parse_int "1"))
end
| _65_2033 -> begin
true
end)
end
in (

let _65_2037 = (FStar_Syntax_Util.arrow_formals t)
in (match (_65_2037) with
| (formals, cod) -> begin
(match (formals) with
| [] -> begin
[]
end
| _65_2040 -> begin
(

let fv_qual = (match ((FStar_Util.find_map quals (fun _65_12 -> (match (_65_12) with
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| _65_2045 -> begin
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

let _65_2053 = (FStar_Util.first_N n formals)
in (match (_65_2053) with
| (tps, rest) -> begin
(mk_indexed_projectors iquals fv_qual refine_domain env l lid inductive_tps tps rest cod)
end))))
end)
end)))
end
| _65_2055 -> begin
[]
end)
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (

let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _159_825 = (FStar_Syntax_Util.incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (_159_825))
end else begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end
in (

let lb = (let _159_830 = (let _159_826 = (FStar_Syntax_Syntax.lid_as_fv lid dd None)
in FStar_Util.Inr (_159_826))
in (let _159_829 = (let _159_827 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars _159_827))
in (let _159_828 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = _159_830; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = _159_829; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _159_828})))
in FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (rng), (lids), (quals))))))


let rec desugar_tycon : FStar_Parser_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (

let tycon_id = (fun _65_13 -> (match (_65_13) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _159_844 = (let _159_843 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_159_843))
in (FStar_Parser_AST.mk_term _159_844 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
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
| _65_2130 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _159_857 = (let _159_856 = (let _159_855 = (binder_to_term b)
in ((out), (_159_855), ((imp_of_aqual b))))
in FStar_Parser_AST.App (_159_856))
in (FStar_Parser_AST.mk_term _159_857 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun _65_14 -> (match (_65_14) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun _65_2145 -> (match (_65_2145) with
| (x, t, _65_2144) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Syntax_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (

let result = (let _159_863 = (let _159_862 = (let _159_861 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_159_861))
in (FStar_Parser_AST.mk_term _159_862 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _159_863 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _159_865 = (FStar_All.pipe_right fields (FStar_List.map (fun _65_2154 -> (match (_65_2154) with
| (x, _65_2151, _65_2153) -> begin
(FStar_Parser_Env.qualify env x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (Some (constrTyp)), (None), (false)))::[])))), (_159_865)))))))
end
| _65_2156 -> begin
(FStar_All.failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals _env mutuals _65_15 -> (match (_65_15) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let _65_2170 = (typars_of_binders _env binders)
in (match (_65_2170) with
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

let tconstr = (let _159_876 = (let _159_875 = (let _159_874 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_159_874))
in (FStar_Parser_AST.mk_term _159_875 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _159_876 binders))
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
| _65_2183 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env bs -> (

let _65_2198 = (FStar_List.fold_left (fun _65_2189 _65_2192 -> (match (((_65_2189), (_65_2192))) with
| ((env, tps), (x, imp)) -> begin
(

let _65_2195 = (FStar_Parser_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (_65_2195) with
| (env, y) -> begin
((env), ((((y), (imp)))::tps))
end))
end)) ((env), ([])) bs)
in (match (_65_2198) with
| (env, bs) -> begin
((env), ((FStar_List.rev bs)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id, bs, kopt))::[] -> begin
(

let kopt = (match (kopt) with
| None -> begin
(let _159_883 = (tm_type_z id.FStar_Ident.idRange)
in Some (_159_883))
end
| _65_2207 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id), (bs), (kopt)))
in (

let _65_2217 = (desugar_abstract_tc quals env [] tc)
in (match (_65_2217) with
| (_65_2211, _65_2213, se, _65_2216) -> begin
(

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _65_2220, typars, k, [], [], quals, rng) -> begin
(

let quals = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
quals
end else begin
(

let _65_2229 = (let _159_885 = (FStar_Range.string_of_range rng)
in (let _159_884 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" _159_885 _159_884)))
in (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals)
end
in (

let t = (match (typars) with
| [] -> begin
k
end
| _65_2234 -> begin
(let _159_888 = (let _159_887 = (let _159_886 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (_159_886)))
in FStar_Syntax_Syntax.Tm_arrow (_159_887))
in (FStar_Syntax_Syntax.mk _159_888 None rng))
end)
in FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t), (quals), (rng)))))
end
| _65_2237 -> begin
se
end)
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in ((env), ((se)::[]))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let _65_2249 = (typars_of_binders env binders)
in (match (_65_2249) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _65_16 -> (match (_65_16) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| _65_2254 -> begin
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
| _65_2262 -> begin
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
in (let _159_894 = (let _159_893 = (FStar_Parser_Env.qualify env id)
in (let _159_892 = (FStar_All.pipe_right quals (FStar_List.filter (fun _65_18 -> (match (_65_18) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| _65_2270 -> begin
true
end))))
in ((_159_893), ([]), (typars), (c), (_159_892), (rng))))
in FStar_Syntax_Syntax.Sig_effect_abbrev (_159_894)))))
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
| (FStar_Parser_AST.TyconRecord (_65_2276))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let _65_2282 = (tycon_record_as_variant trec)
in (match (_65_2282) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| (_65_2286)::_65_2284 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_Env.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals et tc -> (

let _65_2297 = et
in (match (_65_2297) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_65_2299) -> begin
(

let trec = tc
in (

let _65_2304 = (tycon_record_as_variant trec)
in (match (_65_2304) with
| (t, fs) -> begin
(collect_tcs ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((env), (tcs)) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let _65_2316 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_65_2316) with
| (env, _65_2313, se, tconstr) -> begin
((env), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals))))::tcs))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let _65_2328 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_65_2328) with
| (env, _65_2325, se, tconstr) -> begin
((env), ((FStar_Util.Inr (((se), (t), (quals))))::tcs))
end))
end
| _65_2330 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (

let _65_2333 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (_65_2333) with
| (env, tcs) -> begin
(

let tcs = (FStar_List.rev tcs)
in (

let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _65_20 -> (match (_65_20) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, _65_2341, _65_2343, _65_2345, _65_2347), t, quals) -> begin
(

let _65_2357 = (push_tparams env tpars)
in (match (_65_2357) with
| (env_tps, _65_2356) -> begin
(

let t = (desugar_term env_tps t)
in (let _159_904 = (let _159_903 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in (([]), (_159_903)))
in (_159_904)::[]))
end))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, _65_2365, tags, _65_2368), constrs, tconstr, quals) -> begin
(

let tycon = ((tname), (tpars), (k))
in (

let _65_2379 = (push_tparams env tpars)
in (match (_65_2379) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun _65_2383 -> (match (_65_2383) with
| (x, _65_2382) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let _65_2409 = (let _159_916 = (FStar_All.pipe_right constrs (FStar_List.map (fun _65_2390 -> (match (_65_2390) with
| (id, topt, _65_2388, of_notation) -> begin
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

let t = (let _159_908 = (FStar_Parser_Env.default_total env_tps)
in (let _159_907 = (close env_tps t)
in (desugar_term _159_908 _159_907)))
in (

let name = (FStar_Parser_Env.qualify env id)
in (

let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _65_19 -> (match (_65_19) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| _65_2404 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (let _159_915 = (let _159_914 = (let _159_913 = (let _159_912 = (let _159_911 = (let _159_910 = (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total _159_910))
in (FStar_Syntax_Util.arrow data_tpars _159_911))
in ((name), (univs), (_159_912), (tname), (ntps), (quals), (mutuals), (rng)))
in FStar_Syntax_Syntax.Sig_datacon (_159_913))
in ((tps), (_159_914)))
in ((name), (_159_915))))))))
end))))
in (FStar_All.pipe_left FStar_List.split _159_916))
in (match (_65_2409) with
| (constrNames, constrs) -> begin
((([]), (FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs), (tpars), (k), (mutuals), (constrNames), (tags), (rng))))))::constrs
end)))
end)))
end
| _65_2411 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (

let bundle = (let _159_918 = (let _159_917 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in ((sigelts), (quals), (_159_917), (rng)))
in FStar_Syntax_Syntax.Sig_bundle (_159_918))
in (

let env = (FStar_Parser_Env.push_sigelt env0 bundle)
in (

let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projectors quals env)))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _65_21 -> (match (_65_21) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, _65_2420, tps, k, _65_2424, constrs, quals, _65_2428) when ((FStar_List.length constrs) > (Prims.parse_int "1")) -> begin
(

let quals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract quals) then begin
(FStar_Syntax_Syntax.Private)::quals
end else begin
quals
end
in (mk_data_discriminators quals env tname tps k constrs))
end
| _65_2433 -> begin
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

let _65_2457 = (FStar_List.fold_left (fun _65_2442 b -> (match (_65_2442) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| (Some (a), k) -> begin
(

let _65_2450 = (FStar_Parser_Env.push_bv env a)
in (match (_65_2450) with
| (env, a) -> begin
(let _159_927 = (let _159_926 = (FStar_Syntax_Syntax.mk_binder (

let _65_2451 = a
in {FStar_Syntax_Syntax.ppname = _65_2451.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_2451.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (_159_926)::binders)
in ((env), (_159_927)))
end))
end
| _65_2454 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end)
end)) ((env), ([])) binders)
in (match (_65_2457) with
| (env, binders) -> begin
((env), ((FStar_List.rev binders)))
end)))


let rec desugar_effect : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  Prims.bool  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_kind eff_decls actions for_free -> (

let env0 = env
in (

let monad_env = (FStar_Parser_Env.enter_monad_scope env eff_name)
in (

let _65_2471 = (desugar_binders monad_env eff_binders)
in (match (_65_2471) with
| (env, binders) -> begin
(

let eff_k = (let _159_948 = (FStar_Parser_Env.default_total env)
in (desugar_term _159_948 eff_kind))
in (

let _65_2482 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _65_2475 decl -> (match (_65_2475) with
| (env, out) -> begin
(

let _65_2479 = (desugar_decl env decl)
in (match (_65_2479) with
| (env, ses) -> begin
(let _159_952 = (let _159_951 = (FStar_List.hd ses)
in (_159_951)::out)
in ((env), (_159_952)))
end))
end)) ((env), ([]))))
in (match (_65_2482) with
| (env, decls) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let actions = (FStar_All.pipe_right actions (FStar_List.map (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (_65_2486, ((FStar_Parser_AST.TyconAbbrev (name, _65_2489, _65_2491, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (_65_2497, ((def, _65_2504))::((cps_type, _65_2500))::[]); FStar_Parser_AST.range = _65_2495; FStar_Parser_AST.level = _65_2493}), _65_2513))::[]) when (not (for_free)) -> begin
(let _159_958 = (FStar_Parser_Env.qualify env name)
in (let _159_957 = (let _159_954 = (desugar_term env def)
in (FStar_Syntax_Subst.close binders _159_954))
in (let _159_956 = (let _159_955 = (desugar_typ env cps_type)
in (FStar_Syntax_Subst.close binders _159_955))
in {FStar_Syntax_Syntax.action_name = _159_958; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = _159_957; FStar_Syntax_Syntax.action_typ = _159_956})))
end
| FStar_Parser_AST.Tycon (_65_2519, ((FStar_Parser_AST.TyconAbbrev (name, _65_2522, _65_2524, defn), _65_2529))::[]) when for_free -> begin
(let _159_961 = (FStar_Parser_Env.qualify env name)
in (let _159_960 = (let _159_959 = (desugar_term env defn)
in (FStar_Syntax_Subst.close binders _159_959))
in {FStar_Syntax_Syntax.action_name = _159_961; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = _159_960; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
end
| _65_2535 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples)."), (d.FStar_Parser_AST.drange)))))
end))))
in (

let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (

let lookup = (fun s -> (

let l = (FStar_Parser_Env.qualify env (FStar_Ident.mk_ident ((s), (d.FStar_Parser_AST.drange))))
in (let _159_965 = (let _159_964 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) _159_964))
in (([]), (_159_965)))))
in (

let mname = (FStar_Parser_Env.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange) quals)
in (

let se = if for_free then begin
(

let dummy_tscheme = (let _159_966 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (([]), (_159_966)))
in (let _159_972 = (let _159_971 = (let _159_970 = (let _159_967 = (lookup "repr")
in (Prims.snd _159_967))
in (let _159_969 = (lookup "return")
in (let _159_968 = (lookup "bind")
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = _159_970; FStar_Syntax_Syntax.return_repr = _159_969; FStar_Syntax_Syntax.bind_repr = _159_968; FStar_Syntax_Syntax.actions = actions})))
in ((_159_971), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (_159_972)))
end else begin
(

let rr = ((FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) || (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable)))
in (

let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in (let _159_988 = (let _159_987 = (let _159_986 = (lookup "return_wp")
in (let _159_985 = (lookup "bind_wp")
in (let _159_984 = (lookup "if_then_else")
in (let _159_983 = (lookup "ite_wp")
in (let _159_982 = (lookup "stronger")
in (let _159_981 = (lookup "close_wp")
in (let _159_980 = (lookup "assert_p")
in (let _159_979 = (lookup "assume_p")
in (let _159_978 = (lookup "null_wp")
in (let _159_977 = (lookup "trivial")
in (let _159_976 = if rr then begin
(let _159_973 = (lookup "repr")
in (FStar_All.pipe_left Prims.snd _159_973))
end else begin
FStar_Syntax_Syntax.tun
end
in (let _159_975 = if rr then begin
(lookup "return")
end else begin
un_ts
end
in (let _159_974 = if rr then begin
(lookup "bind")
end else begin
un_ts
end
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = _159_986; FStar_Syntax_Syntax.bind_wp = _159_985; FStar_Syntax_Syntax.if_then_else = _159_984; FStar_Syntax_Syntax.ite_wp = _159_983; FStar_Syntax_Syntax.stronger = _159_982; FStar_Syntax_Syntax.close_wp = _159_981; FStar_Syntax_Syntax.assert_p = _159_980; FStar_Syntax_Syntax.assume_p = _159_979; FStar_Syntax_Syntax.null_wp = _159_978; FStar_Syntax_Syntax.trivial = _159_977; FStar_Syntax_Syntax.repr = _159_976; FStar_Syntax_Syntax.return_repr = _159_975; FStar_Syntax_Syntax.bind_repr = _159_974; FStar_Syntax_Syntax.actions = actions})))))))))))))
in ((_159_987), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_new_effect (_159_988))))
end
in (

let env = (FStar_Parser_Env.push_sigelt env0 se)
in (

let env = (FStar_All.pipe_right actions (FStar_List.fold_left (fun env a -> (let _159_991 = (FStar_Syntax_Util.action_as_lb a)
in (FStar_Parser_Env.push_sigelt env _159_991))) env))
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
| FStar_Parser_AST.Fsdoc (_65_2561) -> begin
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
(let _159_995 = (FStar_Parser_Env.push_module_abbrev env x l)
in ((_159_995), ([])))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(

let tcs = (FStar_List.map (fun _65_2579 -> (match (_65_2579) with
| (x, _65_2578) -> begin
x
end)) tcs)
in (let _159_997 = (FStar_List.map trans_qual qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _159_997 tcs)))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _159_999 = (let _159_998 = (desugar_term_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Syntax_Subst.compress _159_998))
in _159_999.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let (lbs, _65_2588) -> begin
(

let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals = (match (quals) with
| (_65_2596)::_65_2594 -> begin
(FStar_List.map trans_qual quals)
end
| _65_2599 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _65_22 -> (match (_65_22) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (_65_2610); FStar_Syntax_Syntax.lbunivs = _65_2608; FStar_Syntax_Syntax.lbtyp = _65_2606; FStar_Syntax_Syntax.lbeff = _65_2604; FStar_Syntax_Syntax.lbdef = _65_2602} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _65_2620; FStar_Syntax_Syntax.lbtyp = _65_2618; FStar_Syntax_Syntax.lbeff = _65_2616; FStar_Syntax_Syntax.lbdef = _65_2614} -> begin
(FStar_Parser_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals = if (FStar_All.pipe_right lets (FStar_Util.for_some (fun _65_2628 -> (match (_65_2628) with
| (_65_2626, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end)))) then begin
(FStar_Syntax_Syntax.Logic)::quals
end else begin
quals
end
in (

let lbs = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _159_1004 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _65_2632 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let _65_2634 = fv
in {FStar_Syntax_Syntax.fv_name = _65_2634.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = _65_2634.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = _65_2632.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _65_2632.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _65_2632.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _65_2632.FStar_Syntax_Syntax.lbdef})))))
in (((Prims.fst lbs)), (_159_1004)))
end else begin
lbs
end
in (

let s = (let _159_1007 = (let _159_1006 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in ((lbs), (d.FStar_Parser_AST.drange), (_159_1006), (quals)))
in FStar_Syntax_Syntax.Sig_let (_159_1007))
in (

let env = (FStar_Parser_Env.push_sigelt env s)
in ((env), ((s)::[]))))))))
end
| _65_2641 -> begin
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
in (let _159_1011 = (let _159_1010 = (let _159_1009 = (let _159_1008 = (FStar_Parser_Env.qualify env id)
in ((_159_1008), (f), ((FStar_Syntax_Syntax.Assumption)::[]), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_assume (_159_1009))
in (_159_1010)::[])
in ((env), (_159_1011))))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(

let t = (let _159_1012 = (close_fun env t)
in (desugar_term env _159_1012))
in (

let quals = if (env.FStar_Parser_Env.iface && env.FStar_Parser_Env.admitted_iface) then begin
(FStar_Parser_AST.Assumption)::quals
end else begin
quals
end
in (

let se = (let _159_1015 = (let _159_1014 = (FStar_Parser_Env.qualify env id)
in (let _159_1013 = (FStar_List.map trans_qual quals)
in ((_159_1014), ([]), (t), (_159_1013), (d.FStar_Parser_AST.drange))))
in FStar_Syntax_Syntax.Sig_declare_typ (_159_1015))
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in ((env), ((se)::[]))))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(

let _65_2668 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (match (_65_2668) with
| (t, _65_2667) -> begin
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

let t = (let _159_1020 = (let _159_1016 = (FStar_Syntax_Syntax.null_binder t)
in (_159_1016)::[])
in (let _159_1019 = (let _159_1018 = (let _159_1017 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (Prims.fst _159_1017))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _159_1018))
in (FStar_Syntax_Util.arrow _159_1020 _159_1019)))
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

let _65_2697 = (desugar_binders env binders)
in (match (_65_2697) with
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

let _65_2713 = (desugar_binders env eff_binders)
in (match (_65_2713) with
| (env, binders) -> begin
(

let _65_2724 = (

let _65_2716 = (head_and_args defn)
in (match (_65_2716) with
| (head, args) -> begin
(

let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_defn env) l)
end
| _65_2720 -> begin
(let _159_1025 = (let _159_1024 = (let _159_1023 = (let _159_1022 = (let _159_1021 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat _159_1021 " not found"))
in (Prims.strcat "Effect " _159_1022))
in ((_159_1023), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_159_1024))
in (Prims.raise _159_1025))
end)
in (let _159_1026 = (desugar_args env args)
in ((ed), (_159_1026))))
end))
in (match (_65_2724) with
| (ed, args) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let sub = (fun _65_2730 -> (match (_65_2730) with
| (_65_2728, x) -> begin
(

let _65_2733 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (_65_2733) with
| (edb, x) -> begin
(

let _65_2734 = if ((FStar_List.length args) <> (FStar_List.length edb)) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected number of arguments to effect constructor"), (defn.FStar_Parser_AST.range)))))
end else begin
()
end
in (

let s = (FStar_Syntax_Util.subst_of_list edb args)
in (let _159_1030 = (let _159_1029 = (FStar_Syntax_Subst.subst s x)
in (FStar_Syntax_Subst.close binders _159_1029))
in (([]), (_159_1030)))))
end))
end))
in (

let ed = (let _159_1044 = (FStar_List.map trans_qual quals)
in (let _159_1043 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _159_1042 = (let _159_1031 = (sub (([]), (ed.FStar_Syntax_Syntax.signature)))
in (Prims.snd _159_1031))
in (let _159_1041 = (sub ed.FStar_Syntax_Syntax.ret_wp)
in (let _159_1040 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (let _159_1039 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (let _159_1038 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (let _159_1037 = (sub ed.FStar_Syntax_Syntax.stronger)
in (let _159_1036 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (let _159_1035 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (let _159_1034 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (let _159_1033 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (let _159_1032 = (sub ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _159_1044; FStar_Syntax_Syntax.mname = _159_1043; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = _159_1042; FStar_Syntax_Syntax.ret_wp = _159_1041; FStar_Syntax_Syntax.bind_wp = _159_1040; FStar_Syntax_Syntax.if_then_else = _159_1039; FStar_Syntax_Syntax.ite_wp = _159_1038; FStar_Syntax_Syntax.stronger = _159_1037; FStar_Syntax_Syntax.close_wp = _159_1036; FStar_Syntax_Syntax.assert_p = _159_1035; FStar_Syntax_Syntax.assume_p = _159_1034; FStar_Syntax_Syntax.null_wp = _159_1033; FStar_Syntax_Syntax.trivial = _159_1032; FStar_Syntax_Syntax.repr = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.return_repr = (([]), (FStar_Syntax_Syntax.tun)); FStar_Syntax_Syntax.bind_repr = (([]), (FStar_Syntax_Syntax.tun)); FStar_Syntax_Syntax.actions = []})))))))))))))
in (

let se = FStar_Syntax_Syntax.Sig_new_effect (((ed), (d.FStar_Parser_AST.drange)))
in (

let env = (FStar_Parser_Env.push_sigelt env0 se)
in ((env), ((se)::[])))))))
end))
end)))
end
| FStar_Parser_AST.NewEffectForFree (_65_2741, FStar_Parser_AST.RedefineEffect (_65_2743)) -> begin
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
(let _159_1051 = (let _159_1050 = (let _159_1049 = (let _159_1048 = (let _159_1047 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat _159_1047 " not found"))
in (Prims.strcat "Effect name " _159_1048))
in ((_159_1049), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_159_1050))
in (Prims.raise _159_1051))
end
| Some (l) -> begin
l
end))
in (

let src = (lookup l.FStar_Parser_AST.msource)
in (

let dst = (lookup l.FStar_Parser_AST.mdest)
in (

let _65_2784 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(let _159_1053 = (let _159_1052 = (desugar_term env t)
in (([]), (_159_1052)))
in ((_159_1053), (None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(let _159_1058 = (let _159_1054 = (desugar_term env wp)
in (([]), (_159_1054)))
in (let _159_1057 = (let _159_1056 = (let _159_1055 = (desugar_term env t)
in (([]), (_159_1055)))
in Some (_159_1056))
in ((_159_1058), (_159_1057))))
end)
in (match (_65_2784) with
| (lift_wp, lift) -> begin
(

let se = FStar_Syntax_Syntax.Sig_sub_effect ((({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift}), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[])))
end)))))
end)))


let desugar_decls : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _65_2790 d -> (match (_65_2790) with
| (env, sigelts) -> begin
(

let _65_2794 = (desugar_decl env d)
in (match (_65_2794) with
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

let _65_2817 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _159_1076 = (FStar_Parser_Env.prepare_module_or_interface true admitted env mname)
in ((_159_1076), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _159_1077 = (FStar_Parser_Env.prepare_module_or_interface false false env mname)
in ((_159_1077), (mname), (decls), (false)))
end)
in (match (_65_2817) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(

let _65_2820 = (desugar_decls env decls)
in (match (_65_2820) with
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
| FStar_Parser_AST.Interface (mname, _65_2831, _65_2833) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (

let _65_2841 = (desugar_modul_common curmod env m)
in (match (_65_2841) with
| (x, y, _65_2840) -> begin
((x), (y))
end))))


let desugar_modul : FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (

let _65_2847 = (desugar_modul_common None env m)
in (match (_65_2847) with
| (env, modul, pop_when_done) -> begin
(

let env = (FStar_Parser_Env.finish_module_or_interface env modul)
in (

let _65_2849 = if (FStar_Options.dump_module modul.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _159_1088 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _159_1088))
end else begin
()
end
in (let _159_1089 = if pop_when_done then begin
(FStar_Parser_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end else begin
env
end
in ((_159_1089), (modul)))))
end)))


let desugar_file : FStar_Parser_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (

let _65_2862 = (FStar_List.fold_left (fun _65_2855 m -> (match (_65_2855) with
| (env, mods) -> begin
(

let _65_2859 = (desugar_modul env m)
in (match (_65_2859) with
| (env, m) -> begin
((env), ((m)::mods))
end))
end)) ((env), ([])) f)
in (match (_65_2862) with
| (env, mods) -> begin
((env), ((FStar_List.rev mods)))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Parser_Env.env  ->  FStar_Parser_Env.env = (fun m en -> (

let _65_2867 = (FStar_Parser_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (_65_2867) with
| (en, pop_when_done) -> begin
(

let en = (FStar_List.fold_left FStar_Parser_Env.push_sigelt (

let _65_2868 = en
in {FStar_Parser_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_Parser_Env.modules = _65_2868.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _65_2868.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _65_2868.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _65_2868.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _65_2868.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _65_2868.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _65_2868.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _65_2868.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _65_2868.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _65_2868.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = _65_2868.FStar_Parser_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (

let env = (FStar_Parser_Env.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_Env.export_interface m.FStar_Syntax_Syntax.name env)
end else begin
env
end))
end)))




