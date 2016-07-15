
open Prims

let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _64_1 -> (match (_64_1) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Syntax_Syntax.Equality)
end
| _64_28 -> begin
None
end))


let trans_qual : FStar_Range.range  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun r _64_2 -> (match (_64_2) with
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

let _64_42 = (FStar_TypeChecker_Errors.warn r "The \'opaque\' qualifier is deprecated; use \'unfoldable\', which is also the default")
in FStar_Syntax_Syntax.Unfoldable)
end
| FStar_Parser_AST.Reflectable -> begin
FStar_Syntax_Syntax.Reflectable
end
| FStar_Parser_AST.Reifiable -> begin
FStar_Syntax_Syntax.Reifiable
end
| FStar_Parser_AST.DefaultEffect -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("The \'default\' qualifier on effects is no longer supported"), (r)))))
end))


let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun _64_3 -> (match (_64_3) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end))


let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _64_4 -> (match (_64_4) with
| FStar_Parser_AST.Hash -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| _64_55 -> begin
None
end))


let arg_withimp_e = (fun imp t -> ((t), ((as_imp imp))))


let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
((t), (Some (FStar_Syntax_Syntax.imp_tag)))
end
| _64_62 -> begin
((t), (None))
end))


let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_64_66) -> begin
true
end
| _64_69 -> begin
false
end)))))


let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _64_74 -> begin
t
end))


let tm_type_z : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _156_23 = (let _156_22 = (FStar_Ident.lid_of_path (("Type0")::[]) r)
in FStar_Parser_AST.Name (_156_22))
in (FStar_Parser_AST.mk_term _156_23 r FStar_Parser_AST.Kind)))


let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _156_27 = (let _156_26 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_156_26))
in (FStar_Parser_AST.mk_term _156_27 r FStar_Parser_AST.Kind)))


let compile_op : Prims.int  ->  Prims.string  ->  Prims.string = (fun arity s -> (

let name_of_char = (fun _64_5 -> (match (_64_5) with
| '&' -> begin
"Amp"
end
| '@' -> begin
"At"
end
| '+' -> begin
"Plus"
end
| '-' when (arity = 1) -> begin
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
| _64_98 -> begin
"UNKNOWN"
end))
in (

let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _156_38 = (let _156_36 = (FStar_Util.char_at s i)
in (name_of_char _156_36))
in (let _156_37 = (aux (i + 1))
in (_156_38)::_156_37))
end)
in (let _156_40 = (let _156_39 = (aux 0)
in (FStar_String.concat "_" _156_39))
in (Prims.strcat "op_" _156_40)))))


let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _156_50 = (let _156_49 = (let _156_48 = (let _156_47 = (compile_op n s)
in ((_156_47), (r)))
in (FStar_Ident.mk_ident _156_48))
in (_156_49)::[])
in (FStar_All.pipe_right _156_50 FStar_Ident.lid_of_ids)))


let op_as_term : FStar_Parser_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.term Prims.option = (fun env arity rng s -> (

let r = (fun l dd -> (let _156_65 = (let _156_64 = (let _156_63 = (FStar_Ident.set_lid_range l rng)
in (FStar_Syntax_Syntax.lid_as_fv _156_63 dd None))
in (FStar_All.pipe_right _156_64 FStar_Syntax_Syntax.fv_to_tm))
in Some (_156_65)))
in (

let fallback = (fun _64_113 -> (match (()) with
| () -> begin
(match (s) with
| "=" -> begin
(r FStar_Syntax_Const.op_Eq FStar_Syntax_Syntax.Delta_equational)
end
| ":=" -> begin
(r FStar_Syntax_Const.op_ColonEq FStar_Syntax_Syntax.Delta_equational)
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
| "-" when (arity = 1) -> begin
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
(r FStar_Syntax_Const.not_lid (FStar_Syntax_Syntax.Delta_unfoldable (2)))
end
| "==" -> begin
(r FStar_Syntax_Const.eq2_lid FStar_Syntax_Syntax.Delta_constant)
end
| "<<" -> begin
(r FStar_Syntax_Const.precedes_lid FStar_Syntax_Syntax.Delta_constant)
end
| "/\\" -> begin
(r FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)))
end
| "\\/" -> begin
(r FStar_Syntax_Const.or_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)))
end
| "==>" -> begin
(r FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_unfoldable (1)))
end
| "<==>" -> begin
(r FStar_Syntax_Const.iff_lid (FStar_Syntax_Syntax.Delta_unfoldable (2)))
end
| _64_141 -> begin
None
end)
end))
in (match ((let _156_68 = (compile_op_lid arity s rng)
in (FStar_Parser_Env.try_lookup_lid env _156_68))) with
| Some (t) -> begin
Some ((Prims.fst t))
end
| _64_145 -> begin
(fallback ())
end))))


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _156_75 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _156_75)))


let rec free_type_vars_b : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_64_154) -> begin
((env), ([]))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let _64_161 = (FStar_Parser_Env.push_bv env x)
in (match (_64_161) with
| (env, _64_160) -> begin
((env), ((x)::[]))
end))
end
| FStar_Parser_AST.Annotated (_64_163, term) -> begin
(let _156_82 = (free_type_vars env term)
in ((env), (_156_82)))
end
| FStar_Parser_AST.TAnnotated (id, _64_169) -> begin
(

let _64_175 = (FStar_Parser_Env.push_bv env id)
in (match (_64_175) with
| (env, _64_174) -> begin
((env), ([]))
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _156_83 = (free_type_vars env t)
in ((env), (_156_83)))
end))
and free_type_vars : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _156_86 = (unparen t)
in _156_86.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (_64_181) -> begin
(FStar_All.failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_Env.try_lookup_id env a)) with
| None -> begin
(a)::[]
end
| _64_187 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Assign (_, t)) | (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_64_221, ts) -> begin
(FStar_List.collect (fun _64_228 -> (match (_64_228) with
| (t, _64_227) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_64_230, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _64_237) -> begin
(let _156_89 = (free_type_vars env t1)
in (let _156_88 = (free_type_vars env t2)
in (FStar_List.append _156_89 _156_88)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(

let _64_246 = (free_type_vars_b env b)
in (match (_64_246) with
| (env, f) -> begin
(let _156_90 = (free_type_vars env t)
in (FStar_List.append f _156_90))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(

let _64_262 = (FStar_List.fold_left (fun _64_255 binder -> (match (_64_255) with
| (env, free) -> begin
(

let _64_259 = (free_type_vars_b env binder)
in (match (_64_259) with
| (env, f) -> begin
((env), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (_64_262) with
| (env, free) -> begin
(let _156_93 = (free_type_vars env body)
in (FStar_List.append free _156_93))
end))
end
| FStar_Parser_AST.Project (t, _64_265) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
[]
end))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (

let rec aux = (fun args t -> (match ((let _156_100 = (unparen t)
in _156_100.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| _64_309 -> begin
((t), (args))
end))
in (aux [] t)))


let close : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _156_105 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _156_105))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _156_109 = (let _156_108 = (let _156_107 = (tm_type x.FStar_Ident.idRange)
in ((x), (_156_107)))
in FStar_Parser_AST.TAnnotated (_156_108))
in (FStar_Parser_AST.mk_binder _156_109 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))


let close_fun : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _156_114 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _156_114))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _156_118 = (let _156_117 = (let _156_116 = (tm_type x.FStar_Ident.idRange)
in ((x), (_156_116)))
in FStar_Parser_AST.TAnnotated (_156_117))
in (FStar_Parser_AST.mk_binder _156_118 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let t = (match ((let _156_119 = (unparen t)
in _156_119.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_64_322) -> begin
t
end
| _64_325 -> begin
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
| _64_335 -> begin
((bs), (t))
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _64_339) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_64_345); FStar_Parser_AST.prange = _64_343}, _64_349) -> begin
true
end
| _64_353 -> begin
false
end))


let rec destruct_app_pattern : FStar_Parser_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _64_365 = (destruct_app_pattern env is_top_level p)
in (match (_64_365) with
| (name, args, _64_364) -> begin
((name), (args), (Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _64_370); FStar_Parser_AST.prange = _64_367}, args) when is_top_level -> begin
(let _156_133 = (let _156_132 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_156_132))
in ((_156_133), (args), (None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _64_381); FStar_Parser_AST.prange = _64_378}, args) -> begin
((FStar_Util.Inl (id)), (args), (None))
end
| _64_389 -> begin
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
| LocalBinder (_64_392) -> begin
_64_392
end))


let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_64_395) -> begin
_64_395
end))


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun _64_6 -> (match (_64_6) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| _64_402 -> begin
(FStar_All.failwith "Impossible")
end))


let as_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_Parser_Env.env) = (fun env imp _64_7 -> (match (_64_7) with
| (None, k) -> begin
(let _156_170 = (FStar_Syntax_Syntax.null_binder k)
in ((_156_170), (env)))
end
| (Some (a), k) -> begin
(

let _64_415 = (FStar_Parser_Env.push_bv env a)
in (match (_64_415) with
| (env, a) -> begin
(((((

let _64_416 = a
in {FStar_Syntax_Syntax.ppname = _64_416.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_416.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), ((trans_aqual imp)))), (env))
end))
end))


type env_t =
FStar_Parser_Env.env


type lenv_t =
FStar_Syntax_Syntax.bv Prims.list


let mk_lb : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.letbinding = (fun _64_421 -> (match (_64_421) with
| (n, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))


let no_annot_abs : FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t None))


let mk_ref_read = (fun tm -> (

let tm' = (let _156_183 = (let _156_182 = (let _156_178 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _156_178))
in (let _156_181 = (let _156_180 = (let _156_179 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (_156_179)))
in (_156_180)::[])
in ((_156_182), (_156_181))))
in FStar_Syntax_Syntax.Tm_app (_156_183))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_alloc = (fun tm -> (

let tm' = (let _156_190 = (let _156_189 = (let _156_185 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _156_185))
in (let _156_188 = (let _156_187 = (let _156_186 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (_156_186)))
in (_156_187)::[])
in ((_156_189), (_156_188))))
in FStar_Syntax_Syntax.Tm_app (_156_190))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_assign = (fun t1 t2 pos -> (

let tm = (let _156_202 = (let _156_201 = (let _156_194 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _156_194))
in (let _156_200 = (let _156_199 = (let _156_195 = (FStar_Syntax_Syntax.as_implicit false)
in ((t1), (_156_195)))
in (let _156_198 = (let _156_197 = (let _156_196 = (FStar_Syntax_Syntax.as_implicit false)
in ((t2), (_156_196)))
in (_156_197)::[])
in (_156_199)::_156_198))
in ((_156_201), (_156_200))))
in FStar_Syntax_Syntax.Tm_app (_156_202))
in (FStar_Syntax_Syntax.mk tm None pos)))


let rec desugar_data_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat) = (fun env p is_mut -> (

let check_linear_pattern_variables = (fun p -> (

let rec pat_vars = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_dot_term (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_constant (_)) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (_64_451, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out _64_459 -> (match (_64_459) with
| (p, _64_458) -> begin
(let _156_249 = (pat_vars p)
in (FStar_Util.set_union out _156_249))
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

let _64_482 = (match (((is_mut), (p.FStar_Parser_AST.pat))) with
| ((false, _)) | ((true, FStar_Parser_AST.PatVar (_))) -> begin
()
end
| (true, _64_480) -> begin
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
| _64_493 -> begin
(

let _64_496 = (push_bv_maybe_mut e x)
in (match (_64_496) with
| (e, x) -> begin
(((x)::l), (e), (x))
end))
end))
in (

let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun b -> (b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText))))) with
| Some (b) -> begin
((l), (e), (b))
end
| _64_505 -> begin
(

let _64_508 = (push_bv_maybe_mut e a)
in (match (_64_508) with
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
| FStar_Parser_AST.PatOr ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.PatOr ((p)::ps) -> begin
(

let _64_530 = (aux loc env p)
in (match (_64_530) with
| (loc, env, var, p, _64_529) -> begin
(

let _64_547 = (FStar_List.fold_left (fun _64_534 p -> (match (_64_534) with
| (loc, env, ps) -> begin
(

let _64_543 = (aux loc env p)
in (match (_64_543) with
| (loc, env, _64_539, p, _64_542) -> begin
((loc), (env), ((p)::ps))
end))
end)) ((loc), (env), ([])) ps)
in (match (_64_547) with
| (loc, env, ps) -> begin
(

let pat = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in ((loc), (env), (var), (pat), (false)))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _64_558 = (aux loc env p)
in (match (_64_558) with
| (loc, env', binder, p, imp) -> begin
(

let binder = (match (binder) with
| LetBinder (_64_560) -> begin
(FStar_All.failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t = (let _156_283 = (close_fun env t)
in (desugar_term env _156_283))
in LocalBinder ((((

let _64_567 = x
in {FStar_Syntax_Syntax.ppname = _64_567.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_567.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (aq))))
end)
in ((loc), (env'), (binder), (p), (imp)))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _156_284 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env), (LocalBinder (((x), (None)))), (_156_284), (false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _156_285 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env), (LocalBinder (((x), (None)))), (_156_285), (false))))
end
| (FStar_Parser_AST.PatTvar (x, aq)) | (FStar_Parser_AST.PatVar (x, aq)) -> begin
(

let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (

let aq = (trans_aqual aq)
in (

let _64_586 = (resolvex loc env x)
in (match (_64_586) with
| (loc, env, xbv) -> begin
(let _156_286 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc), (env), (LocalBinder (((xbv), (aq)))), (_156_286), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _156_287 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), ([])))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_156_287), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _64_592}, args) -> begin
(

let _64_614 = (FStar_List.fold_right (fun arg _64_603 -> (match (_64_603) with
| (loc, env, args) -> begin
(

let _64_610 = (aux loc env arg)
in (match (_64_610) with
| (loc, env, _64_607, arg, imp) -> begin
((loc), (env), ((((arg), (imp)))::args))
end))
end)) args ((loc), (env), ([])))
in (match (_64_614) with
| (loc, env, args) -> begin
(

let l = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _156_290 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_156_290), (false)))))
end))
end
| FStar_Parser_AST.PatApp (_64_618) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let _64_638 = (FStar_List.fold_right (fun pat _64_626 -> (match (_64_626) with
| (loc, env, pats) -> begin
(

let _64_634 = (aux loc env pat)
in (match (_64_634) with
| (loc, env, _64_630, pat, _64_633) -> begin
((loc), (env), ((pat)::pats))
end))
end)) pats ((loc), (env), ([])))
in (match (_64_638) with
| (loc, env, pats) -> begin
(

let pat = (let _156_303 = (let _156_302 = (let _156_298 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _156_298))
in (let _156_301 = (let _156_300 = (let _156_299 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_156_299), ([])))
in FStar_Syntax_Syntax.Pat_cons (_156_300))
in (FStar_All.pipe_left _156_302 _156_301)))
in (FStar_List.fold_right (fun hd tl -> (

let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (let _156_297 = (let _156_296 = (let _156_295 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_156_295), ((((hd), (false)))::(((tl), (false)))::[])))
in FStar_Syntax_Syntax.Pat_cons (_156_296))
in (FStar_All.pipe_left (pos_r r) _156_297)))) pats _156_303))
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc), (env), (LocalBinder (((x), (None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(

let _64_664 = (FStar_List.fold_left (fun _64_651 p -> (match (_64_651) with
| (loc, env, pats) -> begin
(

let _64_660 = (aux loc env p)
in (match (_64_660) with
| (loc, env, _64_656, pat, _64_659) -> begin
((loc), (env), ((((pat), (false)))::pats))
end))
end)) ((loc), (env), ([])) args)
in (match (_64_664) with
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

let _64_670 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) l)
in (match (_64_670) with
| (constr, _64_669) -> begin
(

let l = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| _64_674 -> begin
(FStar_All.failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _156_306 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_156_306), (false)))))
end))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(

let _64_684 = (FStar_List.hd fields)
in (match (_64_684) with
| (f, _64_683) -> begin
(

let _64_688 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_64_688) with
| (record, _64_687) -> begin
(

let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _64_691 -> (match (_64_691) with
| (f, p) -> begin
(let _156_308 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.qualify_field_to_record env record) f)
in ((_156_308), (p)))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _64_696 -> (match (_64_696) with
| (f, _64_695) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _64_700 -> (match (_64_700) with
| (g, _64_699) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_64_703, p) -> begin
p
end)
end))))
in (

let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_Env.constrname)) p.FStar_Parser_AST.prange)), (args)))) p.FStar_Parser_AST.prange)
in (

let _64_715 = (aux loc env app)
in (match (_64_715) with
| (env, e, b, p, _64_714) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(let _156_317 = (let _156_316 = (let _156_315 = (

let _64_720 = fv
in (let _156_314 = (let _156_313 = (let _156_312 = (let _156_311 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_Env.typename), (_156_311)))
in FStar_Syntax_Syntax.Record_ctor (_156_312))
in Some (_156_313))
in {FStar_Syntax_Syntax.fv_name = _64_720.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = _64_720.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _156_314}))
in ((_156_315), (args)))
in FStar_Syntax_Syntax.Pat_cons (_156_316))
in (FStar_All.pipe_left pos _156_317))
end
| _64_723 -> begin
p
end)
in ((env), (e), (b), (p), (false)))
end)))))
end))
end))
end))))
in (

let _64_732 = (aux [] env p)
in (match (_64_732) with
| (_64_726, env, b, p, _64_731) -> begin
(

let _64_733 = (let _156_318 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore _156_318))
in ((env), (b), (p)))
end)))))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p is_mut -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _64_741) -> begin
(let _156_325 = (let _156_324 = (let _156_323 = (FStar_Parser_Env.qualify env x)
in ((_156_323), (FStar_Syntax_Syntax.tun)))
in LetBinder (_156_324))
in ((env), (_156_325), (None)))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _64_748); FStar_Parser_AST.prange = _64_745}, t) -> begin
(let _156_329 = (let _156_328 = (let _156_327 = (FStar_Parser_Env.qualify env x)
in (let _156_326 = (desugar_term env t)
in ((_156_327), (_156_326))))
in LetBinder (_156_328))
in ((env), (_156_329), (None)))
end
| _64_756 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end else begin
(

let _64_760 = (desugar_data_pat env p is_mut)
in (match (_64_760) with
| (env, binder, p) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| _64_768 -> begin
Some (p)
end)
in ((env), (binder), (p)))
end))
end)
and desugar_binding_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun _64_772 env pat -> (

let _64_780 = (desugar_data_pat env pat false)
in (match (_64_780) with
| (env, _64_778, pat) -> begin
((env), (pat))
end)))
and desugar_match_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let _64_785 = env
in {FStar_Parser_Env.curmodule = _64_785.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _64_785.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _64_785.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _64_785.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _64_785.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _64_785.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _64_785.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _64_785.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _64_785.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _64_785.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _64_785.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let _64_790 = env
in {FStar_Parser_Env.curmodule = _64_790.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _64_790.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _64_790.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _64_790.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _64_790.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _64_790.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _64_790.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _64_790.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _64_790.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _64_790.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _64_790.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_machine_integer : FStar_Parser_Env.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env repr _64_797 range -> (match (_64_797) with
| (signedness, width) -> begin
(

let lid = (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "FStar." (match (signedness) with
| FStar_Const.Unsigned -> begin
"U"
end
| FStar_Const.Signed -> begin
""
end)) "Int") (match (width) with
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
end)) ".") (match (signedness) with
| FStar_Const.Unsigned -> begin
"u"
end
| FStar_Const.Signed -> begin
""
end)) "int_to_t")
in (

let lid = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text lid) range)
in (

let lid = (match ((FStar_Parser_Env.try_lookup_lid env lid)) with
| Some (lid) -> begin
(Prims.fst lid)
end
| None -> begin
(let _156_345 = (FStar_Util.format1 "%s not in scope\n" (FStar_Ident.text_of_lid lid))
in (FStar_All.failwith _156_345))
end)
in (

let repr = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (None))))) None range)
in (let _156_350 = (let _156_349 = (let _156_348 = (let _156_347 = (let _156_346 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr), (_156_346)))
in (_156_347)::[])
in ((lid), (_156_348)))
in FStar_Syntax_Syntax.Tm_app (_156_349))
in (FStar_Syntax_Syntax.mk _156_350 None range))))))
end))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (

let mk = (fun e -> (FStar_Syntax_Syntax.mk e None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let _64_821 = e
in {FStar_Syntax_Syntax.n = _64_821.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _64_821.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _64_821.FStar_Syntax_Syntax.vars}))
in (match ((let _156_358 = (unparen top)
in _156_358.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (_64_825) -> begin
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
| FStar_Parser_AST.Op ("*", (_64_851)::(_64_849)::[]) when (let _156_359 = (op_as_term env 2 top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right _156_359 FStar_Option.isNone)) -> begin
(

let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", (t1)::(t2)::[]) -> begin
(

let rest = (flatten t2)
in (t1)::rest)
end
| _64_865 -> begin
(t)::[]
end))
in (

let targs = (let _156_365 = (let _156_362 = (unparen top)
in (flatten _156_362))
in (FStar_All.pipe_right _156_365 (FStar_List.map (fun t -> (let _156_364 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg _156_364))))))
in (

let _64_871 = (let _156_366 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) _156_366))
in (match (_64_871) with
| (tup, _64_870) -> begin
(mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _156_368 = (let _156_367 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) a)
in (Prims.fst _156_367))
in (FStar_All.pipe_left setpos _156_368))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Unexpected operator: " s)), (top.FStar_Parser_AST.range)))))
end
| Some (op) -> begin
(

let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _156_370 = (desugar_term env t)
in ((_156_370), (None))))))
in (mk (FStar_Syntax_Syntax.Tm_app (((op), (args))))))
end)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _64_889; FStar_Ident.ident = _64_887; FStar_Ident.nsstr = _64_885; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _64_898; FStar_Ident.ident = _64_896; FStar_Ident.nsstr = _64_894; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _64_907; FStar_Ident.ident = _64_905; FStar_Ident.nsstr = _64_903; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _64_916; FStar_Ident.ident = _64_914; FStar_Ident.nsstr = _64_912; FStar_Ident.str = "True"}) -> begin
(let _156_371 = (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _156_371 FStar_Syntax_Syntax.Delta_constant None))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _64_925; FStar_Ident.ident = _64_923; FStar_Ident.nsstr = _64_921; FStar_Ident.str = "False"}) -> begin
(let _156_372 = (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _156_372 FStar_Syntax_Syntax.Delta_constant None))
end
| FStar_Parser_AST.Assign (ident, t2) -> begin
(

let t2 = (desugar_term env t2)
in (

let _64_935 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) ident)
in (match (_64_935) with
| (t1, mut) -> begin
(

let _64_936 = if (not (mut)) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Can only assign to mutable values"), (top.FStar_Parser_AST.range)))))
end else begin
()
end
in (mk_ref_assign t1 t2 top.FStar_Parser_AST.range))
end)))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(

let _64_943 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) l)
in (match (_64_943) with
| (tm, mut) -> begin
(

let tm = (setpos tm)
in if mut then begin
(let _156_375 = (let _156_374 = (let _156_373 = (mk_ref_read tm)
in ((_156_373), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval))))
in FStar_Syntax_Syntax.Tm_meta (_156_374))
in (FStar_All.pipe_left mk _156_375))
end else begin
tm
end)
end))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(

let _64_954 = (match ((FStar_Parser_Env.try_lookup_datacon env l)) with
| None -> begin
(let _156_377 = (let _156_376 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) l)
in (FStar_All.pipe_left Prims.fst _156_376))
in ((_156_377), (false)))
end
| Some (head) -> begin
(let _156_378 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in ((_156_378), (true)))
end)
in (match (_64_954) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| _64_957 -> begin
(

let args = (FStar_List.map (fun _64_960 -> (match (_64_960) with
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
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let _64_988 = (FStar_List.fold_left (fun _64_971 b -> (match (_64_971) with
| (env, tparams, typs) -> begin
(

let _64_975 = (desugar_binder env b)
in (match (_64_975) with
| (xopt, t) -> begin
(

let _64_981 = (match (xopt) with
| None -> begin
(let _156_382 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env), (_156_382)))
end
| Some (x) -> begin
(FStar_Parser_Env.push_bv env x)
end)
in (match (_64_981) with
| (env, x) -> begin
(let _156_386 = (let _156_385 = (let _156_384 = (let _156_383 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _156_383))
in (_156_384)::[])
in (FStar_List.append typs _156_385))
in ((env), ((FStar_List.append tparams (((((

let _64_982 = x
in {FStar_Syntax_Syntax.ppname = _64_982.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_982.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (None)))::[]))), (_156_386)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_64_988) with
| (env, _64_986, targs) -> begin
(

let _64_992 = (let _156_387 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) _156_387))
in (match (_64_992) with
| (tup, _64_991) -> begin
(FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let _64_999 = (uncurry binders t)
in (match (_64_999) with
| (bs, t) -> begin
(

let rec aux = (fun env bs _64_8 -> (match (_64_8) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (let _156_394 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos _156_394)))
end
| (hd)::tl -> begin
(

let mlenv = (FStar_Parser_Env.default_ml env)
in (

let bb = (desugar_binder mlenv hd)
in (

let _64_1013 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_64_1013) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_binder env b)) with
| (None, _64_1020) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(

let _64_1028 = (as_binder env None b)
in (match (_64_1028) with
| ((x, _64_1025), env) -> begin
(

let f = (desugar_formula env f)
in (let _156_395 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos _156_395)))
end))
end)
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let _64_1048 = (FStar_List.fold_left (fun _64_1036 pat -> (match (_64_1036) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (_64_1039, t) -> begin
(let _156_399 = (let _156_398 = (free_type_vars env t)
in (FStar_List.append _156_398 ftvs))
in ((env), (_156_399)))
end
| _64_1044 -> begin
((env), (ftvs))
end)
end)) ((env), ([])) binders)
in (match (_64_1048) with
| (_64_1046, ftv) -> begin
(

let ftv = (sort_ftv ftv)
in (

let binders = (let _156_401 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append _156_401 binders))
in (

let rec aux = (fun env bs sc_pat_opt _64_9 -> (match (_64_9) with
| [] -> begin
(

let body = (desugar_term env body)
in (

let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(

let body = (let _156_411 = (let _156_410 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right _156_410 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close _156_411 body))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (None), (body)))::[])))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (let _156_412 = (no_annot_abs (FStar_List.rev bs) body)
in (setpos _156_412))))
end
| (p)::rest -> begin
(

let _64_1072 = (desugar_binding_pat env p)
in (match (_64_1072) with
| (env, b, pat) -> begin
(

let _64_1123 = (match (b) with
| LetBinder (_64_1074) -> begin
(FStar_All.failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt = (match (((pat), (sc_pat_opt))) with
| (None, _64_1082) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _156_414 = (let _156_413 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_156_413), (p)))
in Some (_156_414))
end
| (Some (p), Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (_64_1096), _64_1099) -> begin
(

let tup2 = (let _156_415 = (FStar_Syntax_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _156_415 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (let _156_423 = (let _156_422 = (let _156_421 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (let _156_420 = (let _156_419 = (FStar_Syntax_Syntax.as_arg sc)
in (let _156_418 = (let _156_417 = (let _156_416 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _156_416))
in (_156_417)::[])
in (_156_419)::_156_418))
in ((_156_421), (_156_420))))
in FStar_Syntax_Syntax.Tm_app (_156_422))
in (FStar_Syntax_Syntax.mk _156_423 None top.FStar_Parser_AST.range))
in (

let p = (let _156_424 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p), (false)))::[])))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _156_424))
in Some (((sc), (p))))))
end
| (FStar_Syntax_Syntax.Tm_app (_64_1105, args), FStar_Syntax_Syntax.Pat_cons (_64_1110, pats)) -> begin
(

let tupn = (let _156_425 = (FStar_Syntax_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _156_425 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (let _156_432 = (let _156_431 = (let _156_430 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (let _156_429 = (let _156_428 = (let _156_427 = (let _156_426 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _156_426))
in (_156_427)::[])
in (FStar_List.append args _156_428))
in ((_156_430), (_156_429))))
in FStar_Syntax_Syntax.Tm_app (_156_431))
in (mk _156_432))
in (

let p = (let _156_433 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p), (false)))::[])))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _156_433))
in Some (((sc), (p))))))
end
| _64_1119 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt)))
end)
in (match (_64_1123) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _64_1127; FStar_Parser_AST.level = _64_1125}, phi, _64_1133) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(

let phi = (desugar_formula env phi)
in (let _156_441 = (let _156_440 = (let _156_439 = (FStar_Syntax_Syntax.fvar a FStar_Syntax_Syntax.Delta_equational None)
in (let _156_438 = (let _156_437 = (FStar_Syntax_Syntax.as_arg phi)
in (let _156_436 = (let _156_435 = (let _156_434 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _156_434))
in (_156_435)::[])
in (_156_437)::_156_436))
in ((_156_439), (_156_438))))
in FStar_Syntax_Syntax.Tm_app (_156_440))
in (mk _156_441)))
end
| FStar_Parser_AST.App (_64_1138) -> begin
(

let rec aux = (fun args e -> (match ((let _156_446 = (unparen e)
in _156_446.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(

let arg = (let _156_447 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _156_447))
in (aux ((arg)::args) e))
end
| _64_1150 -> begin
(

let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app (((head), (args))))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _156_450 = (let _156_449 = (let _156_448 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((_156_448), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))
in FStar_Syntax_Syntax.Tm_meta (_156_449))
in (mk _156_450))
end
| FStar_Parser_AST.Let (qual, ((pat, _snd))::_tl, body) -> begin
(

let is_rec = (qual = FStar_Parser_AST.Rec)
in (

let ds_let_rec_or_app = (fun _64_1167 -> (match (()) with
| () -> begin
(

let bindings = (((pat), (_snd)))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _64_1171 -> (match (_64_1171) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _156_454 = (destruct_app_pattern env top_level p)
in ((_156_454), (def)))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _156_455 = (destruct_app_pattern env top_level p)
in ((_156_455), (def)))
end
| _64_1177 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _64_1182); FStar_Parser_AST.prange = _64_1179}, t) -> begin
if top_level then begin
(let _156_458 = (let _156_457 = (let _156_456 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_156_456))
in ((_156_457), ([]), (Some (t))))
in ((_156_458), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (Some (t)))), (def))
end
end
| FStar_Parser_AST.PatVar (id, _64_1191) -> begin
if top_level then begin
(let _156_461 = (let _156_460 = (let _156_459 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_156_459))
in ((_156_460), ([]), (None)))
in ((_156_461), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (None))), (def))
end
end
| _64_1195 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end
end))))
in (

let _64_1224 = (FStar_List.fold_left (fun _64_1200 _64_1209 -> (match (((_64_1200), (_64_1209))) with
| ((env, fnames, rec_bindings), ((f, _64_1203, _64_1205), _64_1208)) -> begin
(

let _64_1220 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let _64_1214 = (FStar_Parser_Env.push_bv env x)
in (match (_64_1214) with
| (env, xx) -> begin
(let _156_465 = (let _156_464 = (FStar_Syntax_Syntax.mk_binder xx)
in (_156_464)::rec_bindings)
in ((env), (FStar_Util.Inl (xx)), (_156_465)))
end))
end
| FStar_Util.Inr (l) -> begin
(let _156_466 = (FStar_Parser_Env.push_top_level_rec_binding env l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in ((_156_466), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (_64_1220) with
| (env, lbname, rec_bindings) -> begin
((env), ((lbname)::fnames), (rec_bindings))
end))
end)) ((env), ([]), ([])) funs)
in (match (_64_1224) with
| (env', fnames, rec_bindings) -> begin
(

let fnames = (FStar_List.rev fnames)
in (

let desugar_one_def = (fun env lbname _64_1235 -> (match (_64_1235) with
| ((_64_1230, args, result_t), def) -> begin
(

let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _156_473 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t)))) _156_473 FStar_Parser_AST.Expr))
end)
in (

let def = (match (args) with
| [] -> begin
def
end
| _64_1242 -> begin
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
(let _156_475 = (let _156_474 = (FStar_Syntax_Util.incr_delta_qualifier body)
in (FStar_Syntax_Syntax.lid_as_fv l _156_474 None))
in FStar_Util.Inr (_156_475))
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
in (let _156_478 = (let _156_477 = (let _156_476 = (FStar_Syntax_Subst.close rec_bindings body)
in ((((is_rec), (lbs))), (_156_476)))
in FStar_Syntax_Syntax.Tm_let (_156_477))
in (FStar_All.pipe_left mk _156_478))))))
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

let _64_1263 = (desugar_binding_pat_maybe_top top_level env pat is_mutable)
in (match (_64_1263) with
| (env, binder, pat) -> begin
(

let tm = (match (binder) with
| LetBinder (l, t) -> begin
(

let body = (desugar_term env t2)
in (

let fv = (let _156_485 = (FStar_Syntax_Util.incr_delta_qualifier t1)
in (FStar_Syntax_Syntax.lid_as_fv l _156_485 None))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((((false), (({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]))), (body)))))))
end
| LocalBinder (x, _64_1272) -> begin
(

let body = (desugar_term env t2)
in (

let body = (match (pat) with
| (None) | (Some ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (_); FStar_Syntax_Syntax.ty = _; FStar_Syntax_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _156_490 = (let _156_489 = (let _156_488 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _156_487 = (let _156_486 = (FStar_Syntax_Util.branch ((pat), (None), (body)))
in (_156_486)::[])
in ((_156_488), (_156_487))))
in FStar_Syntax_Syntax.Tm_match (_156_489))
in (FStar_Syntax_Syntax.mk _156_490 None body.FStar_Syntax_Syntax.pos))
end)
in (let _156_495 = (let _156_494 = (let _156_493 = (let _156_492 = (let _156_491 = (FStar_Syntax_Syntax.mk_binder x)
in (_156_491)::[])
in (FStar_Syntax_Subst.close _156_492 body))
in ((((false), (((mk_lb ((FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t1))))::[]))), (_156_493)))
in FStar_Syntax_Syntax.Tm_let (_156_494))
in (FStar_All.pipe_left mk _156_495))))
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
in (let _156_506 = (let _156_505 = (let _156_504 = (desugar_term env t1)
in (let _156_503 = (let _156_502 = (let _156_497 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (let _156_496 = (desugar_term env t2)
in ((_156_497), (None), (_156_496))))
in (let _156_501 = (let _156_500 = (let _156_499 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (let _156_498 = (desugar_term env t3)
in ((_156_499), (None), (_156_498))))
in (_156_500)::[])
in (_156_502)::_156_501))
in ((_156_504), (_156_503))))
in FStar_Syntax_Syntax.Tm_match (_156_505))
in (mk _156_506)))
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

let desugar_branch = (fun _64_1313 -> (match (_64_1313) with
| (pat, wopt, b) -> begin
(

let _64_1316 = (desugar_match_pat env pat)
in (match (_64_1316) with
| (env, pat) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _156_509 = (desugar_term env e)
in Some (_156_509))
end)
in (

let b = (desugar_term env b)
in (FStar_Syntax_Util.branch ((pat), (wopt), (b)))))
end))
end))
in (let _156_513 = (let _156_512 = (let _156_511 = (desugar_term env e)
in (let _156_510 = (FStar_List.map desugar_branch branches)
in ((_156_511), (_156_510))))
in FStar_Syntax_Syntax.Tm_match (_156_512))
in (FStar_All.pipe_left mk _156_513)))
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
in (let _156_516 = (let _156_515 = (let _156_514 = (desugar_term env e)
in ((_156_514), (annot), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (_156_515))
in (FStar_All.pipe_left mk _156_516)))))
end
| FStar_Parser_AST.Record (_64_1330, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let _64_1341 = (FStar_List.hd fields)
in (match (_64_1341) with
| (f, _64_1340) -> begin
(

let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (

let _64_1347 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_64_1347) with
| (record, _64_1346) -> begin
(

let get_field = (fun xopt f -> (

let fn = f.FStar_Ident.ident
in (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _64_1355 -> (match (_64_1355) with
| (g, _64_1354) -> begin
(

let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_64_1359, e) -> begin
(let _156_524 = (qfn fn)
in ((_156_524), (e)))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _156_527 = (let _156_526 = (let _156_525 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in ((_156_525), (top.FStar_Parser_AST.range)))
in FStar_Syntax_Syntax.Error (_156_526))
in (Prims.raise _156_527))
end
| Some (x) -> begin
(let _156_528 = (qfn fn)
in ((_156_528), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Project (((x), (f)))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level))))
end)
end))))
in (

let recterm = (match (eopt) with
| None -> begin
(let _156_533 = (let _156_532 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _64_1371 -> (match (_64_1371) with
| (f, _64_1370) -> begin
(let _156_531 = (let _156_530 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _156_530))
in ((_156_531), (FStar_Parser_AST.Nothing)))
end))))
in ((record.FStar_Parser_Env.constrname), (_156_532)))
in FStar_Parser_AST.Construct (_156_533))
end
| Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (let _156_535 = (let _156_534 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_156_534))
in (FStar_Parser_AST.mk_term _156_535 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record = (let _156_538 = (let _156_537 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _64_1379 -> (match (_64_1379) with
| (f, _64_1378) -> begin
(get_field (Some (xterm)) f)
end))))
in ((None), (_156_537)))
in FStar_Parser_AST.Record (_156_538))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _64_1395; FStar_Syntax_Syntax.pos = _64_1393; FStar_Syntax_Syntax.vars = _64_1391}, args); FStar_Syntax_Syntax.tk = _64_1389; FStar_Syntax_Syntax.pos = _64_1387; FStar_Syntax_Syntax.vars = _64_1385}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(

let e = (let _156_546 = (let _156_545 = (let _156_544 = (let _156_543 = (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos)
in (let _156_542 = (let _156_541 = (let _156_540 = (let _156_539 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_Env.typename), (_156_539)))
in FStar_Syntax_Syntax.Record_ctor (_156_540))
in Some (_156_541))
in (FStar_Syntax_Syntax.fvar _156_543 FStar_Syntax_Syntax.Delta_constant _156_542)))
in ((_156_544), (args)))
in FStar_Syntax_Syntax.Tm_app (_156_545))
in (FStar_All.pipe_left mk _156_546))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))))))
end
| _64_1409 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(

let _64_1416 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_projector_by_field_name env) f)
in (match (_64_1416) with
| (fieldname, is_rec) -> begin
(

let e = (desugar_term env e)
in (

let fn = (

let _64_1421 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_64_1421) with
| (ns, _64_1420) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (

let qual = if is_rec then begin
Some (FStar_Syntax_Syntax.Record_projector (fn))
end else begin
None
end
in (let _156_552 = (let _156_551 = (let _156_550 = (let _156_547 = (FStar_Ident.set_lid_range fieldname (FStar_Ident.range_of_lid f))
in (FStar_Syntax_Syntax.fvar _156_547 FStar_Syntax_Syntax.Delta_equational qual))
in (let _156_549 = (let _156_548 = (FStar_Syntax_Syntax.as_arg e)
in (_156_548)::[])
in ((_156_550), (_156_549))))
in FStar_Syntax_Syntax.Tm_app (_156_551))
in (FStar_All.pipe_left mk _156_552)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| _64_1431 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _64_1433 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_args : FStar_Parser_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun _64_1438 -> (match (_64_1438) with
| (a, imp) -> begin
(let _156_556 = (desugar_term env a)
in (arg_withimp_e imp _156_556))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r default_ok env t -> (

let fail = (fun msg -> (Prims.raise (FStar_Syntax_Syntax.Error (((msg), (r))))))
in (

let is_requires = (fun _64_1450 -> (match (_64_1450) with
| (t, _64_1449) -> begin
(match ((let _156_564 = (unparen t)
in _156_564.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Requires (_64_1452) -> begin
true
end
| _64_1455 -> begin
false
end)
end))
in (

let is_ensures = (fun _64_1460 -> (match (_64_1460) with
| (t, _64_1459) -> begin
(match ((let _156_567 = (unparen t)
in _156_567.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ensures (_64_1462) -> begin
true
end
| _64_1465 -> begin
false
end)
end))
in (

let is_app = (fun head _64_1471 -> (match (_64_1471) with
| (t, _64_1470) -> begin
(match ((let _156_572 = (unparen t)
in _156_572.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _64_1475; FStar_Parser_AST.level = _64_1473}, _64_1480, _64_1482) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| _64_1486 -> begin
false
end)
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t -> (

let _64_1492 = (head_and_args t)
in (match (_64_1492) with
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
(let _156_576 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_name env) l)
in ((_156_576), (args)))
end
| FStar_Parser_AST.Name (l) when ((let _156_577 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _156_577 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(let _156_578 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in ((_156_578), (args)))
end
| FStar_Parser_AST.Name (l) when ((let _156_579 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _156_579 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(let _156_580 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)
in ((_156_580), (args)))
end
| FStar_Parser_AST.Name (l) when ((((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) && default_ok) -> begin
(let _156_581 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in ((_156_581), ((((t), (FStar_Parser_AST.Nothing)))::[])))
end
| _64_1523 when default_ok -> begin
(let _156_582 = (FStar_Ident.set_lid_range env.FStar_Parser_Env.default_result_effect head.FStar_Parser_AST.range)
in ((_156_582), ((((t), (FStar_Parser_AST.Nothing)))::[])))
end
| _64_1525 -> begin
(let _156_584 = (let _156_583 = (FStar_Parser_AST.term_to_string t)
in (FStar_Util.format1 "%s is not an effect" _156_583))
in (fail _156_584))
end)
end)))
in (

let _64_1528 = (pre_process_comp_typ t)
in (match (_64_1528) with
| (eff, args) -> begin
(

let _64_1529 = if ((FStar_List.length args) = 0) then begin
(let _156_586 = (let _156_585 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" _156_585))
in (fail _156_586))
end else begin
()
end
in (

let _64_1533 = (let _156_588 = (FStar_List.hd args)
in (let _156_587 = (FStar_List.tl args)
in ((_156_588), (_156_587))))
in (match (_64_1533) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (Prims.fst result_arg))
in (

let rest = (desugar_args env rest)
in (

let _64_1558 = (FStar_All.pipe_right rest (FStar_List.partition (fun _64_1539 -> (match (_64_1539) with
| (t, _64_1538) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _64_1545; FStar_Syntax_Syntax.pos = _64_1543; FStar_Syntax_Syntax.vars = _64_1541}, (_64_1550)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| _64_1555 -> begin
false
end)
end))))
in (match (_64_1558) with
| (dec, rest) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _64_1562 -> (match (_64_1562) with
| (t, _64_1561) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_64_1564, ((arg, _64_1567))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| _64_1573 -> begin
(FStar_All.failwith "impos")
end)
end))))
in (

let no_additional_args = (((FStar_List.length decreases_clause) = 0) && ((FStar_List.length rest) = 0))
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

let pattern = (let _156_592 = (let _156_591 = (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _156_591 FStar_Syntax_Syntax.Delta_constant None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _156_592 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app nil ((((pattern), (Some (FStar_Syntax_Syntax.imp_tag))))::[]) None pat.FStar_Syntax_Syntax.pos)))
end
| _64_1588 -> begin
pat
end)
in (let _156_596 = (let _156_595 = (let _156_594 = (let _156_593 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) None pat.FStar_Syntax_Syntax.pos)
in ((_156_593), (aq)))
in (_156_594)::[])
in (ens)::_156_595)
in (req)::_156_596))
end
| _64_1591 -> begin
rest
end)
end else begin
rest
end
in (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.effect_name = eff; FStar_Syntax_Syntax.result_typ = result_typ; FStar_Syntax_Syntax.effect_args = rest; FStar_Syntax_Syntax.flags = (FStar_List.append flags decreases_clause)})))
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
| _64_1603 -> begin
None
end))
in (

let mk = (fun t -> (FStar_Syntax_Syntax.mk t None f.FStar_Parser_AST.range))
in (

let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let _64_1610 = t
in {FStar_Syntax_Syntax.n = _64_1610.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _64_1610.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _64_1610.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let _64_1617 = b
in {FStar_Parser_AST.b = _64_1617.FStar_Parser_AST.b; FStar_Parser_AST.brange = _64_1617.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _64_1617.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _156_631 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _156_631)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(

let _64_1631 = (FStar_Parser_Env.push_bv env a)
in (match (_64_1631) with
| (env, a) -> begin
(

let a = (

let _64_1632 = a
in {FStar_Syntax_Syntax.ppname = _64_1632.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_1632.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats = (desugar_pats env pats)
in (

let body = (desugar_formula env body)
in (

let body = (match (pats) with
| [] -> begin
body
end
| _64_1639 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta (((body), (FStar_Syntax_Syntax.Meta_pattern (pats))))))
end)
in (

let body = (let _156_634 = (let _156_633 = (let _156_632 = (FStar_Syntax_Syntax.mk_binder a)
in (_156_632)::[])
in (no_annot_abs _156_633 body))
in (FStar_All.pipe_left setpos _156_634))
in (let _156_640 = (let _156_639 = (let _156_638 = (let _156_635 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Syntax_Syntax.fvar _156_635 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (let _156_637 = (let _156_636 = (FStar_Syntax_Syntax.as_arg body)
in (_156_636)::[])
in ((_156_638), (_156_637))))
in FStar_Syntax_Syntax.Tm_app (_156_639))
in (FStar_All.pipe_left mk _156_640)))))))
end))
end
| _64_1643 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body = (let _156_655 = (q ((rest), (pats), (body)))
in (let _156_654 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _156_655 _156_654 FStar_Parser_AST.Formula)))
in (let _156_656 = (q (((b)::[]), ([]), (body)))
in (FStar_Parser_AST.mk_term _156_656 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _64_1657 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _156_657 = (unparen f)
in _156_657.FStar_Parser_AST.tm)) with
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
in (let _156_659 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _156_659)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _156_661 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _156_661)))
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
| _64_1715 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (

let _64_1739 = (FStar_List.fold_left (fun _64_1720 b -> (match (_64_1720) with
| (env, out) -> begin
(

let tk = (desugar_binder env (

let _64_1722 = b
in {FStar_Parser_AST.b = _64_1722.FStar_Parser_AST.b; FStar_Parser_AST.brange = _64_1722.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _64_1722.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(

let _64_1731 = (FStar_Parser_Env.push_bv env a)
in (match (_64_1731) with
| (env, a) -> begin
(

let a = (

let _64_1732 = a
in {FStar_Syntax_Syntax.ppname = _64_1732.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_1732.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in ((env), ((((a), ((trans_aqual b.FStar_Parser_AST.aqual))))::out)))
end))
end
| _64_1736 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (_64_1739) with
| (env, tpars) -> begin
((env), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(let _156_668 = (desugar_typ env t)
in ((Some (x)), (_156_668)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _156_669 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None x.FStar_Ident.idRange)
in ((Some (x)), (_156_669)))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _156_670 = (desugar_typ env t)
in ((None), (_156_670)))
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

let binders = (let _156_686 = (let _156_685 = (FStar_Syntax_Util.arrow_formals k)
in (Prims.fst _156_685))
in (FStar_List.append tps _156_686))
in (

let p = (FStar_Ident.range_of_lid t)
in (

let _64_1766 = (FStar_Syntax_Util.args_of_binders binders)
in (match (_64_1766) with
| (binders, args) -> begin
(

let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _64_1770 -> (match (_64_1770) with
| (x, _64_1769) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let binders = (let _156_692 = (let _156_691 = (let _156_690 = (let _156_689 = (let _156_688 = (FStar_Syntax_Syntax.lid_as_fv t FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _156_688))
in (FStar_Syntax_Syntax.mk_Tm_app _156_689 args None p))
in (FStar_All.pipe_left FStar_Syntax_Syntax.null_binder _156_690))
in (_156_691)::[])
in (FStar_List.append imp_binders _156_692))
in (

let disc_type = (let _156_695 = (let _156_694 = (let _156_693 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _156_693))
in (FStar_Syntax_Syntax.mk_Total _156_694))
in (FStar_Syntax_Util.arrow binders _156_695))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (let _156_698 = (let _156_697 = (quals ((FStar_Syntax_Syntax.Logic)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in ((disc_name), ([]), (disc_type), (_156_697), ((FStar_Ident.range_of_lid disc_name))))
in FStar_Syntax_Syntax.Sig_declare_typ (_156_698)))))))))
end))))))


let mk_indexed_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq refine_domain env tc lid inductive_tps imp_tps fields t -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p))
in (

let projectee = (fun ptyp -> (FStar_Syntax_Syntax.gen_bv "projectee" (Some (p)) ptyp))
in (

let tps = (FStar_List.map2 (fun _64_1794 _64_1798 -> (match (((_64_1794), (_64_1798))) with
| ((_64_1792, imp), (x, _64_1797)) -> begin
((x), (imp))
end)) inductive_tps imp_tps)
in (

let _64_1899 = (

let _64_1802 = (FStar_Syntax_Util.head_and_args t)
in (match (_64_1802) with
| (head, args0) -> begin
(

let args = (

let rec arguments = (fun tps args -> (match (((tps), (args))) with
| ([], _64_1808) -> begin
args
end
| (_64_1811, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Not enough arguments to type"), ((FStar_Ident.range_of_lid lid))))))
end
| (((_64_1816, Some (FStar_Syntax_Syntax.Implicit (_64_1818))))::tps', ((_64_1825, Some (FStar_Syntax_Syntax.Implicit (_64_1827))))::args') -> begin
(arguments tps' args')
end
| (((_64_1835, Some (FStar_Syntax_Syntax.Implicit (_64_1837))))::tps', ((_64_1845, _64_1847))::_64_1843) -> begin
(arguments tps' args)
end
| (((_64_1854, _64_1856))::_64_1852, ((a, Some (FStar_Syntax_Syntax.Implicit (_64_1863))))::_64_1860) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected implicit annotation on argument"), (a.FStar_Syntax_Syntax.pos)))))
end
| (((_64_1871, _64_1873))::tps', ((_64_1878, _64_1880))::args') -> begin
(arguments tps' args')
end))
in (arguments inductive_tps args0))
in (

let indices = (FStar_All.pipe_right args (FStar_List.map (fun _64_1885 -> (let _156_730 = (FStar_Syntax_Syntax.new_bv (Some (p)) FStar_Syntax_Syntax.tun)
in (FStar_All.pipe_right _156_730 FStar_Syntax_Syntax.mk_binder)))))
in (

let arg_typ = (let _156_735 = (let _156_731 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _156_731))
in (let _156_734 = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _64_1890 -> (match (_64_1890) with
| (x, imp) -> begin
(let _156_733 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_156_733), (imp)))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app _156_735 _156_734 None p)))
in (

let arg_binder = if (not (refine_domain)) then begin
(let _156_736 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder _156_736))
end else begin
(

let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p)) arg_typ)
in (let _156_745 = (

let _64_1894 = (projectee arg_typ)
in (let _156_744 = (let _156_743 = (let _156_742 = (let _156_741 = (let _156_737 = (FStar_Ident.set_lid_range disc_name p)
in (FStar_Syntax_Syntax.fvar _156_737 FStar_Syntax_Syntax.Delta_equational None))
in (let _156_740 = (let _156_739 = (let _156_738 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _156_738))
in (_156_739)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _156_741 _156_740 None p)))
in (FStar_Syntax_Util.b2t _156_742))
in (FStar_Syntax_Util.refine x _156_743))
in {FStar_Syntax_Syntax.ppname = _64_1894.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_1894.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _156_744}))
in (FStar_Syntax_Syntax.mk_binder _156_745))))
end
in ((arg_binder), (indices))))))
end))
in (match (_64_1899) with
| (arg_binder, indices) -> begin
(

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder))
in (

let imp_binders = (let _156_747 = (FStar_All.pipe_right indices (FStar_List.map (fun _64_1904 -> (match (_64_1904) with
| (x, _64_1903) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (FStar_List.append imp_tps _156_747))
in (

let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (

let arg = (FStar_Syntax_Util.arg_of_non_null_binder arg_binder)
in (

let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _64_1912 -> (match (_64_1912) with
| (a, _64_1911) -> begin
(

let _64_1916 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (_64_1916) with
| (field_name, _64_1915) -> begin
(

let proj = (let _156_751 = (let _156_750 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.fv_to_tm _156_750))
in (FStar_Syntax_Syntax.mk_Tm_app _156_751 ((arg)::[]) None p))
in FStar_Syntax_Syntax.NT (((a), (proj))))
end))
end))))
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (FStar_List.append imp_tps fields)
in (let _156_787 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _64_1925 -> (match (_64_1925) with
| (x, _64_1924) -> begin
(

let _64_1929 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_64_1929) with
| (field_name, _64_1928) -> begin
(

let t = (let _156_755 = (let _156_754 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total _156_754))
in (FStar_Syntax_Util.arrow binders _156_755))
in (

let only_decl = (((let _156_756 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _156_756)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _156_758 = (let _156_757 = (FStar_Parser_Env.current_module env)
in _156_757.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _156_758)))
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

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _64_1941 -> (match (_64_1941) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in if ((i + ntps) = j) then begin
(let _156_763 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in ((_156_763), (b)))
end else begin
if (b && (j < ntps)) then begin
(let _156_767 = (let _156_766 = (let _156_765 = (let _156_764 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in ((_156_764), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (_156_765))
in (pos _156_766))
in ((_156_767), (b)))
end else begin
(let _156_770 = (let _156_769 = (let _156_768 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_156_768))
in (pos _156_769))
in ((_156_770), (b)))
end
end)
end))))
in (

let pat = (let _156_775 = (let _156_773 = (let _156_772 = (let _156_771 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in ((_156_771), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (_156_772))
in (FStar_All.pipe_right _156_773 pos))
in (let _156_774 = (FStar_Syntax_Syntax.bv_to_name projection)
in ((_156_775), (None), (_156_774))))
in (

let body = (let _156_779 = (let _156_778 = (let _156_777 = (let _156_776 = (FStar_Syntax_Util.branch pat)
in (_156_776)::[])
in ((arg_exp), (_156_777)))
in FStar_Syntax_Syntax.Tm_match (_156_778))
in (FStar_Syntax_Syntax.mk _156_779 None p))
in (

let imp = (no_annot_abs binders body)
in (

let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end else begin
FStar_Syntax_Syntax.Delta_equational
end
in (

let lb = (let _156_781 = (let _156_780 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (_156_780))
in {FStar_Syntax_Syntax.lbname = _156_781; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = imp})
in (

let impl = (let _156_786 = (let _156_785 = (let _156_784 = (let _156_783 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _156_783 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_156_784)::[])
in ((((false), ((lb)::[]))), (p), (_156_785), (quals)))
in FStar_Syntax_Syntax.Sig_let (_156_786))
in if no_decl then begin
(impl)::[]
end else begin
(decl)::(impl)::[]
end))))))))
end))))))
end))
end))))
in (FStar_All.pipe_right _156_787 FStar_List.flatten)))))))))
end)))))))


let mk_data_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env _64_1955 -> (match (_64_1955) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _64_1958, t, l, n, quals, _64_1964, _64_1966) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _64_10 -> (match (_64_10) with
| FStar_Syntax_Syntax.RecordConstructor (_64_1971) -> begin
true
end
| _64_1974 -> begin
false
end)))) then begin
false
end else begin
(match ((FStar_Parser_Env.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > 1)
end
| _64_1978 -> begin
true
end)
end
in (

let _64_1982 = (FStar_Syntax_Util.arrow_formals t)
in (match (_64_1982) with
| (formals, cod) -> begin
(match (formals) with
| [] -> begin
[]
end
| _64_1985 -> begin
(

let fv_qual = (match ((FStar_Util.find_map quals (fun _64_11 -> (match (_64_11) with
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| _64_1990 -> begin
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

let _64_1998 = (FStar_Util.first_N n formals)
in (match (_64_1998) with
| (tps, rest) -> begin
(mk_indexed_projectors iquals fv_qual refine_domain env l lid inductive_tps tps rest cod)
end))))
end)
end)))
end
| _64_2000 -> begin
[]
end)
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (

let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _156_812 = (FStar_Syntax_Util.incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (_156_812))
end else begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end
in (

let lb = (let _156_817 = (let _156_813 = (FStar_Syntax_Syntax.lid_as_fv lid dd None)
in FStar_Util.Inr (_156_813))
in (let _156_816 = (let _156_814 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars _156_814))
in (let _156_815 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = _156_817; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = _156_816; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _156_815})))
in FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (rng), (lids), (quals))))))


let rec desugar_tycon : FStar_Parser_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (

let tycon_id = (fun _64_12 -> (match (_64_12) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _156_831 = (let _156_830 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_156_830))
in (FStar_Parser_AST.mk_term _156_831 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
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
| _64_2075 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _156_844 = (let _156_843 = (let _156_842 = (binder_to_term b)
in ((out), (_156_842), ((imp_of_aqual b))))
in FStar_Parser_AST.App (_156_843))
in (FStar_Parser_AST.mk_term _156_844 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun _64_13 -> (match (_64_13) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun _64_2088 -> (match (_64_2088) with
| (x, t) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Syntax_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (

let result = (let _156_850 = (let _156_849 = (let _156_848 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_156_848))
in (FStar_Parser_AST.mk_term _156_849 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _156_850 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _156_852 = (FStar_All.pipe_right fields (FStar_List.map (fun _64_2095 -> (match (_64_2095) with
| (x, _64_2094) -> begin
(FStar_Parser_Env.qualify env x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (Some (constrTyp)), (false)))::[])))), (_156_852)))))))
end
| _64_2097 -> begin
(FStar_All.failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals _env mutuals _64_14 -> (match (_64_14) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let _64_2111 = (typars_of_binders _env binders)
in (match (_64_2111) with
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

let tconstr = (let _156_863 = (let _156_862 = (let _156_861 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_156_861))
in (FStar_Parser_AST.mk_term _156_862 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _156_863 binders))
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
| _64_2124 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env bs -> (

let _64_2139 = (FStar_List.fold_left (fun _64_2130 _64_2133 -> (match (((_64_2130), (_64_2133))) with
| ((env, tps), (x, imp)) -> begin
(

let _64_2136 = (FStar_Parser_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (_64_2136) with
| (env, y) -> begin
((env), ((((y), (imp)))::tps))
end))
end)) ((env), ([])) bs)
in (match (_64_2139) with
| (env, bs) -> begin
((env), ((FStar_List.rev bs)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id, bs, kopt))::[] -> begin
(

let kopt = (match (kopt) with
| None -> begin
(let _156_870 = (tm_type_z id.FStar_Ident.idRange)
in Some (_156_870))
end
| _64_2148 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id), (bs), (kopt)))
in (

let _64_2158 = (desugar_abstract_tc quals env [] tc)
in (match (_64_2158) with
| (_64_2152, _64_2154, se, _64_2157) -> begin
(

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _64_2161, typars, k, [], [], quals, rng) -> begin
(

let quals = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
quals
end else begin
(

let _64_2170 = (let _156_872 = (FStar_Range.string_of_range rng)
in (let _156_871 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" _156_872 _156_871)))
in (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals)
end
in (

let t = (match (typars) with
| [] -> begin
k
end
| _64_2175 -> begin
(let _156_875 = (let _156_874 = (let _156_873 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (_156_873)))
in FStar_Syntax_Syntax.Tm_arrow (_156_874))
in (FStar_Syntax_Syntax.mk _156_875 None rng))
end)
in FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t), (quals), (rng)))))
end
| _64_2178 -> begin
se
end)
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in ((env), ((se)::[]))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let _64_2190 = (typars_of_binders env binders)
in (match (_64_2190) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _64_15 -> (match (_64_15) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| _64_2195 -> begin
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

let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _64_16 -> (match (_64_16) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| _64_2203 -> begin
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
in (let _156_881 = (let _156_880 = (FStar_Parser_Env.qualify env id)
in (let _156_879 = (FStar_All.pipe_right quals (FStar_List.filter (fun _64_17 -> (match (_64_17) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| _64_2211 -> begin
true
end))))
in ((_156_880), ([]), (typars), (c), (_156_879), (rng))))
in FStar_Syntax_Syntax.Sig_effect_abbrev (_156_881)))))
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
| (FStar_Parser_AST.TyconRecord (_64_2217))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let _64_2223 = (tycon_record_as_variant trec)
in (match (_64_2223) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| (_64_2227)::_64_2225 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_Env.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals et tc -> (

let _64_2238 = et
in (match (_64_2238) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_64_2240) -> begin
(

let trec = tc
in (

let _64_2245 = (tycon_record_as_variant trec)
in (match (_64_2245) with
| (t, fs) -> begin
(collect_tcs ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((env), (tcs)) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let _64_2257 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_64_2257) with
| (env, _64_2254, se, tconstr) -> begin
((env), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals))))::tcs))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let _64_2269 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_64_2269) with
| (env, _64_2266, se, tconstr) -> begin
((env), ((FStar_Util.Inr (((se), (t), (quals))))::tcs))
end))
end
| _64_2271 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (

let _64_2274 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (_64_2274) with
| (env, tcs) -> begin
(

let tcs = (FStar_List.rev tcs)
in (

let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _64_19 -> (match (_64_19) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, _64_2282, _64_2284, _64_2286, _64_2288), t, quals) -> begin
(

let _64_2298 = (push_tparams env tpars)
in (match (_64_2298) with
| (env_tps, _64_2297) -> begin
(

let t = (desugar_term env_tps t)
in (let _156_891 = (let _156_890 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in (([]), (_156_890)))
in (_156_891)::[]))
end))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, _64_2306, tags, _64_2309), constrs, tconstr, quals) -> begin
(

let tycon = ((tname), (tpars), (k))
in (

let _64_2320 = (push_tparams env tpars)
in (match (_64_2320) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun _64_2324 -> (match (_64_2324) with
| (x, _64_2323) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let _64_2348 = (let _156_903 = (FStar_All.pipe_right constrs (FStar_List.map (fun _64_2329 -> (match (_64_2329) with
| (id, topt, of_notation) -> begin
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

let t = (let _156_895 = (FStar_Parser_Env.default_total env_tps)
in (let _156_894 = (close env_tps t)
in (desugar_term _156_895 _156_894)))
in (

let name = (FStar_Parser_Env.qualify env id)
in (

let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _64_18 -> (match (_64_18) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| _64_2343 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (let _156_902 = (let _156_901 = (let _156_900 = (let _156_899 = (let _156_898 = (let _156_897 = (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total _156_897))
in (FStar_Syntax_Util.arrow data_tpars _156_898))
in ((name), (univs), (_156_899), (tname), (ntps), (quals), (mutuals), (rng)))
in FStar_Syntax_Syntax.Sig_datacon (_156_900))
in ((tps), (_156_901)))
in ((name), (_156_902))))))))
end))))
in (FStar_All.pipe_left FStar_List.split _156_903))
in (match (_64_2348) with
| (constrNames, constrs) -> begin
((([]), (FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs), (tpars), (k), (mutuals), (constrNames), (tags), (rng))))))::constrs
end)))
end)))
end
| _64_2350 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (

let bundle = (let _156_905 = (let _156_904 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in ((sigelts), (quals), (_156_904), (rng)))
in FStar_Syntax_Syntax.Sig_bundle (_156_905))
in (

let env = (FStar_Parser_Env.push_sigelt env0 bundle)
in (

let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projectors quals env)))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _64_20 -> (match (_64_20) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, _64_2359, tps, k, _64_2363, constrs, quals, _64_2367) when ((FStar_List.length constrs) > 1) -> begin
(

let quals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract quals) then begin
(FStar_Syntax_Syntax.Private)::quals
end else begin
quals
end
in (mk_data_discriminators quals env tname tps k constrs))
end
| _64_2372 -> begin
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

let _64_2396 = (FStar_List.fold_left (fun _64_2381 b -> (match (_64_2381) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| (Some (a), k) -> begin
(

let _64_2389 = (FStar_Parser_Env.push_bv env a)
in (match (_64_2389) with
| (env, a) -> begin
(let _156_914 = (let _156_913 = (FStar_Syntax_Syntax.mk_binder (

let _64_2390 = a
in {FStar_Syntax_Syntax.ppname = _64_2390.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_2390.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (_156_913)::binders)
in ((env), (_156_914)))
end))
end
| _64_2393 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end)
end)) ((env), ([])) binders)
in (match (_64_2396) with
| (env, binders) -> begin
((env), ((FStar_List.rev binders)))
end)))


let rec desugar_effect : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (Prims.string  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term))  ->  FStar_Syntax_Syntax.action Prims.list  ->  FStar_Syntax_Syntax.sigelt)  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_kind eff_decls actions mk -> (

let env0 = env
in (

let monad_env = (FStar_Parser_Env.enter_monad_scope env eff_name)
in (

let _64_2410 = (desugar_binders monad_env eff_binders)
in (match (_64_2410) with
| (env, binders) -> begin
(

let eff_k = (let _156_973 = (FStar_Parser_Env.default_total env)
in (desugar_term _156_973 eff_kind))
in (

let _64_2421 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _64_2414 decl -> (match (_64_2414) with
| (env, out) -> begin
(

let _64_2418 = (desugar_decl env decl)
in (match (_64_2418) with
| (env, ses) -> begin
(let _156_977 = (let _156_976 = (FStar_List.hd ses)
in (_156_976)::out)
in ((env), (_156_977)))
end))
end)) ((env), ([]))))
in (match (_64_2421) with
| (env, decls) -> begin
(

let actions = (FStar_All.pipe_right actions (FStar_List.collect (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (_64_2424, (FStar_Parser_AST.TyconAbbrev (name, _64_2427, _64_2429, defn))::[]) -> begin
(

let a = (let _156_980 = (FStar_Parser_Env.qualify env name)
in (let _156_979 = (desugar_term env defn)
in {FStar_Syntax_Syntax.action_name = _156_980; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = _156_979; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
in (a)::[])
end
| _64_2438 -> begin
[]
end))))
in (

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (

let lookup = (fun s -> (

let l = (FStar_Parser_Env.qualify env (FStar_Ident.mk_ident ((s), (d.FStar_Parser_AST.drange))))
in (let _156_984 = (let _156_983 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) _156_983))
in (([]), (_156_984)))))
in (

let mname = (FStar_Parser_Env.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange) quals)
in (

let se = (mk mname qualifiers binders eff_k lookup actions)
in (

let env = (FStar_Parser_Env.push_sigelt env0 se)
in (

let env = (FStar_All.pipe_right actions (FStar_List.fold_left (fun env a -> (let _156_987 = (FStar_Syntax_Util.action_as_lb a)
in (FStar_Parser_Env.push_sigelt env _156_987))) env))
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
| FStar_Parser_AST.TopLevelModule (_64_2462) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Multiple modules in a file are no longer supported"), (d.FStar_Parser_AST.drange)))))
end
| FStar_Parser_AST.Open (lid) -> begin
(

let env = (FStar_Parser_Env.push_namespace env lid)
in ((env), ([])))
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(let _156_991 = (FStar_Parser_Env.push_module_abbrev env x l)
in ((_156_991), ([])))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(let _156_992 = (FStar_List.map trans_qual qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _156_992 tcs))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _156_994 = (let _156_993 = (desugar_term_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Syntax_Subst.compress _156_993))
in _156_994.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let (lbs, _64_2482) -> begin
(

let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals = (match (quals) with
| (_64_2490)::_64_2488 -> begin
(FStar_List.map trans_qual quals)
end
| _64_2493 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _64_21 -> (match (_64_21) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (_64_2504); FStar_Syntax_Syntax.lbunivs = _64_2502; FStar_Syntax_Syntax.lbtyp = _64_2500; FStar_Syntax_Syntax.lbeff = _64_2498; FStar_Syntax_Syntax.lbdef = _64_2496} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _64_2514; FStar_Syntax_Syntax.lbtyp = _64_2512; FStar_Syntax_Syntax.lbeff = _64_2510; FStar_Syntax_Syntax.lbdef = _64_2508} -> begin
(FStar_Parser_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals = if (FStar_All.pipe_right lets (FStar_Util.for_some (fun _64_2522 -> (match (_64_2522) with
| (_64_2520, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end)))) then begin
(FStar_Syntax_Syntax.Logic)::quals
end else begin
quals
end
in (

let lbs = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _156_999 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _64_2526 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let _64_2528 = fv
in {FStar_Syntax_Syntax.fv_name = _64_2528.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = _64_2528.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = _64_2526.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _64_2526.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _64_2526.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _64_2526.FStar_Syntax_Syntax.lbdef})))))
in (((Prims.fst lbs)), (_156_999)))
end else begin
lbs
end
in (

let s = (let _156_1002 = (let _156_1001 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in ((lbs), (d.FStar_Parser_AST.drange), (_156_1001), (quals)))
in FStar_Syntax_Syntax.Sig_let (_156_1002))
in (

let env = (FStar_Parser_Env.push_sigelt env s)
in ((env), ((s)::[]))))))))
end
| _64_2535 -> begin
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
in (let _156_1006 = (let _156_1005 = (let _156_1004 = (let _156_1003 = (FStar_Parser_Env.qualify env id)
in ((_156_1003), (f), ((FStar_Syntax_Syntax.Assumption)::[]), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_assume (_156_1004))
in (_156_1005)::[])
in ((env), (_156_1006))))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(

let t = (let _156_1007 = (close_fun env t)
in (desugar_term env _156_1007))
in (

let quals = if (env.FStar_Parser_Env.iface && env.FStar_Parser_Env.admitted_iface) then begin
(FStar_Parser_AST.Assumption)::quals
end else begin
quals
end
in (

let se = (let _156_1010 = (let _156_1009 = (FStar_Parser_Env.qualify env id)
in (let _156_1008 = (FStar_List.map trans_qual quals)
in ((_156_1009), ([]), (t), (_156_1008), (d.FStar_Parser_AST.drange))))
in FStar_Syntax_Syntax.Sig_declare_typ (_156_1010))
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in ((env), ((se)::[]))))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(

let _64_2562 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (match (_64_2562) with
| (t, _64_2561) -> begin
(

let l = (FStar_Parser_Env.qualify env id)
in (

let se = FStar_Syntax_Syntax.Sig_datacon (((l), ([]), (t), (FStar_Syntax_Const.exn_lid), (0), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((FStar_Syntax_Const.exn_lid)::[]), (d.FStar_Parser_AST.drange)))
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

let t = (let _156_1015 = (let _156_1011 = (FStar_Syntax_Syntax.null_binder t)
in (_156_1011)::[])
in (let _156_1014 = (let _156_1013 = (let _156_1012 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (Prims.fst _156_1012))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _156_1013))
in (FStar_Syntax_Util.arrow _156_1015 _156_1014)))
in (

let l = (FStar_Parser_Env.qualify env id)
in (

let se = FStar_Syntax_Syntax.Sig_datacon (((l), ([]), (t), (FStar_Syntax_Const.exn_lid), (0), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((FStar_Syntax_Const.exn_lid)::[]), (d.FStar_Parser_AST.drange)))
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

let _64_2591 = (desugar_binders env binders)
in (match (_64_2591) with
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

let _64_2607 = (desugar_binders env eff_binders)
in (match (_64_2607) with
| (env, binders) -> begin
(

let _64_2618 = (

let _64_2610 = (head_and_args defn)
in (match (_64_2610) with
| (head, args) -> begin
(

let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_defn env) l)
end
| _64_2614 -> begin
(let _156_1020 = (let _156_1019 = (let _156_1018 = (let _156_1017 = (let _156_1016 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat "Effect " _156_1016))
in (Prims.strcat _156_1017 " not found"))
in ((_156_1018), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_156_1019))
in (Prims.raise _156_1020))
end)
in (let _156_1021 = (desugar_args env args)
in ((ed), (_156_1021))))
end))
in (match (_64_2618) with
| (ed, args) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let sub = (fun _64_2624 -> (match (_64_2624) with
| (_64_2622, x) -> begin
(

let _64_2627 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (_64_2627) with
| (edb, x) -> begin
(

let _64_2628 = if ((FStar_List.length args) <> (FStar_List.length edb)) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected number of arguments to effect constructor"), (defn.FStar_Parser_AST.range)))))
end else begin
()
end
in (

let s = (FStar_Syntax_Util.subst_of_list edb args)
in (let _156_1025 = (let _156_1024 = (FStar_Syntax_Subst.subst s x)
in (FStar_Syntax_Subst.close binders _156_1024))
in (([]), (_156_1025)))))
end))
end))
in (

let ed = (let _156_1039 = (FStar_List.map trans_qual quals)
in (let _156_1038 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _156_1037 = (let _156_1026 = (sub (([]), (ed.FStar_Syntax_Syntax.signature)))
in (Prims.snd _156_1026))
in (let _156_1036 = (sub ed.FStar_Syntax_Syntax.ret_wp)
in (let _156_1035 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (let _156_1034 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (let _156_1033 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (let _156_1032 = (sub ed.FStar_Syntax_Syntax.stronger)
in (let _156_1031 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (let _156_1030 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (let _156_1029 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (let _156_1028 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (let _156_1027 = (sub ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _156_1039; FStar_Syntax_Syntax.mname = _156_1038; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = _156_1037; FStar_Syntax_Syntax.ret_wp = _156_1036; FStar_Syntax_Syntax.bind_wp = _156_1035; FStar_Syntax_Syntax.if_then_else = _156_1034; FStar_Syntax_Syntax.ite_wp = _156_1033; FStar_Syntax_Syntax.stronger = _156_1032; FStar_Syntax_Syntax.close_wp = _156_1031; FStar_Syntax_Syntax.assert_p = _156_1030; FStar_Syntax_Syntax.assume_p = _156_1029; FStar_Syntax_Syntax.null_wp = _156_1028; FStar_Syntax_Syntax.trivial = _156_1027; FStar_Syntax_Syntax.repr = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.return_repr = (([]), (FStar_Syntax_Syntax.tun)); FStar_Syntax_Syntax.bind_repr = (([]), (FStar_Syntax_Syntax.tun)); FStar_Syntax_Syntax.actions = []})))))))))))))
in (

let se = FStar_Syntax_Syntax.Sig_new_effect (((ed), (d.FStar_Parser_AST.drange)))
in (

let env = (FStar_Parser_Env.push_sigelt env0 se)
in ((env), ((se)::[])))))))
end))
end)))
end
| FStar_Parser_AST.NewEffectForFree (_64_2635, FStar_Parser_AST.RedefineEffect (_64_2637)) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.NewEffectForFree (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls, actions)) -> begin
(desugar_effect env d quals eff_name eff_binders eff_kind eff_decls actions (fun mname qualifiers binders eff_k lookup actions -> (

let dummy_tscheme = (let _156_1050 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (([]), (_156_1050)))
in (let _156_1059 = (let _156_1058 = (let _156_1057 = (lookup "ite_wp")
in (let _156_1056 = (lookup "stronger")
in (let _156_1055 = (lookup "null_wp")
in (let _156_1054 = (let _156_1051 = (lookup "repr")
in (Prims.snd _156_1051))
in (let _156_1053 = (lookup "return")
in (let _156_1052 = (lookup "bind")
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = _156_1057; FStar_Syntax_Syntax.stronger = _156_1056; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = _156_1055; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = _156_1054; FStar_Syntax_Syntax.return_repr = _156_1053; FStar_Syntax_Syntax.bind_repr = _156_1052; FStar_Syntax_Syntax.actions = actions}))))))
in ((_156_1058), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (_156_1059)))))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls, actions)) -> begin
(desugar_effect env d quals eff_name eff_binders eff_kind eff_decls actions (fun mname qualifiers binders eff_k lookup actions -> (

let rr = ((FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) || (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable)))
in (

let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in (let _156_1085 = (let _156_1084 = (let _156_1083 = (lookup "return_wp")
in (let _156_1082 = (lookup "bind_wp")
in (let _156_1081 = (lookup "if_then_else")
in (let _156_1080 = (lookup "ite_wp")
in (let _156_1079 = (lookup "stronger")
in (let _156_1078 = (lookup "close_wp")
in (let _156_1077 = (lookup "assert_p")
in (let _156_1076 = (lookup "assume_p")
in (let _156_1075 = (lookup "null_wp")
in (let _156_1074 = (lookup "trivial")
in (let _156_1073 = if rr then begin
(let _156_1070 = (lookup "repr")
in (FStar_All.pipe_left Prims.snd _156_1070))
end else begin
FStar_Syntax_Syntax.tun
end
in (let _156_1072 = if rr then begin
(lookup "return")
end else begin
un_ts
end
in (let _156_1071 = if rr then begin
(lookup "bind")
end else begin
un_ts
end
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = _156_1083; FStar_Syntax_Syntax.bind_wp = _156_1082; FStar_Syntax_Syntax.if_then_else = _156_1081; FStar_Syntax_Syntax.ite_wp = _156_1080; FStar_Syntax_Syntax.stronger = _156_1079; FStar_Syntax_Syntax.close_wp = _156_1078; FStar_Syntax_Syntax.assert_p = _156_1077; FStar_Syntax_Syntax.assume_p = _156_1076; FStar_Syntax_Syntax.null_wp = _156_1075; FStar_Syntax_Syntax.trivial = _156_1074; FStar_Syntax_Syntax.repr = _156_1073; FStar_Syntax_Syntax.return_repr = _156_1072; FStar_Syntax_Syntax.bind_repr = _156_1071; FStar_Syntax_Syntax.actions = actions})))))))))))))
in ((_156_1084), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_new_effect (_156_1085))))))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(

let lookup = (fun l -> (match ((FStar_Parser_Env.try_lookup_effect_name env l)) with
| None -> begin
(let _156_1092 = (let _156_1091 = (let _156_1090 = (let _156_1089 = (let _156_1088 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat "Effect name " _156_1088))
in (Prims.strcat _156_1089 " not found"))
in ((_156_1090), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_156_1091))
in (Prims.raise _156_1092))
end
| Some (l) -> begin
l
end))
in (

let src = (lookup l.FStar_Parser_AST.msource)
in (

let dst = (lookup l.FStar_Parser_AST.mdest)
in (

let _64_2693 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(let _156_1094 = (let _156_1093 = (desugar_term env t)
in (([]), (_156_1093)))
in ((_156_1094), (None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(let _156_1099 = (let _156_1095 = (desugar_term env wp)
in (([]), (_156_1095)))
in (let _156_1098 = (let _156_1097 = (let _156_1096 = (desugar_term env t)
in (([]), (_156_1096)))
in Some (_156_1097))
in ((_156_1099), (_156_1098))))
end)
in (match (_64_2693) with
| (lift_wp, lift) -> begin
(

let se = FStar_Syntax_Syntax.Sig_sub_effect ((({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift}), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[])))
end)))))
end)))


let desugar_decls : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _64_2699 d -> (match (_64_2699) with
| (env, sigelts) -> begin
(

let _64_2703 = (desugar_decl env d)
in (match (_64_2703) with
| (env, se) -> begin
((env), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls))


let open_prims_all : FStar_Parser_AST.decl Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.all_lid)) FStar_Range.dummyRange))::[]


let desugar_modul_common : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod) -> begin
(FStar_Parser_Env.finish_module_or_interface env prev_mod)
end)
in (

let _64_2726 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _156_1112 = (FStar_Parser_Env.prepare_module_or_interface true admitted env mname)
in ((_156_1112), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _156_1113 = (FStar_Parser_Env.prepare_module_or_interface false false env mname)
in ((_156_1113), (mname), (decls), (false)))
end)
in (match (_64_2726) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(

let _64_2729 = (desugar_decls env decls)
in (match (_64_2729) with
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
| FStar_Parser_AST.Interface (mname, _64_2740, _64_2742) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (

let _64_2750 = (desugar_modul_common curmod env m)
in (match (_64_2750) with
| (x, y, _64_2749) -> begin
((x), (y))
end))))


let desugar_modul : FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (

let _64_2756 = (desugar_modul_common None env m)
in (match (_64_2756) with
| (env, modul, pop_when_done) -> begin
(

let env = (FStar_Parser_Env.finish_module_or_interface env modul)
in (

let _64_2758 = if (FStar_Options.dump_module modul.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _156_1124 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _156_1124))
end else begin
()
end
in (let _156_1125 = if pop_when_done then begin
(FStar_Parser_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end else begin
env
end
in ((_156_1125), (modul)))))
end)))


let desugar_file : FStar_Parser_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (

let _64_2771 = (FStar_List.fold_left (fun _64_2764 m -> (match (_64_2764) with
| (env, mods) -> begin
(

let _64_2768 = (desugar_modul env m)
in (match (_64_2768) with
| (env, m) -> begin
((env), ((m)::mods))
end))
end)) ((env), ([])) f)
in (match (_64_2771) with
| (env, mods) -> begin
((env), ((FStar_List.rev mods)))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Parser_Env.env  ->  FStar_Parser_Env.env = (fun m en -> (

let _64_2776 = (FStar_Parser_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (_64_2776) with
| (en, pop_when_done) -> begin
(

let en = (FStar_List.fold_left FStar_Parser_Env.push_sigelt (

let _64_2777 = en
in {FStar_Parser_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_Parser_Env.modules = _64_2777.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _64_2777.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _64_2777.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _64_2777.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _64_2777.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _64_2777.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _64_2777.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _64_2777.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _64_2777.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _64_2777.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = _64_2777.FStar_Parser_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (

let env = (FStar_Parser_Env.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_Env.export_interface m.FStar_Syntax_Syntax.name env)
end else begin
env
end))
end)))




