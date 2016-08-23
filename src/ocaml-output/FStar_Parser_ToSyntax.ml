
open Prims
# 38 "FStar.Parser.ToSyntax.fst"
let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _64_1 -> (match (_64_1) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Syntax_Syntax.Equality)
end
| _64_29 -> begin
None
end))

# 43 "FStar.Parser.ToSyntax.fst"
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
# 56 "FStar.Parser.ToSyntax.fst"
let _64_43 = (FStar_TypeChecker_Errors.warn r "The \'opaque\' qualifier is deprecated since its use was strangely schizophrenic. There were two overloaded uses: (1) Given \'opaque val f : t\', the behavior was to exclude the definition of \'f\' to the SMT solver. This corresponds roughly to the new \'irreducible\' qualifier. (2) Given \'opaque type t = t\'\', the behavior was to provide the definition of \'t\' to the SMT solver, but not to inline it, unless absolutely required for unification. This corresponds roughly to the behavior of \'unfoldable\' (which is currently the default).")
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

# 61 "FStar.Parser.ToSyntax.fst"
let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun _64_3 -> (match (_64_3) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end))

# 65 "FStar.Parser.ToSyntax.fst"
let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _64_4 -> (match (_64_4) with
| FStar_Parser_AST.Hash -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| _64_58 -> begin
None
end))

# 69 "FStar.Parser.ToSyntax.fst"
let arg_withimp_e = (fun imp t -> ((t), ((as_imp imp))))

# 71 "FStar.Parser.ToSyntax.fst"
let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
((t), (Some (FStar_Syntax_Syntax.imp_tag)))
end
| _64_65 -> begin
((t), (None))
end))

# 75 "FStar.Parser.ToSyntax.fst"
let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_64_69) -> begin
true
end
| _64_72 -> begin
false
end)))))

# 80 "FStar.Parser.ToSyntax.fst"
let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _64_77 -> begin
t
end))

# 84 "FStar.Parser.ToSyntax.fst"
let tm_type_z : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _157_23 = (let _157_22 = (FStar_Ident.lid_of_path (("Type0")::[]) r)
in FStar_Parser_AST.Name (_157_22))
in (FStar_Parser_AST.mk_term _157_23 r FStar_Parser_AST.Kind)))

# 86 "FStar.Parser.ToSyntax.fst"
let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _157_27 = (let _157_26 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_157_26))
in (FStar_Parser_AST.mk_term _157_27 r FStar_Parser_AST.Kind)))

# 87 "FStar.Parser.ToSyntax.fst"
let compile_op : Prims.int  ->  Prims.string  ->  Prims.string = (fun arity s -> (
# 90 "FStar.Parser.ToSyntax.fst"
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
| _64_101 -> begin
"UNKNOWN"
end))
in (
# 109 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _157_38 = (let _157_36 = (FStar_Util.char_at s i)
in (name_of_char _157_36))
in (let _157_37 = (aux (i + 1))
in (_157_38)::_157_37))
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
| _64_110 -> begin
(let _157_40 = (let _157_39 = (aux 0)
in (FStar_String.concat "_" _157_39))
in (Prims.strcat "op_" _157_40))
end))))

# 118 "FStar.Parser.ToSyntax.fst"
let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _157_50 = (let _157_49 = (let _157_48 = (let _157_47 = (compile_op n s)
in ((_157_47), (r)))
in (FStar_Ident.mk_ident _157_48))
in (_157_49)::[])
in (FStar_All.pipe_right _157_50 FStar_Ident.lid_of_ids)))

# 120 "FStar.Parser.ToSyntax.fst"
let op_as_term : FStar_Parser_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.term Prims.option = (fun env arity rng s -> (
# 123 "FStar.Parser.ToSyntax.fst"
let r = (fun l dd -> (let _157_65 = (let _157_64 = (let _157_63 = (FStar_Ident.set_lid_range l rng)
in (FStar_Syntax_Syntax.lid_as_fv _157_63 dd None))
in (FStar_All.pipe_right _157_64 FStar_Syntax_Syntax.fv_to_tm))
in Some (_157_65)))
in (
# 124 "FStar.Parser.ToSyntax.fst"
let fallback = (fun _64_122 -> (match (()) with
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
| _64_150 -> begin
None
end)
end))
in (match ((let _157_68 = (compile_op_lid arity s rng)
in (FStar_Parser_Env.try_lookup_lid env _157_68))) with
| Some (t) -> begin
Some ((Prims.fst t))
end
| _64_154 -> begin
(fallback ())
end))))

# 156 "FStar.Parser.ToSyntax.fst"
let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _157_75 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _157_75)))

# 160 "FStar.Parser.ToSyntax.fst"
let rec free_type_vars_b : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_64_163) -> begin
((env), ([]))
end
| FStar_Parser_AST.TVariable (x) -> begin
(
# 165 "FStar.Parser.ToSyntax.fst"
let _64_170 = (FStar_Parser_Env.push_bv env x)
in (match (_64_170) with
| (env, _64_169) -> begin
((env), ((x)::[]))
end))
end
| FStar_Parser_AST.Annotated (_64_172, term) -> begin
(let _157_82 = (free_type_vars env term)
in ((env), (_157_82)))
end
| FStar_Parser_AST.TAnnotated (id, _64_178) -> begin
(
# 170 "FStar.Parser.ToSyntax.fst"
let _64_184 = (FStar_Parser_Env.push_bv env id)
in (match (_64_184) with
| (env, _64_183) -> begin
((env), ([]))
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _157_83 = (free_type_vars env t)
in ((env), (_157_83)))
end))
and free_type_vars : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _157_86 = (unparen t)
in _157_86.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (_64_190) -> begin
(FStar_All.failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_Env.try_lookup_id env a)) with
| None -> begin
(a)::[]
end
| _64_196 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Assign (_, t)) | (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_64_230, ts) -> begin
(FStar_List.collect (fun _64_237 -> (match (_64_237) with
| (t, _64_236) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_64_239, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _64_246) -> begin
(let _157_89 = (free_type_vars env t1)
in (let _157_88 = (free_type_vars env t2)
in (FStar_List.append _157_89 _157_88)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(
# 201 "FStar.Parser.ToSyntax.fst"
let _64_255 = (free_type_vars_b env b)
in (match (_64_255) with
| (env, f) -> begin
(let _157_90 = (free_type_vars env t)
in (FStar_List.append f _157_90))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(
# 206 "FStar.Parser.ToSyntax.fst"
let _64_271 = (FStar_List.fold_left (fun _64_264 binder -> (match (_64_264) with
| (env, free) -> begin
(
# 207 "FStar.Parser.ToSyntax.fst"
let _64_268 = (free_type_vars_b env binder)
in (match (_64_268) with
| (env, f) -> begin
((env), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (_64_271) with
| (env, free) -> begin
(let _157_93 = (free_type_vars env body)
in (FStar_List.append free _157_93))
end))
end
| FStar_Parser_AST.Project (t, _64_274) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
[]
end))

# 223 "FStar.Parser.ToSyntax.fst"
let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (
# 226 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun args t -> (match ((let _157_100 = (unparen t)
in _157_100.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| _64_321 -> begin
((t), (args))
end))
in (aux [] t)))

# 230 "FStar.Parser.ToSyntax.fst"
let close : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 233 "FStar.Parser.ToSyntax.fst"
let ftv = (let _157_105 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _157_105))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 236 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _157_109 = (let _157_108 = (let _157_107 = (tm_type x.FStar_Ident.idRange)
in ((x), (_157_107)))
in FStar_Parser_AST.TAnnotated (_157_108))
in (FStar_Parser_AST.mk_binder _157_109 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 237 "FStar.Parser.ToSyntax.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))

# 238 "FStar.Parser.ToSyntax.fst"
let close_fun : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 241 "FStar.Parser.ToSyntax.fst"
let ftv = (let _157_114 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _157_114))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 244 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _157_118 = (let _157_117 = (let _157_116 = (tm_type x.FStar_Ident.idRange)
in ((x), (_157_116)))
in FStar_Parser_AST.TAnnotated (_157_117))
in (FStar_Parser_AST.mk_binder _157_118 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 245 "FStar.Parser.ToSyntax.fst"
let t = (match ((let _157_119 = (unparen t)
in _157_119.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_64_334) -> begin
t
end
| _64_337 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end)
in (
# 248 "FStar.Parser.ToSyntax.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result)))
end))

# 249 "FStar.Parser.ToSyntax.fst"
let rec uncurry : FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term) = (fun bs t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (binders, t) -> begin
(uncurry (FStar_List.append bs binders) t)
end
| _64_347 -> begin
((bs), (t))
end))

# 253 "FStar.Parser.ToSyntax.fst"
let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _64_351) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_64_357); FStar_Parser_AST.prange = _64_355}, _64_361) -> begin
true
end
| _64_365 -> begin
false
end))

# 258 "FStar.Parser.ToSyntax.fst"
let rec destruct_app_pattern : FStar_Parser_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 262 "FStar.Parser.ToSyntax.fst"
let _64_377 = (destruct_app_pattern env is_top_level p)
in (match (_64_377) with
| (name, args, _64_376) -> begin
((name), (args), (Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _64_382); FStar_Parser_AST.prange = _64_379}, args) when is_top_level -> begin
(let _157_133 = (let _157_132 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_157_132))
in ((_157_133), (args), (None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _64_393); FStar_Parser_AST.prange = _64_390}, args) -> begin
((FStar_Util.Inl (id)), (args), (None))
end
| _64_401 -> begin
(FStar_All.failwith "Not an app pattern")
end))

# 269 "FStar.Parser.ToSyntax.fst"
type bnd =
| LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * FStar_Syntax_Syntax.term)

# 272 "FStar.Parser.ToSyntax.fst"
let is_LocalBinder = (fun _discr_ -> (match (_discr_) with
| LocalBinder (_) -> begin
true
end
| _ -> begin
false
end))

# 273 "FStar.Parser.ToSyntax.fst"
let is_LetBinder = (fun _discr_ -> (match (_discr_) with
| LetBinder (_) -> begin
true
end
| _ -> begin
false
end))

# 272 "FStar.Parser.ToSyntax.fst"
let ___LocalBinder____0 = (fun projectee -> (match (projectee) with
| LocalBinder (_64_404) -> begin
_64_404
end))

# 273 "FStar.Parser.ToSyntax.fst"
let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_64_407) -> begin
_64_407
end))

# 273 "FStar.Parser.ToSyntax.fst"
let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun _64_6 -> (match (_64_6) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| _64_414 -> begin
(FStar_All.failwith "Impossible")
end))

# 276 "FStar.Parser.ToSyntax.fst"
let as_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_Parser_Env.env) = (fun env imp _64_7 -> (match (_64_7) with
| (None, k) -> begin
(let _157_170 = (FStar_Syntax_Syntax.null_binder k)
in ((_157_170), (env)))
end
| (Some (a), k) -> begin
(
# 280 "FStar.Parser.ToSyntax.fst"
let _64_427 = (FStar_Parser_Env.push_bv env a)
in (match (_64_427) with
| (env, a) -> begin
(((((
# 281 "FStar.Parser.ToSyntax.fst"
let _64_428 = a
in {FStar_Syntax_Syntax.ppname = _64_428.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_428.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), ((trans_aqual imp)))), (env))
end))
end))

# 281 "FStar.Parser.ToSyntax.fst"
type env_t =
FStar_Parser_Env.env

# 283 "FStar.Parser.ToSyntax.fst"
type lenv_t =
FStar_Syntax_Syntax.bv Prims.list

# 284 "FStar.Parser.ToSyntax.fst"
let mk_lb : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.letbinding = (fun _64_433 -> (match (_64_433) with
| (n, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))

# 286 "FStar.Parser.ToSyntax.fst"
let no_annot_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t None))

# 287 "FStar.Parser.ToSyntax.fst"
let mk_ref_read = (fun tm -> (
# 290 "FStar.Parser.ToSyntax.fst"
let tm' = (let _157_183 = (let _157_182 = (let _157_178 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _157_178))
in (let _157_181 = (let _157_180 = (let _157_179 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (_157_179)))
in (_157_180)::[])
in ((_157_182), (_157_181))))
in FStar_Syntax_Syntax.Tm_app (_157_183))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))

# 293 "FStar.Parser.ToSyntax.fst"
let mk_ref_alloc = (fun tm -> (
# 296 "FStar.Parser.ToSyntax.fst"
let tm' = (let _157_190 = (let _157_189 = (let _157_185 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _157_185))
in (let _157_188 = (let _157_187 = (let _157_186 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (_157_186)))
in (_157_187)::[])
in ((_157_189), (_157_188))))
in FStar_Syntax_Syntax.Tm_app (_157_190))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))

# 299 "FStar.Parser.ToSyntax.fst"
let mk_ref_assign = (fun t1 t2 pos -> (
# 302 "FStar.Parser.ToSyntax.fst"
let tm = (let _157_202 = (let _157_201 = (let _157_194 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _157_194))
in (let _157_200 = (let _157_199 = (let _157_195 = (FStar_Syntax_Syntax.as_implicit false)
in ((t1), (_157_195)))
in (let _157_198 = (let _157_197 = (let _157_196 = (FStar_Syntax_Syntax.as_implicit false)
in ((t2), (_157_196)))
in (_157_197)::[])
in (_157_199)::_157_198))
in ((_157_201), (_157_200))))
in FStar_Syntax_Syntax.Tm_app (_157_202))
in (FStar_Syntax_Syntax.mk tm None pos)))

# 305 "FStar.Parser.ToSyntax.fst"
let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun _64_8 -> (match (_64_8) with
| ("repr") | ("post") | ("pre") | ("wp") -> begin
true
end
| _64_450 -> begin
false
end))

# 309 "FStar.Parser.ToSyntax.fst"
let rec desugar_data_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat) = (fun env p is_mut -> (
# 313 "FStar.Parser.ToSyntax.fst"
let check_linear_pattern_variables = (fun p -> (
# 314 "FStar.Parser.ToSyntax.fst"
let rec pat_vars = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_dot_term (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_constant (_)) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (_64_470, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out _64_478 -> (match (_64_478) with
| (p, _64_477) -> begin
(let _157_251 = (pat_vars p)
in (FStar_Util.set_union out _157_251))
end)) FStar_Syntax_Syntax.no_names))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(
# 323 "FStar.Parser.ToSyntax.fst"
let xs = (pat_vars hd)
in if (not ((FStar_Util.for_all (fun p -> (
# 324 "FStar.Parser.ToSyntax.fst"
let ys = (pat_vars p)
in ((FStar_Util.set_is_subset_of xs ys) && (FStar_Util.set_is_subset_of ys xs)))) tl))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Disjunctive pattern binds different variables in each case"), (p.FStar_Syntax_Syntax.p)))))
end else begin
xs
end)
end))
in (pat_vars p)))
in (
# 331 "FStar.Parser.ToSyntax.fst"
let _64_501 = (match (((is_mut), (p.FStar_Parser_AST.pat))) with
| ((false, _)) | ((true, FStar_Parser_AST.PatVar (_))) -> begin
()
end
| (true, _64_499) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("let-mutable is for variables only"), (p.FStar_Parser_AST.prange)))))
end)
in (
# 338 "FStar.Parser.ToSyntax.fst"
let push_bv_maybe_mut = if is_mut then begin
FStar_Parser_Env.push_bv_mutable
end else begin
FStar_Parser_Env.push_bv
end
in (
# 340 "FStar.Parser.ToSyntax.fst"
let resolvex = (fun l e x -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText))))) with
| Some (y) -> begin
((l), (e), (y))
end
| _64_512 -> begin
(
# 344 "FStar.Parser.ToSyntax.fst"
let _64_515 = (push_bv_maybe_mut e x)
in (match (_64_515) with
| (e, x) -> begin
(((x)::l), (e), (x))
end))
end))
in (
# 346 "FStar.Parser.ToSyntax.fst"
let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun b -> (b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText))))) with
| Some (b) -> begin
((l), (e), (b))
end
| _64_524 -> begin
(
# 350 "FStar.Parser.ToSyntax.fst"
let _64_527 = (push_bv_maybe_mut e a)
in (match (_64_527) with
| (e, a) -> begin
(((a)::l), (e), (a))
end))
end))
in (
# 352 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun loc env p -> (
# 353 "FStar.Parser.ToSyntax.fst"
let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Parser_AST.prange))
in (
# 354 "FStar.Parser.ToSyntax.fst"
let pos_r = (fun r q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r))
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (op) -> begin
(let _157_287 = (let _157_286 = (let _157_285 = (let _157_284 = (let _157_283 = (compile_op 0 op)
in (FStar_Ident.id_of_text _157_283))
in ((_157_284), (None)))
in FStar_Parser_AST.PatVar (_157_285))
in {FStar_Parser_AST.pat = _157_286; FStar_Parser_AST.prange = p.FStar_Parser_AST.prange})
in (aux loc env _157_287))
end
| FStar_Parser_AST.PatOr ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.PatOr ((p)::ps) -> begin
(
# 360 "FStar.Parser.ToSyntax.fst"
let _64_551 = (aux loc env p)
in (match (_64_551) with
| (loc, env, var, p, _64_550) -> begin
(
# 361 "FStar.Parser.ToSyntax.fst"
let _64_568 = (FStar_List.fold_left (fun _64_555 p -> (match (_64_555) with
| (loc, env, ps) -> begin
(
# 362 "FStar.Parser.ToSyntax.fst"
let _64_564 = (aux loc env p)
in (match (_64_564) with
| (loc, env, _64_560, p, _64_563) -> begin
((loc), (env), ((p)::ps))
end))
end)) ((loc), (env), ([])) ps)
in (match (_64_568) with
| (loc, env, ps) -> begin
(
# 364 "FStar.Parser.ToSyntax.fst"
let pat = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in ((loc), (env), (var), (pat), (false)))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 368 "FStar.Parser.ToSyntax.fst"
let _64_579 = (aux loc env p)
in (match (_64_579) with
| (loc, env', binder, p, imp) -> begin
(
# 369 "FStar.Parser.ToSyntax.fst"
let binder = (match (binder) with
| LetBinder (_64_581) -> begin
(FStar_All.failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(
# 372 "FStar.Parser.ToSyntax.fst"
let t = (let _157_290 = (close_fun env t)
in (desugar_term env _157_290))
in LocalBinder ((((
# 373 "FStar.Parser.ToSyntax.fst"
let _64_588 = x
in {FStar_Syntax_Syntax.ppname = _64_588.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_588.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (aq))))
end)
in ((loc), (env'), (binder), (p), (imp)))
end))
end
| FStar_Parser_AST.PatWild -> begin
(
# 377 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _157_291 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env), (LocalBinder (((x), (None)))), (_157_291), (false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(
# 381 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _157_292 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env), (LocalBinder (((x), (None)))), (_157_292), (false))))
end
| (FStar_Parser_AST.PatTvar (x, aq)) | (FStar_Parser_AST.PatVar (x, aq)) -> begin
(
# 386 "FStar.Parser.ToSyntax.fst"
let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (
# 387 "FStar.Parser.ToSyntax.fst"
let aq = (trans_aqual aq)
in (
# 388 "FStar.Parser.ToSyntax.fst"
let _64_607 = (resolvex loc env x)
in (match (_64_607) with
| (loc, env, xbv) -> begin
(let _157_293 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc), (env), (LocalBinder (((xbv), (aq)))), (_157_293), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(
# 392 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_datacon env) l)
in (
# 393 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _157_294 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), ([])))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_157_294), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _64_613}, args) -> begin
(
# 397 "FStar.Parser.ToSyntax.fst"
let _64_635 = (FStar_List.fold_right (fun arg _64_624 -> (match (_64_624) with
| (loc, env, args) -> begin
(
# 398 "FStar.Parser.ToSyntax.fst"
let _64_631 = (aux loc env arg)
in (match (_64_631) with
| (loc, env, _64_628, arg, imp) -> begin
((loc), (env), ((((arg), (imp)))::args))
end))
end)) args ((loc), (env), ([])))
in (match (_64_635) with
| (loc, env, args) -> begin
(
# 400 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_datacon env) l)
in (
# 401 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _157_297 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_157_297), (false)))))
end))
end
| FStar_Parser_AST.PatApp (_64_639) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(
# 407 "FStar.Parser.ToSyntax.fst"
let _64_659 = (FStar_List.fold_right (fun pat _64_647 -> (match (_64_647) with
| (loc, env, pats) -> begin
(
# 408 "FStar.Parser.ToSyntax.fst"
let _64_655 = (aux loc env pat)
in (match (_64_655) with
| (loc, env, _64_651, pat, _64_654) -> begin
((loc), (env), ((pat)::pats))
end))
end)) pats ((loc), (env), ([])))
in (match (_64_659) with
| (loc, env, pats) -> begin
(
# 410 "FStar.Parser.ToSyntax.fst"
let pat = (let _157_310 = (let _157_309 = (let _157_305 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _157_305))
in (let _157_308 = (let _157_307 = (let _157_306 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_157_306), ([])))
in FStar_Syntax_Syntax.Pat_cons (_157_307))
in (FStar_All.pipe_left _157_309 _157_308)))
in (FStar_List.fold_right (fun hd tl -> (
# 411 "FStar.Parser.ToSyntax.fst"
let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (let _157_304 = (let _157_303 = (let _157_302 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_157_302), ((((hd), (false)))::(((tl), (false)))::[])))
in FStar_Syntax_Syntax.Pat_cons (_157_303))
in (FStar_All.pipe_left (pos_r r) _157_304)))) pats _157_310))
in (
# 414 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc), (env), (LocalBinder (((x), (None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(
# 418 "FStar.Parser.ToSyntax.fst"
let _64_685 = (FStar_List.fold_left (fun _64_672 p -> (match (_64_672) with
| (loc, env, pats) -> begin
(
# 419 "FStar.Parser.ToSyntax.fst"
let _64_681 = (aux loc env p)
in (match (_64_681) with
| (loc, env, _64_677, pat, _64_680) -> begin
((loc), (env), ((((pat), (false)))::pats))
end))
end)) ((loc), (env), ([])) args)
in (match (_64_685) with
| (loc, env, args) -> begin
(
# 421 "FStar.Parser.ToSyntax.fst"
let args = (FStar_List.rev args)
in (
# 422 "FStar.Parser.ToSyntax.fst"
let l = if dep then begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end else begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end
in (
# 424 "FStar.Parser.ToSyntax.fst"
let _64_691 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) l)
in (match (_64_691) with
| (constr, _64_690) -> begin
(
# 425 "FStar.Parser.ToSyntax.fst"
let l = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| _64_695 -> begin
(FStar_All.failwith "impossible")
end)
in (
# 428 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _157_313 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_157_313), (false)))))
end))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(
# 435 "FStar.Parser.ToSyntax.fst"
let _64_705 = (FStar_List.hd fields)
in (match (_64_705) with
| (f, _64_704) -> begin
(
# 436 "FStar.Parser.ToSyntax.fst"
let _64_709 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_64_709) with
| (record, _64_708) -> begin
(
# 437 "FStar.Parser.ToSyntax.fst"
let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _64_712 -> (match (_64_712) with
| (f, p) -> begin
(let _157_315 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.qualify_field_to_record env record) f)
in ((_157_315), (p)))
end))))
in (
# 439 "FStar.Parser.ToSyntax.fst"
let args = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _64_717 -> (match (_64_717) with
| (f, _64_716) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _64_721 -> (match (_64_721) with
| (g, _64_720) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_64_724, p) -> begin
p
end)
end))))
in (
# 443 "FStar.Parser.ToSyntax.fst"
let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_Env.constrname)) p.FStar_Parser_AST.prange)), (args)))) p.FStar_Parser_AST.prange)
in (
# 444 "FStar.Parser.ToSyntax.fst"
let _64_736 = (aux loc env app)
in (match (_64_736) with
| (env, e, b, p, _64_735) -> begin
(
# 445 "FStar.Parser.ToSyntax.fst"
let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(let _157_324 = (let _157_323 = (let _157_322 = (
# 446 "FStar.Parser.ToSyntax.fst"
let _64_741 = fv
in (let _157_321 = (let _157_320 = (let _157_319 = (let _157_318 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_Env.typename), (_157_318)))
in FStar_Syntax_Syntax.Record_ctor (_157_319))
in Some (_157_320))
in {FStar_Syntax_Syntax.fv_name = _64_741.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = _64_741.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _157_321}))
in ((_157_322), (args)))
in FStar_Syntax_Syntax.Pat_cons (_157_323))
in (FStar_All.pipe_left pos _157_324))
end
| _64_744 -> begin
p
end)
in ((env), (e), (b), (p), (false)))
end)))))
end))
end))
end))))
in (
# 450 "FStar.Parser.ToSyntax.fst"
let _64_753 = (aux [] env p)
in (match (_64_753) with
| (_64_747, env, b, p, _64_752) -> begin
(
# 451 "FStar.Parser.ToSyntax.fst"
let _64_754 = (let _157_325 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore _157_325))
in ((env), (b), (p)))
end)))))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p is_mut -> (
# 455 "FStar.Parser.ToSyntax.fst"
let mklet = (fun x -> (let _157_334 = (let _157_333 = (let _157_332 = (FStar_Parser_Env.qualify env x)
in ((_157_332), (FStar_Syntax_Syntax.tun)))
in LetBinder (_157_333))
in ((env), (_157_334), (None))))
in if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(let _157_336 = (let _157_335 = (compile_op 0 x)
in (FStar_Ident.id_of_text _157_335))
in (mklet _157_336))
end
| FStar_Parser_AST.PatVar (x, _64_766) -> begin
(mklet x)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _64_773); FStar_Parser_AST.prange = _64_770}, t) -> begin
(let _157_340 = (let _157_339 = (let _157_338 = (FStar_Parser_Env.qualify env x)
in (let _157_337 = (desugar_term env t)
in ((_157_338), (_157_337))))
in LetBinder (_157_339))
in ((env), (_157_340), (None)))
end
| _64_781 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end else begin
(
# 464 "FStar.Parser.ToSyntax.fst"
let _64_785 = (desugar_data_pat env p is_mut)
in (match (_64_785) with
| (env, binder, p) -> begin
(
# 465 "FStar.Parser.ToSyntax.fst"
let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| _64_793 -> begin
Some (p)
end)
in ((env), (binder), (p)))
end))
end))
and desugar_binding_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun _64_797 env pat -> (
# 474 "FStar.Parser.ToSyntax.fst"
let _64_805 = (desugar_data_pat env pat false)
in (match (_64_805) with
| (env, _64_803, pat) -> begin
((env), (pat))
end)))
and desugar_match_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (
# 480 "FStar.Parser.ToSyntax.fst"
let env = (
# 480 "FStar.Parser.ToSyntax.fst"
let _64_810 = env
in {FStar_Parser_Env.curmodule = _64_810.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _64_810.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _64_810.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _64_810.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _64_810.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _64_810.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _64_810.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _64_810.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _64_810.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _64_810.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _64_810.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (
# 484 "FStar.Parser.ToSyntax.fst"
let env = (
# 484 "FStar.Parser.ToSyntax.fst"
let _64_815 = env
in {FStar_Parser_Env.curmodule = _64_815.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _64_815.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _64_815.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _64_815.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _64_815.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _64_815.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _64_815.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _64_815.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _64_815.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _64_815.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _64_815.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_machine_integer : FStar_Parser_Env.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env repr _64_822 range -> (match (_64_822) with
| (signedness, width) -> begin
(
# 488 "FStar.Parser.ToSyntax.fst"
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
# 493 "FStar.Parser.ToSyntax.fst"
let lid = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text lid) range)
in (
# 494 "FStar.Parser.ToSyntax.fst"
let lid = (match ((FStar_Parser_Env.try_lookup_lid env lid)) with
| Some (lid) -> begin
(Prims.fst lid)
end
| None -> begin
(let _157_356 = (FStar_Util.format1 "%s not in scope\n" (FStar_Ident.text_of_lid lid))
in (FStar_All.failwith _157_356))
end)
in (
# 497 "FStar.Parser.ToSyntax.fst"
let repr = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (None))))) None range)
in (let _157_361 = (let _157_360 = (let _157_359 = (let _157_358 = (let _157_357 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr), (_157_357)))
in (_157_358)::[])
in ((lid), (_157_359)))
in FStar_Syntax_Syntax.Tm_app (_157_360))
in (FStar_Syntax_Syntax.mk _157_361 None range))))))
end))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (
# 501 "FStar.Parser.ToSyntax.fst"
let mk = (fun e -> (FStar_Syntax_Syntax.mk e None top.FStar_Parser_AST.range))
in (
# 502 "FStar.Parser.ToSyntax.fst"
let setpos = (fun e -> (
# 502 "FStar.Parser.ToSyntax.fst"
let _64_846 = e
in {FStar_Syntax_Syntax.n = _64_846.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _64_846.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _64_846.FStar_Syntax_Syntax.vars}))
in (match ((let _157_369 = (unparen top)
in _157_369.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (_64_850) -> begin
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
| FStar_Parser_AST.Op ("*", (_64_876)::(_64_874)::[]) when (let _157_370 = (op_as_term env 2 top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right _157_370 FStar_Option.isNone)) -> begin
(
# 524 "FStar.Parser.ToSyntax.fst"
let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", (t1)::(t2)::[]) -> begin
(let _157_373 = (flatten t1)
in (FStar_List.append _157_373 ((t2)::[])))
end
| _64_889 -> begin
(t)::[]
end))
in (
# 528 "FStar.Parser.ToSyntax.fst"
let targs = (let _157_377 = (let _157_374 = (unparen top)
in (flatten _157_374))
in (FStar_All.pipe_right _157_377 (FStar_List.map (fun t -> (let _157_376 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg _157_376))))))
in (
# 529 "FStar.Parser.ToSyntax.fst"
let _64_895 = (let _157_378 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) _157_378))
in (match (_64_895) with
| (tup, _64_894) -> begin
(mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _157_380 = (let _157_379 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) a)
in (Prims.fst _157_379))
in (FStar_All.pipe_left setpos _157_380))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Unexpected or unbound operator: " s)), (top.FStar_Parser_AST.range)))))
end
| Some (op) -> begin
if ((FStar_List.length args) > 0) then begin
(
# 540 "FStar.Parser.ToSyntax.fst"
let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _157_382 = (desugar_term env t)
in ((_157_382), (None))))))
in (mk (FStar_Syntax_Syntax.Tm_app (((op), (args))))))
end else begin
op
end
end)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _64_913; FStar_Ident.ident = _64_911; FStar_Ident.nsstr = _64_909; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _64_922; FStar_Ident.ident = _64_920; FStar_Ident.nsstr = _64_918; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _64_931; FStar_Ident.ident = _64_929; FStar_Ident.nsstr = _64_927; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _64_940; FStar_Ident.ident = _64_938; FStar_Ident.nsstr = _64_936; FStar_Ident.str = "True"}) -> begin
(let _157_383 = (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _157_383 FStar_Syntax_Syntax.Delta_constant None))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _64_949; FStar_Ident.ident = _64_947; FStar_Ident.nsstr = _64_945; FStar_Ident.str = "False"}) -> begin
(let _157_384 = (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _157_384 FStar_Syntax_Syntax.Delta_constant None))
end
| FStar_Parser_AST.Var ({FStar_Ident.ns = (eff)::rest; FStar_Ident.ident = {FStar_Ident.idText = txt; FStar_Ident.idRange = _64_957}; FStar_Ident.nsstr = _64_955; FStar_Ident.str = _64_953}) when ((is_special_effect_combinator txt) && (let _157_385 = (FStar_Ident.lid_of_ids ((eff)::rest))
in (FStar_Parser_Env.is_effect_name env _157_385))) -> begin
(match ((let _157_386 = (FStar_Ident.lid_of_ids ((eff)::rest))
in (FStar_Parser_Env.try_lookup_effect_defn env _157_386))) with
| Some (ed) -> begin
(let _157_387 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" txt))) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.fvar _157_387 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
end
| None -> begin
(FStar_All.failwith "immpossible special_effect_combinator")
end)
end
| FStar_Parser_AST.Assign (ident, t2) -> begin
(
# 561 "FStar.Parser.ToSyntax.fst"
let t2 = (desugar_term env t2)
in (
# 562 "FStar.Parser.ToSyntax.fst"
let _64_975 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) ident)
in (match (_64_975) with
| (t1, mut) -> begin
(
# 563 "FStar.Parser.ToSyntax.fst"
let _64_976 = if (not (mut)) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Can only assign to mutable values"), (top.FStar_Parser_AST.range)))))
end else begin
()
end
in (mk_ref_assign t1 t2 top.FStar_Parser_AST.range))
end)))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(
# 569 "FStar.Parser.ToSyntax.fst"
let _64_983 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) l)
in (match (_64_983) with
| (tm, mut) -> begin
(
# 570 "FStar.Parser.ToSyntax.fst"
let tm = (setpos tm)
in if mut then begin
(let _157_390 = (let _157_389 = (let _157_388 = (mk_ref_read tm)
in ((_157_388), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval))))
in FStar_Syntax_Syntax.Tm_meta (_157_389))
in (FStar_All.pipe_left mk _157_390))
end else begin
tm
end)
end))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(match ((FStar_Parser_Env.try_lookup_datacon env l)) with
| Some (head) -> begin
(
# 577 "FStar.Parser.ToSyntax.fst"
let _64_993 = (let _157_391 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in ((_157_391), (true)))
in (match (_64_993) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| _64_996 -> begin
(
# 581 "FStar.Parser.ToSyntax.fst"
let args = (FStar_List.map (fun _64_999 -> (match (_64_999) with
| (t, imp) -> begin
(
# 582 "FStar.Parser.ToSyntax.fst"
let te = (desugar_term env t)
in (arg_withimp_e imp te))
end)) args)
in (
# 584 "FStar.Parser.ToSyntax.fst"
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
# 590 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.expand_module_abbrev env l)
in (
# 591 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_namespace env l)
in (match (args) with
| ((e, _64_1008))::[] -> begin
(desugar_term_maybe_top top_level env e)
end
| _64_1012 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("The Foo.Bar (...) local open takes exactly one argument"), (top.FStar_Parser_AST.range)))))
end)))
end)
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(
# 600 "FStar.Parser.ToSyntax.fst"
let _64_1037 = (FStar_List.fold_left (fun _64_1020 b -> (match (_64_1020) with
| (env, tparams, typs) -> begin
(
# 601 "FStar.Parser.ToSyntax.fst"
let _64_1024 = (desugar_binder env b)
in (match (_64_1024) with
| (xopt, t) -> begin
(
# 602 "FStar.Parser.ToSyntax.fst"
let _64_1030 = (match (xopt) with
| None -> begin
(let _157_395 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env), (_157_395)))
end
| Some (x) -> begin
(FStar_Parser_Env.push_bv env x)
end)
in (match (_64_1030) with
| (env, x) -> begin
(let _157_399 = (let _157_398 = (let _157_397 = (let _157_396 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _157_396))
in (_157_397)::[])
in (FStar_List.append typs _157_398))
in ((env), ((FStar_List.append tparams (((((
# 606 "FStar.Parser.ToSyntax.fst"
let _64_1031 = x
in {FStar_Syntax_Syntax.ppname = _64_1031.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_1031.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (None)))::[]))), (_157_399)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_64_1037) with
| (env, _64_1035, targs) -> begin
(
# 609 "FStar.Parser.ToSyntax.fst"
let _64_1041 = (let _157_400 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) _157_400))
in (match (_64_1041) with
| (tup, _64_1040) -> begin
(FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(
# 613 "FStar.Parser.ToSyntax.fst"
let _64_1048 = (uncurry binders t)
in (match (_64_1048) with
| (bs, t) -> begin
(
# 614 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun env bs _64_9 -> (match (_64_9) with
| [] -> begin
(
# 616 "FStar.Parser.ToSyntax.fst"
let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (let _157_407 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos _157_407)))
end
| (hd)::tl -> begin
(
# 620 "FStar.Parser.ToSyntax.fst"
let mlenv = (FStar_Parser_Env.default_ml env)
in (
# 621 "FStar.Parser.ToSyntax.fst"
let bb = (desugar_binder mlenv hd)
in (
# 622 "FStar.Parser.ToSyntax.fst"
let _64_1062 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_64_1062) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_binder env b)) with
| (None, _64_1069) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(
# 631 "FStar.Parser.ToSyntax.fst"
let _64_1077 = (as_binder env None b)
in (match (_64_1077) with
| ((x, _64_1074), env) -> begin
(
# 632 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env f)
in (let _157_408 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos _157_408)))
end))
end)
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(
# 637 "FStar.Parser.ToSyntax.fst"
let _64_1097 = (FStar_List.fold_left (fun _64_1085 pat -> (match (_64_1085) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (_64_1088, t) -> begin
(let _157_412 = (let _157_411 = (free_type_vars env t)
in (FStar_List.append _157_411 ftvs))
in ((env), (_157_412)))
end
| _64_1093 -> begin
((env), (ftvs))
end)
end)) ((env), ([])) binders)
in (match (_64_1097) with
| (_64_1095, ftv) -> begin
(
# 641 "FStar.Parser.ToSyntax.fst"
let ftv = (sort_ftv ftv)
in (
# 642 "FStar.Parser.ToSyntax.fst"
let binders = (let _157_414 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append _157_414 binders))
in (
# 651 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun env bs sc_pat_opt _64_10 -> (match (_64_10) with
| [] -> begin
(
# 653 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env body)
in (
# 654 "FStar.Parser.ToSyntax.fst"
let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(
# 656 "FStar.Parser.ToSyntax.fst"
let body = (let _157_424 = (let _157_423 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right _157_423 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close _157_424 body))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (None), (body)))::[])))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (let _157_425 = (no_annot_abs (FStar_List.rev bs) body)
in (setpos _157_425))))
end
| (p)::rest -> begin
(
# 662 "FStar.Parser.ToSyntax.fst"
let _64_1121 = (desugar_binding_pat env p)
in (match (_64_1121) with
| (env, b, pat) -> begin
(
# 663 "FStar.Parser.ToSyntax.fst"
let _64_1172 = (match (b) with
| LetBinder (_64_1123) -> begin
(FStar_All.failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(
# 666 "FStar.Parser.ToSyntax.fst"
let sc_pat_opt = (match (((pat), (sc_pat_opt))) with
| (None, _64_1131) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _157_427 = (let _157_426 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_157_426), (p)))
in Some (_157_427))
end
| (Some (p), Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (_64_1145), _64_1148) -> begin
(
# 672 "FStar.Parser.ToSyntax.fst"
let tup2 = (let _157_428 = (FStar_Syntax_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _157_428 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (
# 673 "FStar.Parser.ToSyntax.fst"
let sc = (let _157_436 = (let _157_435 = (let _157_434 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (let _157_433 = (let _157_432 = (FStar_Syntax_Syntax.as_arg sc)
in (let _157_431 = (let _157_430 = (let _157_429 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _157_429))
in (_157_430)::[])
in (_157_432)::_157_431))
in ((_157_434), (_157_433))))
in FStar_Syntax_Syntax.Tm_app (_157_435))
in (FStar_Syntax_Syntax.mk _157_436 None top.FStar_Parser_AST.range))
in (
# 674 "FStar.Parser.ToSyntax.fst"
let p = (let _157_437 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p), (false)))::[])))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _157_437))
in Some (((sc), (p))))))
end
| (FStar_Syntax_Syntax.Tm_app (_64_1154, args), FStar_Syntax_Syntax.Pat_cons (_64_1159, pats)) -> begin
(
# 677 "FStar.Parser.ToSyntax.fst"
let tupn = (let _157_438 = (FStar_Syntax_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _157_438 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (
# 678 "FStar.Parser.ToSyntax.fst"
let sc = (let _157_445 = (let _157_444 = (let _157_443 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (let _157_442 = (let _157_441 = (let _157_440 = (let _157_439 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _157_439))
in (_157_440)::[])
in (FStar_List.append args _157_441))
in ((_157_443), (_157_442))))
in FStar_Syntax_Syntax.Tm_app (_157_444))
in (mk _157_445))
in (
# 679 "FStar.Parser.ToSyntax.fst"
let p = (let _157_446 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p), (false)))::[])))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _157_446))
in Some (((sc), (p))))))
end
| _64_1168 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt)))
end)
in (match (_64_1172) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _64_1176; FStar_Parser_AST.level = _64_1174}, phi, _64_1182) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(
# 690 "FStar.Parser.ToSyntax.fst"
let phi = (desugar_formula env phi)
in (let _157_454 = (let _157_453 = (let _157_452 = (FStar_Syntax_Syntax.fvar a FStar_Syntax_Syntax.Delta_equational None)
in (let _157_451 = (let _157_450 = (FStar_Syntax_Syntax.as_arg phi)
in (let _157_449 = (let _157_448 = (let _157_447 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _157_447))
in (_157_448)::[])
in (_157_450)::_157_449))
in ((_157_452), (_157_451))))
in FStar_Syntax_Syntax.Tm_app (_157_453))
in (mk _157_454)))
end
| FStar_Parser_AST.App (_64_1187) -> begin
(
# 696 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun args e -> (match ((let _157_459 = (unparen e)
in _157_459.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(
# 698 "FStar.Parser.ToSyntax.fst"
let arg = (let _157_460 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _157_460))
in (aux ((arg)::args) e))
end
| _64_1199 -> begin
(
# 701 "FStar.Parser.ToSyntax.fst"
let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app (((head), (args))))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _157_463 = (let _157_462 = (let _157_461 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((_157_461), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))
in FStar_Syntax_Syntax.Tm_meta (_157_462))
in (mk _157_463))
end
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(
# 710 "FStar.Parser.ToSyntax.fst"
let lid = (FStar_Parser_Env.expand_module_abbrev env lid)
in (
# 711 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_namespace env lid)
in (desugar_term_maybe_top top_level env e)))
end
| FStar_Parser_AST.Let (qual, ((pat, _snd))::_tl, body) -> begin
(
# 715 "FStar.Parser.ToSyntax.fst"
let is_rec = (qual = FStar_Parser_AST.Rec)
in (
# 716 "FStar.Parser.ToSyntax.fst"
let ds_let_rec_or_app = (fun _64_1222 -> (match (()) with
| () -> begin
(
# 717 "FStar.Parser.ToSyntax.fst"
let bindings = (((pat), (_snd)))::_tl
in (
# 718 "FStar.Parser.ToSyntax.fst"
let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _64_1226 -> (match (_64_1226) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _157_467 = (destruct_app_pattern env top_level p)
in ((_157_467), (def)))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _157_468 = (destruct_app_pattern env top_level p)
in ((_157_468), (def)))
end
| _64_1232 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _64_1237); FStar_Parser_AST.prange = _64_1234}, t) -> begin
if top_level then begin
(let _157_471 = (let _157_470 = (let _157_469 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_157_469))
in ((_157_470), ([]), (Some (t))))
in ((_157_471), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (Some (t)))), (def))
end
end
| FStar_Parser_AST.PatVar (id, _64_1246) -> begin
if top_level then begin
(let _157_474 = (let _157_473 = (let _157_472 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_157_472))
in ((_157_473), ([]), (None)))
in ((_157_474), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (None))), (def))
end
end
| _64_1250 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end
end))))
in (
# 735 "FStar.Parser.ToSyntax.fst"
let _64_1279 = (FStar_List.fold_left (fun _64_1255 _64_1264 -> (match (((_64_1255), (_64_1264))) with
| ((env, fnames, rec_bindings), ((f, _64_1258, _64_1260), _64_1263)) -> begin
(
# 737 "FStar.Parser.ToSyntax.fst"
let _64_1275 = (match (f) with
| FStar_Util.Inl (x) -> begin
(
# 739 "FStar.Parser.ToSyntax.fst"
let _64_1269 = (FStar_Parser_Env.push_bv env x)
in (match (_64_1269) with
| (env, xx) -> begin
(let _157_478 = (let _157_477 = (FStar_Syntax_Syntax.mk_binder xx)
in (_157_477)::rec_bindings)
in ((env), (FStar_Util.Inl (xx)), (_157_478)))
end))
end
| FStar_Util.Inr (l) -> begin
(let _157_479 = (FStar_Parser_Env.push_top_level_rec_binding env l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in ((_157_479), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (_64_1275) with
| (env, lbname, rec_bindings) -> begin
((env), ((lbname)::fnames), (rec_bindings))
end))
end)) ((env), ([]), ([])) funs)
in (match (_64_1279) with
| (env', fnames, rec_bindings) -> begin
(
# 745 "FStar.Parser.ToSyntax.fst"
let fnames = (FStar_List.rev fnames)
in (
# 747 "FStar.Parser.ToSyntax.fst"
let desugar_one_def = (fun env lbname _64_1290 -> (match (_64_1290) with
| ((_64_1285, args, result_t), def) -> begin
(
# 748 "FStar.Parser.ToSyntax.fst"
let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _157_486 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t)))) _157_486 FStar_Parser_AST.Expr))
end)
in (
# 751 "FStar.Parser.ToSyntax.fst"
let def = (match (args) with
| [] -> begin
def
end
| _64_1297 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.un_curry_abs args def) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
end)
in (
# 754 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env def)
in (
# 755 "FStar.Parser.ToSyntax.fst"
let lbname = (match (lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl (x)
end
| FStar_Util.Inr (l) -> begin
(let _157_488 = (let _157_487 = (FStar_Syntax_Util.incr_delta_qualifier body)
in (FStar_Syntax_Syntax.lid_as_fv l _157_487 None))
in FStar_Util.Inr (_157_488))
end)
in (
# 758 "FStar.Parser.ToSyntax.fst"
let body = if is_rec then begin
(FStar_Syntax_Subst.close rec_bindings body)
end else begin
body
end
in (mk_lb ((lbname), (FStar_Syntax_Syntax.tun), (body))))))))
end))
in (
# 760 "FStar.Parser.ToSyntax.fst"
let lbs = (FStar_List.map2 (desugar_one_def (if is_rec then begin
env'
end else begin
env
end)) fnames funs)
in (
# 761 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env' body)
in (let _157_491 = (let _157_490 = (let _157_489 = (FStar_Syntax_Subst.close rec_bindings body)
in ((((is_rec), (lbs))), (_157_489)))
in FStar_Syntax_Syntax.Tm_let (_157_490))
in (FStar_All.pipe_left mk _157_491))))))
end))))
end))
in (
# 765 "FStar.Parser.ToSyntax.fst"
let ds_non_rec = (fun pat t1 t2 -> (
# 766 "FStar.Parser.ToSyntax.fst"
let t1 = (desugar_term env t1)
in (
# 767 "FStar.Parser.ToSyntax.fst"
let is_mutable = (qual = FStar_Parser_AST.Mutable)
in (
# 769 "FStar.Parser.ToSyntax.fst"
let t1 = if is_mutable then begin
(mk_ref_alloc t1)
end else begin
t1
end
in (
# 773 "FStar.Parser.ToSyntax.fst"
let _64_1318 = (desugar_binding_pat_maybe_top top_level env pat is_mutable)
in (match (_64_1318) with
| (env, binder, pat) -> begin
(
# 774 "FStar.Parser.ToSyntax.fst"
let tm = (match (binder) with
| LetBinder (l, t) -> begin
(
# 776 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env t2)
in (
# 777 "FStar.Parser.ToSyntax.fst"
let fv = (let _157_498 = (FStar_Syntax_Util.incr_delta_qualifier t1)
in (FStar_Syntax_Syntax.lid_as_fv l _157_498 None))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((((false), (({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]))), (body)))))))
end
| LocalBinder (x, _64_1327) -> begin
(
# 781 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env t2)
in (
# 782 "FStar.Parser.ToSyntax.fst"
let body = (match (pat) with
| (None) | (Some ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (_); FStar_Syntax_Syntax.ty = _; FStar_Syntax_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _157_503 = (let _157_502 = (let _157_501 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _157_500 = (let _157_499 = (FStar_Syntax_Util.branch ((pat), (None), (body)))
in (_157_499)::[])
in ((_157_501), (_157_500))))
in FStar_Syntax_Syntax.Tm_match (_157_502))
in (FStar_Syntax_Syntax.mk _157_503 None body.FStar_Syntax_Syntax.pos))
end)
in (let _157_508 = (let _157_507 = (let _157_506 = (let _157_505 = (let _157_504 = (FStar_Syntax_Syntax.mk_binder x)
in (_157_504)::[])
in (FStar_Syntax_Subst.close _157_505 body))
in ((((false), (((mk_lb ((FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t1))))::[]))), (_157_506)))
in FStar_Syntax_Syntax.Tm_let (_157_507))
in (FStar_All.pipe_left mk _157_508))))
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
# 800 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (let _157_519 = (let _157_518 = (let _157_517 = (desugar_term env t1)
in (let _157_516 = (let _157_515 = (let _157_510 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (let _157_509 = (desugar_term env t2)
in ((_157_510), (None), (_157_509))))
in (let _157_514 = (let _157_513 = (let _157_512 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (let _157_511 = (desugar_term env t3)
in ((_157_512), (None), (_157_511))))
in (_157_513)::[])
in (_157_515)::_157_514))
in ((_157_517), (_157_516))))
in FStar_Syntax_Syntax.Tm_match (_157_518))
in (mk _157_519)))
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(
# 806 "FStar.Parser.ToSyntax.fst"
let r = top.FStar_Parser_AST.range
in (
# 807 "FStar.Parser.ToSyntax.fst"
let handler = (FStar_Parser_AST.mk_function branches r r)
in (
# 808 "FStar.Parser.ToSyntax.fst"
let body = (FStar_Parser_AST.mk_function (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatConst (FStar_Const.Const_unit)) r)), (None), (e)))::[]) r r)
in (
# 809 "FStar.Parser.ToSyntax.fst"
let a1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (FStar_Syntax_Const.try_with_lid)) r top.FStar_Parser_AST.level)), (body), (FStar_Parser_AST.Nothing)))) r top.FStar_Parser_AST.level)
in (
# 810 "FStar.Parser.ToSyntax.fst"
let a2 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((a1), (handler), (FStar_Parser_AST.Nothing)))) r top.FStar_Parser_AST.level)
in (desugar_term env a2))))))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(
# 814 "FStar.Parser.ToSyntax.fst"
let desugar_branch = (fun _64_1368 -> (match (_64_1368) with
| (pat, wopt, b) -> begin
(
# 815 "FStar.Parser.ToSyntax.fst"
let _64_1371 = (desugar_match_pat env pat)
in (match (_64_1371) with
| (env, pat) -> begin
(
# 816 "FStar.Parser.ToSyntax.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _157_522 = (desugar_term env e)
in Some (_157_522))
end)
in (
# 819 "FStar.Parser.ToSyntax.fst"
let b = (desugar_term env b)
in (FStar_Syntax_Util.branch ((pat), (wopt), (b)))))
end))
end))
in (let _157_526 = (let _157_525 = (let _157_524 = (desugar_term env e)
in (let _157_523 = (FStar_List.map desugar_branch branches)
in ((_157_524), (_157_523))))
in FStar_Syntax_Syntax.Tm_match (_157_525))
in (FStar_All.pipe_left mk _157_526)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(
# 824 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.default_ml env)
in (
# 825 "FStar.Parser.ToSyntax.fst"
let c = (desugar_comp t.FStar_Parser_AST.range true env t)
in (
# 826 "FStar.Parser.ToSyntax.fst"
let annot = if (FStar_Syntax_Util.is_ml_comp c) then begin
FStar_Util.Inl ((FStar_Syntax_Util.comp_result c))
end else begin
FStar_Util.Inr (c)
end
in (let _157_529 = (let _157_528 = (let _157_527 = (desugar_term env e)
in ((_157_527), (annot), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (_157_528))
in (FStar_All.pipe_left mk _157_529)))))
end
| FStar_Parser_AST.Record (_64_1385, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(
# 835 "FStar.Parser.ToSyntax.fst"
let _64_1396 = (FStar_List.hd fields)
in (match (_64_1396) with
| (f, _64_1395) -> begin
(
# 836 "FStar.Parser.ToSyntax.fst"
let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (
# 837 "FStar.Parser.ToSyntax.fst"
let _64_1402 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_64_1402) with
| (record, _64_1401) -> begin
(
# 838 "FStar.Parser.ToSyntax.fst"
let get_field = (fun xopt f -> (
# 839 "FStar.Parser.ToSyntax.fst"
let fn = f.FStar_Ident.ident
in (
# 840 "FStar.Parser.ToSyntax.fst"
let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _64_1410 -> (match (_64_1410) with
| (g, _64_1409) -> begin
(
# 841 "FStar.Parser.ToSyntax.fst"
let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_64_1414, e) -> begin
(let _157_537 = (qfn fn)
in ((_157_537), (e)))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _157_540 = (let _157_539 = (let _157_538 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in ((_157_538), (top.FStar_Parser_AST.range)))
in FStar_Syntax_Syntax.Error (_157_539))
in (Prims.raise _157_540))
end
| Some (x) -> begin
(let _157_541 = (qfn fn)
in ((_157_541), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Project (((x), (f)))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level))))
end)
end))))
in (
# 852 "FStar.Parser.ToSyntax.fst"
let recterm = (match (eopt) with
| None -> begin
(let _157_546 = (let _157_545 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _64_1426 -> (match (_64_1426) with
| (f, _64_1425) -> begin
(let _157_544 = (let _157_543 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _157_543))
in ((_157_544), (FStar_Parser_AST.Nothing)))
end))))
in ((record.FStar_Parser_Env.constrname), (_157_545)))
in FStar_Parser_AST.Construct (_157_546))
end
| Some (e) -> begin
(
# 859 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (
# 860 "FStar.Parser.ToSyntax.fst"
let xterm = (let _157_548 = (let _157_547 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_157_547))
in (FStar_Parser_AST.mk_term _157_548 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (
# 861 "FStar.Parser.ToSyntax.fst"
let record = (let _157_551 = (let _157_550 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _64_1434 -> (match (_64_1434) with
| (f, _64_1433) -> begin
(get_field (Some (xterm)) f)
end))))
in ((None), (_157_550)))
in FStar_Parser_AST.Record (_157_551))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (
# 864 "FStar.Parser.ToSyntax.fst"
let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (
# 865 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _64_1450; FStar_Syntax_Syntax.pos = _64_1448; FStar_Syntax_Syntax.vars = _64_1446}, args); FStar_Syntax_Syntax.tk = _64_1444; FStar_Syntax_Syntax.pos = _64_1442; FStar_Syntax_Syntax.vars = _64_1440}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(
# 868 "FStar.Parser.ToSyntax.fst"
let e = (let _157_559 = (let _157_558 = (let _157_557 = (let _157_556 = (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos)
in (let _157_555 = (let _157_554 = (let _157_553 = (let _157_552 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_Env.typename), (_157_552)))
in FStar_Syntax_Syntax.Record_ctor (_157_553))
in Some (_157_554))
in (FStar_Syntax_Syntax.fvar _157_556 FStar_Syntax_Syntax.Delta_constant _157_555)))
in ((_157_557), (args)))
in FStar_Syntax_Syntax.Tm_app (_157_558))
in (FStar_All.pipe_left mk _157_559))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))))))
end
| _64_1464 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(
# 876 "FStar.Parser.ToSyntax.fst"
let _64_1471 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_projector_by_field_name env) f)
in (match (_64_1471) with
| (fieldname, is_rec) -> begin
(
# 877 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env e)
in (
# 878 "FStar.Parser.ToSyntax.fst"
let fn = (
# 879 "FStar.Parser.ToSyntax.fst"
let _64_1476 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_64_1476) with
| (ns, _64_1475) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (
# 881 "FStar.Parser.ToSyntax.fst"
let qual = if is_rec then begin
Some (FStar_Syntax_Syntax.Record_projector (fn))
end else begin
None
end
in (let _157_565 = (let _157_564 = (let _157_563 = (let _157_560 = (FStar_Ident.set_lid_range fieldname (FStar_Ident.range_of_lid f))
in (FStar_Syntax_Syntax.fvar _157_560 FStar_Syntax_Syntax.Delta_equational qual))
in (let _157_562 = (let _157_561 = (FStar_Syntax_Syntax.as_arg e)
in (_157_561)::[])
in ((_157_563), (_157_562))))
in FStar_Syntax_Syntax.Tm_app (_157_564))
in (FStar_All.pipe_left mk _157_565)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| _64_1486 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _64_1488 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_args : FStar_Parser_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun _64_1493 -> (match (_64_1493) with
| (a, imp) -> begin
(let _157_569 = (desugar_term env a)
in (arg_withimp_e imp _157_569))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r default_ok env t -> (
# 898 "FStar.Parser.ToSyntax.fst"
let fail = (fun msg -> (Prims.raise (FStar_Syntax_Syntax.Error (((msg), (r))))))
in (
# 899 "FStar.Parser.ToSyntax.fst"
let is_requires = (fun _64_1505 -> (match (_64_1505) with
| (t, _64_1504) -> begin
(match ((let _157_577 = (unparen t)
in _157_577.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Requires (_64_1507) -> begin
true
end
| _64_1510 -> begin
false
end)
end))
in (
# 902 "FStar.Parser.ToSyntax.fst"
let is_ensures = (fun _64_1515 -> (match (_64_1515) with
| (t, _64_1514) -> begin
(match ((let _157_580 = (unparen t)
in _157_580.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ensures (_64_1517) -> begin
true
end
| _64_1520 -> begin
false
end)
end))
in (
# 905 "FStar.Parser.ToSyntax.fst"
let is_app = (fun head _64_1526 -> (match (_64_1526) with
| (t, _64_1525) -> begin
(match ((let _157_585 = (unparen t)
in _157_585.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _64_1530; FStar_Parser_AST.level = _64_1528}, _64_1535, _64_1537) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| _64_1541 -> begin
false
end)
end))
in (
# 908 "FStar.Parser.ToSyntax.fst"
let is_decreases = (is_app "decreases")
in (
# 909 "FStar.Parser.ToSyntax.fst"
let pre_process_comp_typ = (fun t -> (
# 910 "FStar.Parser.ToSyntax.fst"
let _64_1547 = (head_and_args t)
in (match (_64_1547) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(
# 913 "FStar.Parser.ToSyntax.fst"
let unit_tm = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type)), (FStar_Parser_AST.Nothing))
in (
# 914 "FStar.Parser.ToSyntax.fst"
let nil_pat = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr)), (FStar_Parser_AST.Nothing))
in (
# 915 "FStar.Parser.ToSyntax.fst"
let req_true = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Requires ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.true_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Formula)), (None)))) t.FStar_Parser_AST.range FStar_Parser_AST.Type)), (FStar_Parser_AST.Nothing))
in (
# 916 "FStar.Parser.ToSyntax.fst"
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
# 923 "FStar.Parser.ToSyntax.fst"
let head = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_name env) lemma)
in ((head), (args)))))))
end
| FStar_Parser_AST.Name (l) when (FStar_Parser_Env.is_effect_name env l) -> begin
(let _157_589 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_name env) l)
in ((_157_589), (args)))
end
| FStar_Parser_AST.Name (l) when ((let _157_590 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _157_590 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(let _157_591 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in ((_157_591), (args)))
end
| FStar_Parser_AST.Name (l) when ((let _157_592 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _157_592 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(let _157_593 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)
in ((_157_593), (args)))
end
| FStar_Parser_AST.Name (l) when ((((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) && default_ok) -> begin
(let _157_594 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in ((_157_594), ((((t), (FStar_Parser_AST.Nothing)))::[])))
end
| _64_1578 when default_ok -> begin
(let _157_595 = (FStar_Ident.set_lid_range env.FStar_Parser_Env.default_result_effect head.FStar_Parser_AST.range)
in ((_157_595), ((((t), (FStar_Parser_AST.Nothing)))::[])))
end
| _64_1580 -> begin
(let _157_597 = (let _157_596 = (FStar_Parser_AST.term_to_string t)
in (FStar_Util.format1 "%s is not an effect" _157_596))
in (fail _157_597))
end)
end)))
in (
# 953 "FStar.Parser.ToSyntax.fst"
let _64_1583 = (pre_process_comp_typ t)
in (match (_64_1583) with
| (eff, args) -> begin
(
# 954 "FStar.Parser.ToSyntax.fst"
let _64_1584 = if ((FStar_List.length args) = 0) then begin
(let _157_599 = (let _157_598 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" _157_598))
in (fail _157_599))
end else begin
()
end
in (
# 956 "FStar.Parser.ToSyntax.fst"
let _64_1588 = (let _157_601 = (FStar_List.hd args)
in (let _157_600 = (FStar_List.tl args)
in ((_157_601), (_157_600))))
in (match (_64_1588) with
| (result_arg, rest) -> begin
(
# 957 "FStar.Parser.ToSyntax.fst"
let result_typ = (desugar_typ env (Prims.fst result_arg))
in (
# 958 "FStar.Parser.ToSyntax.fst"
let rest = (desugar_args env rest)
in (
# 959 "FStar.Parser.ToSyntax.fst"
let _64_1613 = (FStar_All.pipe_right rest (FStar_List.partition (fun _64_1594 -> (match (_64_1594) with
| (t, _64_1593) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _64_1600; FStar_Syntax_Syntax.pos = _64_1598; FStar_Syntax_Syntax.vars = _64_1596}, (_64_1605)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| _64_1610 -> begin
false
end)
end))))
in (match (_64_1613) with
| (dec, rest) -> begin
(
# 965 "FStar.Parser.ToSyntax.fst"
let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _64_1617 -> (match (_64_1617) with
| (t, _64_1616) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_64_1619, ((arg, _64_1622))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| _64_1628 -> begin
(FStar_All.failwith "impos")
end)
end))))
in (
# 969 "FStar.Parser.ToSyntax.fst"
let no_additional_args = (((FStar_List.length decreases_clause) = 0) && ((FStar_List.length rest) = 0))
in if (no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid)) then begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end else begin
if (no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid)) then begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end else begin
(
# 977 "FStar.Parser.ToSyntax.fst"
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
# 983 "FStar.Parser.ToSyntax.fst"
let rest = if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid) then begin
(match (rest) with
| (req)::(ens)::((pat, aq))::[] -> begin
(
# 987 "FStar.Parser.ToSyntax.fst"
let pat = (match (pat.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
(
# 989 "FStar.Parser.ToSyntax.fst"
let nil = (FStar_Syntax_Syntax.mk_Tm_uinst pat ((FStar_Syntax_Syntax.U_succ (FStar_Syntax_Syntax.U_zero))::[]))
in (
# 990 "FStar.Parser.ToSyntax.fst"
let pattern = (let _157_605 = (let _157_604 = (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _157_604 FStar_Syntax_Syntax.Delta_constant None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _157_605 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app nil ((((pattern), (Some (FStar_Syntax_Syntax.imp_tag))))::[]) None pat.FStar_Syntax_Syntax.pos)))
end
| _64_1643 -> begin
pat
end)
in (let _157_609 = (let _157_608 = (let _157_607 = (let _157_606 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) None pat.FStar_Syntax_Syntax.pos)
in ((_157_606), (aq)))
in (_157_607)::[])
in (ens)::_157_608)
in (req)::_157_609))
end
| _64_1646 -> begin
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
# 1003 "FStar.Parser.ToSyntax.fst"
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
| _64_1658 -> begin
None
end))
in (
# 1010 "FStar.Parser.ToSyntax.fst"
let mk = (fun t -> (FStar_Syntax_Syntax.mk t None f.FStar_Parser_AST.range))
in (
# 1011 "FStar.Parser.ToSyntax.fst"
let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (
# 1012 "FStar.Parser.ToSyntax.fst"
let setpos = (fun t -> (
# 1012 "FStar.Parser.ToSyntax.fst"
let _64_1665 = t
in {FStar_Syntax_Syntax.n = _64_1665.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _64_1665.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _64_1665.FStar_Syntax_Syntax.vars}))
in (
# 1013 "FStar.Parser.ToSyntax.fst"
let desugar_quant = (fun q b pats body -> (
# 1014 "FStar.Parser.ToSyntax.fst"
let tk = (desugar_binder env (
# 1014 "FStar.Parser.ToSyntax.fst"
let _64_1672 = b
in {FStar_Parser_AST.b = _64_1672.FStar_Parser_AST.b; FStar_Parser_AST.brange = _64_1672.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _64_1672.FStar_Parser_AST.aqual}))
in (
# 1015 "FStar.Parser.ToSyntax.fst"
let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _157_644 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _157_644)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(
# 1018 "FStar.Parser.ToSyntax.fst"
let _64_1686 = (FStar_Parser_Env.push_bv env a)
in (match (_64_1686) with
| (env, a) -> begin
(
# 1019 "FStar.Parser.ToSyntax.fst"
let a = (
# 1019 "FStar.Parser.ToSyntax.fst"
let _64_1687 = a
in {FStar_Syntax_Syntax.ppname = _64_1687.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_1687.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (
# 1020 "FStar.Parser.ToSyntax.fst"
let pats = (desugar_pats env pats)
in (
# 1021 "FStar.Parser.ToSyntax.fst"
let body = (desugar_formula env body)
in (
# 1022 "FStar.Parser.ToSyntax.fst"
let body = (match (pats) with
| [] -> begin
body
end
| _64_1694 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta (((body), (FStar_Syntax_Syntax.Meta_pattern (pats))))))
end)
in (
# 1025 "FStar.Parser.ToSyntax.fst"
let body = (let _157_647 = (let _157_646 = (let _157_645 = (FStar_Syntax_Syntax.mk_binder a)
in (_157_645)::[])
in (no_annot_abs _157_646 body))
in (FStar_All.pipe_left setpos _157_647))
in (let _157_653 = (let _157_652 = (let _157_651 = (let _157_648 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Syntax_Syntax.fvar _157_648 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (let _157_650 = (let _157_649 = (FStar_Syntax_Syntax.as_arg body)
in (_157_649)::[])
in ((_157_651), (_157_650))))
in FStar_Syntax_Syntax.Tm_app (_157_652))
in (FStar_All.pipe_left mk _157_653)))))))
end))
end
| _64_1698 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1030 "FStar.Parser.ToSyntax.fst"
let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(
# 1032 "FStar.Parser.ToSyntax.fst"
let rest = (b')::_rest
in (
# 1033 "FStar.Parser.ToSyntax.fst"
let body = (let _157_668 = (q ((rest), (pats), (body)))
in (let _157_667 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _157_668 _157_667 FStar_Parser_AST.Formula)))
in (let _157_669 = (q (((b)::[]), ([]), (body)))
in (FStar_Parser_AST.mk_term _157_669 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _64_1712 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _157_670 = (unparen f)
in _157_670.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(
# 1039 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env f)
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((l), (f.FStar_Syntax_Syntax.pos), (p)))))))))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall ((_1)::(_2)::_3, pats, body) -> begin
(
# 1046 "FStar.Parser.ToSyntax.fst"
let binders = (_1)::(_2)::_3
in (let _157_672 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _157_672)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(
# 1050 "FStar.Parser.ToSyntax.fst"
let binders = (_1)::(_2)::_3
in (let _157_674 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _157_674)))
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
| _64_1770 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (
# 1065 "FStar.Parser.ToSyntax.fst"
let _64_1794 = (FStar_List.fold_left (fun _64_1775 b -> (match (_64_1775) with
| (env, out) -> begin
(
# 1066 "FStar.Parser.ToSyntax.fst"
let tk = (desugar_binder env (
# 1066 "FStar.Parser.ToSyntax.fst"
let _64_1777 = b
in {FStar_Parser_AST.b = _64_1777.FStar_Parser_AST.b; FStar_Parser_AST.brange = _64_1777.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _64_1777.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(
# 1069 "FStar.Parser.ToSyntax.fst"
let _64_1786 = (FStar_Parser_Env.push_bv env a)
in (match (_64_1786) with
| (env, a) -> begin
(
# 1070 "FStar.Parser.ToSyntax.fst"
let a = (
# 1070 "FStar.Parser.ToSyntax.fst"
let _64_1787 = a
in {FStar_Syntax_Syntax.ppname = _64_1787.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_1787.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in ((env), ((((a), ((trans_aqual b.FStar_Parser_AST.aqual))))::out)))
end))
end
| _64_1791 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (_64_1794) with
| (env, tpars) -> begin
((env), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(let _157_681 = (desugar_typ env t)
in ((Some (x)), (_157_681)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _157_682 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None x.FStar_Ident.idRange)
in ((Some (x)), (_157_682)))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _157_683 = (desugar_typ env t)
in ((None), (_157_683)))
end
| FStar_Parser_AST.Variable (x) -> begin
((Some (x)), (FStar_Syntax_Syntax.tun))
end))

# 1080 "FStar.Parser.ToSyntax.fst"
let mk_data_discriminators : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  FStar_Ident.lid  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun quals env t tps k datas -> (
# 1083 "FStar.Parser.ToSyntax.fst"
let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_Env.iface) || env.FStar_Parser_Env.admitted_iface) then begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (
# 1086 "FStar.Parser.ToSyntax.fst"
let binders = (let _157_699 = (let _157_698 = (FStar_Syntax_Util.arrow_formals k)
in (Prims.fst _157_698))
in (FStar_List.append tps _157_699))
in (
# 1087 "FStar.Parser.ToSyntax.fst"
let p = (FStar_Ident.range_of_lid t)
in (
# 1088 "FStar.Parser.ToSyntax.fst"
let _64_1821 = (FStar_Syntax_Util.args_of_binders binders)
in (match (_64_1821) with
| (binders, args) -> begin
(
# 1089 "FStar.Parser.ToSyntax.fst"
let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _64_1825 -> (match (_64_1825) with
| (x, _64_1824) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (
# 1090 "FStar.Parser.ToSyntax.fst"
let binders = (let _157_705 = (let _157_704 = (let _157_703 = (let _157_702 = (let _157_701 = (FStar_Syntax_Syntax.lid_as_fv t FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _157_701))
in (FStar_Syntax_Syntax.mk_Tm_app _157_702 args None p))
in (FStar_All.pipe_left FStar_Syntax_Syntax.null_binder _157_703))
in (_157_704)::[])
in (FStar_List.append imp_binders _157_705))
in (
# 1091 "FStar.Parser.ToSyntax.fst"
let disc_type = (let _157_708 = (let _157_707 = (let _157_706 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _157_706))
in (FStar_Syntax_Syntax.mk_Total _157_707))
in (FStar_Syntax_Util.arrow binders _157_708))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (
# 1093 "FStar.Parser.ToSyntax.fst"
let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (let _157_711 = (let _157_710 = (quals ((FStar_Syntax_Syntax.Logic)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in ((disc_name), ([]), (disc_type), (_157_710), ((FStar_Ident.range_of_lid disc_name))))
in FStar_Syntax_Syntax.Sig_declare_typ (_157_711)))))))))
end))))))

# 1094 "FStar.Parser.ToSyntax.fst"
let mk_indexed_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq refine_domain env tc lid inductive_tps imp_tps fields t -> (
# 1097 "FStar.Parser.ToSyntax.fst"
let p = (FStar_Ident.range_of_lid lid)
in (
# 1098 "FStar.Parser.ToSyntax.fst"
let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p))
in (
# 1099 "FStar.Parser.ToSyntax.fst"
let projectee = (fun ptyp -> (FStar_Syntax_Syntax.gen_bv "projectee" (Some (p)) ptyp))
in (
# 1100 "FStar.Parser.ToSyntax.fst"
let tps = (FStar_List.map2 (fun _64_1849 _64_1853 -> (match (((_64_1849), (_64_1853))) with
| ((_64_1847, imp), (x, _64_1852)) -> begin
((x), (imp))
end)) inductive_tps imp_tps)
in (
# 1101 "FStar.Parser.ToSyntax.fst"
let _64_1954 = (
# 1102 "FStar.Parser.ToSyntax.fst"
let _64_1857 = (FStar_Syntax_Util.head_and_args t)
in (match (_64_1857) with
| (head, args0) -> begin
(
# 1103 "FStar.Parser.ToSyntax.fst"
let args = (
# 1104 "FStar.Parser.ToSyntax.fst"
let rec arguments = (fun tps args -> (match (((tps), (args))) with
| ([], _64_1863) -> begin
args
end
| (_64_1866, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Not enough arguments to type"), ((FStar_Ident.range_of_lid lid))))))
end
| (((_64_1871, Some (FStar_Syntax_Syntax.Implicit (_64_1873))))::tps', ((_64_1880, Some (FStar_Syntax_Syntax.Implicit (_64_1882))))::args') -> begin
(arguments tps' args')
end
| (((_64_1890, Some (FStar_Syntax_Syntax.Implicit (_64_1892))))::tps', ((_64_1900, _64_1902))::_64_1898) -> begin
(arguments tps' args)
end
| (((_64_1909, _64_1911))::_64_1907, ((a, Some (FStar_Syntax_Syntax.Implicit (_64_1918))))::_64_1915) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected implicit annotation on argument"), (a.FStar_Syntax_Syntax.pos)))))
end
| (((_64_1926, _64_1928))::tps', ((_64_1933, _64_1935))::args') -> begin
(arguments tps' args')
end))
in (arguments inductive_tps args0))
in (
# 1113 "FStar.Parser.ToSyntax.fst"
let indices = (FStar_All.pipe_right args (FStar_List.map (fun _64_1940 -> (let _157_743 = (FStar_Syntax_Syntax.new_bv (Some (p)) FStar_Syntax_Syntax.tun)
in (FStar_All.pipe_right _157_743 FStar_Syntax_Syntax.mk_binder)))))
in (
# 1114 "FStar.Parser.ToSyntax.fst"
let arg_typ = (let _157_748 = (let _157_744 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _157_744))
in (let _157_747 = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _64_1945 -> (match (_64_1945) with
| (x, imp) -> begin
(let _157_746 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_157_746), (imp)))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app _157_748 _157_747 None p)))
in (
# 1116 "FStar.Parser.ToSyntax.fst"
let arg_binder = if (not (refine_domain)) then begin
(let _157_749 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder _157_749))
end else begin
(
# 1119 "FStar.Parser.ToSyntax.fst"
let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (
# 1120 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p)) arg_typ)
in (let _157_758 = (
# 1121 "FStar.Parser.ToSyntax.fst"
let _64_1949 = (projectee arg_typ)
in (let _157_757 = (let _157_756 = (let _157_755 = (let _157_754 = (let _157_750 = (FStar_Ident.set_lid_range disc_name p)
in (FStar_Syntax_Syntax.fvar _157_750 FStar_Syntax_Syntax.Delta_equational None))
in (let _157_753 = (let _157_752 = (let _157_751 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _157_751))
in (_157_752)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _157_754 _157_753 None p)))
in (FStar_Syntax_Util.b2t _157_755))
in (FStar_Syntax_Util.refine x _157_756))
in {FStar_Syntax_Syntax.ppname = _64_1949.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_1949.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _157_757}))
in (FStar_Syntax_Syntax.mk_binder _157_758))))
end
in ((arg_binder), (indices))))))
end))
in (match (_64_1954) with
| (arg_binder, indices) -> begin
(
# 1125 "FStar.Parser.ToSyntax.fst"
let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder))
in (
# 1126 "FStar.Parser.ToSyntax.fst"
let imp_binders = (let _157_760 = (FStar_All.pipe_right indices (FStar_List.map (fun _64_1959 -> (match (_64_1959) with
| (x, _64_1958) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (FStar_List.append imp_tps _157_760))
in (
# 1127 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (
# 1129 "FStar.Parser.ToSyntax.fst"
let arg = (FStar_Syntax_Util.arg_of_non_null_binder arg_binder)
in (
# 1131 "FStar.Parser.ToSyntax.fst"
let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _64_1967 -> (match (_64_1967) with
| (a, _64_1966) -> begin
(
# 1132 "FStar.Parser.ToSyntax.fst"
let _64_1971 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (_64_1971) with
| (field_name, _64_1970) -> begin
(
# 1133 "FStar.Parser.ToSyntax.fst"
let proj = (let _157_764 = (let _157_763 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.fv_to_tm _157_763))
in (FStar_Syntax_Syntax.mk_Tm_app _157_764 ((arg)::[]) None p))
in FStar_Syntax_Syntax.NT (((a), (proj))))
end))
end))))
in (
# 1136 "FStar.Parser.ToSyntax.fst"
let ntps = (FStar_List.length tps)
in (
# 1137 "FStar.Parser.ToSyntax.fst"
let all_params = (FStar_List.append imp_tps fields)
in (let _157_800 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _64_1980 -> (match (_64_1980) with
| (x, _64_1979) -> begin
(
# 1140 "FStar.Parser.ToSyntax.fst"
let _64_1984 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_64_1984) with
| (field_name, _64_1983) -> begin
(
# 1141 "FStar.Parser.ToSyntax.fst"
let t = (let _157_768 = (let _157_767 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total _157_767))
in (FStar_Syntax_Util.arrow binders _157_768))
in (
# 1142 "FStar.Parser.ToSyntax.fst"
let only_decl = (((let _157_769 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _157_769)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _157_771 = (let _157_770 = (FStar_Parser_Env.current_module env)
in _157_770.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _157_771)))
in (
# 1146 "FStar.Parser.ToSyntax.fst"
let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (
# 1147 "FStar.Parser.ToSyntax.fst"
let quals = (fun q -> if only_decl then begin
(FStar_Syntax_Syntax.Assumption)::q
end else begin
q
end)
in (
# 1148 "FStar.Parser.ToSyntax.fst"
let quals = (quals ((FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals))
in (
# 1149 "FStar.Parser.ToSyntax.fst"
let decl = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), ([]), (t), (quals), ((FStar_Ident.range_of_lid field_name))))
in if only_decl then begin
(decl)::[]
end else begin
(
# 1152 "FStar.Parser.ToSyntax.fst"
let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (
# 1153 "FStar.Parser.ToSyntax.fst"
let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _64_1996 -> (match (_64_1996) with
| (x, imp) -> begin
(
# 1154 "FStar.Parser.ToSyntax.fst"
let b = (FStar_Syntax_Syntax.is_implicit imp)
in if ((i + ntps) = j) then begin
(let _157_776 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in ((_157_776), (b)))
end else begin
if (b && (j < ntps)) then begin
(let _157_780 = (let _157_779 = (let _157_778 = (let _157_777 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in ((_157_777), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (_157_778))
in (pos _157_779))
in ((_157_780), (b)))
end else begin
(let _157_783 = (let _157_782 = (let _157_781 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_157_781))
in (pos _157_782))
in ((_157_783), (b)))
end
end)
end))))
in (
# 1160 "FStar.Parser.ToSyntax.fst"
let pat = (let _157_788 = (let _157_786 = (let _157_785 = (let _157_784 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in ((_157_784), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (_157_785))
in (FStar_All.pipe_right _157_786 pos))
in (let _157_787 = (FStar_Syntax_Syntax.bv_to_name projection)
in ((_157_788), (None), (_157_787))))
in (
# 1161 "FStar.Parser.ToSyntax.fst"
let body = (let _157_792 = (let _157_791 = (let _157_790 = (let _157_789 = (FStar_Syntax_Util.branch pat)
in (_157_789)::[])
in ((arg_exp), (_157_790)))
in FStar_Syntax_Syntax.Tm_match (_157_791))
in (FStar_Syntax_Syntax.mk _157_792 None p))
in (
# 1162 "FStar.Parser.ToSyntax.fst"
let imp = (no_annot_abs binders body)
in (
# 1163 "FStar.Parser.ToSyntax.fst"
let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end else begin
FStar_Syntax_Syntax.Delta_equational
end
in (
# 1166 "FStar.Parser.ToSyntax.fst"
let lb = (let _157_794 = (let _157_793 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (_157_793))
in {FStar_Syntax_Syntax.lbname = _157_794; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = imp})
in (
# 1171 "FStar.Parser.ToSyntax.fst"
let impl = (let _157_799 = (let _157_798 = (let _157_797 = (let _157_796 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _157_796 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_157_797)::[])
in ((((false), ((lb)::[]))), (p), (_157_798), (quals)))
in FStar_Syntax_Syntax.Sig_let (_157_799))
in if no_decl then begin
(impl)::[]
end else begin
(decl)::(impl)::[]
end))))))))
end))))))
end))
end))))
in (FStar_All.pipe_right _157_800 FStar_List.flatten)))))))))
end)))))))

# 1172 "FStar.Parser.ToSyntax.fst"
let mk_data_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env _64_2010 -> (match (_64_2010) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _64_2013, t, l, n, quals, _64_2019, _64_2021) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(
# 1177 "FStar.Parser.ToSyntax.fst"
let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _64_11 -> (match (_64_11) with
| FStar_Syntax_Syntax.RecordConstructor (_64_2026) -> begin
true
end
| _64_2029 -> begin
false
end)))) then begin
false
end else begin
(match ((FStar_Parser_Env.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > 1)
end
| _64_2033 -> begin
true
end)
end
in (
# 1183 "FStar.Parser.ToSyntax.fst"
let _64_2037 = (FStar_Syntax_Util.arrow_formals t)
in (match (_64_2037) with
| (formals, cod) -> begin
(match (formals) with
| [] -> begin
[]
end
| _64_2040 -> begin
(
# 1187 "FStar.Parser.ToSyntax.fst"
let fv_qual = (match ((FStar_Util.find_map quals (fun _64_12 -> (match (_64_12) with
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| _64_2045 -> begin
None
end)))) with
| None -> begin
FStar_Syntax_Syntax.Data_ctor
end
| Some (q) -> begin
q
end)
in (
# 1190 "FStar.Parser.ToSyntax.fst"
let iquals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract iquals) then begin
(FStar_Syntax_Syntax.Private)::iquals
end else begin
iquals
end
in (
# 1193 "FStar.Parser.ToSyntax.fst"
let _64_2053 = (FStar_Util.first_N n formals)
in (match (_64_2053) with
| (tps, rest) -> begin
(mk_indexed_projectors iquals fv_qual refine_domain env l lid inductive_tps tps rest cod)
end))))
end)
end)))
end
| _64_2055 -> begin
[]
end)
end))

# 1197 "FStar.Parser.ToSyntax.fst"
let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (
# 1200 "FStar.Parser.ToSyntax.fst"
let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _157_825 = (FStar_Syntax_Util.incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (_157_825))
end else begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end
in (
# 1203 "FStar.Parser.ToSyntax.fst"
let lb = (let _157_830 = (let _157_826 = (FStar_Syntax_Syntax.lid_as_fv lid dd None)
in FStar_Util.Inr (_157_826))
in (let _157_829 = (let _157_827 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars _157_827))
in (let _157_828 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = _157_830; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = _157_829; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _157_828})))
in FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (rng), (lids), (quals))))))

# 1210 "FStar.Parser.ToSyntax.fst"
let rec desugar_tycon : FStar_Parser_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (
# 1213 "FStar.Parser.ToSyntax.fst"
let tycon_id = (fun _64_13 -> (match (_64_13) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (
# 1218 "FStar.Parser.ToSyntax.fst"
let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _157_844 = (let _157_843 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_157_843))
in (FStar_Parser_AST.mk_term _157_844 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| (FStar_Parser_AST.TAnnotated (a, _)) | (FStar_Parser_AST.TVariable (a)) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar (a)) a.FStar_Ident.idRange FStar_Parser_AST.Type)
end
| FStar_Parser_AST.NoName (t) -> begin
t
end))
in (
# 1224 "FStar.Parser.ToSyntax.fst"
let tot = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) rng FStar_Parser_AST.Expr)
in (
# 1225 "FStar.Parser.ToSyntax.fst"
let with_constructor_effect = (fun t -> (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((tot), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level))
in (
# 1226 "FStar.Parser.ToSyntax.fst"
let apply_binders = (fun t binders -> (
# 1227 "FStar.Parser.ToSyntax.fst"
let imp_of_aqual = (fun b -> (match (b.FStar_Parser_AST.aqual) with
| Some (FStar_Parser_AST.Implicit) -> begin
FStar_Parser_AST.Hash
end
| _64_2130 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _157_857 = (let _157_856 = (let _157_855 = (binder_to_term b)
in ((out), (_157_855), ((imp_of_aqual b))))
in FStar_Parser_AST.App (_157_856))
in (FStar_Parser_AST.mk_term _157_857 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (
# 1232 "FStar.Parser.ToSyntax.fst"
let tycon_record_as_variant = (fun _64_14 -> (match (_64_14) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(
# 1234 "FStar.Parser.ToSyntax.fst"
let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (
# 1235 "FStar.Parser.ToSyntax.fst"
let mfields = (FStar_List.map (fun _64_2145 -> (match (_64_2145) with
| (x, t, _64_2144) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Syntax_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (
# 1236 "FStar.Parser.ToSyntax.fst"
let result = (let _157_863 = (let _157_862 = (let _157_861 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_157_861))
in (FStar_Parser_AST.mk_term _157_862 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _157_863 parms))
in (
# 1237 "FStar.Parser.ToSyntax.fst"
let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _157_865 = (FStar_All.pipe_right fields (FStar_List.map (fun _64_2154 -> (match (_64_2154) with
| (x, _64_2151, _64_2153) -> begin
(FStar_Parser_Env.qualify env x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (Some (constrTyp)), (None), (false)))::[])))), (_157_865)))))))
end
| _64_2156 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1241 "FStar.Parser.ToSyntax.fst"
let desugar_abstract_tc = (fun quals _env mutuals _64_15 -> (match (_64_15) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(
# 1243 "FStar.Parser.ToSyntax.fst"
let _64_2170 = (typars_of_binders _env binders)
in (match (_64_2170) with
| (_env', typars) -> begin
(
# 1244 "FStar.Parser.ToSyntax.fst"
let k = (match (kopt) with
| None -> begin
FStar_Syntax_Util.ktype
end
| Some (k) -> begin
(desugar_term _env' k)
end)
in (
# 1247 "FStar.Parser.ToSyntax.fst"
let tconstr = (let _157_876 = (let _157_875 = (let _157_874 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_157_874))
in (FStar_Parser_AST.mk_term _157_875 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _157_876 binders))
in (
# 1248 "FStar.Parser.ToSyntax.fst"
let qlid = (FStar_Parser_Env.qualify _env id)
in (
# 1249 "FStar.Parser.ToSyntax.fst"
let typars = (FStar_Syntax_Subst.close_binders typars)
in (
# 1250 "FStar.Parser.ToSyntax.fst"
let k = (FStar_Syntax_Subst.close typars k)
in (
# 1251 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_inductive_typ (((qlid), ([]), (typars), (k), (mutuals), ([]), (quals), (rng)))
in (
# 1252 "FStar.Parser.ToSyntax.fst"
let _env = (FStar_Parser_Env.push_top_level_rec_binding _env id FStar_Syntax_Syntax.Delta_constant)
in (
# 1253 "FStar.Parser.ToSyntax.fst"
let _env2 = (FStar_Parser_Env.push_top_level_rec_binding _env' id FStar_Syntax_Syntax.Delta_constant)
in ((_env), (_env2), (se), (tconstr))))))))))
end))
end
| _64_2183 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (
# 1256 "FStar.Parser.ToSyntax.fst"
let push_tparams = (fun env bs -> (
# 1257 "FStar.Parser.ToSyntax.fst"
let _64_2198 = (FStar_List.fold_left (fun _64_2189 _64_2192 -> (match (((_64_2189), (_64_2192))) with
| ((env, tps), (x, imp)) -> begin
(
# 1258 "FStar.Parser.ToSyntax.fst"
let _64_2195 = (FStar_Parser_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (_64_2195) with
| (env, y) -> begin
((env), ((((y), (imp)))::tps))
end))
end)) ((env), ([])) bs)
in (match (_64_2198) with
| (env, bs) -> begin
((env), ((FStar_List.rev bs)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id, bs, kopt))::[] -> begin
(
# 1263 "FStar.Parser.ToSyntax.fst"
let kopt = (match (kopt) with
| None -> begin
(let _157_883 = (tm_type_z id.FStar_Ident.idRange)
in Some (_157_883))
end
| _64_2207 -> begin
kopt
end)
in (
# 1266 "FStar.Parser.ToSyntax.fst"
let tc = FStar_Parser_AST.TyconAbstract (((id), (bs), (kopt)))
in (
# 1267 "FStar.Parser.ToSyntax.fst"
let _64_2217 = (desugar_abstract_tc quals env [] tc)
in (match (_64_2217) with
| (_64_2211, _64_2213, se, _64_2216) -> begin
(
# 1268 "FStar.Parser.ToSyntax.fst"
let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _64_2220, typars, k, [], [], quals, rng) -> begin
(
# 1270 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
quals
end else begin
(
# 1272 "FStar.Parser.ToSyntax.fst"
let _64_2229 = (let _157_885 = (FStar_Range.string_of_range rng)
in (let _157_884 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" _157_885 _157_884)))
in (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals)
end
in (
# 1275 "FStar.Parser.ToSyntax.fst"
let t = (match (typars) with
| [] -> begin
k
end
| _64_2234 -> begin
(let _157_888 = (let _157_887 = (let _157_886 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (_157_886)))
in FStar_Syntax_Syntax.Tm_arrow (_157_887))
in (FStar_Syntax_Syntax.mk _157_888 None rng))
end)
in FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t), (quals), (rng)))))
end
| _64_2237 -> begin
se
end)
in (
# 1280 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in ((env), ((se)::[]))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(
# 1285 "FStar.Parser.ToSyntax.fst"
let _64_2249 = (typars_of_binders env binders)
in (match (_64_2249) with
| (env', typars) -> begin
(
# 1286 "FStar.Parser.ToSyntax.fst"
let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _64_16 -> (match (_64_16) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| _64_2254 -> begin
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
# 1292 "FStar.Parser.ToSyntax.fst"
let t0 = t
in (
# 1293 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _64_17 -> (match (_64_17) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| _64_2262 -> begin
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
# 1298 "FStar.Parser.ToSyntax.fst"
let se = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Effect)) then begin
(
# 1300 "FStar.Parser.ToSyntax.fst"
let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (
# 1301 "FStar.Parser.ToSyntax.fst"
let typars = (FStar_Syntax_Subst.close_binders typars)
in (
# 1302 "FStar.Parser.ToSyntax.fst"
let c = (FStar_Syntax_Subst.close_comp typars c)
in (let _157_894 = (let _157_893 = (FStar_Parser_Env.qualify env id)
in (let _157_892 = (FStar_All.pipe_right quals (FStar_List.filter (fun _64_18 -> (match (_64_18) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| _64_2270 -> begin
true
end))))
in ((_157_893), ([]), (typars), (c), (_157_892), (rng))))
in FStar_Syntax_Syntax.Sig_effect_abbrev (_157_894)))))
end else begin
(
# 1304 "FStar.Parser.ToSyntax.fst"
let t = (desugar_typ env' t)
in (
# 1305 "FStar.Parser.ToSyntax.fst"
let nm = (FStar_Parser_Env.qualify env id)
in (mk_typ_abbrev nm [] typars k t ((nm)::[]) quals rng)))
end
in (
# 1308 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in ((env), ((se)::[])))))))
end))
end
| (FStar_Parser_AST.TyconRecord (_64_2276))::[] -> begin
(
# 1312 "FStar.Parser.ToSyntax.fst"
let trec = (FStar_List.hd tcs)
in (
# 1313 "FStar.Parser.ToSyntax.fst"
let _64_2282 = (tycon_record_as_variant trec)
in (match (_64_2282) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| (_64_2286)::_64_2284 -> begin
(
# 1317 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1318 "FStar.Parser.ToSyntax.fst"
let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_Env.qualify env) (tycon_id x))) tcs)
in (
# 1319 "FStar.Parser.ToSyntax.fst"
let rec collect_tcs = (fun quals et tc -> (
# 1320 "FStar.Parser.ToSyntax.fst"
let _64_2297 = et
in (match (_64_2297) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_64_2299) -> begin
(
# 1323 "FStar.Parser.ToSyntax.fst"
let trec = tc
in (
# 1324 "FStar.Parser.ToSyntax.fst"
let _64_2304 = (tycon_record_as_variant trec)
in (match (_64_2304) with
| (t, fs) -> begin
(collect_tcs ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((env), (tcs)) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(
# 1327 "FStar.Parser.ToSyntax.fst"
let _64_2316 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_64_2316) with
| (env, _64_2313, se, tconstr) -> begin
((env), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals))))::tcs))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(
# 1330 "FStar.Parser.ToSyntax.fst"
let _64_2328 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_64_2328) with
| (env, _64_2325, se, tconstr) -> begin
((env), ((FStar_Util.Inr (((se), (t), (quals))))::tcs))
end))
end
| _64_2330 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (
# 1333 "FStar.Parser.ToSyntax.fst"
let _64_2333 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (_64_2333) with
| (env, tcs) -> begin
(
# 1334 "FStar.Parser.ToSyntax.fst"
let tcs = (FStar_List.rev tcs)
in (
# 1335 "FStar.Parser.ToSyntax.fst"
let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _64_20 -> (match (_64_20) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, _64_2341, _64_2343, _64_2345, _64_2347), t, quals) -> begin
(
# 1337 "FStar.Parser.ToSyntax.fst"
let _64_2357 = (push_tparams env tpars)
in (match (_64_2357) with
| (env_tps, _64_2356) -> begin
(
# 1338 "FStar.Parser.ToSyntax.fst"
let t = (desugar_term env_tps t)
in (let _157_904 = (let _157_903 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in (([]), (_157_903)))
in (_157_904)::[]))
end))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, _64_2365, tags, _64_2368), constrs, tconstr, quals) -> begin
(
# 1342 "FStar.Parser.ToSyntax.fst"
let tycon = ((tname), (tpars), (k))
in (
# 1343 "FStar.Parser.ToSyntax.fst"
let _64_2379 = (push_tparams env tpars)
in (match (_64_2379) with
| (env_tps, tps) -> begin
(
# 1344 "FStar.Parser.ToSyntax.fst"
let data_tpars = (FStar_List.map (fun _64_2383 -> (match (_64_2383) with
| (x, _64_2382) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (
# 1345 "FStar.Parser.ToSyntax.fst"
let _64_2409 = (let _157_916 = (FStar_All.pipe_right constrs (FStar_List.map (fun _64_2390 -> (match (_64_2390) with
| (id, topt, _64_2388, of_notation) -> begin
(
# 1347 "FStar.Parser.ToSyntax.fst"
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
# 1355 "FStar.Parser.ToSyntax.fst"
let t = (let _157_908 = (FStar_Parser_Env.default_total env_tps)
in (let _157_907 = (close env_tps t)
in (desugar_term _157_908 _157_907)))
in (
# 1356 "FStar.Parser.ToSyntax.fst"
let name = (FStar_Parser_Env.qualify env id)
in (
# 1357 "FStar.Parser.ToSyntax.fst"
let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _64_19 -> (match (_64_19) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| _64_2404 -> begin
[]
end))))
in (
# 1360 "FStar.Parser.ToSyntax.fst"
let ntps = (FStar_List.length data_tpars)
in (let _157_915 = (let _157_914 = (let _157_913 = (let _157_912 = (let _157_911 = (let _157_910 = (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total _157_910))
in (FStar_Syntax_Util.arrow data_tpars _157_911))
in ((name), (univs), (_157_912), (tname), (ntps), (quals), (mutuals), (rng)))
in FStar_Syntax_Syntax.Sig_datacon (_157_913))
in ((tps), (_157_914)))
in ((name), (_157_915))))))))
end))))
in (FStar_All.pipe_left FStar_List.split _157_916))
in (match (_64_2409) with
| (constrNames, constrs) -> begin
((([]), (FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs), (tpars), (k), (mutuals), (constrNames), (tags), (rng))))))::constrs
end)))
end)))
end
| _64_2411 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1365 "FStar.Parser.ToSyntax.fst"
let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (
# 1366 "FStar.Parser.ToSyntax.fst"
let bundle = (let _157_918 = (let _157_917 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in ((sigelts), (quals), (_157_917), (rng)))
in FStar_Syntax_Syntax.Sig_bundle (_157_918))
in (
# 1367 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 bundle)
in (
# 1368 "FStar.Parser.ToSyntax.fst"
let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projectors quals env)))
in (
# 1369 "FStar.Parser.ToSyntax.fst"
let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _64_21 -> (match (_64_21) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, _64_2420, tps, k, _64_2424, constrs, quals, _64_2428) when ((FStar_List.length constrs) > 1) -> begin
(
# 1371 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract quals) then begin
(FStar_Syntax_Syntax.Private)::quals
end else begin
quals
end
in (mk_data_discriminators quals env tname tps k constrs))
end
| _64_2433 -> begin
[]
end))))
in (
# 1376 "FStar.Parser.ToSyntax.fst"
let ops = (FStar_List.append discs data_ops)
in (
# 1377 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env ops)
in ((env), ((FStar_List.append ((bundle)::[]) ops))))))))))))
end)))))
end
| [] -> begin
(FStar_All.failwith "impossible")
end))))))))))

# 1380 "FStar.Parser.ToSyntax.fst"
let desugar_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.binder Prims.list) = (fun env binders -> (
# 1383 "FStar.Parser.ToSyntax.fst"
let _64_2457 = (FStar_List.fold_left (fun _64_2442 b -> (match (_64_2442) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| (Some (a), k) -> begin
(
# 1386 "FStar.Parser.ToSyntax.fst"
let _64_2450 = (FStar_Parser_Env.push_bv env a)
in (match (_64_2450) with
| (env, a) -> begin
(let _157_927 = (let _157_926 = (FStar_Syntax_Syntax.mk_binder (
# 1387 "FStar.Parser.ToSyntax.fst"
let _64_2451 = a
in {FStar_Syntax_Syntax.ppname = _64_2451.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _64_2451.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (_157_926)::binders)
in ((env), (_157_927)))
end))
end
| _64_2454 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end)
end)) ((env), ([])) binders)
in (match (_64_2457) with
| (env, binders) -> begin
((env), ((FStar_List.rev binders)))
end)))

# 1390 "FStar.Parser.ToSyntax.fst"
let rec desugar_effect : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  Prims.bool  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_kind eff_decls actions for_free -> (
# 1393 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1394 "FStar.Parser.ToSyntax.fst"
let monad_env = (FStar_Parser_Env.enter_monad_scope env eff_name)
in (
# 1395 "FStar.Parser.ToSyntax.fst"
let _64_2471 = (desugar_binders monad_env eff_binders)
in (match (_64_2471) with
| (env, binders) -> begin
(
# 1396 "FStar.Parser.ToSyntax.fst"
let eff_k = (let _157_948 = (FStar_Parser_Env.default_total env)
in (desugar_term _157_948 eff_kind))
in (
# 1397 "FStar.Parser.ToSyntax.fst"
let _64_2482 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _64_2475 decl -> (match (_64_2475) with
| (env, out) -> begin
(
# 1398 "FStar.Parser.ToSyntax.fst"
let _64_2479 = (desugar_decl env decl)
in (match (_64_2479) with
| (env, ses) -> begin
(let _157_952 = (let _157_951 = (FStar_List.hd ses)
in (_157_951)::out)
in ((env), (_157_952)))
end))
end)) ((env), ([]))))
in (match (_64_2482) with
| (env, decls) -> begin
(
# 1400 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_Syntax_Subst.close_binders binders)
in (
# 1401 "FStar.Parser.ToSyntax.fst"
let actions = (FStar_All.pipe_right actions (FStar_List.map (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (_64_2486, ((FStar_Parser_AST.TyconAbbrev (name, _64_2489, _64_2491, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (_64_2497, ((def, _64_2504))::((cps_type, _64_2500))::[]); FStar_Parser_AST.range = _64_2495; FStar_Parser_AST.level = _64_2493}), _64_2513))::[]) when (not (for_free)) -> begin
(let _157_958 = (FStar_Parser_Env.qualify env name)
in (let _157_957 = (let _157_954 = (desugar_term env def)
in (FStar_Syntax_Subst.close binders _157_954))
in (let _157_956 = (let _157_955 = (desugar_typ env cps_type)
in (FStar_Syntax_Subst.close binders _157_955))
in {FStar_Syntax_Syntax.action_name = _157_958; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = _157_957; FStar_Syntax_Syntax.action_typ = _157_956})))
end
| FStar_Parser_AST.Tycon (_64_2519, ((FStar_Parser_AST.TyconAbbrev (name, _64_2522, _64_2524, defn), _64_2529))::[]) when for_free -> begin
(let _157_961 = (FStar_Parser_Env.qualify env name)
in (let _157_960 = (let _157_959 = (desugar_term env defn)
in (FStar_Syntax_Subst.close binders _157_959))
in {FStar_Syntax_Syntax.action_name = _157_961; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = _157_960; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
end
| _64_2535 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples)."), (d.FStar_Parser_AST.drange)))))
end))))
in (
# 1427 "FStar.Parser.ToSyntax.fst"
let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (
# 1428 "FStar.Parser.ToSyntax.fst"
let lookup = (fun s -> (
# 1429 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env (FStar_Ident.mk_ident ((s), (d.FStar_Parser_AST.drange))))
in (let _157_965 = (let _157_964 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) _157_964))
in (([]), (_157_965)))))
in (
# 1431 "FStar.Parser.ToSyntax.fst"
let mname = (FStar_Parser_Env.qualify env0 eff_name)
in (
# 1432 "FStar.Parser.ToSyntax.fst"
let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange) quals)
in (
# 1433 "FStar.Parser.ToSyntax.fst"
let se = if for_free then begin
(
# 1435 "FStar.Parser.ToSyntax.fst"
let dummy_tscheme = (let _157_966 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (([]), (_157_966)))
in (let _157_972 = (let _157_971 = (let _157_970 = (let _157_967 = (lookup "repr")
in (Prims.snd _157_967))
in (let _157_969 = (lookup "return")
in (let _157_968 = (lookup "bind")
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = _157_970; FStar_Syntax_Syntax.return_repr = _157_969; FStar_Syntax_Syntax.bind_repr = _157_968; FStar_Syntax_Syntax.actions = actions})))
in ((_157_971), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (_157_972)))
end else begin
(
# 1458 "FStar.Parser.ToSyntax.fst"
let rr = ((FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) || (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable)))
in (
# 1460 "FStar.Parser.ToSyntax.fst"
let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in (let _157_988 = (let _157_987 = (let _157_986 = (lookup "return_wp")
in (let _157_985 = (lookup "bind_wp")
in (let _157_984 = (lookup "if_then_else")
in (let _157_983 = (lookup "ite_wp")
in (let _157_982 = (lookup "stronger")
in (let _157_981 = (lookup "close_wp")
in (let _157_980 = (lookup "assert_p")
in (let _157_979 = (lookup "assume_p")
in (let _157_978 = (lookup "null_wp")
in (let _157_977 = (lookup "trivial")
in (let _157_976 = if rr then begin
(let _157_973 = (lookup "repr")
in (FStar_All.pipe_left Prims.snd _157_973))
end else begin
FStar_Syntax_Syntax.tun
end
in (let _157_975 = if rr then begin
(lookup "return")
end else begin
un_ts
end
in (let _157_974 = if rr then begin
(lookup "bind")
end else begin
un_ts
end
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = _157_986; FStar_Syntax_Syntax.bind_wp = _157_985; FStar_Syntax_Syntax.if_then_else = _157_984; FStar_Syntax_Syntax.ite_wp = _157_983; FStar_Syntax_Syntax.stronger = _157_982; FStar_Syntax_Syntax.close_wp = _157_981; FStar_Syntax_Syntax.assert_p = _157_980; FStar_Syntax_Syntax.assume_p = _157_979; FStar_Syntax_Syntax.null_wp = _157_978; FStar_Syntax_Syntax.trivial = _157_977; FStar_Syntax_Syntax.repr = _157_976; FStar_Syntax_Syntax.return_repr = _157_975; FStar_Syntax_Syntax.bind_repr = _157_974; FStar_Syntax_Syntax.actions = actions})))))))))))))
in ((_157_987), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_new_effect (_157_988))))
end
in (
# 1483 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 se)
in (
# 1484 "FStar.Parser.ToSyntax.fst"
let env = (FStar_All.pipe_right actions (FStar_List.fold_left (fun env a -> (let _157_991 = (FStar_Syntax_Util.action_as_lb a)
in (FStar_Parser_Env.push_sigelt env _157_991))) env))
in (
# 1487 "FStar.Parser.ToSyntax.fst"
let env = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable)) then begin
(
# 1489 "FStar.Parser.ToSyntax.fst"
let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_Parser_Env.qualify monad_env))
in (
# 1490 "FStar.Parser.ToSyntax.fst"
let refl_decl = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable)::[]), (d.FStar_Parser_AST.drange)))
in (FStar_Parser_Env.push_sigelt env refl_decl)))
end else begin
env
end
in ((env), ((se)::[]))))))))))))
end)))
end)))))
and desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (
# 1496 "FStar.Parser.ToSyntax.fst"
let trans_qual = (trans_qual d.FStar_Parser_AST.drange)
in (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(
# 1499 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_pragma ((((trans_pragma p)), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[])))
end
| FStar_Parser_AST.Fsdoc (_64_2561) -> begin
((env), ([]))
end
| FStar_Parser_AST.TopLevelModule (_64_2564) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Multiple modules in a file are no longer supported"), (d.FStar_Parser_AST.drange)))))
end
| FStar_Parser_AST.Open (lid) -> begin
(
# 1508 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_namespace env lid)
in ((env), ([])))
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(let _157_995 = (FStar_Parser_Env.push_module_abbrev env x l)
in ((_157_995), ([])))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(
# 1515 "FStar.Parser.ToSyntax.fst"
let tcs = (FStar_List.map (fun _64_2580 -> (match (_64_2580) with
| (x, _64_2579) -> begin
x
end)) tcs)
in (let _157_997 = (FStar_List.map trans_qual qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _157_997 tcs)))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _157_999 = (let _157_998 = (desugar_term_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Syntax_Subst.compress _157_998))
in _157_999.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let (lbs, _64_2589) -> begin
(
# 1521 "FStar.Parser.ToSyntax.fst"
let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (
# 1522 "FStar.Parser.ToSyntax.fst"
let quals = (match (quals) with
| (_64_2597)::_64_2595 -> begin
(FStar_List.map trans_qual quals)
end
| _64_2600 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _64_22 -> (match (_64_22) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (_64_2611); FStar_Syntax_Syntax.lbunivs = _64_2609; FStar_Syntax_Syntax.lbtyp = _64_2607; FStar_Syntax_Syntax.lbeff = _64_2605; FStar_Syntax_Syntax.lbdef = _64_2603} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _64_2621; FStar_Syntax_Syntax.lbtyp = _64_2619; FStar_Syntax_Syntax.lbeff = _64_2617; FStar_Syntax_Syntax.lbdef = _64_2615} -> begin
(FStar_Parser_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (
# 1527 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right lets (FStar_Util.for_some (fun _64_2629 -> (match (_64_2629) with
| (_64_2627, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end)))) then begin
(FStar_Syntax_Syntax.Logic)::quals
end else begin
quals
end
in (
# 1531 "FStar.Parser.ToSyntax.fst"
let lbs = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _157_1004 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 1533 "FStar.Parser.ToSyntax.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 1534 "FStar.Parser.ToSyntax.fst"
let _64_2633 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((
# 1534 "FStar.Parser.ToSyntax.fst"
let _64_2635 = fv
in {FStar_Syntax_Syntax.fv_name = _64_2635.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = _64_2635.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = _64_2633.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _64_2633.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _64_2633.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _64_2633.FStar_Syntax_Syntax.lbdef})))))
in (((Prims.fst lbs)), (_157_1004)))
end else begin
lbs
end
in (
# 1536 "FStar.Parser.ToSyntax.fst"
let s = (let _157_1007 = (let _157_1006 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in ((lbs), (d.FStar_Parser_AST.drange), (_157_1006), (quals)))
in FStar_Syntax_Syntax.Sig_let (_157_1007))
in (
# 1537 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env s)
in ((env), ((s)::[]))))))))
end
| _64_2642 -> begin
(FStar_All.failwith "Desugaring a let did not produce a let")
end)
end
| FStar_Parser_AST.Main (t) -> begin
(
# 1543 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env t)
in (
# 1544 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_main (((e), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[]))))
end
| FStar_Parser_AST.Assume (atag, id, t) -> begin
(
# 1548 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env t)
in (let _157_1011 = (let _157_1010 = (let _157_1009 = (let _157_1008 = (FStar_Parser_Env.qualify env id)
in ((_157_1008), (f), ((FStar_Syntax_Syntax.Assumption)::[]), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_assume (_157_1009))
in (_157_1010)::[])
in ((env), (_157_1011))))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(
# 1552 "FStar.Parser.ToSyntax.fst"
let t = (let _157_1012 = (close_fun env t)
in (desugar_term env _157_1012))
in (
# 1553 "FStar.Parser.ToSyntax.fst"
let quals = if (env.FStar_Parser_Env.iface && env.FStar_Parser_Env.admitted_iface) then begin
(FStar_Parser_AST.Assumption)::quals
end else begin
quals
end
in (
# 1554 "FStar.Parser.ToSyntax.fst"
let se = (let _157_1015 = (let _157_1014 = (FStar_Parser_Env.qualify env id)
in (let _157_1013 = (FStar_List.map trans_qual quals)
in ((_157_1014), ([]), (t), (_157_1013), (d.FStar_Parser_AST.drange))))
in FStar_Syntax_Syntax.Sig_declare_typ (_157_1015))
in (
# 1555 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in ((env), ((se)::[]))))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(
# 1559 "FStar.Parser.ToSyntax.fst"
let _64_2669 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (match (_64_2669) with
| (t, _64_2668) -> begin
(
# 1560 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env id)
in (
# 1561 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_datacon (((l), ([]), (t), (FStar_Syntax_Const.exn_lid), (0), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((FStar_Syntax_Const.exn_lid)::[]), (d.FStar_Parser_AST.drange)))
in (
# 1562 "FStar.Parser.ToSyntax.fst"
let se' = FStar_Syntax_Syntax.Sig_bundle ((((se)::[]), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((l)::[]), (d.FStar_Parser_AST.drange)))
in (
# 1563 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se')
in (
# 1564 "FStar.Parser.ToSyntax.fst"
let data_ops = (mk_data_projectors [] env (([]), (se)))
in (
# 1565 "FStar.Parser.ToSyntax.fst"
let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (
# 1566 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in ((env), ((FStar_List.append ((se')::discs) data_ops))))))))))
end))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(
# 1570 "FStar.Parser.ToSyntax.fst"
let t = (desugar_term env term)
in (
# 1571 "FStar.Parser.ToSyntax.fst"
let t = (let _157_1020 = (let _157_1016 = (FStar_Syntax_Syntax.null_binder t)
in (_157_1016)::[])
in (let _157_1019 = (let _157_1018 = (let _157_1017 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (Prims.fst _157_1017))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _157_1018))
in (FStar_Syntax_Util.arrow _157_1020 _157_1019)))
in (
# 1572 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env id)
in (
# 1573 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_datacon (((l), ([]), (t), (FStar_Syntax_Const.exn_lid), (0), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((FStar_Syntax_Const.exn_lid)::[]), (d.FStar_Parser_AST.drange)))
in (
# 1574 "FStar.Parser.ToSyntax.fst"
let se' = FStar_Syntax_Syntax.Sig_bundle ((((se)::[]), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((l)::[]), (d.FStar_Parser_AST.drange)))
in (
# 1575 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se')
in (
# 1576 "FStar.Parser.ToSyntax.fst"
let data_ops = (mk_data_projectors [] env (([]), (se)))
in (
# 1577 "FStar.Parser.ToSyntax.fst"
let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (
# 1578 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in ((env), ((FStar_List.append ((se')::discs) data_ops))))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(
# 1582 "FStar.Parser.ToSyntax.fst"
let _64_2698 = (desugar_binders env binders)
in (match (_64_2698) with
| (env_k, binders) -> begin
(
# 1583 "FStar.Parser.ToSyntax.fst"
let k = (desugar_term env_k k)
in (
# 1584 "FStar.Parser.ToSyntax.fst"
let name = (FStar_Parser_Env.qualify env id)
in (
# 1585 "FStar.Parser.ToSyntax.fst"
let se = (mk_typ_abbrev name [] binders FStar_Syntax_Syntax.tun k ((name)::[]) [] d.FStar_Parser_AST.drange)
in (
# 1586 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in ((env), ((se)::[]))))))
end))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(
# 1590 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1591 "FStar.Parser.ToSyntax.fst"
let _64_2714 = (desugar_binders env eff_binders)
in (match (_64_2714) with
| (env, binders) -> begin
(
# 1592 "FStar.Parser.ToSyntax.fst"
let _64_2725 = (
# 1593 "FStar.Parser.ToSyntax.fst"
let _64_2717 = (head_and_args defn)
in (match (_64_2717) with
| (head, args) -> begin
(
# 1594 "FStar.Parser.ToSyntax.fst"
let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_defn env) l)
end
| _64_2721 -> begin
(let _157_1025 = (let _157_1024 = (let _157_1023 = (let _157_1022 = (let _157_1021 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat _157_1021 " not found"))
in (Prims.strcat "Effect " _157_1022))
in ((_157_1023), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_157_1024))
in (Prims.raise _157_1025))
end)
in (let _157_1026 = (desugar_args env args)
in ((ed), (_157_1026))))
end))
in (match (_64_2725) with
| (ed, args) -> begin
(
# 1598 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_Syntax_Subst.close_binders binders)
in (
# 1599 "FStar.Parser.ToSyntax.fst"
let sub = (fun _64_2731 -> (match (_64_2731) with
| (_64_2729, x) -> begin
(
# 1600 "FStar.Parser.ToSyntax.fst"
let _64_2734 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (_64_2734) with
| (edb, x) -> begin
(
# 1601 "FStar.Parser.ToSyntax.fst"
let _64_2735 = if ((FStar_List.length args) <> (FStar_List.length edb)) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected number of arguments to effect constructor"), (defn.FStar_Parser_AST.range)))))
end else begin
()
end
in (
# 1603 "FStar.Parser.ToSyntax.fst"
let s = (FStar_Syntax_Util.subst_of_list edb args)
in (let _157_1030 = (let _157_1029 = (FStar_Syntax_Subst.subst s x)
in (FStar_Syntax_Subst.close binders _157_1029))
in (([]), (_157_1030)))))
end))
end))
in (
# 1605 "FStar.Parser.ToSyntax.fst"
let ed = (let _157_1044 = (FStar_List.map trans_qual quals)
in (let _157_1043 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _157_1042 = (let _157_1031 = (sub (([]), (ed.FStar_Syntax_Syntax.signature)))
in (Prims.snd _157_1031))
in (let _157_1041 = (sub ed.FStar_Syntax_Syntax.ret_wp)
in (let _157_1040 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (let _157_1039 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (let _157_1038 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (let _157_1037 = (sub ed.FStar_Syntax_Syntax.stronger)
in (let _157_1036 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (let _157_1035 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (let _157_1034 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (let _157_1033 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (let _157_1032 = (sub ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _157_1044; FStar_Syntax_Syntax.mname = _157_1043; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = _157_1042; FStar_Syntax_Syntax.ret_wp = _157_1041; FStar_Syntax_Syntax.bind_wp = _157_1040; FStar_Syntax_Syntax.if_then_else = _157_1039; FStar_Syntax_Syntax.ite_wp = _157_1038; FStar_Syntax_Syntax.stronger = _157_1037; FStar_Syntax_Syntax.close_wp = _157_1036; FStar_Syntax_Syntax.assert_p = _157_1035; FStar_Syntax_Syntax.assume_p = _157_1034; FStar_Syntax_Syntax.null_wp = _157_1033; FStar_Syntax_Syntax.trivial = _157_1032; FStar_Syntax_Syntax.repr = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.return_repr = (([]), (FStar_Syntax_Syntax.tun)); FStar_Syntax_Syntax.bind_repr = (([]), (FStar_Syntax_Syntax.tun)); FStar_Syntax_Syntax.actions = []})))))))))))))
in (
# 1627 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect (((ed), (d.FStar_Parser_AST.drange)))
in (
# 1628 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 se)
in ((env), ((se)::[])))))))
end))
end)))
end
| FStar_Parser_AST.NewEffectForFree (_64_2742, FStar_Parser_AST.RedefineEffect (_64_2744)) -> begin
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
# 1641 "FStar.Parser.ToSyntax.fst"
let lookup = (fun l -> (match ((FStar_Parser_Env.try_lookup_effect_name env l)) with
| None -> begin
(let _157_1051 = (let _157_1050 = (let _157_1049 = (let _157_1048 = (let _157_1047 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat _157_1047 " not found"))
in (Prims.strcat "Effect name " _157_1048))
in ((_157_1049), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_157_1050))
in (Prims.raise _157_1051))
end
| Some (l) -> begin
l
end))
in (
# 1644 "FStar.Parser.ToSyntax.fst"
let src = (lookup l.FStar_Parser_AST.msource)
in (
# 1645 "FStar.Parser.ToSyntax.fst"
let dst = (lookup l.FStar_Parser_AST.mdest)
in (
# 1646 "FStar.Parser.ToSyntax.fst"
let _64_2785 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(let _157_1053 = (let _157_1052 = (desugar_term env t)
in (([]), (_157_1052)))
in ((_157_1053), (None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(let _157_1058 = (let _157_1054 = (desugar_term env wp)
in (([]), (_157_1054)))
in (let _157_1057 = (let _157_1056 = (let _157_1055 = (desugar_term env t)
in (([]), (_157_1055)))
in Some (_157_1056))
in ((_157_1058), (_157_1057))))
end)
in (match (_64_2785) with
| (lift_wp, lift) -> begin
(
# 1649 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect ((({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift}), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[])))
end)))))
end)))

# 1650 "FStar.Parser.ToSyntax.fst"
let desugar_decls : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _64_2791 d -> (match (_64_2791) with
| (env, sigelts) -> begin
(
# 1654 "FStar.Parser.ToSyntax.fst"
let _64_2795 = (desugar_decl env d)
in (match (_64_2795) with
| (env, se) -> begin
((env), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls))

# 1655 "FStar.Parser.ToSyntax.fst"
let open_prims_all : (FStar_Parser_AST.fsdoc Prims.option  ->  FStar_Parser_AST.decl) Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.all_lid)) FStar_Range.dummyRange))::[]

# 1659 "FStar.Parser.ToSyntax.fst"
let desugar_modul_common : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (
# 1665 "FStar.Parser.ToSyntax.fst"
let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod) -> begin
(FStar_Parser_Env.finish_module_or_interface env prev_mod)
end)
in (
# 1668 "FStar.Parser.ToSyntax.fst"
let _64_2818 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _157_1076 = (FStar_Parser_Env.prepare_module_or_interface true admitted env mname)
in ((_157_1076), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _157_1077 = (FStar_Parser_Env.prepare_module_or_interface false false env mname)
in ((_157_1077), (mname), (decls), (false)))
end)
in (match (_64_2818) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(
# 1673 "FStar.Parser.ToSyntax.fst"
let _64_2821 = (desugar_decls env decls)
in (match (_64_2821) with
| (env, sigelts) -> begin
(
# 1674 "FStar.Parser.ToSyntax.fst"
let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in ((env), (modul), (pop_when_done)))
end))
end))))

# 1680 "FStar.Parser.ToSyntax.fst"
let desugar_partial_modul : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (
# 1683 "FStar.Parser.ToSyntax.fst"
let m = if (FStar_Options.interactive_fsi ()) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface (((mname), (decls), (true)))
end
| FStar_Parser_AST.Interface (mname, _64_2832, _64_2834) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (
# 1690 "FStar.Parser.ToSyntax.fst"
let _64_2842 = (desugar_modul_common curmod env m)
in (match (_64_2842) with
| (x, y, _64_2841) -> begin
((x), (y))
end))))

# 1691 "FStar.Parser.ToSyntax.fst"
let desugar_modul : FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (
# 1694 "FStar.Parser.ToSyntax.fst"
let _64_2848 = (desugar_modul_common None env m)
in (match (_64_2848) with
| (env, modul, pop_when_done) -> begin
(
# 1695 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.finish_module_or_interface env modul)
in (
# 1696 "FStar.Parser.ToSyntax.fst"
let _64_2850 = if (FStar_Options.dump_module modul.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _157_1088 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _157_1088))
end else begin
()
end
in (let _157_1089 = if pop_when_done then begin
(FStar_Parser_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end else begin
env
end
in ((_157_1089), (modul)))))
end)))

# 1698 "FStar.Parser.ToSyntax.fst"
let desugar_file : FStar_Parser_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (
# 1701 "FStar.Parser.ToSyntax.fst"
let _64_2863 = (FStar_List.fold_left (fun _64_2856 m -> (match (_64_2856) with
| (env, mods) -> begin
(
# 1702 "FStar.Parser.ToSyntax.fst"
let _64_2860 = (desugar_modul env m)
in (match (_64_2860) with
| (env, m) -> begin
((env), ((m)::mods))
end))
end)) ((env), ([])) f)
in (match (_64_2863) with
| (env, mods) -> begin
((env), ((FStar_List.rev mods)))
end)))

# 1704 "FStar.Parser.ToSyntax.fst"
let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Parser_Env.env  ->  FStar_Parser_Env.env = (fun m en -> (
# 1707 "FStar.Parser.ToSyntax.fst"
let _64_2868 = (FStar_Parser_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (_64_2868) with
| (en, pop_when_done) -> begin
(
# 1708 "FStar.Parser.ToSyntax.fst"
let en = (FStar_List.fold_left FStar_Parser_Env.push_sigelt (
# 1708 "FStar.Parser.ToSyntax.fst"
let _64_2869 = en
in {FStar_Parser_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_Parser_Env.modules = _64_2869.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _64_2869.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _64_2869.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _64_2869.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _64_2869.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _64_2869.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _64_2869.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _64_2869.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _64_2869.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _64_2869.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = _64_2869.FStar_Parser_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (
# 1709 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_Env.export_interface m.FStar_Syntax_Syntax.name env)
end else begin
env
end))
end)))




