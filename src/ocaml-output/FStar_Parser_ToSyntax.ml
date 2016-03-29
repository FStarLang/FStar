
open Prims
# 40 "FStar.Parser.ToSyntax.fst"
let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _46_1 -> (match (_46_1) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Syntax_Syntax.Equality)
end
| _46_28 -> begin
None
end))

# 45 "FStar.Parser.ToSyntax.fst"
let trans_qual : FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun _46_2 -> (match (_46_2) with
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
| FStar_Parser_AST.DefaultEffect -> begin
FStar_Syntax_Syntax.DefaultEffect (None)
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
FStar_Syntax_Syntax.Unfoldable
end))

# 59 "FStar.Parser.ToSyntax.fst"
let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun _46_3 -> (match (_46_3) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end))

# 63 "FStar.Parser.ToSyntax.fst"
let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _46_4 -> (match (_46_4) with
| FStar_Parser_AST.Hash -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| _46_50 -> begin
None
end))

# 66 "FStar.Parser.ToSyntax.fst"
let arg_withimp_e = (fun imp t -> (t, (as_imp imp)))

# 68 "FStar.Parser.ToSyntax.fst"
let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
(t, Some (FStar_Syntax_Syntax.imp_tag))
end
| _46_57 -> begin
(t, None)
end))

# 73 "FStar.Parser.ToSyntax.fst"
let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_46_61) -> begin
true
end
| _46_64 -> begin
false
end)))))

# 78 "FStar.Parser.ToSyntax.fst"
let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _46_69 -> begin
t
end))

# 82 "FStar.Parser.ToSyntax.fst"
let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _125_21 = (let _125_20 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_125_20))
in (FStar_Parser_AST.mk_term _125_21 r FStar_Parser_AST.Kind)))

# 84 "FStar.Parser.ToSyntax.fst"
let rec delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (
# 85 "FStar.Parser.ToSyntax.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_46_74) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv.FStar_Syntax_Syntax.fv_delta
end
| (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_match (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
FStar_Syntax_Syntax.Delta_equational
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) -> begin
FStar_Syntax_Syntax.Delta_constant
end
| (FStar_Syntax_Syntax.Tm_uinst (t, _)) | (FStar_Syntax_Syntax.Tm_refine ({FStar_Syntax_Syntax.ppname = _; FStar_Syntax_Syntax.index = _; FStar_Syntax_Syntax.sort = t}, _)) | (FStar_Syntax_Syntax.Tm_meta (t, _)) | (FStar_Syntax_Syntax.Tm_ascribed (t, _, _)) | (FStar_Syntax_Syntax.Tm_app (t, _)) | (FStar_Syntax_Syntax.Tm_abs (_, t, _)) | (FStar_Syntax_Syntax.Tm_let (_, t)) -> begin
(delta_qualifier t)
end)))

# 105 "FStar.Parser.ToSyntax.fst"
let incr_delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (
# 106 "FStar.Parser.ToSyntax.fst"
let d = (delta_qualifier t)
in (
# 107 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun d -> (match (d) with
| FStar_Syntax_Syntax.Delta_equational -> begin
d
end
| FStar_Syntax_Syntax.Delta_constant -> begin
FStar_Syntax_Syntax.Delta_unfoldable (1)
end
| FStar_Syntax_Syntax.Delta_unfoldable (i) -> begin
FStar_Syntax_Syntax.Delta_unfoldable ((i + 1))
end
| FStar_Syntax_Syntax.Delta_abstract (d) -> begin
(aux d)
end))
in (aux d))))

# 114 "FStar.Parser.ToSyntax.fst"
let compile_op : Prims.int  ->  Prims.string  ->  Prims.string = (fun arity s -> (
# 115 "FStar.Parser.ToSyntax.fst"
let name_of_char = (fun _46_5 -> (match (_46_5) with
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
| _46_169 -> begin
"UNKNOWN"
end))
in (
# 134 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _125_41 = (let _125_39 = (FStar_Util.char_at s i)
in (name_of_char _125_39))
in (let _125_40 = (aux (i + 1))
in (_125_41)::_125_40))
end)
in (let _125_43 = (let _125_42 = (aux 0)
in (FStar_String.concat "_" _125_42))
in (Prims.strcat "op_" _125_43)))))

# 140 "FStar.Parser.ToSyntax.fst"
let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _125_53 = (let _125_52 = (let _125_51 = (let _125_50 = (compile_op n s)
in (_125_50, r))
in (FStar_Ident.mk_ident _125_51))
in (_125_52)::[])
in (FStar_All.pipe_right _125_53 FStar_Ident.lid_of_ids)))

# 142 "FStar.Parser.ToSyntax.fst"
let op_as_term : FStar_Parser_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.term Prims.option = (fun env arity rng s -> (
# 143 "FStar.Parser.ToSyntax.fst"
let r = (fun l dd -> (let _125_68 = (let _125_67 = (let _125_66 = (FStar_Ident.set_lid_range l rng)
in (FStar_Syntax_Syntax.lid_as_fv _125_66 dd None))
in (FStar_All.pipe_right _125_67 FStar_Syntax_Syntax.fv_to_tm))
in Some (_125_68)))
in (
# 144 "FStar.Parser.ToSyntax.fst"
let fallback = (fun _46_184 -> (match (()) with
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
| _46_212 -> begin
None
end)
end))
in (match ((let _125_71 = (compile_op_lid arity s rng)
in (FStar_Parser_Env.try_lookup_lid env _125_71))) with
| Some (t) -> begin
Some (t)
end
| _46_216 -> begin
(fallback ())
end))))

# 178 "FStar.Parser.ToSyntax.fst"
let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _125_78 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _125_78)))

# 182 "FStar.Parser.ToSyntax.fst"
let rec free_type_vars_b : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_46_225) -> begin
(env, [])
end
| FStar_Parser_AST.TVariable (x) -> begin
(
# 185 "FStar.Parser.ToSyntax.fst"
let _46_232 = (FStar_Parser_Env.push_bv env x)
in (match (_46_232) with
| (env, _46_231) -> begin
(env, (x)::[])
end))
end
| FStar_Parser_AST.Annotated (_46_234, term) -> begin
(let _125_85 = (free_type_vars env term)
in (env, _125_85))
end
| FStar_Parser_AST.TAnnotated (id, _46_240) -> begin
(
# 190 "FStar.Parser.ToSyntax.fst"
let _46_246 = (FStar_Parser_Env.push_bv env id)
in (match (_46_246) with
| (env, _46_245) -> begin
(env, [])
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _125_86 = (free_type_vars env t)
in (env, _125_86))
end))
and free_type_vars : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _125_89 = (unparen t)
in _125_89.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (_46_252) -> begin
(FStar_All.failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_Env.try_lookup_id env a)) with
| None -> begin
(a)::[]
end
| _46_258 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_46_288, ts) -> begin
(FStar_List.collect (fun _46_295 -> (match (_46_295) with
| (t, _46_294) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_46_297, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _46_304) -> begin
(let _125_92 = (free_type_vars env t1)
in (let _125_91 = (free_type_vars env t2)
in (FStar_List.append _125_92 _125_91)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(
# 220 "FStar.Parser.ToSyntax.fst"
let _46_313 = (free_type_vars_b env b)
in (match (_46_313) with
| (env, f) -> begin
(let _125_93 = (free_type_vars env t)
in (FStar_List.append f _125_93))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(
# 225 "FStar.Parser.ToSyntax.fst"
let _46_329 = (FStar_List.fold_left (fun _46_322 binder -> (match (_46_322) with
| (env, free) -> begin
(
# 226 "FStar.Parser.ToSyntax.fst"
let _46_326 = (free_type_vars_b env binder)
in (match (_46_326) with
| (env, f) -> begin
(env, (FStar_List.append f free))
end))
end)) (env, []) binders)
in (match (_46_329) with
| (env, free) -> begin
(let _125_96 = (free_type_vars env body)
in (FStar_List.append free _125_96))
end))
end
| FStar_Parser_AST.Project (t, _46_332) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
[]
end))

# 243 "FStar.Parser.ToSyntax.fst"
let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (
# 244 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun args t -> (match ((let _125_103 = (unparen t)
in _125_103.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _46_376 -> begin
(t, args)
end))
in (aux [] t)))

# 250 "FStar.Parser.ToSyntax.fst"
let close : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 251 "FStar.Parser.ToSyntax.fst"
let ftv = (let _125_108 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _125_108))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 254 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _125_112 = (let _125_111 = (let _125_110 = (tm_type x.FStar_Ident.idRange)
in (x, _125_110))
in FStar_Parser_AST.TAnnotated (_125_111))
in (FStar_Parser_AST.mk_binder _125_112 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 255 "FStar.Parser.ToSyntax.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))

# 258 "FStar.Parser.ToSyntax.fst"
let close_fun : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 259 "FStar.Parser.ToSyntax.fst"
let ftv = (let _125_117 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _125_117))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 262 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _125_121 = (let _125_120 = (let _125_119 = (tm_type x.FStar_Ident.idRange)
in (x, _125_119))
in FStar_Parser_AST.TAnnotated (_125_120))
in (FStar_Parser_AST.mk_binder _125_121 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 263 "FStar.Parser.ToSyntax.fst"
let t = (match ((let _125_122 = (unparen t)
in _125_122.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_46_389) -> begin
t
end
| _46_392 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level), t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end)
in (
# 266 "FStar.Parser.ToSyntax.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result)))
end))

# 269 "FStar.Parser.ToSyntax.fst"
let rec uncurry : FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term) = (fun bs t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (binders, t) -> begin
(uncurry (FStar_List.append bs binders) t)
end
| _46_402 -> begin
(bs, t)
end))

# 273 "FStar.Parser.ToSyntax.fst"
let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _46_406) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_46_412); FStar_Parser_AST.prange = _46_410}, _46_416) -> begin
true
end
| _46_420 -> begin
false
end))

# 278 "FStar.Parser.ToSyntax.fst"
let rec destruct_app_pattern : FStar_Parser_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 280 "FStar.Parser.ToSyntax.fst"
let _46_432 = (destruct_app_pattern env is_top_level p)
in (match (_46_432) with
| (name, args, _46_431) -> begin
(name, args, Some (t))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _46_437); FStar_Parser_AST.prange = _46_434}, args) when is_top_level -> begin
(let _125_136 = (let _125_135 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_125_135))
in (_125_136, args, None))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _46_448); FStar_Parser_AST.prange = _46_445}, args) -> begin
(FStar_Util.Inl (id), args, None)
end
| _46_456 -> begin
(FStar_All.failwith "Not an app pattern")
end))

# 289 "FStar.Parser.ToSyntax.fst"
type bnd =
| LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * FStar_Syntax_Syntax.term)

# 290 "FStar.Parser.ToSyntax.fst"
let is_LocalBinder = (fun _discr_ -> (match (_discr_) with
| LocalBinder (_) -> begin
true
end
| _ -> begin
false
end))

# 291 "FStar.Parser.ToSyntax.fst"
let is_LetBinder = (fun _discr_ -> (match (_discr_) with
| LetBinder (_) -> begin
true
end
| _ -> begin
false
end))

# 290 "FStar.Parser.ToSyntax.fst"
let ___LocalBinder____0 = (fun projectee -> (match (projectee) with
| LocalBinder (_46_459) -> begin
_46_459
end))

# 291 "FStar.Parser.ToSyntax.fst"
let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_46_462) -> begin
_46_462
end))

# 292 "FStar.Parser.ToSyntax.fst"
let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun _46_6 -> (match (_46_6) with
| LocalBinder (a, aq) -> begin
(a, aq)
end
| _46_469 -> begin
(FStar_All.failwith "Impossible")
end))

# 295 "FStar.Parser.ToSyntax.fst"
let as_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_Parser_Env.env) = (fun env imp _46_7 -> (match (_46_7) with
| (None, k) -> begin
(let _125_173 = (FStar_Syntax_Syntax.null_binder k)
in (_125_173, env))
end
| (Some (a), k) -> begin
(
# 298 "FStar.Parser.ToSyntax.fst"
let _46_482 = (FStar_Parser_Env.push_bv env a)
in (match (_46_482) with
| (env, a) -> begin
(((
# 299 "FStar.Parser.ToSyntax.fst"
let _46_483 = a
in {FStar_Syntax_Syntax.ppname = _46_483.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _46_483.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}), (trans_aqual imp)), env)
end))
end))

# 301 "FStar.Parser.ToSyntax.fst"
type env_t =
FStar_Parser_Env.env

# 302 "FStar.Parser.ToSyntax.fst"
type lenv_t =
FStar_Syntax_Syntax.bv Prims.list

# 304 "FStar.Parser.ToSyntax.fst"
let mk_lb : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.letbinding = (fun _46_488 -> (match (_46_488) with
| (n, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))

# 305 "FStar.Parser.ToSyntax.fst"
let no_annot_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t None))

# 307 "FStar.Parser.ToSyntax.fst"
let rec desugar_data_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat) = (fun env p -> (
# 308 "FStar.Parser.ToSyntax.fst"
let check_linear_pattern_variables = (fun p -> (
# 309 "FStar.Parser.ToSyntax.fst"
let rec pat_vars = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_dot_term (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_constant (_)) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (_46_509, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out _46_517 -> (match (_46_517) with
| (p, _46_516) -> begin
(let _125_219 = (pat_vars p)
in (FStar_Util.set_union out _125_219))
end)) FStar_Syntax_Syntax.no_names))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj (hd::tl) -> begin
(
# 318 "FStar.Parser.ToSyntax.fst"
let xs = (pat_vars hd)
in if (not ((FStar_Util.for_all (fun p -> (
# 319 "FStar.Parser.ToSyntax.fst"
let ys = (pat_vars p)
in ((FStar_Util.set_is_subset_of xs ys) && (FStar_Util.set_is_subset_of ys xs)))) tl))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Disjunctive pattern binds different variables in each case", p.FStar_Syntax_Syntax.p))))
end else begin
xs
end)
end))
in (pat_vars p)))
in (
# 326 "FStar.Parser.ToSyntax.fst"
let resolvex = (fun l e x -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText))))) with
| Some (y) -> begin
(l, e, y)
end
| _46_535 -> begin
(
# 330 "FStar.Parser.ToSyntax.fst"
let _46_538 = (FStar_Parser_Env.push_bv e x)
in (match (_46_538) with
| (e, x) -> begin
((x)::l, e, x)
end))
end))
in (
# 332 "FStar.Parser.ToSyntax.fst"
let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun b -> (b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText))))) with
| Some (b) -> begin
(l, e, b)
end
| _46_547 -> begin
(
# 336 "FStar.Parser.ToSyntax.fst"
let _46_550 = (FStar_Parser_Env.push_bv e a)
in (match (_46_550) with
| (e, a) -> begin
((a)::l, e, a)
end))
end))
in (
# 338 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun loc env p -> (
# 339 "FStar.Parser.ToSyntax.fst"
let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Parser_AST.prange))
in (
# 340 "FStar.Parser.ToSyntax.fst"
let pos_r = (fun r q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r))
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.PatOr (p::ps) -> begin
(
# 344 "FStar.Parser.ToSyntax.fst"
let _46_572 = (aux loc env p)
in (match (_46_572) with
| (loc, env, var, p, _46_571) -> begin
(
# 345 "FStar.Parser.ToSyntax.fst"
let _46_589 = (FStar_List.fold_left (fun _46_576 p -> (match (_46_576) with
| (loc, env, ps) -> begin
(
# 346 "FStar.Parser.ToSyntax.fst"
let _46_585 = (aux loc env p)
in (match (_46_585) with
| (loc, env, _46_581, p, _46_584) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_46_589) with
| (loc, env, ps) -> begin
(
# 348 "FStar.Parser.ToSyntax.fst"
let pat = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in (loc, env, var, pat, false))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 352 "FStar.Parser.ToSyntax.fst"
let _46_600 = (aux loc env p)
in (match (_46_600) with
| (loc, env', binder, p, imp) -> begin
(
# 353 "FStar.Parser.ToSyntax.fst"
let binder = (match (binder) with
| LetBinder (_46_602) -> begin
(FStar_All.failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(
# 356 "FStar.Parser.ToSyntax.fst"
let t = (let _125_249 = (close_fun env t)
in (desugar_term env _125_249))
in LocalBinder (((
# 357 "FStar.Parser.ToSyntax.fst"
let _46_609 = x
in {FStar_Syntax_Syntax.ppname = _46_609.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _46_609.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), aq)))
end)
in (loc, env', binder, p, imp))
end))
end
| FStar_Parser_AST.PatWild -> begin
(
# 361 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _125_250 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in (loc, env, LocalBinder ((x, None)), _125_250, false)))
end
| FStar_Parser_AST.PatConst (c) -> begin
(
# 365 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _125_251 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in (loc, env, LocalBinder ((x, None)), _125_251, false)))
end
| (FStar_Parser_AST.PatTvar (x, aq)) | (FStar_Parser_AST.PatVar (x, aq)) -> begin
(
# 370 "FStar.Parser.ToSyntax.fst"
let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (
# 371 "FStar.Parser.ToSyntax.fst"
let aq = (trans_aqual aq)
in (
# 372 "FStar.Parser.ToSyntax.fst"
let _46_628 = (resolvex loc env x)
in (match (_46_628) with
| (loc, env, xbv) -> begin
(let _125_252 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in (loc, env, LocalBinder ((xbv, aq)), _125_252, imp))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(
# 376 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_datacon env) l)
in (
# 377 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _125_253 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, []))))
in (loc, env, LocalBinder ((x, None)), _125_253, false))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _46_634}, args) -> begin
(
# 381 "FStar.Parser.ToSyntax.fst"
let _46_656 = (FStar_List.fold_right (fun arg _46_645 -> (match (_46_645) with
| (loc, env, args) -> begin
(
# 382 "FStar.Parser.ToSyntax.fst"
let _46_652 = (aux loc env arg)
in (match (_46_652) with
| (loc, env, _46_649, arg, imp) -> begin
(loc, env, ((arg, imp))::args)
end))
end)) args (loc, env, []))
in (match (_46_656) with
| (loc, env, args) -> begin
(
# 384 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_datacon env) l)
in (
# 385 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _125_256 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _125_256, false))))
end))
end
| FStar_Parser_AST.PatApp (_46_660) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(
# 391 "FStar.Parser.ToSyntax.fst"
let _46_680 = (FStar_List.fold_right (fun pat _46_668 -> (match (_46_668) with
| (loc, env, pats) -> begin
(
# 392 "FStar.Parser.ToSyntax.fst"
let _46_676 = (aux loc env pat)
in (match (_46_676) with
| (loc, env, _46_672, pat, _46_675) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_46_680) with
| (loc, env, pats) -> begin
(
# 394 "FStar.Parser.ToSyntax.fst"
let pat = (let _125_269 = (let _125_268 = (let _125_264 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _125_264))
in (let _125_267 = (let _125_266 = (let _125_265 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_125_265, []))
in FStar_Syntax_Syntax.Pat_cons (_125_266))
in (FStar_All.pipe_left _125_268 _125_267)))
in (FStar_List.fold_right (fun hd tl -> (
# 395 "FStar.Parser.ToSyntax.fst"
let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (let _125_263 = (let _125_262 = (let _125_261 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_125_261, ((hd, false))::((tl, false))::[]))
in FStar_Syntax_Syntax.Pat_cons (_125_262))
in (FStar_All.pipe_left (pos_r r) _125_263)))) pats _125_269))
in (
# 398 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (loc, env, LocalBinder ((x, None)), pat, false)))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(
# 402 "FStar.Parser.ToSyntax.fst"
let _46_706 = (FStar_List.fold_left (fun _46_693 p -> (match (_46_693) with
| (loc, env, pats) -> begin
(
# 403 "FStar.Parser.ToSyntax.fst"
let _46_702 = (aux loc env p)
in (match (_46_702) with
| (loc, env, _46_698, pat, _46_701) -> begin
(loc, env, ((pat, false))::pats)
end))
end)) (loc, env, []) args)
in (match (_46_706) with
| (loc, env, args) -> begin
(
# 405 "FStar.Parser.ToSyntax.fst"
let args = (FStar_List.rev args)
in (
# 406 "FStar.Parser.ToSyntax.fst"
let l = if dep then begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end else begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end
in (
# 408 "FStar.Parser.ToSyntax.fst"
let constr = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (
# 409 "FStar.Parser.ToSyntax.fst"
let l = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| _46_713 -> begin
(FStar_All.failwith "impossible")
end)
in (
# 412 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _125_272 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _125_272, false)))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(
# 419 "FStar.Parser.ToSyntax.fst"
let _46_723 = (FStar_List.hd fields)
in (match (_46_723) with
| (f, _46_722) -> begin
(
# 420 "FStar.Parser.ToSyntax.fst"
let _46_727 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_46_727) with
| (record, _46_726) -> begin
(
# 421 "FStar.Parser.ToSyntax.fst"
let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _46_730 -> (match (_46_730) with
| (f, p) -> begin
(let _125_274 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.qualify_field_to_record env record) f)
in (_125_274, p))
end))))
in (
# 423 "FStar.Parser.ToSyntax.fst"
let args = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _46_735 -> (match (_46_735) with
| (f, _46_734) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _46_739 -> (match (_46_739) with
| (g, _46_738) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_46_742, p) -> begin
p
end)
end))))
in (
# 427 "FStar.Parser.ToSyntax.fst"
let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_Env.constrname)) p.FStar_Parser_AST.prange), args))) p.FStar_Parser_AST.prange)
in (
# 428 "FStar.Parser.ToSyntax.fst"
let _46_754 = (aux loc env app)
in (match (_46_754) with
| (env, e, b, p, _46_753) -> begin
(
# 429 "FStar.Parser.ToSyntax.fst"
let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(let _125_283 = (let _125_282 = (let _125_281 = (
# 430 "FStar.Parser.ToSyntax.fst"
let _46_759 = fv
in (let _125_280 = (let _125_279 = (let _125_278 = (let _125_277 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _125_277))
in FStar_Syntax_Syntax.Record_ctor (_125_278))
in Some (_125_279))
in {FStar_Syntax_Syntax.fv_name = _46_759.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = _46_759.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _125_280}))
in (_125_281, args))
in FStar_Syntax_Syntax.Pat_cons (_125_282))
in (FStar_All.pipe_left pos _125_283))
end
| _46_762 -> begin
p
end)
in (env, e, b, p, false))
end)))))
end))
end))
end))))
in (
# 434 "FStar.Parser.ToSyntax.fst"
let _46_771 = (aux [] env p)
in (match (_46_771) with
| (_46_765, env, b, p, _46_770) -> begin
(
# 435 "FStar.Parser.ToSyntax.fst"
let _46_772 = (let _125_284 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore _125_284))
in (env, b, p))
end)))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _46_779) -> begin
(let _125_290 = (let _125_289 = (let _125_288 = (FStar_Parser_Env.qualify env x)
in (_125_288, FStar_Syntax_Syntax.tun))
in LetBinder (_125_289))
in (env, _125_290, None))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _46_786); FStar_Parser_AST.prange = _46_783}, t) -> begin
(let _125_294 = (let _125_293 = (let _125_292 = (FStar_Parser_Env.qualify env x)
in (let _125_291 = (desugar_term env t)
in (_125_292, _125_291)))
in LetBinder (_125_293))
in (env, _125_294, None))
end
| _46_794 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern at the top-level", p.FStar_Parser_AST.prange))))
end)
end else begin
(
# 446 "FStar.Parser.ToSyntax.fst"
let _46_798 = (desugar_data_pat env p)
in (match (_46_798) with
| (env, binder, p) -> begin
(
# 447 "FStar.Parser.ToSyntax.fst"
let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| _46_806 -> begin
Some (p)
end)
in (env, binder, p))
end))
end)
and desugar_binding_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun _46_810 env pat -> (
# 456 "FStar.Parser.ToSyntax.fst"
let _46_818 = (desugar_data_pat env pat)
in (match (_46_818) with
| (env, _46_816, pat) -> begin
(env, pat)
end)))
and desugar_match_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (
# 462 "FStar.Parser.ToSyntax.fst"
let env = (
# 462 "FStar.Parser.ToSyntax.fst"
let _46_823 = env
in {FStar_Parser_Env.curmodule = _46_823.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _46_823.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _46_823.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.sigaccum = _46_823.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _46_823.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _46_823.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _46_823.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _46_823.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _46_823.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _46_823.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (
# 466 "FStar.Parser.ToSyntax.fst"
let env = (
# 466 "FStar.Parser.ToSyntax.fst"
let _46_828 = env
in {FStar_Parser_Env.curmodule = _46_828.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _46_828.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _46_828.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.sigaccum = _46_828.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _46_828.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _46_828.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _46_828.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _46_828.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _46_828.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _46_828.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (
# 470 "FStar.Parser.ToSyntax.fst"
let mk = (fun e -> (FStar_Syntax_Syntax.mk e None top.FStar_Parser_AST.range))
in (
# 471 "FStar.Parser.ToSyntax.fst"
let setpos = (fun e -> (
# 471 "FStar.Parser.ToSyntax.fst"
let _46_838 = e
in {FStar_Syntax_Syntax.n = _46_838.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _46_838.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _46_838.FStar_Syntax_Syntax.vars}))
in (match ((let _125_313 = (unparen top)
in _125_313.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (_46_842) -> begin
(desugar_formula env top)
end
| FStar_Parser_AST.Requires (t, lopt) -> begin
(desugar_formula env t)
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(desugar_formula env t)
end
| FStar_Parser_AST.Const (c) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (c)))
end
| FStar_Parser_AST.Op ("=!=", args) -> begin
(desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Op (("~", ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Op (("==", args))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))::[]))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op ("*", _46_862::_46_860::[]) when (let _125_314 = (op_as_term env 2 top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right _125_314 FStar_Option.isNone)) -> begin
(
# 489 "FStar.Parser.ToSyntax.fst"
let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", t1::t2::[]) -> begin
(
# 491 "FStar.Parser.ToSyntax.fst"
let rest = (flatten t2)
in (t1)::rest)
end
| _46_876 -> begin
(t)::[]
end))
in (
# 494 "FStar.Parser.ToSyntax.fst"
let targs = (let _125_320 = (let _125_317 = (unparen top)
in (flatten _125_317))
in (FStar_All.pipe_right _125_320 (FStar_List.map (fun t -> (let _125_319 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg _125_319))))))
in (
# 495 "FStar.Parser.ToSyntax.fst"
let tup = (let _125_321 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) _125_321))
in (mk (FStar_Syntax_Syntax.Tm_app ((tup, targs)))))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _125_322 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) a)
in (FStar_All.pipe_left setpos _125_322))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Unexpected operator: " s), top.FStar_Parser_AST.range))))
end
| Some (op) -> begin
(
# 505 "FStar.Parser.ToSyntax.fst"
let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _125_324 = (desugar_term env t)
in (_125_324, None)))))
in (mk (FStar_Syntax_Syntax.Tm_app ((op, args)))))
end)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _46_897; FStar_Ident.ident = _46_895; FStar_Ident.nsstr = _46_893; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _46_906; FStar_Ident.ident = _46_904; FStar_Ident.nsstr = _46_902; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _46_915; FStar_Ident.ident = _46_913; FStar_Ident.nsstr = _46_911; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _46_924; FStar_Ident.ident = _46_922; FStar_Ident.nsstr = _46_920; FStar_Ident.str = "True"}) -> begin
(let _125_325 = (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _125_325 FStar_Syntax_Syntax.Delta_constant None))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _46_933; FStar_Ident.ident = _46_931; FStar_Ident.nsstr = _46_929; FStar_Ident.str = "False"}) -> begin
(let _125_326 = (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _125_326 FStar_Syntax_Syntax.Delta_constant None))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(let _125_327 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (FStar_All.pipe_left setpos _125_327))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(
# 520 "FStar.Parser.ToSyntax.fst"
let _46_948 = (match ((FStar_Parser_Env.try_lookup_datacon env l)) with
| None -> begin
(let _125_328 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (_125_328, false))
end
| Some (head) -> begin
(let _125_329 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in (_125_329, true))
end)
in (match (_46_948) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| _46_951 -> begin
(
# 526 "FStar.Parser.ToSyntax.fst"
let args = (FStar_List.map (fun _46_954 -> (match (_46_954) with
| (t, imp) -> begin
(
# 527 "FStar.Parser.ToSyntax.fst"
let te = (desugar_term env t)
in (arg_withimp_e imp te))
end)) args)
in (
# 529 "FStar.Parser.ToSyntax.fst"
let app = (mk (FStar_Syntax_Syntax.Tm_app ((head, args))))
in if is_data then begin
(mk (FStar_Syntax_Syntax.Tm_meta ((app, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))))
end else begin
app
end))
end)
end))
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(
# 536 "FStar.Parser.ToSyntax.fst"
let _46_982 = (FStar_List.fold_left (fun _46_965 b -> (match (_46_965) with
| (env, tparams, typs) -> begin
(
# 537 "FStar.Parser.ToSyntax.fst"
let _46_969 = (desugar_binder env b)
in (match (_46_969) with
| (xopt, t) -> begin
(
# 538 "FStar.Parser.ToSyntax.fst"
let _46_975 = (match (xopt) with
| None -> begin
(let _125_333 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (env, _125_333))
end
| Some (x) -> begin
(FStar_Parser_Env.push_bv env x)
end)
in (match (_46_975) with
| (env, x) -> begin
(let _125_337 = (let _125_336 = (let _125_335 = (let _125_334 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _125_334))
in (_125_335)::[])
in (FStar_List.append typs _125_336))
in (env, (FStar_List.append tparams ((((
# 542 "FStar.Parser.ToSyntax.fst"
let _46_976 = x
in {FStar_Syntax_Syntax.ppname = _46_976.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _46_976.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), None))::[])), _125_337))
end))
end))
end)) (env, [], []) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_46_982) with
| (env, _46_980, targs) -> begin
(
# 545 "FStar.Parser.ToSyntax.fst"
let tup = (let _125_338 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) _125_338))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app ((tup, targs)))))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(
# 549 "FStar.Parser.ToSyntax.fst"
let _46_990 = (uncurry binders t)
in (match (_46_990) with
| (bs, t) -> begin
(
# 550 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun env bs _46_8 -> (match (_46_8) with
| [] -> begin
(
# 552 "FStar.Parser.ToSyntax.fst"
let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (let _125_345 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos _125_345)))
end
| hd::tl -> begin
(
# 556 "FStar.Parser.ToSyntax.fst"
let mlenv = (FStar_Parser_Env.default_ml env)
in (
# 557 "FStar.Parser.ToSyntax.fst"
let bb = (desugar_binder mlenv hd)
in (
# 558 "FStar.Parser.ToSyntax.fst"
let _46_1004 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_46_1004) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_binder env b)) with
| (None, _46_1011) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(
# 567 "FStar.Parser.ToSyntax.fst"
let _46_1019 = (as_binder env None b)
in (match (_46_1019) with
| ((x, _46_1016), env) -> begin
(
# 568 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env f)
in (let _125_346 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos _125_346)))
end))
end)
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(
# 573 "FStar.Parser.ToSyntax.fst"
let _46_1039 = (FStar_List.fold_left (fun _46_1027 pat -> (match (_46_1027) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (_46_1030, t) -> begin
(let _125_350 = (let _125_349 = (free_type_vars env t)
in (FStar_List.append _125_349 ftvs))
in (env, _125_350))
end
| _46_1035 -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_46_1039) with
| (_46_1037, ftv) -> begin
(
# 577 "FStar.Parser.ToSyntax.fst"
let ftv = (sort_ftv ftv)
in (
# 578 "FStar.Parser.ToSyntax.fst"
let binders = (let _125_352 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar ((a, Some (FStar_Parser_AST.Implicit)))) top.FStar_Parser_AST.range))))
in (FStar_List.append _125_352 binders))
in (
# 587 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun env bs sc_pat_opt _46_9 -> (match (_46_9) with
| [] -> begin
(
# 589 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env body)
in (
# 590 "FStar.Parser.ToSyntax.fst"
let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(
# 592 "FStar.Parser.ToSyntax.fst"
let body = (let _125_362 = (let _125_361 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right _125_361 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close _125_362 body))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((sc, ((pat, None, body))::[]))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (let _125_363 = (no_annot_abs (FStar_List.rev bs) body)
in (setpos _125_363))))
end
| p::rest -> begin
(
# 598 "FStar.Parser.ToSyntax.fst"
let _46_1063 = (desugar_binding_pat env p)
in (match (_46_1063) with
| (env, b, pat) -> begin
(
# 599 "FStar.Parser.ToSyntax.fst"
let _46_1114 = (match (b) with
| LetBinder (_46_1065) -> begin
(FStar_All.failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(
# 602 "FStar.Parser.ToSyntax.fst"
let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _46_1073) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _125_365 = (let _125_364 = (FStar_Syntax_Syntax.bv_to_name x)
in (_125_364, p))
in Some (_125_365))
end
| (Some (p), Some (sc, p')) -> begin
(match ((sc.FStar_Syntax_Syntax.n, p'.FStar_Syntax_Syntax.v)) with
| (FStar_Syntax_Syntax.Tm_name (_46_1087), _46_1090) -> begin
(
# 608 "FStar.Parser.ToSyntax.fst"
let tup2 = (let _125_366 = (FStar_Syntax_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _125_366 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (
# 609 "FStar.Parser.ToSyntax.fst"
let sc = (let _125_374 = (let _125_373 = (let _125_372 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (let _125_371 = (let _125_370 = (FStar_Syntax_Syntax.as_arg sc)
in (let _125_369 = (let _125_368 = (let _125_367 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _125_367))
in (_125_368)::[])
in (_125_370)::_125_369))
in (_125_372, _125_371)))
in FStar_Syntax_Syntax.Tm_app (_125_373))
in (FStar_Syntax_Syntax.mk _125_374 None top.FStar_Parser_AST.range))
in (
# 610 "FStar.Parser.ToSyntax.fst"
let p = (let _125_375 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tup2, ((p', false))::((p, false))::[]))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _125_375))
in Some ((sc, p)))))
end
| (FStar_Syntax_Syntax.Tm_app (_46_1096, args), FStar_Syntax_Syntax.Pat_cons (_46_1101, pats)) -> begin
(
# 613 "FStar.Parser.ToSyntax.fst"
let tupn = (let _125_376 = (FStar_Syntax_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _125_376 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (
# 614 "FStar.Parser.ToSyntax.fst"
let sc = (let _125_383 = (let _125_382 = (let _125_381 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (let _125_380 = (let _125_379 = (let _125_378 = (let _125_377 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _125_377))
in (_125_378)::[])
in (FStar_List.append args _125_379))
in (_125_381, _125_380)))
in FStar_Syntax_Syntax.Tm_app (_125_382))
in (mk _125_383))
in (
# 615 "FStar.Parser.ToSyntax.fst"
let p = (let _125_384 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tupn, (FStar_List.append pats (((p, false))::[]))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _125_384))
in Some ((sc, p)))))
end
| _46_1110 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((x, aq), sc_pat_opt))
end)
in (match (_46_1114) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _46_1118; FStar_Parser_AST.level = _46_1116}, phi, _46_1124) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(
# 626 "FStar.Parser.ToSyntax.fst"
let phi = (desugar_formula env phi)
in (let _125_392 = (let _125_391 = (let _125_390 = (FStar_Syntax_Syntax.fvar a FStar_Syntax_Syntax.Delta_equational None)
in (let _125_389 = (let _125_388 = (FStar_Syntax_Syntax.as_arg phi)
in (let _125_387 = (let _125_386 = (let _125_385 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _125_385))
in (_125_386)::[])
in (_125_388)::_125_387))
in (_125_390, _125_389)))
in FStar_Syntax_Syntax.Tm_app (_125_391))
in (mk _125_392)))
end
| FStar_Parser_AST.App (_46_1129) -> begin
(
# 632 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun args e -> (match ((let _125_397 = (unparen e)
in _125_397.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(
# 634 "FStar.Parser.ToSyntax.fst"
let arg = (let _125_398 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _125_398))
in (aux ((arg)::args) e))
end
| _46_1141 -> begin
(
# 637 "FStar.Parser.ToSyntax.fst"
let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app ((head, args)))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _125_401 = (let _125_400 = (let _125_399 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range), t1))::[], t2))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in (_125_399, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))
in FStar_Syntax_Syntax.Tm_meta (_125_400))
in (mk _125_401))
end
| FStar_Parser_AST.Let (is_rec, (pat, _snd)::_tl, body) -> begin
(
# 646 "FStar.Parser.ToSyntax.fst"
let ds_let_rec_or_app = (fun _46_1157 -> (match (()) with
| () -> begin
(
# 647 "FStar.Parser.ToSyntax.fst"
let bindings = ((pat, _snd))::_tl
in (
# 648 "FStar.Parser.ToSyntax.fst"
let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _46_1161 -> (match (_46_1161) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _125_405 = (destruct_app_pattern env top_level p)
in (_125_405, def))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _125_406 = (destruct_app_pattern env top_level p)
in (_125_406, def))
end
| _46_1167 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _46_1172); FStar_Parser_AST.prange = _46_1169}, t) -> begin
if top_level then begin
(let _125_409 = (let _125_408 = (let _125_407 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_125_407))
in (_125_408, [], Some (t)))
in (_125_409, def))
end else begin
((FStar_Util.Inl (id), [], Some (t)), def)
end
end
| FStar_Parser_AST.PatVar (id, _46_1181) -> begin
if top_level then begin
(let _125_412 = (let _125_411 = (let _125_410 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_125_410))
in (_125_411, [], None))
in (_125_412, def))
end else begin
((FStar_Util.Inl (id), [], None), def)
end
end
| _46_1185 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected let binding", p.FStar_Parser_AST.prange))))
end)
end)
end
end))))
in (
# 665 "FStar.Parser.ToSyntax.fst"
let _46_1214 = (FStar_List.fold_left (fun _46_1190 _46_1199 -> (match ((_46_1190, _46_1199)) with
| ((env, fnames, rec_bindings), ((f, _46_1193, _46_1195), _46_1198)) -> begin
(
# 667 "FStar.Parser.ToSyntax.fst"
let _46_1210 = (match (f) with
| FStar_Util.Inl (x) -> begin
(
# 669 "FStar.Parser.ToSyntax.fst"
let _46_1204 = (FStar_Parser_Env.push_bv env x)
in (match (_46_1204) with
| (env, xx) -> begin
(let _125_416 = (let _125_415 = (FStar_Syntax_Syntax.mk_binder xx)
in (_125_415)::rec_bindings)
in (env, FStar_Util.Inl (xx), _125_416))
end))
end
| FStar_Util.Inr (l) -> begin
(let _125_417 = (FStar_Parser_Env.push_top_level_rec_binding env l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in (_125_417, FStar_Util.Inr (l), rec_bindings))
end)
in (match (_46_1210) with
| (env, lbname, rec_bindings) -> begin
(env, (lbname)::fnames, rec_bindings)
end))
end)) (env, [], []) funs)
in (match (_46_1214) with
| (env', fnames, rec_bindings) -> begin
(
# 675 "FStar.Parser.ToSyntax.fst"
let fnames = (FStar_List.rev fnames)
in (
# 677 "FStar.Parser.ToSyntax.fst"
let desugar_one_def = (fun env lbname _46_1225 -> (match (_46_1225) with
| ((_46_1220, args, result_t), def) -> begin
(
# 678 "FStar.Parser.ToSyntax.fst"
let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _125_424 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed ((def, t))) _125_424 FStar_Parser_AST.Expr))
end)
in (
# 681 "FStar.Parser.ToSyntax.fst"
let def = (match (args) with
| [] -> begin
def
end
| _46_1232 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.un_curry_abs args def) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
end)
in (
# 684 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env def)
in (
# 685 "FStar.Parser.ToSyntax.fst"
let lbname = (match (lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl (x)
end
| FStar_Util.Inr (l) -> begin
(let _125_426 = (let _125_425 = (incr_delta_qualifier body)
in (FStar_Syntax_Syntax.lid_as_fv l _125_425 None))
in FStar_Util.Inr (_125_426))
end)
in (
# 688 "FStar.Parser.ToSyntax.fst"
let body = if is_rec then begin
(FStar_Syntax_Subst.close rec_bindings body)
end else begin
body
end
in (mk_lb (lbname, FStar_Syntax_Syntax.tun, body)))))))
end))
in (
# 690 "FStar.Parser.ToSyntax.fst"
let lbs = (FStar_List.map2 (desugar_one_def (if is_rec then begin
env'
end else begin
env
end)) fnames funs)
in (
# 691 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env' body)
in (let _125_429 = (let _125_428 = (let _125_427 = (FStar_Syntax_Subst.close rec_bindings body)
in ((is_rec, lbs), _125_427))
in FStar_Syntax_Syntax.Tm_let (_125_428))
in (FStar_All.pipe_left mk _125_429))))))
end))))
end))
in (
# 695 "FStar.Parser.ToSyntax.fst"
let ds_non_rec = (fun pat t1 t2 -> (
# 696 "FStar.Parser.ToSyntax.fst"
let t1 = (desugar_term env t1)
in (
# 697 "FStar.Parser.ToSyntax.fst"
let _46_1251 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_46_1251) with
| (env, binder, pat) -> begin
(match (binder) with
| LetBinder (l, t) -> begin
(
# 700 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env t2)
in (
# 701 "FStar.Parser.ToSyntax.fst"
let fv = (let _125_436 = (incr_delta_qualifier t1)
in (FStar_Syntax_Syntax.lid_as_fv l _125_436 None))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]), body))))))
end
| LocalBinder (x, _46_1260) -> begin
(
# 705 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env t2)
in (
# 706 "FStar.Parser.ToSyntax.fst"
let body = (match (pat) with
| (None) | (Some ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (_); FStar_Syntax_Syntax.ty = _; FStar_Syntax_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _125_441 = (let _125_440 = (let _125_439 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _125_438 = (let _125_437 = (FStar_Syntax_Util.branch (pat, None, body))
in (_125_437)::[])
in (_125_439, _125_438)))
in FStar_Syntax_Syntax.Tm_match (_125_440))
in (FStar_Syntax_Syntax.mk _125_441 None body.FStar_Syntax_Syntax.pos))
end)
in (let _125_446 = (let _125_445 = (let _125_444 = (let _125_443 = (let _125_442 = (FStar_Syntax_Syntax.mk_binder x)
in (_125_442)::[])
in (FStar_Syntax_Subst.close _125_443 body))
in ((false, ((mk_lb (FStar_Util.Inl (x), x.FStar_Syntax_Syntax.sort, t1)))::[]), _125_444))
in FStar_Syntax_Syntax.Tm_let (_125_445))
in (FStar_All.pipe_left mk _125_446))))
end)
end))))
in if (is_rec || (is_app_pattern pat)) then begin
(ds_let_rec_or_app ())
end else begin
(ds_non_rec pat _snd body)
end))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(
# 720 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (let _125_457 = (let _125_456 = (let _125_455 = (desugar_term env t1)
in (let _125_454 = (let _125_453 = (let _125_448 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (let _125_447 = (desugar_term env t2)
in (_125_448, None, _125_447)))
in (let _125_452 = (let _125_451 = (let _125_450 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (let _125_449 = (desugar_term env t3)
in (_125_450, None, _125_449)))
in (_125_451)::[])
in (_125_453)::_125_452))
in (_125_455, _125_454)))
in FStar_Syntax_Syntax.Tm_match (_125_456))
in (mk _125_457)))
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(
# 726 "FStar.Parser.ToSyntax.fst"
let r = top.FStar_Parser_AST.range
in (
# 727 "FStar.Parser.ToSyntax.fst"
let handler = (FStar_Parser_AST.mk_function branches r r)
in (
# 728 "FStar.Parser.ToSyntax.fst"
let body = (FStar_Parser_AST.mk_function ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatConst (FStar_Const.Const_unit)) r), None, e))::[]) r r)
in (
# 729 "FStar.Parser.ToSyntax.fst"
let a1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (FStar_Syntax_Const.try_with_lid)) r top.FStar_Parser_AST.level), body, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (
# 730 "FStar.Parser.ToSyntax.fst"
let a2 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((a1, handler, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (desugar_term env a2))))))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(
# 734 "FStar.Parser.ToSyntax.fst"
let desugar_branch = (fun _46_1300 -> (match (_46_1300) with
| (pat, wopt, b) -> begin
(
# 735 "FStar.Parser.ToSyntax.fst"
let _46_1303 = (desugar_match_pat env pat)
in (match (_46_1303) with
| (env, pat) -> begin
(
# 736 "FStar.Parser.ToSyntax.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _125_460 = (desugar_term env e)
in Some (_125_460))
end)
in (
# 739 "FStar.Parser.ToSyntax.fst"
let b = (desugar_term env b)
in (FStar_Syntax_Util.branch (pat, wopt, b))))
end))
end))
in (let _125_464 = (let _125_463 = (let _125_462 = (desugar_term env e)
in (let _125_461 = (FStar_List.map desugar_branch branches)
in (_125_462, _125_461)))
in FStar_Syntax_Syntax.Tm_match (_125_463))
in (FStar_All.pipe_left mk _125_464)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(
# 744 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.default_ml env)
in (
# 745 "FStar.Parser.ToSyntax.fst"
let c = (desugar_comp t.FStar_Parser_AST.range true env t)
in (
# 746 "FStar.Parser.ToSyntax.fst"
let annot = if (FStar_Syntax_Util.is_ml_comp c) then begin
FStar_Util.Inl ((FStar_Syntax_Util.comp_result c))
end else begin
FStar_Util.Inr (c)
end
in (let _125_467 = (let _125_466 = (let _125_465 = (desugar_term env e)
in (_125_465, annot, None))
in FStar_Syntax_Syntax.Tm_ascribed (_125_466))
in (FStar_All.pipe_left mk _125_467)))))
end
| FStar_Parser_AST.Record (_46_1317, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected empty record", top.FStar_Parser_AST.range))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(
# 755 "FStar.Parser.ToSyntax.fst"
let _46_1328 = (FStar_List.hd fields)
in (match (_46_1328) with
| (f, _46_1327) -> begin
(
# 756 "FStar.Parser.ToSyntax.fst"
let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (
# 757 "FStar.Parser.ToSyntax.fst"
let _46_1334 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_46_1334) with
| (record, _46_1333) -> begin
(
# 758 "FStar.Parser.ToSyntax.fst"
let get_field = (fun xopt f -> (
# 759 "FStar.Parser.ToSyntax.fst"
let fn = f.FStar_Ident.ident
in (
# 760 "FStar.Parser.ToSyntax.fst"
let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _46_1342 -> (match (_46_1342) with
| (g, _46_1341) -> begin
(
# 761 "FStar.Parser.ToSyntax.fst"
let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_46_1346, e) -> begin
(let _125_475 = (qfn fn)
in (_125_475, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _125_478 = (let _125_477 = (let _125_476 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in (_125_476, top.FStar_Parser_AST.range))
in FStar_Syntax_Syntax.Error (_125_477))
in (Prims.raise _125_478))
end
| Some (x) -> begin
(let _125_479 = (qfn fn)
in (_125_479, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Project ((x, f))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end))))
in (
# 772 "FStar.Parser.ToSyntax.fst"
let recterm = (match (eopt) with
| None -> begin
(let _125_484 = (let _125_483 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _46_1358 -> (match (_46_1358) with
| (f, _46_1357) -> begin
(let _125_482 = (let _125_481 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _125_481))
in (_125_482, FStar_Parser_AST.Nothing))
end))))
in (record.FStar_Parser_Env.constrname, _125_483))
in FStar_Parser_AST.Construct (_125_484))
end
| Some (e) -> begin
(
# 779 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (
# 780 "FStar.Parser.ToSyntax.fst"
let xterm = (let _125_486 = (let _125_485 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_125_485))
in (FStar_Parser_AST.mk_term _125_486 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (
# 781 "FStar.Parser.ToSyntax.fst"
let record = (let _125_489 = (let _125_488 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _46_1366 -> (match (_46_1366) with
| (f, _46_1365) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _125_488))
in FStar_Parser_AST.Record (_125_489))
in FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar ((x, None))) x.FStar_Ident.idRange), e))::[], (FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level))))))
end)
in (
# 784 "FStar.Parser.ToSyntax.fst"
let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (
# 785 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _46_1382; FStar_Syntax_Syntax.pos = _46_1380; FStar_Syntax_Syntax.vars = _46_1378}, args); FStar_Syntax_Syntax.tk = _46_1376; FStar_Syntax_Syntax.pos = _46_1374; FStar_Syntax_Syntax.vars = _46_1372}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(
# 788 "FStar.Parser.ToSyntax.fst"
let e = (let _125_497 = (let _125_496 = (let _125_495 = (let _125_494 = (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos)
in (let _125_493 = (let _125_492 = (let _125_491 = (let _125_490 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _125_490))
in FStar_Syntax_Syntax.Record_ctor (_125_491))
in Some (_125_492))
in (FStar_Syntax_Syntax.fvar _125_494 FStar_Syntax_Syntax.Delta_constant _125_493)))
in (_125_495, args))
in FStar_Syntax_Syntax.Tm_app (_125_496))
in (FStar_All.pipe_left mk _125_497))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end
| _46_1396 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(
# 796 "FStar.Parser.ToSyntax.fst"
let _46_1403 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_projector_by_field_name env) f)
in (match (_46_1403) with
| (fieldname, is_rec) -> begin
(
# 797 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env e)
in (
# 798 "FStar.Parser.ToSyntax.fst"
let fn = (
# 799 "FStar.Parser.ToSyntax.fst"
let _46_1408 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_46_1408) with
| (ns, _46_1407) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (
# 801 "FStar.Parser.ToSyntax.fst"
let qual = if is_rec then begin
Some (FStar_Syntax_Syntax.Record_projector (fn))
end else begin
None
end
in (let _125_503 = (let _125_502 = (let _125_501 = (let _125_498 = (FStar_Ident.set_lid_range fieldname (FStar_Ident.range_of_lid f))
in (FStar_Syntax_Syntax.fvar _125_498 FStar_Syntax_Syntax.Delta_equational qual))
in (let _125_500 = (let _125_499 = (FStar_Syntax_Syntax.as_arg e)
in (_125_499)::[])
in (_125_501, _125_500)))
in FStar_Syntax_Syntax.Tm_app (_125_502))
in (FStar_All.pipe_left mk _125_503)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| _46_1418 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _46_1420 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_args : FStar_Parser_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun _46_1425 -> (match (_46_1425) with
| (a, imp) -> begin
(let _125_507 = (desugar_term env a)
in (arg_withimp_e imp _125_507))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r default_ok env t -> (
# 818 "FStar.Parser.ToSyntax.fst"
let fail = (fun msg -> (Prims.raise (FStar_Syntax_Syntax.Error ((msg, r)))))
in (
# 819 "FStar.Parser.ToSyntax.fst"
let is_requires = (fun _46_1437 -> (match (_46_1437) with
| (t, _46_1436) -> begin
(match ((let _125_515 = (unparen t)
in _125_515.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Requires (_46_1439) -> begin
true
end
| _46_1442 -> begin
false
end)
end))
in (
# 822 "FStar.Parser.ToSyntax.fst"
let is_ensures = (fun _46_1447 -> (match (_46_1447) with
| (t, _46_1446) -> begin
(match ((let _125_518 = (unparen t)
in _125_518.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ensures (_46_1449) -> begin
true
end
| _46_1452 -> begin
false
end)
end))
in (
# 825 "FStar.Parser.ToSyntax.fst"
let is_app = (fun head _46_1458 -> (match (_46_1458) with
| (t, _46_1457) -> begin
(match ((let _125_523 = (unparen t)
in _125_523.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _46_1462; FStar_Parser_AST.level = _46_1460}, _46_1467, _46_1469) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| _46_1473 -> begin
false
end)
end))
in (
# 828 "FStar.Parser.ToSyntax.fst"
let pre_process_comp_typ = (fun t -> (
# 829 "FStar.Parser.ToSyntax.fst"
let _46_1478 = (head_and_args t)
in (match (_46_1478) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(
# 832 "FStar.Parser.ToSyntax.fst"
let unit_tm = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (
# 833 "FStar.Parser.ToSyntax.fst"
let nil_pat = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr), FStar_Parser_AST.Nothing)
in (
# 834 "FStar.Parser.ToSyntax.fst"
let args = (match (args) with
| [] -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Not enough arguments to \'Lemma\'", t.FStar_Parser_AST.range))))
end
| ens::[] -> begin
(
# 837 "FStar.Parser.ToSyntax.fst"
let req_true = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Requires (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.true_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Formula), None))) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (unit_tm)::(req_true)::(ens)::(nil_pat)::[])
end
| req::ens::[] when ((is_requires req) && (is_ensures ens)) -> begin
(unit_tm)::(req)::(ens)::(nil_pat)::[]
end
| req::ens::dec::[] when (((is_requires req) && (is_ensures ens)) && (is_app "decreases" dec)) -> begin
(unit_tm)::(req)::(ens)::(nil_pat)::(dec)::[]
end
| more -> begin
(unit_tm)::more
end)
in (
# 842 "FStar.Parser.ToSyntax.fst"
let head = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_name env) lemma)
in (head, args)))))
end
| FStar_Parser_AST.Name (l) when (FStar_Parser_Env.is_effect_name env l) -> begin
(let _125_526 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_name env) l)
in (_125_526, args))
end
| FStar_Parser_AST.Name (l) when ((let _125_527 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _125_527 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(let _125_528 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in (_125_528, args))
end
| FStar_Parser_AST.Name (l) when ((let _125_529 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _125_529 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(let _125_530 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)
in (_125_530, args))
end
| FStar_Parser_AST.Name (l) when ((((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) && default_ok) -> begin
(let _125_531 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in (_125_531, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _46_1506 when default_ok -> begin
(let _125_532 = (FStar_Ident.set_lid_range env.FStar_Parser_Env.default_result_effect head.FStar_Parser_AST.range)
in (_125_532, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _46_1508 -> begin
(let _125_534 = (let _125_533 = (FStar_Parser_AST.term_to_string t)
in (FStar_Util.format1 "%s is not an effect" _125_533))
in (fail _125_534))
end)
end)))
in (
# 872 "FStar.Parser.ToSyntax.fst"
let _46_1511 = (pre_process_comp_typ t)
in (match (_46_1511) with
| (eff, args) -> begin
(
# 873 "FStar.Parser.ToSyntax.fst"
let _46_1512 = if ((FStar_List.length args) = 0) then begin
(let _125_536 = (let _125_535 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" _125_535))
in (fail _125_536))
end else begin
()
end
in (
# 875 "FStar.Parser.ToSyntax.fst"
let _46_1516 = (let _125_538 = (FStar_List.hd args)
in (let _125_537 = (FStar_List.tl args)
in (_125_538, _125_537)))
in (match (_46_1516) with
| (result_arg, rest) -> begin
(
# 876 "FStar.Parser.ToSyntax.fst"
let result_typ = (desugar_typ env (Prims.fst result_arg))
in (
# 877 "FStar.Parser.ToSyntax.fst"
let rest = (desugar_args env rest)
in (
# 878 "FStar.Parser.ToSyntax.fst"
let _46_1541 = (FStar_All.pipe_right rest (FStar_List.partition (fun _46_1522 -> (match (_46_1522) with
| (t, _46_1521) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _46_1528; FStar_Syntax_Syntax.pos = _46_1526; FStar_Syntax_Syntax.vars = _46_1524}, _46_1533::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| _46_1538 -> begin
false
end)
end))))
in (match (_46_1541) with
| (dec, rest) -> begin
(
# 884 "FStar.Parser.ToSyntax.fst"
let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _46_1545 -> (match (_46_1545) with
| (t, _46_1544) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_46_1547, (arg, _46_1550)::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| _46_1556 -> begin
(FStar_All.failwith "impos")
end)
end))))
in (
# 888 "FStar.Parser.ToSyntax.fst"
let no_additional_args = (((FStar_List.length decreases_clause) = 0) && ((FStar_List.length rest) = 0))
in if (no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid)) then begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end else begin
if (no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid)) then begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end else begin
(
# 896 "FStar.Parser.ToSyntax.fst"
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
# 902 "FStar.Parser.ToSyntax.fst"
let rest = if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid) then begin
(match (rest) with
| req::ens::(pat, aq)::[] -> begin
(
# 906 "FStar.Parser.ToSyntax.fst"
let pat = (match (pat.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
(
# 908 "FStar.Parser.ToSyntax.fst"
let nil = (FStar_Syntax_Syntax.mk_Tm_uinst pat ((FStar_Syntax_Syntax.U_succ (FStar_Syntax_Syntax.U_zero))::[]))
in (
# 909 "FStar.Parser.ToSyntax.fst"
let pattern = (let _125_542 = (let _125_541 = (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _125_541 FStar_Syntax_Syntax.Delta_constant None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _125_542 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app nil (((pattern, Some (FStar_Syntax_Syntax.imp_tag)))::[]) None pat.FStar_Syntax_Syntax.pos)))
end
| _46_1571 -> begin
pat
end)
in (let _125_546 = (let _125_545 = (let _125_544 = (let _125_543 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((pat, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)))) None pat.FStar_Syntax_Syntax.pos)
in (_125_543, aq))
in (_125_544)::[])
in (ens)::_125_545)
in (req)::_125_546))
end
| _46_1574 -> begin
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
end))))))))
and desugar_formula : env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env f -> (
# 922 "FStar.Parser.ToSyntax.fst"
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
| _46_1586 -> begin
None
end))
in (
# 929 "FStar.Parser.ToSyntax.fst"
let mk = (fun t -> (FStar_Syntax_Syntax.mk t None f.FStar_Parser_AST.range))
in (
# 930 "FStar.Parser.ToSyntax.fst"
let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (
# 931 "FStar.Parser.ToSyntax.fst"
let setpos = (fun t -> (
# 931 "FStar.Parser.ToSyntax.fst"
let _46_1593 = t
in {FStar_Syntax_Syntax.n = _46_1593.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _46_1593.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _46_1593.FStar_Syntax_Syntax.vars}))
in (
# 932 "FStar.Parser.ToSyntax.fst"
let desugar_quant = (fun q b pats body -> (
# 933 "FStar.Parser.ToSyntax.fst"
let tk = (desugar_binder env (
# 933 "FStar.Parser.ToSyntax.fst"
let _46_1600 = b
in {FStar_Parser_AST.b = _46_1600.FStar_Parser_AST.b; FStar_Parser_AST.brange = _46_1600.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _46_1600.FStar_Parser_AST.aqual}))
in (
# 934 "FStar.Parser.ToSyntax.fst"
let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _125_581 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _125_581)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(
# 937 "FStar.Parser.ToSyntax.fst"
let _46_1614 = (FStar_Parser_Env.push_bv env a)
in (match (_46_1614) with
| (env, a) -> begin
(
# 938 "FStar.Parser.ToSyntax.fst"
let a = (
# 938 "FStar.Parser.ToSyntax.fst"
let _46_1615 = a
in {FStar_Syntax_Syntax.ppname = _46_1615.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _46_1615.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (
# 939 "FStar.Parser.ToSyntax.fst"
let pats = (desugar_pats env pats)
in (
# 940 "FStar.Parser.ToSyntax.fst"
let body = (desugar_formula env body)
in (
# 941 "FStar.Parser.ToSyntax.fst"
let body = (match (pats) with
| [] -> begin
body
end
| _46_1622 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((body, FStar_Syntax_Syntax.Meta_pattern (pats)))))
end)
in (
# 944 "FStar.Parser.ToSyntax.fst"
let body = (let _125_584 = (let _125_583 = (let _125_582 = (FStar_Syntax_Syntax.mk_binder a)
in (_125_582)::[])
in (no_annot_abs _125_583 body))
in (FStar_All.pipe_left setpos _125_584))
in (let _125_590 = (let _125_589 = (let _125_588 = (let _125_585 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Syntax_Syntax.fvar _125_585 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (let _125_587 = (let _125_586 = (FStar_Syntax_Syntax.as_arg body)
in (_125_586)::[])
in (_125_588, _125_587)))
in FStar_Syntax_Syntax.Tm_app (_125_589))
in (FStar_All.pipe_left mk _125_590)))))))
end))
end
| _46_1626 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 949 "FStar.Parser.ToSyntax.fst"
let push_quant = (fun q binders pats body -> (match (binders) with
| b::b'::_rest -> begin
(
# 951 "FStar.Parser.ToSyntax.fst"
let rest = (b')::_rest
in (
# 952 "FStar.Parser.ToSyntax.fst"
let body = (let _125_605 = (q (rest, pats, body))
in (let _125_604 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _125_605 _125_604 FStar_Parser_AST.Formula)))
in (let _125_606 = (q ((b)::[], [], body))
in (FStar_Parser_AST.mk_term _125_606 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _46_1640 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _125_607 = (unparen f)
in _125_607.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(
# 958 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env f)
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((l, f.FStar_Syntax_Syntax.pos, p)))))))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall (_1::_2::_3, pats, body) -> begin
(
# 965 "FStar.Parser.ToSyntax.fst"
let binders = (_1)::(_2)::_3
in (let _125_609 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _125_609)))
end
| FStar_Parser_AST.QExists (_1::_2::_3, pats, body) -> begin
(
# 969 "FStar.Parser.ToSyntax.fst"
let binders = (_1)::(_2)::_3
in (let _125_611 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _125_611)))
end
| FStar_Parser_AST.QForall (b::[], pats, body) -> begin
(desugar_quant FStar_Syntax_Const.forall_lid b pats body)
end
| FStar_Parser_AST.QExists (b::[], pats, body) -> begin
(desugar_quant FStar_Syntax_Const.exists_lid b pats body)
end
| FStar_Parser_AST.Paren (f) -> begin
(desugar_formula env f)
end
| _46_1698 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (
# 984 "FStar.Parser.ToSyntax.fst"
let _46_1722 = (FStar_List.fold_left (fun _46_1703 b -> (match (_46_1703) with
| (env, out) -> begin
(
# 985 "FStar.Parser.ToSyntax.fst"
let tk = (desugar_binder env (
# 985 "FStar.Parser.ToSyntax.fst"
let _46_1705 = b
in {FStar_Parser_AST.b = _46_1705.FStar_Parser_AST.b; FStar_Parser_AST.brange = _46_1705.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _46_1705.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(
# 988 "FStar.Parser.ToSyntax.fst"
let _46_1714 = (FStar_Parser_Env.push_bv env a)
in (match (_46_1714) with
| (env, a) -> begin
(
# 989 "FStar.Parser.ToSyntax.fst"
let a = (
# 989 "FStar.Parser.ToSyntax.fst"
let _46_1715 = a
in {FStar_Syntax_Syntax.ppname = _46_1715.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _46_1715.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (env, ((a, (trans_aqual b.FStar_Parser_AST.aqual)))::out))
end))
end
| _46_1719 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected binder", b.FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_46_1722) with
| (env, tpars) -> begin
(env, (FStar_List.rev tpars))
end)))
and desugar_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(let _125_618 = (desugar_typ env t)
in (Some (x), _125_618))
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _125_619 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None x.FStar_Ident.idRange)
in (Some (x), _125_619))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _125_620 = (desugar_typ env t)
in (None, _125_620))
end
| FStar_Parser_AST.Variable (x) -> begin
(Some (x), FStar_Syntax_Syntax.tun)
end))

# 1001 "FStar.Parser.ToSyntax.fst"
let mk_data_discriminators : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  FStar_Ident.lid  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun quals env t tps k datas -> (
# 1002 "FStar.Parser.ToSyntax.fst"
let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_Env.iface) || env.FStar_Parser_Env.admitted_iface) then begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (
# 1005 "FStar.Parser.ToSyntax.fst"
let binders = (let _125_636 = (let _125_635 = (FStar_Syntax_Util.arrow_formals k)
in (Prims.fst _125_635))
in (FStar_List.append tps _125_636))
in (
# 1006 "FStar.Parser.ToSyntax.fst"
let p = (FStar_Ident.range_of_lid t)
in (
# 1007 "FStar.Parser.ToSyntax.fst"
let _46_1749 = (FStar_Syntax_Util.args_of_binders binders)
in (match (_46_1749) with
| (binders, args) -> begin
(
# 1008 "FStar.Parser.ToSyntax.fst"
let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _46_1753 -> (match (_46_1753) with
| (x, _46_1752) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
in (
# 1009 "FStar.Parser.ToSyntax.fst"
let binders = (let _125_642 = (let _125_641 = (let _125_640 = (let _125_639 = (let _125_638 = (FStar_Syntax_Syntax.lid_as_fv t FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _125_638))
in (FStar_Syntax_Syntax.mk_Tm_app _125_639 args None p))
in (FStar_All.pipe_left FStar_Syntax_Syntax.null_binder _125_640))
in (_125_641)::[])
in (FStar_List.append imp_binders _125_642))
in (
# 1010 "FStar.Parser.ToSyntax.fst"
let disc_type = (let _125_645 = (let _125_644 = (let _125_643 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _125_643))
in (FStar_Syntax_Syntax.mk_Total _125_644))
in (FStar_Syntax_Util.arrow binders _125_645))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (
# 1012 "FStar.Parser.ToSyntax.fst"
let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (let _125_648 = (let _125_647 = (quals ((FStar_Syntax_Syntax.Logic)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in (disc_name, [], disc_type, _125_647, (FStar_Ident.range_of_lid disc_name)))
in FStar_Syntax_Syntax.Sig_declare_typ (_125_648)))))))))
end))))))

# 1015 "FStar.Parser.ToSyntax.fst"
let mk_indexed_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq refine_domain env tc lid inductive_tps imp_tps fields t -> (
# 1016 "FStar.Parser.ToSyntax.fst"
let p = (FStar_Ident.range_of_lid lid)
in (
# 1017 "FStar.Parser.ToSyntax.fst"
let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p))
in (
# 1018 "FStar.Parser.ToSyntax.fst"
let projectee = (fun ptyp -> (FStar_Syntax_Syntax.gen_bv "projectee" (Some (p)) ptyp))
in (
# 1019 "FStar.Parser.ToSyntax.fst"
let tps = (FStar_List.map2 (fun _46_1777 _46_1781 -> (match ((_46_1777, _46_1781)) with
| ((_46_1775, imp), (x, _46_1780)) -> begin
(x, imp)
end)) inductive_tps imp_tps)
in (
# 1020 "FStar.Parser.ToSyntax.fst"
let _46_1882 = (
# 1021 "FStar.Parser.ToSyntax.fst"
let _46_1785 = (FStar_Syntax_Util.head_and_args t)
in (match (_46_1785) with
| (head, args0) -> begin
(
# 1022 "FStar.Parser.ToSyntax.fst"
let args = (
# 1023 "FStar.Parser.ToSyntax.fst"
let rec arguments = (fun tps args -> (match ((tps, args)) with
| ([], _46_1791) -> begin
args
end
| (_46_1794, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Not enough arguments to type", (FStar_Ident.range_of_lid lid)))))
end
| ((_46_1799, Some (FStar_Syntax_Syntax.Implicit (_46_1801)))::tps', (_46_1808, Some (FStar_Syntax_Syntax.Implicit (_46_1810)))::args') -> begin
(arguments tps' args')
end
| ((_46_1818, Some (FStar_Syntax_Syntax.Implicit (_46_1820)))::tps', (_46_1828, _46_1830)::_46_1826) -> begin
(arguments tps' args)
end
| ((_46_1837, _46_1839)::_46_1835, (a, Some (FStar_Syntax_Syntax.Implicit (_46_1846)))::_46_1843) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected implicit annotation on argument", a.FStar_Syntax_Syntax.pos))))
end
| ((_46_1854, _46_1856)::tps', (_46_1861, _46_1863)::args') -> begin
(arguments tps' args')
end))
in (arguments inductive_tps args0))
in (
# 1032 "FStar.Parser.ToSyntax.fst"
let indices = (FStar_All.pipe_right args (FStar_List.map (fun _46_1868 -> (let _125_680 = (FStar_Syntax_Syntax.new_bv (Some (p)) FStar_Syntax_Syntax.tun)
in (FStar_All.pipe_right _125_680 FStar_Syntax_Syntax.mk_binder)))))
in (
# 1033 "FStar.Parser.ToSyntax.fst"
let arg_typ = (let _125_685 = (let _125_681 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _125_681))
in (let _125_684 = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _46_1873 -> (match (_46_1873) with
| (x, imp) -> begin
(let _125_683 = (FStar_Syntax_Syntax.bv_to_name x)
in (_125_683, imp))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app _125_685 _125_684 None p)))
in (
# 1035 "FStar.Parser.ToSyntax.fst"
let arg_binder = if (not (refine_domain)) then begin
(let _125_686 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder _125_686))
end else begin
(
# 1038 "FStar.Parser.ToSyntax.fst"
let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (
# 1039 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p)) arg_typ)
in (let _125_695 = (
# 1040 "FStar.Parser.ToSyntax.fst"
let _46_1877 = (projectee arg_typ)
in (let _125_694 = (let _125_693 = (let _125_692 = (let _125_691 = (let _125_687 = (FStar_Ident.set_lid_range disc_name p)
in (FStar_Syntax_Syntax.fvar _125_687 FStar_Syntax_Syntax.Delta_equational None))
in (let _125_690 = (let _125_689 = (let _125_688 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _125_688))
in (_125_689)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _125_691 _125_690 None p)))
in (FStar_Syntax_Util.b2t _125_692))
in (FStar_Syntax_Util.refine x _125_693))
in {FStar_Syntax_Syntax.ppname = _46_1877.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _46_1877.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _125_694}))
in (FStar_Syntax_Syntax.mk_binder _125_695))))
end
in (arg_binder, indices)))))
end))
in (match (_46_1882) with
| (arg_binder, indices) -> begin
(
# 1044 "FStar.Parser.ToSyntax.fst"
let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder))
in (
# 1045 "FStar.Parser.ToSyntax.fst"
let imp_binders = (let _125_697 = (FStar_All.pipe_right indices (FStar_List.map (fun _46_1887 -> (match (_46_1887) with
| (x, _46_1886) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
in (FStar_List.append imp_tps _125_697))
in (
# 1046 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (
# 1048 "FStar.Parser.ToSyntax.fst"
let arg = (FStar_Syntax_Util.arg_of_non_null_binder arg_binder)
in (
# 1050 "FStar.Parser.ToSyntax.fst"
let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _46_1895 -> (match (_46_1895) with
| (a, _46_1894) -> begin
(
# 1051 "FStar.Parser.ToSyntax.fst"
let _46_1899 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (_46_1899) with
| (field_name, _46_1898) -> begin
(
# 1052 "FStar.Parser.ToSyntax.fst"
let proj = (let _125_701 = (let _125_700 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.fv_to_tm _125_700))
in (FStar_Syntax_Syntax.mk_Tm_app _125_701 ((arg)::[]) None p))
in FStar_Syntax_Syntax.NT ((a, proj)))
end))
end))))
in (
# 1055 "FStar.Parser.ToSyntax.fst"
let ntps = (FStar_List.length tps)
in (
# 1056 "FStar.Parser.ToSyntax.fst"
let all_params = (FStar_List.append imp_tps fields)
in (let _125_737 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _46_1908 -> (match (_46_1908) with
| (x, _46_1907) -> begin
(
# 1059 "FStar.Parser.ToSyntax.fst"
let _46_1912 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_46_1912) with
| (field_name, _46_1911) -> begin
(
# 1060 "FStar.Parser.ToSyntax.fst"
let t = (let _125_705 = (let _125_704 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total _125_704))
in (FStar_Syntax_Util.arrow binders _125_705))
in (
# 1061 "FStar.Parser.ToSyntax.fst"
let only_decl = (((let _125_706 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _125_706)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _125_708 = (let _125_707 = (FStar_Parser_Env.current_module env)
in _125_707.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _125_708)))
in (
# 1065 "FStar.Parser.ToSyntax.fst"
let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (
# 1066 "FStar.Parser.ToSyntax.fst"
let quals = (fun q -> if only_decl then begin
(FStar_Syntax_Syntax.Assumption)::q
end else begin
q
end)
in (
# 1067 "FStar.Parser.ToSyntax.fst"
let quals = (quals ((FStar_Syntax_Syntax.Projector ((lid, x.FStar_Syntax_Syntax.ppname)))::iquals))
in (
# 1068 "FStar.Parser.ToSyntax.fst"
let decl = FStar_Syntax_Syntax.Sig_declare_typ ((field_name, [], t, quals, (FStar_Ident.range_of_lid field_name)))
in if only_decl then begin
(decl)::[]
end else begin
(
# 1071 "FStar.Parser.ToSyntax.fst"
let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (
# 1072 "FStar.Parser.ToSyntax.fst"
let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _46_1924 -> (match (_46_1924) with
| (x, imp) -> begin
(
# 1073 "FStar.Parser.ToSyntax.fst"
let b = (FStar_Syntax_Syntax.is_implicit imp)
in if ((i + ntps) = j) then begin
(let _125_713 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in (_125_713, b))
end else begin
if (b && (j < ntps)) then begin
(let _125_717 = (let _125_716 = (let _125_715 = (let _125_714 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (_125_714, FStar_Syntax_Syntax.tun))
in FStar_Syntax_Syntax.Pat_dot_term (_125_715))
in (pos _125_716))
in (_125_717, b))
end else begin
(let _125_720 = (let _125_719 = (let _125_718 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_125_718))
in (pos _125_719))
in (_125_720, b))
end
end)
end))))
in (
# 1079 "FStar.Parser.ToSyntax.fst"
let pat = (let _125_725 = (let _125_723 = (let _125_722 = (let _125_721 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in (_125_721, arg_pats))
in FStar_Syntax_Syntax.Pat_cons (_125_722))
in (FStar_All.pipe_right _125_723 pos))
in (let _125_724 = (FStar_Syntax_Syntax.bv_to_name projection)
in (_125_725, None, _125_724)))
in (
# 1080 "FStar.Parser.ToSyntax.fst"
let body = (let _125_729 = (let _125_728 = (let _125_727 = (let _125_726 = (FStar_Syntax_Util.branch pat)
in (_125_726)::[])
in (arg_exp, _125_727))
in FStar_Syntax_Syntax.Tm_match (_125_728))
in (FStar_Syntax_Syntax.mk _125_729 None p))
in (
# 1081 "FStar.Parser.ToSyntax.fst"
let imp = (no_annot_abs binders body)
in (
# 1082 "FStar.Parser.ToSyntax.fst"
let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end else begin
FStar_Syntax_Syntax.Delta_equational
end
in (
# 1085 "FStar.Parser.ToSyntax.fst"
let lb = (let _125_731 = (let _125_730 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (_125_730))
in {FStar_Syntax_Syntax.lbname = _125_731; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = imp})
in (
# 1090 "FStar.Parser.ToSyntax.fst"
let impl = (let _125_736 = (let _125_735 = (let _125_734 = (let _125_733 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _125_733 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_125_734)::[])
in ((false, (lb)::[]), p, _125_735, quals))
in FStar_Syntax_Syntax.Sig_let (_125_736))
in if no_decl then begin
(impl)::[]
end else begin
(decl)::(impl)::[]
end))))))))
end))))))
end))
end))))
in (FStar_All.pipe_right _125_737 FStar_List.flatten)))))))))
end)))))))

# 1093 "FStar.Parser.ToSyntax.fst"
let mk_data_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env _46_1938 -> (match (_46_1938) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _46_1941, t, l, n, quals, _46_1947, _46_1949) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(
# 1096 "FStar.Parser.ToSyntax.fst"
let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _46_10 -> (match (_46_10) with
| FStar_Syntax_Syntax.RecordConstructor (_46_1954) -> begin
true
end
| _46_1957 -> begin
false
end)))) then begin
false
end else begin
(match ((FStar_Parser_Env.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > 1)
end
| _46_1961 -> begin
true
end)
end
in (
# 1102 "FStar.Parser.ToSyntax.fst"
let _46_1965 = (FStar_Syntax_Util.arrow_formals t)
in (match (_46_1965) with
| (formals, cod) -> begin
(match (formals) with
| [] -> begin
[]
end
| _46_1968 -> begin
(
# 1106 "FStar.Parser.ToSyntax.fst"
let fv_qual = (match ((FStar_Util.find_map quals (fun _46_11 -> (match (_46_11) with
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((lid, fns)))
end
| _46_1973 -> begin
None
end)))) with
| None -> begin
FStar_Syntax_Syntax.Data_ctor
end
| Some (q) -> begin
q
end)
in (
# 1109 "FStar.Parser.ToSyntax.fst"
let iquals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract iquals) then begin
(FStar_Syntax_Syntax.Private)::iquals
end else begin
iquals
end
in (
# 1112 "FStar.Parser.ToSyntax.fst"
let _46_1981 = (FStar_Util.first_N n formals)
in (match (_46_1981) with
| (tps, rest) -> begin
(mk_indexed_projectors iquals fv_qual refine_domain env l lid inductive_tps tps rest cod)
end))))
end)
end)))
end
| _46_1983 -> begin
[]
end)
end))

# 1118 "FStar.Parser.ToSyntax.fst"
let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (
# 1119 "FStar.Parser.ToSyntax.fst"
let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _125_762 = (incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (_125_762))
end else begin
(incr_delta_qualifier t)
end
in (
# 1122 "FStar.Parser.ToSyntax.fst"
let lb = (let _125_767 = (let _125_763 = (FStar_Syntax_Syntax.lid_as_fv lid dd None)
in FStar_Util.Inr (_125_763))
in (let _125_766 = (let _125_764 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars _125_764))
in (let _125_765 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = _125_767; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = _125_766; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _125_765})))
in FStar_Syntax_Syntax.Sig_let (((false, (lb)::[]), rng, lids, quals)))))

# 1131 "FStar.Parser.ToSyntax.fst"
let rec desugar_tycon : FStar_Parser_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (
# 1132 "FStar.Parser.ToSyntax.fst"
let tycon_id = (fun _46_12 -> (match (_46_12) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (
# 1137 "FStar.Parser.ToSyntax.fst"
let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _125_781 = (let _125_780 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_125_780))
in (FStar_Parser_AST.mk_term _125_781 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| (FStar_Parser_AST.TAnnotated (a, _)) | (FStar_Parser_AST.TVariable (a)) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar (a)) a.FStar_Ident.idRange FStar_Parser_AST.Type)
end
| FStar_Parser_AST.NoName (t) -> begin
t
end))
in (
# 1143 "FStar.Parser.ToSyntax.fst"
let tot = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) rng FStar_Parser_AST.Expr)
in (
# 1144 "FStar.Parser.ToSyntax.fst"
let with_constructor_effect = (fun t -> (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((tot, t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level))
in (
# 1145 "FStar.Parser.ToSyntax.fst"
let apply_binders = (fun t binders -> (
# 1146 "FStar.Parser.ToSyntax.fst"
let imp_of_aqual = (fun b -> (match (b.FStar_Parser_AST.aqual) with
| Some (FStar_Parser_AST.Implicit) -> begin
FStar_Parser_AST.Hash
end
| _46_2058 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _125_794 = (let _125_793 = (let _125_792 = (binder_to_term b)
in (out, _125_792, (imp_of_aqual b)))
in FStar_Parser_AST.App (_125_793))
in (FStar_Parser_AST.mk_term _125_794 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (
# 1151 "FStar.Parser.ToSyntax.fst"
let tycon_record_as_variant = (fun _46_13 -> (match (_46_13) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(
# 1153 "FStar.Parser.ToSyntax.fst"
let constrName = (FStar_Ident.mk_ident ((Prims.strcat "Mk" id.FStar_Ident.idText), id.FStar_Ident.idRange))
in (
# 1154 "FStar.Parser.ToSyntax.fst"
let mfields = (FStar_List.map (fun _46_2071 -> (match (_46_2071) with
| (x, t) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated (((FStar_Syntax_Util.mangle_field_name x), t))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (
# 1155 "FStar.Parser.ToSyntax.fst"
let result = (let _125_800 = (let _125_799 = (let _125_798 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_125_798))
in (FStar_Parser_AST.mk_term _125_799 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _125_800 parms))
in (
# 1156 "FStar.Parser.ToSyntax.fst"
let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _125_802 = (FStar_All.pipe_right fields (FStar_List.map (fun _46_2078 -> (match (_46_2078) with
| (x, _46_2077) -> begin
(FStar_Parser_Env.qualify env x)
end))))
in (FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _125_802))))))
end
| _46_2080 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1160 "FStar.Parser.ToSyntax.fst"
let desugar_abstract_tc = (fun quals _env mutuals _46_14 -> (match (_46_14) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(
# 1162 "FStar.Parser.ToSyntax.fst"
let _46_2094 = (typars_of_binders _env binders)
in (match (_46_2094) with
| (_env', typars) -> begin
(
# 1163 "FStar.Parser.ToSyntax.fst"
let k = (match (kopt) with
| None -> begin
FStar_Syntax_Util.ktype
end
| Some (k) -> begin
(desugar_term _env' k)
end)
in (
# 1166 "FStar.Parser.ToSyntax.fst"
let tconstr = (let _125_813 = (let _125_812 = (let _125_811 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_125_811))
in (FStar_Parser_AST.mk_term _125_812 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _125_813 binders))
in (
# 1167 "FStar.Parser.ToSyntax.fst"
let qlid = (FStar_Parser_Env.qualify _env id)
in (
# 1168 "FStar.Parser.ToSyntax.fst"
let typars = (FStar_Syntax_Subst.close_binders typars)
in (
# 1169 "FStar.Parser.ToSyntax.fst"
let k = (FStar_Syntax_Subst.close typars k)
in (
# 1170 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_inductive_typ ((qlid, [], typars, k, mutuals, [], quals, rng))
in (
# 1171 "FStar.Parser.ToSyntax.fst"
let _env = (FStar_Parser_Env.push_top_level_rec_binding _env id FStar_Syntax_Syntax.Delta_constant)
in (
# 1172 "FStar.Parser.ToSyntax.fst"
let _env2 = (FStar_Parser_Env.push_top_level_rec_binding _env' id FStar_Syntax_Syntax.Delta_constant)
in (_env, _env2, se, tconstr)))))))))
end))
end
| _46_2107 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (
# 1175 "FStar.Parser.ToSyntax.fst"
let push_tparams = (fun env bs -> (
# 1176 "FStar.Parser.ToSyntax.fst"
let _46_2122 = (FStar_List.fold_left (fun _46_2113 _46_2116 -> (match ((_46_2113, _46_2116)) with
| ((env, tps), (x, imp)) -> begin
(
# 1177 "FStar.Parser.ToSyntax.fst"
let _46_2119 = (FStar_Parser_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (_46_2119) with
| (env, y) -> begin
(env, ((y, imp))::tps)
end))
end)) (env, []) bs)
in (match (_46_2122) with
| (env, bs) -> begin
(env, (FStar_List.rev bs))
end)))
in (match (tcs) with
| FStar_Parser_AST.TyconAbstract (_46_2124)::[] -> begin
(
# 1182 "FStar.Parser.ToSyntax.fst"
let tc = (FStar_List.hd tcs)
in (
# 1183 "FStar.Parser.ToSyntax.fst"
let _46_2135 = (desugar_abstract_tc quals env [] tc)
in (match (_46_2135) with
| (_46_2129, _46_2131, se, _46_2134) -> begin
(
# 1184 "FStar.Parser.ToSyntax.fst"
let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _46_2138, typars, k, [], [], quals, rng) -> begin
(
# 1186 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
quals
end else begin
(
# 1188 "FStar.Parser.ToSyntax.fst"
let _46_2147 = (let _125_821 = (FStar_Range.string_of_range rng)
in (let _125_820 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" _125_821 _125_820)))
in (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals)
end
in (
# 1191 "FStar.Parser.ToSyntax.fst"
let t = (match (typars) with
| [] -> begin
k
end
| _46_2152 -> begin
(let _125_824 = (let _125_823 = (let _125_822 = (FStar_Syntax_Syntax.mk_Total k)
in (typars, _125_822))
in FStar_Syntax_Syntax.Tm_arrow (_125_823))
in (FStar_Syntax_Syntax.mk _125_824 None rng))
end)
in FStar_Syntax_Syntax.Sig_declare_typ ((l, [], t, quals, rng))))
end
| _46_2155 -> begin
se
end)
in (
# 1196 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))
end)))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t)::[] -> begin
(
# 1201 "FStar.Parser.ToSyntax.fst"
let _46_2167 = (typars_of_binders env binders)
in (match (_46_2167) with
| (env', typars) -> begin
(
# 1202 "FStar.Parser.ToSyntax.fst"
let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _46_15 -> (match (_46_15) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| _46_2172 -> begin
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
# 1208 "FStar.Parser.ToSyntax.fst"
let t0 = t
in (
# 1209 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _46_16 -> (match (_46_16) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| _46_2180 -> begin
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
# 1214 "FStar.Parser.ToSyntax.fst"
let se = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Effect)) then begin
(
# 1216 "FStar.Parser.ToSyntax.fst"
let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (
# 1217 "FStar.Parser.ToSyntax.fst"
let typars = (FStar_Syntax_Subst.close_binders typars)
in (
# 1218 "FStar.Parser.ToSyntax.fst"
let c = (FStar_Syntax_Subst.close_comp typars c)
in (let _125_830 = (let _125_829 = (FStar_Parser_Env.qualify env id)
in (let _125_828 = (FStar_All.pipe_right quals (FStar_List.filter (fun _46_17 -> (match (_46_17) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| _46_2188 -> begin
true
end))))
in (_125_829, [], typars, c, _125_828, rng)))
in FStar_Syntax_Syntax.Sig_effect_abbrev (_125_830)))))
end else begin
(
# 1220 "FStar.Parser.ToSyntax.fst"
let t = (desugar_typ env' t)
in (
# 1221 "FStar.Parser.ToSyntax.fst"
let nm = (FStar_Parser_Env.qualify env id)
in (mk_typ_abbrev nm [] typars k t ((nm)::[]) quals rng)))
end
in (
# 1224 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[]))))))
end))
end
| FStar_Parser_AST.TyconRecord (_46_2194)::[] -> begin
(
# 1228 "FStar.Parser.ToSyntax.fst"
let trec = (FStar_List.hd tcs)
in (
# 1229 "FStar.Parser.ToSyntax.fst"
let _46_2200 = (tycon_record_as_variant trec)
in (match (_46_2200) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| _46_2204::_46_2202 -> begin
(
# 1233 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1234 "FStar.Parser.ToSyntax.fst"
let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_Env.qualify env) (tycon_id x))) tcs)
in (
# 1235 "FStar.Parser.ToSyntax.fst"
let rec collect_tcs = (fun quals et tc -> (
# 1236 "FStar.Parser.ToSyntax.fst"
let _46_2215 = et
in (match (_46_2215) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_46_2217) -> begin
(
# 1239 "FStar.Parser.ToSyntax.fst"
let trec = tc
in (
# 1240 "FStar.Parser.ToSyntax.fst"
let _46_2222 = (tycon_record_as_variant trec)
in (match (_46_2222) with
| (t, fs) -> begin
(collect_tcs ((FStar_Syntax_Syntax.RecordType (fs))::quals) (env, tcs) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(
# 1243 "FStar.Parser.ToSyntax.fst"
let _46_2234 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_46_2234) with
| (env, _46_2231, se, tconstr) -> begin
(env, (FStar_Util.Inl ((se, constructors, tconstr, quals)))::tcs)
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(
# 1246 "FStar.Parser.ToSyntax.fst"
let _46_2246 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_46_2246) with
| (env, _46_2243, se, tconstr) -> begin
(env, (FStar_Util.Inr ((se, t, quals)))::tcs)
end))
end
| _46_2248 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (
# 1249 "FStar.Parser.ToSyntax.fst"
let _46_2251 = (FStar_List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_46_2251) with
| (env, tcs) -> begin
(
# 1250 "FStar.Parser.ToSyntax.fst"
let tcs = (FStar_List.rev tcs)
in (
# 1251 "FStar.Parser.ToSyntax.fst"
let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _46_19 -> (match (_46_19) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, _46_2259, _46_2261, _46_2263, _46_2265), t, quals) -> begin
(
# 1253 "FStar.Parser.ToSyntax.fst"
let _46_2275 = (push_tparams env tpars)
in (match (_46_2275) with
| (env_tps, _46_2274) -> begin
(
# 1254 "FStar.Parser.ToSyntax.fst"
let t = (desugar_term env_tps t)
in (let _125_840 = (let _125_839 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in ([], _125_839))
in (_125_840)::[]))
end))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, _46_2283, tags, _46_2286), constrs, tconstr, quals) -> begin
(
# 1258 "FStar.Parser.ToSyntax.fst"
let tycon = (tname, tpars, k)
in (
# 1259 "FStar.Parser.ToSyntax.fst"
let _46_2297 = (push_tparams env tpars)
in (match (_46_2297) with
| (env_tps, tps) -> begin
(
# 1260 "FStar.Parser.ToSyntax.fst"
let data_tpars = (FStar_List.map (fun _46_2301 -> (match (_46_2301) with
| (x, _46_2300) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end)) tps)
in (
# 1261 "FStar.Parser.ToSyntax.fst"
let _46_2325 = (let _125_852 = (FStar_All.pipe_right constrs (FStar_List.map (fun _46_2306 -> (match (_46_2306) with
| (id, topt, of_notation) -> begin
(
# 1263 "FStar.Parser.ToSyntax.fst"
let t = if of_notation then begin
(match (topt) with
| Some (t) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level None))::[], tconstr))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
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
# 1271 "FStar.Parser.ToSyntax.fst"
let t = (let _125_844 = (FStar_Parser_Env.default_total env_tps)
in (let _125_843 = (close env_tps t)
in (desugar_term _125_844 _125_843)))
in (
# 1272 "FStar.Parser.ToSyntax.fst"
let name = (FStar_Parser_Env.qualify env id)
in (
# 1273 "FStar.Parser.ToSyntax.fst"
let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _46_18 -> (match (_46_18) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| _46_2320 -> begin
[]
end))))
in (
# 1276 "FStar.Parser.ToSyntax.fst"
let ntps = (FStar_List.length data_tpars)
in (let _125_851 = (let _125_850 = (let _125_849 = (let _125_848 = (let _125_847 = (let _125_846 = (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total _125_846))
in (FStar_Syntax_Util.arrow data_tpars _125_847))
in (name, univs, _125_848, tname, ntps, quals, mutuals, rng))
in FStar_Syntax_Syntax.Sig_datacon (_125_849))
in (tps, _125_850))
in (name, _125_851)))))))
end))))
in (FStar_All.pipe_left FStar_List.split _125_852))
in (match (_46_2325) with
| (constrNames, constrs) -> begin
(([], FStar_Syntax_Syntax.Sig_inductive_typ ((tname, univs, tpars, k, mutuals, constrNames, tags, rng))))::constrs
end)))
end)))
end
| _46_2327 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1281 "FStar.Parser.ToSyntax.fst"
let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (
# 1282 "FStar.Parser.ToSyntax.fst"
let bundle = (let _125_854 = (let _125_853 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _125_853, rng))
in FStar_Syntax_Syntax.Sig_bundle (_125_854))
in (
# 1283 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 bundle)
in (
# 1284 "FStar.Parser.ToSyntax.fst"
let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projectors quals env)))
in (
# 1285 "FStar.Parser.ToSyntax.fst"
let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _46_20 -> (match (_46_20) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, _46_2336, tps, k, _46_2340, constrs, quals, _46_2344) when ((FStar_List.length constrs) > 1) -> begin
(
# 1287 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract quals) then begin
(FStar_Syntax_Syntax.Private)::quals
end else begin
quals
end
in (mk_data_discriminators quals env tname tps k constrs))
end
| _46_2349 -> begin
[]
end))))
in (
# 1292 "FStar.Parser.ToSyntax.fst"
let ops = (FStar_List.append discs data_ops)
in (
# 1293 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env ops)
in (env, (FStar_List.append ((bundle)::[]) ops)))))))))))
end)))))
end
| [] -> begin
(FStar_All.failwith "impossible")
end))))))))))

# 1298 "FStar.Parser.ToSyntax.fst"
let desugar_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.binder Prims.list) = (fun env binders -> (
# 1299 "FStar.Parser.ToSyntax.fst"
let _46_2373 = (FStar_List.fold_left (fun _46_2358 b -> (match (_46_2358) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| (Some (a), k) -> begin
(
# 1302 "FStar.Parser.ToSyntax.fst"
let _46_2366 = (FStar_Parser_Env.push_bv env a)
in (match (_46_2366) with
| (env, a) -> begin
(let _125_863 = (let _125_862 = (FStar_Syntax_Syntax.mk_binder (
# 1303 "FStar.Parser.ToSyntax.fst"
let _46_2367 = a
in {FStar_Syntax_Syntax.ppname = _46_2367.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _46_2367.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (_125_862)::binders)
in (env, _125_863))
end))
end
| _46_2370 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Missing name in binder", b.FStar_Parser_AST.brange))))
end)
end)) (env, []) binders)
in (match (_46_2373) with
| (env, binders) -> begin
(env, (FStar_List.rev binders))
end)))

# 1308 "FStar.Parser.ToSyntax.fst"
let rec desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(
# 1310 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_pragma (((trans_pragma p), d.FStar_Parser_AST.drange))
in (env, (se)::[]))
end
| FStar_Parser_AST.Open (lid) -> begin
(
# 1314 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_namespace env lid)
in (env, []))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(let _125_868 = (FStar_List.map trans_qual qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _125_868 tcs))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _125_870 = (let _125_869 = (desugar_term_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((isrec, lets, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Syntax_Subst.compress _125_869))
in _125_870.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let (lbs, _46_2393) -> begin
(
# 1323 "FStar.Parser.ToSyntax.fst"
let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (
# 1324 "FStar.Parser.ToSyntax.fst"
let quals = (match (quals) with
| _46_2401::_46_2399 -> begin
(FStar_List.map trans_qual quals)
end
| _46_2404 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _46_21 -> (match (_46_21) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (_46_2415); FStar_Syntax_Syntax.lbunivs = _46_2413; FStar_Syntax_Syntax.lbtyp = _46_2411; FStar_Syntax_Syntax.lbeff = _46_2409; FStar_Syntax_Syntax.lbdef = _46_2407} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _46_2425; FStar_Syntax_Syntax.lbtyp = _46_2423; FStar_Syntax_Syntax.lbeff = _46_2421; FStar_Syntax_Syntax.lbdef = _46_2419} -> begin
(FStar_Parser_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (
# 1329 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right lets (FStar_Util.for_some (fun _46_2433 -> (match (_46_2433) with
| (_46_2431, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end)))) then begin
(FStar_Syntax_Syntax.Logic)::quals
end else begin
quals
end
in (
# 1333 "FStar.Parser.ToSyntax.fst"
let lbs = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _125_875 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 1335 "FStar.Parser.ToSyntax.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 1336 "FStar.Parser.ToSyntax.fst"
let _46_2437 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((
# 1336 "FStar.Parser.ToSyntax.fst"
let _46_2439 = fv
in {FStar_Syntax_Syntax.fv_name = _46_2439.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = _46_2439.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = _46_2437.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _46_2437.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _46_2437.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _46_2437.FStar_Syntax_Syntax.lbdef})))))
in ((Prims.fst lbs), _125_875))
end else begin
lbs
end
in (
# 1338 "FStar.Parser.ToSyntax.fst"
let s = (let _125_878 = (let _125_877 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (lbs, d.FStar_Parser_AST.drange, _125_877, quals))
in FStar_Syntax_Syntax.Sig_let (_125_878))
in (
# 1339 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env s)
in (env, (s)::[])))))))
end
| _46_2446 -> begin
(FStar_All.failwith "Desugaring a let did not produce a let")
end)
end
| FStar_Parser_AST.Main (t) -> begin
(
# 1345 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env t)
in (
# 1346 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, d.FStar_Parser_AST.drange))
in (env, (se)::[])))
end
| FStar_Parser_AST.Assume (atag, id, t) -> begin
(
# 1350 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env t)
in (let _125_882 = (let _125_881 = (let _125_880 = (let _125_879 = (FStar_Parser_Env.qualify env id)
in (_125_879, f, (FStar_Syntax_Syntax.Assumption)::[], d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Sig_assume (_125_880))
in (_125_881)::[])
in (env, _125_882)))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(
# 1354 "FStar.Parser.ToSyntax.fst"
let t = (let _125_883 = (close_fun env t)
in (desugar_term env _125_883))
in (
# 1355 "FStar.Parser.ToSyntax.fst"
let quals = if (env.FStar_Parser_Env.iface && env.FStar_Parser_Env.admitted_iface) then begin
(FStar_Parser_AST.Assumption)::quals
end else begin
quals
end
in (
# 1356 "FStar.Parser.ToSyntax.fst"
let se = (let _125_886 = (let _125_885 = (FStar_Parser_Env.qualify env id)
in (let _125_884 = (FStar_List.map trans_qual quals)
in (_125_885, [], t, _125_884, d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_declare_typ (_125_886))
in (
# 1357 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(
# 1361 "FStar.Parser.ToSyntax.fst"
let t = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (
# 1362 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env id)
in (
# 1363 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_datacon ((l, [], t, FStar_Syntax_Const.exn_lid, 0, (FStar_Syntax_Syntax.ExceptionConstructor)::[], (FStar_Syntax_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (
# 1364 "FStar.Parser.ToSyntax.fst"
let se' = FStar_Syntax_Syntax.Sig_bundle (((se)::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (
# 1365 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se')
in (
# 1366 "FStar.Parser.ToSyntax.fst"
let data_ops = (mk_data_projectors [] env ([], se))
in (
# 1367 "FStar.Parser.ToSyntax.fst"
let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (
# 1368 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops))))))))))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(
# 1372 "FStar.Parser.ToSyntax.fst"
let t = (desugar_term env term)
in (
# 1373 "FStar.Parser.ToSyntax.fst"
let t = (let _125_890 = (let _125_887 = (FStar_Syntax_Syntax.null_binder t)
in (_125_887)::[])
in (let _125_889 = (let _125_888 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _125_888))
in (FStar_Syntax_Util.arrow _125_890 _125_889)))
in (
# 1374 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env id)
in (
# 1375 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_datacon ((l, [], t, FStar_Syntax_Const.exn_lid, 0, (FStar_Syntax_Syntax.ExceptionConstructor)::[], (FStar_Syntax_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (
# 1376 "FStar.Parser.ToSyntax.fst"
let se' = FStar_Syntax_Syntax.Sig_bundle (((se)::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (
# 1377 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se')
in (
# 1378 "FStar.Parser.ToSyntax.fst"
let data_ops = (mk_data_projectors [] env ([], se))
in (
# 1379 "FStar.Parser.ToSyntax.fst"
let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (
# 1380 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops)))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(
# 1384 "FStar.Parser.ToSyntax.fst"
let _46_2499 = (desugar_binders env binders)
in (match (_46_2499) with
| (env_k, binders) -> begin
(
# 1385 "FStar.Parser.ToSyntax.fst"
let k = (desugar_term env_k k)
in (
# 1386 "FStar.Parser.ToSyntax.fst"
let name = (FStar_Parser_Env.qualify env id)
in (
# 1387 "FStar.Parser.ToSyntax.fst"
let se = (mk_typ_abbrev name [] binders FStar_Syntax_Syntax.tun k ((name)::[]) [] d.FStar_Parser_AST.drange)
in (
# 1388 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))))
end))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(
# 1392 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1393 "FStar.Parser.ToSyntax.fst"
let _46_2515 = (desugar_binders env eff_binders)
in (match (_46_2515) with
| (env, binders) -> begin
(
# 1394 "FStar.Parser.ToSyntax.fst"
let _46_2526 = (
# 1395 "FStar.Parser.ToSyntax.fst"
let _46_2518 = (head_and_args defn)
in (match (_46_2518) with
| (head, args) -> begin
(
# 1396 "FStar.Parser.ToSyntax.fst"
let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_defn env) l)
end
| _46_2522 -> begin
(let _125_895 = (let _125_894 = (let _125_893 = (let _125_892 = (let _125_891 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat "Effect " _125_891))
in (Prims.strcat _125_892 " not found"))
in (_125_893, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_125_894))
in (Prims.raise _125_895))
end)
in (let _125_896 = (desugar_args env args)
in (ed, _125_896)))
end))
in (match (_46_2526) with
| (ed, args) -> begin
(
# 1400 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_Syntax_Subst.close_binders binders)
in (
# 1401 "FStar.Parser.ToSyntax.fst"
let sub = (fun _46_2532 -> (match (_46_2532) with
| (_46_2530, x) -> begin
(
# 1402 "FStar.Parser.ToSyntax.fst"
let _46_2535 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (_46_2535) with
| (edb, x) -> begin
(
# 1403 "FStar.Parser.ToSyntax.fst"
let s = (FStar_Syntax_Util.subst_of_list edb args)
in (let _125_900 = (let _125_899 = (FStar_Syntax_Subst.subst s x)
in (FStar_Syntax_Subst.close binders _125_899))
in ([], _125_900)))
end))
end))
in (
# 1405 "FStar.Parser.ToSyntax.fst"
let ed = (let _125_917 = (FStar_List.map trans_qual quals)
in (let _125_916 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _125_915 = (let _125_901 = (sub ([], ed.FStar_Syntax_Syntax.signature))
in (Prims.snd _125_901))
in (let _125_914 = (sub ed.FStar_Syntax_Syntax.ret)
in (let _125_913 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (let _125_912 = (sub ed.FStar_Syntax_Syntax.bind_wlp)
in (let _125_911 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (let _125_910 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (let _125_909 = (sub ed.FStar_Syntax_Syntax.ite_wlp)
in (let _125_908 = (sub ed.FStar_Syntax_Syntax.wp_binop)
in (let _125_907 = (sub ed.FStar_Syntax_Syntax.wp_as_type)
in (let _125_906 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (let _125_905 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (let _125_904 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (let _125_903 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (let _125_902 = (sub ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _125_917; FStar_Syntax_Syntax.mname = _125_916; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = _125_915; FStar_Syntax_Syntax.ret = _125_914; FStar_Syntax_Syntax.bind_wp = _125_913; FStar_Syntax_Syntax.bind_wlp = _125_912; FStar_Syntax_Syntax.if_then_else = _125_911; FStar_Syntax_Syntax.ite_wp = _125_910; FStar_Syntax_Syntax.ite_wlp = _125_909; FStar_Syntax_Syntax.wp_binop = _125_908; FStar_Syntax_Syntax.wp_as_type = _125_907; FStar_Syntax_Syntax.close_wp = _125_906; FStar_Syntax_Syntax.assert_p = _125_905; FStar_Syntax_Syntax.assume_p = _125_904; FStar_Syntax_Syntax.null_wp = _125_903; FStar_Syntax_Syntax.trivial = _125_902}))))))))))))))))
in (
# 1425 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (
# 1426 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 se)
in (env, (se)::[]))))))
end))
end)))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls)) -> begin
(
# 1430 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1431 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.enter_monad_scope env eff_name)
in (
# 1432 "FStar.Parser.ToSyntax.fst"
let _46_2553 = (desugar_binders env eff_binders)
in (match (_46_2553) with
| (env, binders) -> begin
(
# 1433 "FStar.Parser.ToSyntax.fst"
let eff_k = (let _125_918 = (FStar_Parser_Env.default_total env)
in (desugar_term _125_918 eff_kind))
in (
# 1434 "FStar.Parser.ToSyntax.fst"
let _46_2564 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _46_2557 decl -> (match (_46_2557) with
| (env, out) -> begin
(
# 1435 "FStar.Parser.ToSyntax.fst"
let _46_2561 = (desugar_decl env decl)
in (match (_46_2561) with
| (env, ses) -> begin
(let _125_922 = (let _125_921 = (FStar_List.hd ses)
in (_125_921)::out)
in (env, _125_922))
end))
end)) (env, [])))
in (match (_46_2564) with
| (env, decls) -> begin
(
# 1437 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_Syntax_Subst.close_binders binders)
in (
# 1438 "FStar.Parser.ToSyntax.fst"
let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (
# 1439 "FStar.Parser.ToSyntax.fst"
let lookup = (fun s -> (
# 1440 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env (FStar_Ident.mk_ident (s, d.FStar_Parser_AST.drange)))
in (let _125_926 = (let _125_925 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) _125_925))
in ([], _125_926))))
in (
# 1442 "FStar.Parser.ToSyntax.fst"
let ed = (let _125_941 = (FStar_List.map trans_qual quals)
in (let _125_940 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _125_939 = (lookup "return")
in (let _125_938 = (lookup "bind_wp")
in (let _125_937 = (lookup "bind_wlp")
in (let _125_936 = (lookup "if_then_else")
in (let _125_935 = (lookup "ite_wp")
in (let _125_934 = (lookup "ite_wlp")
in (let _125_933 = (lookup "wp_binop")
in (let _125_932 = (lookup "wp_as_type")
in (let _125_931 = (lookup "close_wp")
in (let _125_930 = (lookup "assert_p")
in (let _125_929 = (lookup "assume_p")
in (let _125_928 = (lookup "null_wp")
in (let _125_927 = (lookup "trivial")
in {FStar_Syntax_Syntax.qualifiers = _125_941; FStar_Syntax_Syntax.mname = _125_940; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret = _125_939; FStar_Syntax_Syntax.bind_wp = _125_938; FStar_Syntax_Syntax.bind_wlp = _125_937; FStar_Syntax_Syntax.if_then_else = _125_936; FStar_Syntax_Syntax.ite_wp = _125_935; FStar_Syntax_Syntax.ite_wlp = _125_934; FStar_Syntax_Syntax.wp_binop = _125_933; FStar_Syntax_Syntax.wp_as_type = _125_932; FStar_Syntax_Syntax.close_wp = _125_931; FStar_Syntax_Syntax.assert_p = _125_930; FStar_Syntax_Syntax.assume_p = _125_929; FStar_Syntax_Syntax.null_wp = _125_928; FStar_Syntax_Syntax.trivial = _125_927})))))))))))))))
in (
# 1462 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (
# 1463 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 se)
in (env, (se)::[])))))))
end)))
end))))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(
# 1467 "FStar.Parser.ToSyntax.fst"
let lookup = (fun l -> (match ((FStar_Parser_Env.try_lookup_effect_name env l)) with
| None -> begin
(let _125_948 = (let _125_947 = (let _125_946 = (let _125_945 = (let _125_944 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat "Effect name " _125_944))
in (Prims.strcat _125_945 " not found"))
in (_125_946, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_125_947))
in (Prims.raise _125_948))
end
| Some (l) -> begin
l
end))
in (
# 1470 "FStar.Parser.ToSyntax.fst"
let src = (lookup l.FStar_Parser_AST.msource)
in (
# 1471 "FStar.Parser.ToSyntax.fst"
let dst = (lookup l.FStar_Parser_AST.mdest)
in (
# 1472 "FStar.Parser.ToSyntax.fst"
let lift = (let _125_949 = (desugar_term env l.FStar_Parser_AST.lift_op)
in ([], _125_949))
in (
# 1473 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect (({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift = lift}, d.FStar_Parser_AST.drange))
in (env, (se)::[]))))))
end))

# 1476 "FStar.Parser.ToSyntax.fst"
let desugar_decls : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _46_2588 d -> (match (_46_2588) with
| (env, sigelts) -> begin
(
# 1478 "FStar.Parser.ToSyntax.fst"
let _46_2592 = (desugar_decl env d)
in (match (_46_2592) with
| (env, se) -> begin
(env, (FStar_List.append sigelts se))
end))
end)) (env, []) decls))

# 1481 "FStar.Parser.ToSyntax.fst"
let open_prims_all : FStar_Parser_AST.decl Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.all_lid)) FStar_Range.dummyRange))::[]

# 1488 "FStar.Parser.ToSyntax.fst"
let desugar_modul_common : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (
# 1489 "FStar.Parser.ToSyntax.fst"
let open_ns = (fun mname d -> (
# 1490 "FStar.Parser.ToSyntax.fst"
let d = if ((FStar_List.length mname.FStar_Ident.ns) <> 0) then begin
(let _125_968 = (let _125_967 = (let _125_966 = (FStar_Ident.lid_of_ids mname.FStar_Ident.ns)
in FStar_Parser_AST.Open (_125_966))
in (FStar_Parser_AST.mk_decl _125_967 (FStar_Ident.range_of_lid mname)))
in (_125_968)::d)
end else begin
d
end
in d))
in (
# 1494 "FStar.Parser.ToSyntax.fst"
let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod) -> begin
(FStar_Parser_Env.finish_module_or_interface env prev_mod)
end)
in (
# 1497 "FStar.Parser.ToSyntax.fst"
let _46_2619 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _125_970 = (FStar_Parser_Env.prepare_module_or_interface true admitted env mname)
in (let _125_969 = (open_ns mname decls)
in (_125_970, mname, _125_969, true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _125_972 = (FStar_Parser_Env.prepare_module_or_interface false false env mname)
in (let _125_971 = (open_ns mname decls)
in (_125_972, mname, _125_971, false)))
end)
in (match (_46_2619) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(
# 1502 "FStar.Parser.ToSyntax.fst"
let _46_2622 = (desugar_decls env decls)
in (match (_46_2622) with
| (env, sigelts) -> begin
(
# 1503 "FStar.Parser.ToSyntax.fst"
let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in (env, modul, pop_when_done))
end))
end)))))

# 1511 "FStar.Parser.ToSyntax.fst"
let desugar_partial_modul : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (
# 1512 "FStar.Parser.ToSyntax.fst"
let m = if (FStar_ST.read FStar_Options.interactive_fsi) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface ((mname, decls, true))
end
| FStar_Parser_AST.Interface (mname, _46_2633, _46_2635) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (
# 1519 "FStar.Parser.ToSyntax.fst"
let _46_2643 = (desugar_modul_common curmod env m)
in (match (_46_2643) with
| (x, y, _46_2642) -> begin
(x, y)
end))))

# 1522 "FStar.Parser.ToSyntax.fst"
let desugar_modul : FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (
# 1523 "FStar.Parser.ToSyntax.fst"
let _46_2649 = (desugar_modul_common None env m)
in (match (_46_2649) with
| (env, modul, pop_when_done) -> begin
(
# 1524 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.finish_module_or_interface env modul)
in (
# 1525 "FStar.Parser.ToSyntax.fst"
let _46_2651 = if (FStar_Options.should_dump modul.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _125_983 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _125_983))
end else begin
()
end
in (let _125_984 = if pop_when_done then begin
(FStar_Parser_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end else begin
env
end
in (_125_984, modul))))
end)))

# 1529 "FStar.Parser.ToSyntax.fst"
let desugar_file : FStar_Parser_Env.env  ->  FStar_Parser_AST.file  ->  Prims.bool  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f needs_interleaving -> (
# 1530 "FStar.Parser.ToSyntax.fst"
let _46_2666 = (FStar_List.fold_left (fun _46_2658 m -> (match (_46_2658) with
| (env, mods) -> begin
(
# 1531 "FStar.Parser.ToSyntax.fst"
let m = if needs_interleaving then begin
(FStar_Parser_Interleave.interleave_modul m)
end else begin
m
end
in (
# 1532 "FStar.Parser.ToSyntax.fst"
let _46_2663 = (desugar_modul env m)
in (match (_46_2663) with
| (env, m) -> begin
(env, (m)::mods)
end)))
end)) (env, []) f)
in (match (_46_2666) with
| (env, mods) -> begin
(env, (FStar_List.rev mods))
end)))

# 1536 "FStar.Parser.ToSyntax.fst"
let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Parser_Env.env  ->  FStar_Parser_Env.env = (fun m en -> (
# 1537 "FStar.Parser.ToSyntax.fst"
let _46_2671 = (FStar_Parser_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (_46_2671) with
| (en, pop_when_done) -> begin
(
# 1538 "FStar.Parser.ToSyntax.fst"
let en = (FStar_List.fold_left FStar_Parser_Env.push_sigelt (
# 1538 "FStar.Parser.ToSyntax.fst"
let _46_2672 = en
in {FStar_Parser_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_Parser_Env.modules = _46_2672.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _46_2672.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.sigaccum = _46_2672.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _46_2672.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _46_2672.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _46_2672.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _46_2672.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _46_2672.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _46_2672.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = _46_2672.FStar_Parser_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (
# 1539 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_Env.export_interface m.FStar_Syntax_Syntax.name env)
end else begin
env
end))
end)))




