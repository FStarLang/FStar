
open Prims
# 40 "FStar.Parser.ToSyntax.fst"
let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _51_1 -> (match (_51_1) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Syntax_Syntax.Equality)
end
| _51_28 -> begin
None
end))

# 45 "FStar.Parser.ToSyntax.fst"
let trans_qual : FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun _51_2 -> (match (_51_2) with
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
let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun _51_3 -> (match (_51_3) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions -> begin
FStar_Syntax_Syntax.ResetOptions
end))

# 63 "FStar.Parser.ToSyntax.fst"
let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _51_4 -> (match (_51_4) with
| (FStar_Parser_AST.Hash) | (FStar_Parser_AST.FsTypApp) -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| _51_50 -> begin
None
end))

# 67 "FStar.Parser.ToSyntax.fst"
let arg_withimp_e = (fun imp t -> (t, (as_imp imp)))

# 69 "FStar.Parser.ToSyntax.fst"
let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
(t, Some (FStar_Syntax_Syntax.imp_tag))
end
| _51_57 -> begin
(t, None)
end))

# 74 "FStar.Parser.ToSyntax.fst"
let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_51_61) -> begin
true
end
| _51_64 -> begin
false
end)))))

# 79 "FStar.Parser.ToSyntax.fst"
let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _51_69 -> begin
t
end))

# 83 "FStar.Parser.ToSyntax.fst"
let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _132_21 = (let _132_20 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_132_20))
in (FStar_Parser_AST.mk_term _132_21 r FStar_Parser_AST.Kind)))

# 85 "FStar.Parser.ToSyntax.fst"
let rec delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (
# 86 "FStar.Parser.ToSyntax.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_51_74) -> begin
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

# 106 "FStar.Parser.ToSyntax.fst"
let incr_delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (
# 107 "FStar.Parser.ToSyntax.fst"
let d = (delta_qualifier t)
in (match (d) with
| FStar_Syntax_Syntax.Delta_equational -> begin
d
end
| FStar_Syntax_Syntax.Delta_constant -> begin
FStar_Syntax_Syntax.Delta_unfoldable (1)
end
| FStar_Syntax_Syntax.Delta_unfoldable (i) -> begin
FStar_Syntax_Syntax.Delta_unfoldable ((i + 1))
end)))

# 113 "FStar.Parser.ToSyntax.fst"
let compile_op : Prims.int  ->  Prims.string  ->  Prims.string = (fun arity s -> (
# 114 "FStar.Parser.ToSyntax.fst"
let name_of_char = (fun _51_5 -> (match (_51_5) with
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
| _51_165 -> begin
"UNKNOWN"
end))
in (
# 133 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _132_39 = (let _132_37 = (FStar_Util.char_at s i)
in (name_of_char _132_37))
in (let _132_38 = (aux (i + 1))
in (_132_39)::_132_38))
end)
in (let _132_41 = (let _132_40 = (aux 0)
in (FStar_String.concat "_" _132_40))
in (Prims.strcat "op_" _132_41)))))

# 139 "FStar.Parser.ToSyntax.fst"
let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _132_51 = (let _132_50 = (let _132_49 = (let _132_48 = (compile_op n s)
in (_132_48, r))
in (FStar_Ident.mk_ident _132_49))
in (_132_50)::[])
in (FStar_All.pipe_right _132_51 FStar_Ident.lid_of_ids)))

# 141 "FStar.Parser.ToSyntax.fst"
let op_as_fv : FStar_Parser_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env arity rng s -> (
# 142 "FStar.Parser.ToSyntax.fst"
let r = (fun l dd -> (let _132_65 = (let _132_64 = (FStar_Ident.set_lid_range l rng)
in (FStar_Syntax_Syntax.lid_as_fv _132_64 dd None))
in Some (_132_65)))
in (
# 143 "FStar.Parser.ToSyntax.fst"
let fallback = (fun _51_180 -> (match (()) with
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
| _51_208 -> begin
None
end)
end))
in (match ((let _132_68 = (compile_op_lid arity s rng)
in (FStar_Parser_Env.try_lookup_lid env _132_68))) with
| Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _51_214; FStar_Syntax_Syntax.pos = _51_212; FStar_Syntax_Syntax.vars = _51_210}) -> begin
Some (fv)
end
| _51_220 -> begin
(fallback ())
end))))

# 177 "FStar.Parser.ToSyntax.fst"
let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _132_75 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _132_75)))

# 181 "FStar.Parser.ToSyntax.fst"
let rec free_type_vars_b : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_51_229) -> begin
(env, [])
end
| FStar_Parser_AST.TVariable (x) -> begin
(
# 184 "FStar.Parser.ToSyntax.fst"
let _51_236 = (FStar_Parser_Env.push_bv env x)
in (match (_51_236) with
| (env, _51_235) -> begin
(env, (x)::[])
end))
end
| FStar_Parser_AST.Annotated (_51_238, term) -> begin
(let _132_82 = (free_type_vars env term)
in (env, _132_82))
end
| FStar_Parser_AST.TAnnotated (id, _51_244) -> begin
(
# 189 "FStar.Parser.ToSyntax.fst"
let _51_250 = (FStar_Parser_Env.push_bv env id)
in (match (_51_250) with
| (env, _51_249) -> begin
(env, [])
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _132_83 = (free_type_vars env t)
in (env, _132_83))
end))
and free_type_vars : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _132_86 = (unparen t)
in _132_86.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (_51_256) -> begin
(FStar_All.failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_Env.try_lookup_id env a)) with
| None -> begin
(a)::[]
end
| _51_262 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_51_292, ts) -> begin
(FStar_List.collect (fun _51_299 -> (match (_51_299) with
| (t, _51_298) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_51_301, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _51_308) -> begin
(let _132_89 = (free_type_vars env t1)
in (let _132_88 = (free_type_vars env t2)
in (FStar_List.append _132_89 _132_88)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(
# 219 "FStar.Parser.ToSyntax.fst"
let _51_317 = (free_type_vars_b env b)
in (match (_51_317) with
| (env, f) -> begin
(let _132_90 = (free_type_vars env t)
in (FStar_List.append f _132_90))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(
# 224 "FStar.Parser.ToSyntax.fst"
let _51_333 = (FStar_List.fold_left (fun _51_326 binder -> (match (_51_326) with
| (env, free) -> begin
(
# 225 "FStar.Parser.ToSyntax.fst"
let _51_330 = (free_type_vars_b env binder)
in (match (_51_330) with
| (env, f) -> begin
(env, (FStar_List.append f free))
end))
end)) (env, []) binders)
in (match (_51_333) with
| (env, free) -> begin
(let _132_93 = (free_type_vars env body)
in (FStar_List.append free _132_93))
end))
end
| FStar_Parser_AST.Project (t, _51_336) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) -> begin
[]
end
| (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
(FStar_Parser_AST.error "Unexpected type in free_type_vars computation" t t.FStar_Parser_AST.range)
end))

# 242 "FStar.Parser.ToSyntax.fst"
let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (
# 243 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun args t -> (match ((let _132_100 = (unparen t)
in _132_100.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _51_380 -> begin
(t, args)
end))
in (aux [] t)))

# 249 "FStar.Parser.ToSyntax.fst"
let close : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 250 "FStar.Parser.ToSyntax.fst"
let ftv = (let _132_105 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _132_105))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 253 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _132_109 = (let _132_108 = (let _132_107 = (tm_type x.FStar_Ident.idRange)
in (x, _132_107))
in FStar_Parser_AST.TAnnotated (_132_108))
in (FStar_Parser_AST.mk_binder _132_109 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 254 "FStar.Parser.ToSyntax.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))

# 257 "FStar.Parser.ToSyntax.fst"
let close_fun : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 258 "FStar.Parser.ToSyntax.fst"
let ftv = (let _132_114 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _132_114))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 261 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _132_118 = (let _132_117 = (let _132_116 = (tm_type x.FStar_Ident.idRange)
in (x, _132_116))
in FStar_Parser_AST.TAnnotated (_132_117))
in (FStar_Parser_AST.mk_binder _132_118 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 262 "FStar.Parser.ToSyntax.fst"
let t = (match ((let _132_119 = (unparen t)
in _132_119.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_51_393) -> begin
t
end
| _51_396 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level), t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end)
in (
# 265 "FStar.Parser.ToSyntax.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result)))
end))

# 268 "FStar.Parser.ToSyntax.fst"
let rec uncurry : FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term) = (fun bs t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (binders, t) -> begin
(uncurry (FStar_List.append bs binders) t)
end
| _51_406 -> begin
(bs, t)
end))

# 272 "FStar.Parser.ToSyntax.fst"
let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _51_410) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_51_416); FStar_Parser_AST.prange = _51_414}, _51_420) -> begin
true
end
| _51_424 -> begin
false
end))

# 277 "FStar.Parser.ToSyntax.fst"
let rec destruct_app_pattern : FStar_Parser_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 279 "FStar.Parser.ToSyntax.fst"
let _51_436 = (destruct_app_pattern env is_top_level p)
in (match (_51_436) with
| (name, args, _51_435) -> begin
(name, args, Some (t))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _51_441); FStar_Parser_AST.prange = _51_438}, args) when is_top_level -> begin
(let _132_133 = (let _132_132 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_132_132))
in (_132_133, args, None))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _51_452); FStar_Parser_AST.prange = _51_449}, args) -> begin
(FStar_Util.Inl (id), args, None)
end
| _51_460 -> begin
(FStar_All.failwith "Not an app pattern")
end))

# 288 "FStar.Parser.ToSyntax.fst"
type bnd =
| LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * FStar_Syntax_Syntax.term)

# 289 "FStar.Parser.ToSyntax.fst"
let is_LocalBinder = (fun _discr_ -> (match (_discr_) with
| LocalBinder (_) -> begin
true
end
| _ -> begin
false
end))

# 290 "FStar.Parser.ToSyntax.fst"
let is_LetBinder = (fun _discr_ -> (match (_discr_) with
| LetBinder (_) -> begin
true
end
| _ -> begin
false
end))

# 289 "FStar.Parser.ToSyntax.fst"
let ___LocalBinder____0 : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun projectee -> (match (projectee) with
| LocalBinder (_51_463) -> begin
_51_463
end))

# 290 "FStar.Parser.ToSyntax.fst"
let ___LetBinder____0 : bnd  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| LetBinder (_51_466) -> begin
_51_466
end))

# 291 "FStar.Parser.ToSyntax.fst"
let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun _51_6 -> (match (_51_6) with
| LocalBinder (a, aq) -> begin
(a, aq)
end
| _51_473 -> begin
(FStar_All.failwith "Impossible")
end))

# 294 "FStar.Parser.ToSyntax.fst"
let as_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_Parser_Env.env) = (fun env imp _51_7 -> (match (_51_7) with
| (None, k) -> begin
(let _132_170 = (FStar_Syntax_Syntax.null_binder k)
in (_132_170, env))
end
| (Some (a), k) -> begin
(
# 297 "FStar.Parser.ToSyntax.fst"
let _51_486 = (FStar_Parser_Env.push_bv env a)
in (match (_51_486) with
| (env, a) -> begin
(((
# 298 "FStar.Parser.ToSyntax.fst"
let _51_487 = a
in {FStar_Syntax_Syntax.ppname = _51_487.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _51_487.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}), (trans_aqual imp)), env)
end))
end))

# 300 "FStar.Parser.ToSyntax.fst"
type env_t =
FStar_Parser_Env.env

# 301 "FStar.Parser.ToSyntax.fst"
type lenv_t =
FStar_Syntax_Syntax.bv Prims.list

# 303 "FStar.Parser.ToSyntax.fst"
let mk_lb : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.letbinding = (fun _51_492 -> (match (_51_492) with
| (n, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))

# 304 "FStar.Parser.ToSyntax.fst"
let no_annot_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t None))

# 306 "FStar.Parser.ToSyntax.fst"
let rec desugar_data_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat) = (fun env p -> (
# 307 "FStar.Parser.ToSyntax.fst"
let check_linear_pattern_variables = (fun p -> (
# 308 "FStar.Parser.ToSyntax.fst"
let rec pat_vars = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_dot_term (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_constant (_)) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (_51_513, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out _51_521 -> (match (_51_521) with
| (p, _51_520) -> begin
(let _132_216 = (pat_vars p)
in (FStar_Util.set_union out _132_216))
end)) FStar_Syntax_Syntax.no_names))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj (hd::tl) -> begin
(
# 317 "FStar.Parser.ToSyntax.fst"
let xs = (pat_vars hd)
in if (not ((FStar_Util.for_all (fun p -> (
# 318 "FStar.Parser.ToSyntax.fst"
let ys = (pat_vars p)
in ((FStar_Util.set_is_subset_of xs ys) && (FStar_Util.set_is_subset_of ys xs)))) tl))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Disjunctive pattern binds different variables in each case", p.FStar_Syntax_Syntax.p))))
end else begin
xs
end)
end))
in (pat_vars p)))
in (
# 325 "FStar.Parser.ToSyntax.fst"
let resolvex = (fun l e x -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText))))) with
| Some (y) -> begin
(l, e, y)
end
| _51_539 -> begin
(
# 329 "FStar.Parser.ToSyntax.fst"
let _51_542 = (FStar_Parser_Env.push_bv e x)
in (match (_51_542) with
| (e, x) -> begin
((x)::l, e, x)
end))
end))
in (
# 331 "FStar.Parser.ToSyntax.fst"
let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun b -> (b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText))))) with
| Some (b) -> begin
(l, e, b)
end
| _51_551 -> begin
(
# 335 "FStar.Parser.ToSyntax.fst"
let _51_554 = (FStar_Parser_Env.push_bv e a)
in (match (_51_554) with
| (e, a) -> begin
((a)::l, e, a)
end))
end))
in (
# 337 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun loc env p -> (
# 338 "FStar.Parser.ToSyntax.fst"
let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Parser_AST.prange))
in (
# 339 "FStar.Parser.ToSyntax.fst"
let pos_r = (fun r q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r))
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.PatOr (p::ps) -> begin
(
# 343 "FStar.Parser.ToSyntax.fst"
let _51_576 = (aux loc env p)
in (match (_51_576) with
| (loc, env, var, p, _51_575) -> begin
(
# 344 "FStar.Parser.ToSyntax.fst"
let _51_593 = (FStar_List.fold_left (fun _51_580 p -> (match (_51_580) with
| (loc, env, ps) -> begin
(
# 345 "FStar.Parser.ToSyntax.fst"
let _51_589 = (aux loc env p)
in (match (_51_589) with
| (loc, env, _51_585, p, _51_588) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_51_593) with
| (loc, env, ps) -> begin
(
# 347 "FStar.Parser.ToSyntax.fst"
let pat = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in (loc, env, var, pat, false))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 351 "FStar.Parser.ToSyntax.fst"
let _51_604 = (aux loc env p)
in (match (_51_604) with
| (loc, env', binder, p, imp) -> begin
(
# 352 "FStar.Parser.ToSyntax.fst"
let binder = (match (binder) with
| LetBinder (_51_606) -> begin
(FStar_All.failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(
# 355 "FStar.Parser.ToSyntax.fst"
let t = (let _132_246 = (close_fun env t)
in (desugar_term env _132_246))
in LocalBinder (((
# 356 "FStar.Parser.ToSyntax.fst"
let _51_613 = x
in {FStar_Syntax_Syntax.ppname = _51_613.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _51_613.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), aq)))
end)
in (loc, env', binder, p, imp))
end))
end
| FStar_Parser_AST.PatWild -> begin
(
# 360 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _132_247 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in (loc, env, LocalBinder ((x, None)), _132_247, false)))
end
| FStar_Parser_AST.PatConst (c) -> begin
(
# 364 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _132_248 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in (loc, env, LocalBinder ((x, None)), _132_248, false)))
end
| (FStar_Parser_AST.PatTvar (x, imp)) | (FStar_Parser_AST.PatVar (x, imp)) -> begin
(
# 369 "FStar.Parser.ToSyntax.fst"
let aq = if imp then begin
Some (FStar_Syntax_Syntax.imp_tag)
end else begin
None
end
in (
# 370 "FStar.Parser.ToSyntax.fst"
let _51_631 = (resolvex loc env x)
in (match (_51_631) with
| (loc, env, xbv) -> begin
(let _132_249 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in (loc, env, LocalBinder ((xbv, aq)), _132_249, imp))
end)))
end
| FStar_Parser_AST.PatName (l) -> begin
(
# 374 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_datacon env) l)
in (
# 375 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _132_250 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, []))))
in (loc, env, LocalBinder ((x, None)), _132_250, false))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _51_637}, args) -> begin
(
# 379 "FStar.Parser.ToSyntax.fst"
let _51_659 = (FStar_List.fold_right (fun arg _51_648 -> (match (_51_648) with
| (loc, env, args) -> begin
(
# 380 "FStar.Parser.ToSyntax.fst"
let _51_655 = (aux loc env arg)
in (match (_51_655) with
| (loc, env, _51_652, arg, imp) -> begin
(loc, env, ((arg, imp))::args)
end))
end)) args (loc, env, []))
in (match (_51_659) with
| (loc, env, args) -> begin
(
# 382 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_datacon env) l)
in (
# 383 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _132_253 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _132_253, false))))
end))
end
| FStar_Parser_AST.PatApp (_51_663) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(
# 389 "FStar.Parser.ToSyntax.fst"
let _51_683 = (FStar_List.fold_right (fun pat _51_671 -> (match (_51_671) with
| (loc, env, pats) -> begin
(
# 390 "FStar.Parser.ToSyntax.fst"
let _51_679 = (aux loc env pat)
in (match (_51_679) with
| (loc, env, _51_675, pat, _51_678) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_51_683) with
| (loc, env, pats) -> begin
(
# 392 "FStar.Parser.ToSyntax.fst"
let pat = (let _132_266 = (let _132_265 = (let _132_261 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _132_261))
in (let _132_264 = (let _132_263 = (let _132_262 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_132_262, []))
in FStar_Syntax_Syntax.Pat_cons (_132_263))
in (FStar_All.pipe_left _132_265 _132_264)))
in (FStar_List.fold_right (fun hd tl -> (
# 393 "FStar.Parser.ToSyntax.fst"
let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (let _132_260 = (let _132_259 = (let _132_258 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_132_258, ((hd, false))::((tl, false))::[]))
in FStar_Syntax_Syntax.Pat_cons (_132_259))
in (FStar_All.pipe_left (pos_r r) _132_260)))) pats _132_266))
in (
# 396 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (loc, env, LocalBinder ((x, None)), pat, false)))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(
# 400 "FStar.Parser.ToSyntax.fst"
let _51_709 = (FStar_List.fold_left (fun _51_696 p -> (match (_51_696) with
| (loc, env, pats) -> begin
(
# 401 "FStar.Parser.ToSyntax.fst"
let _51_705 = (aux loc env p)
in (match (_51_705) with
| (loc, env, _51_701, pat, _51_704) -> begin
(loc, env, ((pat, false))::pats)
end))
end)) (loc, env, []) args)
in (match (_51_709) with
| (loc, env, args) -> begin
(
# 403 "FStar.Parser.ToSyntax.fst"
let args = (FStar_List.rev args)
in (
# 404 "FStar.Parser.ToSyntax.fst"
let l = if dep then begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end else begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end
in (
# 406 "FStar.Parser.ToSyntax.fst"
let constr = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (
# 407 "FStar.Parser.ToSyntax.fst"
let l = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| _51_716 -> begin
(FStar_All.failwith "impossible")
end)
in (
# 410 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _132_269 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _132_269, false)))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(
# 417 "FStar.Parser.ToSyntax.fst"
let _51_726 = (FStar_List.hd fields)
in (match (_51_726) with
| (f, _51_725) -> begin
(
# 418 "FStar.Parser.ToSyntax.fst"
let _51_730 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_51_730) with
| (record, _51_729) -> begin
(
# 419 "FStar.Parser.ToSyntax.fst"
let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _51_733 -> (match (_51_733) with
| (f, p) -> begin
(let _132_271 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.qualify_field_to_record env record) f)
in (_132_271, p))
end))))
in (
# 421 "FStar.Parser.ToSyntax.fst"
let args = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _51_738 -> (match (_51_738) with
| (f, _51_737) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _51_742 -> (match (_51_742) with
| (g, _51_741) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_51_745, p) -> begin
p
end)
end))))
in (
# 425 "FStar.Parser.ToSyntax.fst"
let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_Env.constrname)) p.FStar_Parser_AST.prange), args))) p.FStar_Parser_AST.prange)
in (
# 426 "FStar.Parser.ToSyntax.fst"
let _51_757 = (aux loc env app)
in (match (_51_757) with
| (env, e, b, p, _51_756) -> begin
(
# 427 "FStar.Parser.ToSyntax.fst"
let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(let _132_280 = (let _132_279 = (let _132_278 = (
# 428 "FStar.Parser.ToSyntax.fst"
let _51_762 = fv
in (let _132_277 = (let _132_276 = (let _132_275 = (let _132_274 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _132_274))
in FStar_Syntax_Syntax.Record_ctor (_132_275))
in Some (_132_276))
in {FStar_Syntax_Syntax.fv_name = _51_762.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = _51_762.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _132_277}))
in (_132_278, args))
in FStar_Syntax_Syntax.Pat_cons (_132_279))
in (FStar_All.pipe_left pos _132_280))
end
| _51_765 -> begin
p
end)
in (env, e, b, p, false))
end)))))
end))
end))
end))))
in (
# 432 "FStar.Parser.ToSyntax.fst"
let _51_774 = (aux [] env p)
in (match (_51_774) with
| (_51_768, env, b, p, _51_773) -> begin
(
# 433 "FStar.Parser.ToSyntax.fst"
let _51_775 = (let _132_281 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore _132_281))
in (env, b, p))
end)))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _51_782) -> begin
(let _132_287 = (let _132_286 = (let _132_285 = (FStar_Parser_Env.qualify env x)
in (_132_285, FStar_Syntax_Syntax.tun))
in LetBinder (_132_286))
in (env, _132_287, None))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _51_789); FStar_Parser_AST.prange = _51_786}, t) -> begin
(let _132_291 = (let _132_290 = (let _132_289 = (FStar_Parser_Env.qualify env x)
in (let _132_288 = (desugar_term env t)
in (_132_289, _132_288)))
in LetBinder (_132_290))
in (env, _132_291, None))
end
| _51_797 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern at the top-level", p.FStar_Parser_AST.prange))))
end)
end else begin
(
# 444 "FStar.Parser.ToSyntax.fst"
let _51_801 = (desugar_data_pat env p)
in (match (_51_801) with
| (env, binder, p) -> begin
(
# 445 "FStar.Parser.ToSyntax.fst"
let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| _51_809 -> begin
Some (p)
end)
in (env, binder, p))
end))
end)
and desugar_binding_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun _51_813 env pat -> (
# 454 "FStar.Parser.ToSyntax.fst"
let _51_821 = (desugar_data_pat env pat)
in (match (_51_821) with
| (env, _51_819, pat) -> begin
(env, pat)
end)))
and desugar_match_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (
# 460 "FStar.Parser.ToSyntax.fst"
let env = (
# 460 "FStar.Parser.ToSyntax.fst"
let _51_826 = env
in {FStar_Parser_Env.curmodule = _51_826.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _51_826.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _51_826.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.sigaccum = _51_826.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _51_826.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _51_826.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _51_826.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _51_826.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _51_826.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _51_826.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (
# 464 "FStar.Parser.ToSyntax.fst"
let env = (
# 464 "FStar.Parser.ToSyntax.fst"
let _51_831 = env
in {FStar_Parser_Env.curmodule = _51_831.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _51_831.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _51_831.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.sigaccum = _51_831.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _51_831.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _51_831.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _51_831.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _51_831.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _51_831.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _51_831.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (
# 468 "FStar.Parser.ToSyntax.fst"
let mk = (fun e -> (FStar_Syntax_Syntax.mk e None top.FStar_Parser_AST.range))
in (
# 469 "FStar.Parser.ToSyntax.fst"
let setpos = (fun e -> (
# 469 "FStar.Parser.ToSyntax.fst"
let _51_841 = e
in {FStar_Syntax_Syntax.n = _51_841.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _51_841.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _51_841.FStar_Syntax_Syntax.vars}))
in (match ((let _132_310 = (unparen top)
in _132_310.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (_51_845) -> begin
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
| FStar_Parser_AST.Op ("*", _51_865::_51_863::[]) when (let _132_311 = (op_as_fv env 2 top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right _132_311 FStar_Option.isNone)) -> begin
(
# 487 "FStar.Parser.ToSyntax.fst"
let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", t1::t2::[]) -> begin
(
# 489 "FStar.Parser.ToSyntax.fst"
let rest = (flatten t2)
in (t1)::rest)
end
| _51_879 -> begin
(t)::[]
end))
in (
# 492 "FStar.Parser.ToSyntax.fst"
let targs = (let _132_317 = (let _132_314 = (unparen top)
in (flatten _132_314))
in (FStar_All.pipe_right _132_317 (FStar_List.map (fun t -> (let _132_316 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg _132_316))))))
in (
# 493 "FStar.Parser.ToSyntax.fst"
let tup = (let _132_318 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) _132_318))
in (mk (FStar_Syntax_Syntax.Tm_app ((tup, targs)))))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _132_319 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) a)
in (FStar_All.pipe_left setpos _132_319))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_fv env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Unexpected operator: " s), top.FStar_Parser_AST.range))))
end
| Some (fv) -> begin
(
# 503 "FStar.Parser.ToSyntax.fst"
let op = (FStar_Syntax_Syntax.fv_to_tm fv)
in (
# 504 "FStar.Parser.ToSyntax.fst"
let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _132_321 = (desugar_term env t)
in (_132_321, None)))))
in (mk (FStar_Syntax_Syntax.Tm_app ((op, args))))))
end)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _51_901; FStar_Ident.ident = _51_899; FStar_Ident.nsstr = _51_897; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _51_910; FStar_Ident.ident = _51_908; FStar_Ident.nsstr = _51_906; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _51_919; FStar_Ident.ident = _51_917; FStar_Ident.nsstr = _51_915; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(let _132_322 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (FStar_All.pipe_left setpos _132_322))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(
# 517 "FStar.Parser.ToSyntax.fst"
let _51_934 = (match ((FStar_Parser_Env.try_lookup_datacon env l)) with
| None -> begin
(let _132_323 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (_132_323, false))
end
| Some (head) -> begin
(let _132_324 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in (_132_324, true))
end)
in (match (_51_934) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| _51_937 -> begin
(
# 523 "FStar.Parser.ToSyntax.fst"
let args = (FStar_List.map (fun _51_940 -> (match (_51_940) with
| (t, imp) -> begin
(
# 524 "FStar.Parser.ToSyntax.fst"
let te = (desugar_term env t)
in (arg_withimp_e imp te))
end)) args)
in (
# 526 "FStar.Parser.ToSyntax.fst"
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
# 533 "FStar.Parser.ToSyntax.fst"
let _51_968 = (FStar_List.fold_left (fun _51_951 b -> (match (_51_951) with
| (env, tparams, typs) -> begin
(
# 534 "FStar.Parser.ToSyntax.fst"
let _51_955 = (desugar_binder env b)
in (match (_51_955) with
| (xopt, t) -> begin
(
# 535 "FStar.Parser.ToSyntax.fst"
let _51_961 = (match (xopt) with
| None -> begin
(let _132_328 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (env, _132_328))
end
| Some (x) -> begin
(FStar_Parser_Env.push_bv env x)
end)
in (match (_51_961) with
| (env, x) -> begin
(let _132_332 = (let _132_331 = (let _132_330 = (let _132_329 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _132_329))
in (_132_330)::[])
in (FStar_List.append typs _132_331))
in (env, (FStar_List.append tparams ((((
# 539 "FStar.Parser.ToSyntax.fst"
let _51_962 = x
in {FStar_Syntax_Syntax.ppname = _51_962.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _51_962.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), None))::[])), _132_332))
end))
end))
end)) (env, [], []) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_51_968) with
| (env, _51_966, targs) -> begin
(
# 542 "FStar.Parser.ToSyntax.fst"
let tup = (let _132_333 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) _132_333))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app ((tup, targs)))))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(
# 546 "FStar.Parser.ToSyntax.fst"
let _51_976 = (uncurry binders t)
in (match (_51_976) with
| (bs, t) -> begin
(
# 547 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun env bs _51_8 -> (match (_51_8) with
| [] -> begin
(
# 549 "FStar.Parser.ToSyntax.fst"
let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (let _132_340 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos _132_340)))
end
| hd::tl -> begin
(
# 553 "FStar.Parser.ToSyntax.fst"
let mlenv = (FStar_Parser_Env.default_ml env)
in (
# 554 "FStar.Parser.ToSyntax.fst"
let bb = (desugar_binder mlenv hd)
in (
# 555 "FStar.Parser.ToSyntax.fst"
let _51_990 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_51_990) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_binder env b)) with
| (None, _51_997) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(
# 564 "FStar.Parser.ToSyntax.fst"
let _51_1005 = (as_binder env None b)
in (match (_51_1005) with
| ((x, _51_1002), env) -> begin
(
# 565 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env f)
in (let _132_341 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos _132_341)))
end))
end)
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(
# 570 "FStar.Parser.ToSyntax.fst"
let _51_1025 = (FStar_List.fold_left (fun _51_1013 pat -> (match (_51_1013) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (_51_1016, t) -> begin
(let _132_345 = (let _132_344 = (free_type_vars env t)
in (FStar_List.append _132_344 ftvs))
in (env, _132_345))
end
| _51_1021 -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_51_1025) with
| (_51_1023, ftv) -> begin
(
# 574 "FStar.Parser.ToSyntax.fst"
let ftv = (sort_ftv ftv)
in (
# 575 "FStar.Parser.ToSyntax.fst"
let binders = (let _132_347 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar ((a, true))) top.FStar_Parser_AST.range))))
in (FStar_List.append _132_347 binders))
in (
# 584 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun env bs sc_pat_opt _51_9 -> (match (_51_9) with
| [] -> begin
(
# 586 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env body)
in (
# 587 "FStar.Parser.ToSyntax.fst"
let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(
# 589 "FStar.Parser.ToSyntax.fst"
let body = (let _132_357 = (let _132_356 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right _132_356 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close _132_357 body))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((sc, ((pat, None, body))::[]))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (let _132_358 = (no_annot_abs (FStar_List.rev bs) body)
in (setpos _132_358))))
end
| p::rest -> begin
(
# 595 "FStar.Parser.ToSyntax.fst"
let _51_1049 = (desugar_binding_pat env p)
in (match (_51_1049) with
| (env, b, pat) -> begin
(
# 596 "FStar.Parser.ToSyntax.fst"
let _51_1100 = (match (b) with
| LetBinder (_51_1051) -> begin
(FStar_All.failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(
# 599 "FStar.Parser.ToSyntax.fst"
let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _51_1059) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _132_360 = (let _132_359 = (FStar_Syntax_Syntax.bv_to_name x)
in (_132_359, p))
in Some (_132_360))
end
| (Some (p), Some (sc, p')) -> begin
(match ((sc.FStar_Syntax_Syntax.n, p'.FStar_Syntax_Syntax.v)) with
| (FStar_Syntax_Syntax.Tm_name (_51_1073), _51_1076) -> begin
(
# 605 "FStar.Parser.ToSyntax.fst"
let tup2 = (let _132_361 = (FStar_Syntax_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _132_361 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (
# 606 "FStar.Parser.ToSyntax.fst"
let sc = (let _132_369 = (let _132_368 = (let _132_367 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (let _132_366 = (let _132_365 = (FStar_Syntax_Syntax.as_arg sc)
in (let _132_364 = (let _132_363 = (let _132_362 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _132_362))
in (_132_363)::[])
in (_132_365)::_132_364))
in (_132_367, _132_366)))
in FStar_Syntax_Syntax.Tm_app (_132_368))
in (FStar_Syntax_Syntax.mk _132_369 None top.FStar_Parser_AST.range))
in (
# 607 "FStar.Parser.ToSyntax.fst"
let p = (let _132_370 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tup2, ((p', false))::((p, false))::[]))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _132_370))
in Some ((sc, p)))))
end
| (FStar_Syntax_Syntax.Tm_app (_51_1082, args), FStar_Syntax_Syntax.Pat_cons (_51_1087, pats)) -> begin
(
# 610 "FStar.Parser.ToSyntax.fst"
let tupn = (let _132_371 = (FStar_Syntax_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _132_371 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (
# 611 "FStar.Parser.ToSyntax.fst"
let sc = (let _132_378 = (let _132_377 = (let _132_376 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (let _132_375 = (let _132_374 = (let _132_373 = (let _132_372 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _132_372))
in (_132_373)::[])
in (FStar_List.append args _132_374))
in (_132_376, _132_375)))
in FStar_Syntax_Syntax.Tm_app (_132_377))
in (mk _132_378))
in (
# 612 "FStar.Parser.ToSyntax.fst"
let p = (let _132_379 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tupn, (FStar_List.append pats (((p, false))::[]))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _132_379))
in Some ((sc, p)))))
end
| _51_1096 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((x, aq), sc_pat_opt))
end)
in (match (_51_1100) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _51_1104; FStar_Parser_AST.level = _51_1102}, phi, _51_1110) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(
# 623 "FStar.Parser.ToSyntax.fst"
let phi = (desugar_formula env phi)
in (let _132_387 = (let _132_386 = (let _132_385 = (FStar_Syntax_Syntax.fvar a FStar_Syntax_Syntax.Delta_equational None)
in (let _132_384 = (let _132_383 = (FStar_Syntax_Syntax.as_arg phi)
in (let _132_382 = (let _132_381 = (let _132_380 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _132_380))
in (_132_381)::[])
in (_132_383)::_132_382))
in (_132_385, _132_384)))
in FStar_Syntax_Syntax.Tm_app (_132_386))
in (mk _132_387)))
end
| FStar_Parser_AST.App (_51_1115) -> begin
(
# 629 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun args e -> (match ((let _132_392 = (unparen e)
in _132_392.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(
# 631 "FStar.Parser.ToSyntax.fst"
let arg = (let _132_393 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _132_393))
in (aux ((arg)::args) e))
end
| _51_1127 -> begin
(
# 634 "FStar.Parser.ToSyntax.fst"
let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app ((head, args)))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _132_396 = (let _132_395 = (let _132_394 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range), t1))::[], t2))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in (_132_394, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))
in FStar_Syntax_Syntax.Tm_meta (_132_395))
in (mk _132_396))
end
| FStar_Parser_AST.Let (is_rec, (pat, _snd)::_tl, body) -> begin
(
# 643 "FStar.Parser.ToSyntax.fst"
let ds_let_rec_or_app = (fun _51_1143 -> (match (()) with
| () -> begin
(
# 644 "FStar.Parser.ToSyntax.fst"
let bindings = ((pat, _snd))::_tl
in (
# 645 "FStar.Parser.ToSyntax.fst"
let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _51_1147 -> (match (_51_1147) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _132_400 = (destruct_app_pattern env top_level p)
in (_132_400, def))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _132_401 = (destruct_app_pattern env top_level p)
in (_132_401, def))
end
| _51_1153 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _51_1158); FStar_Parser_AST.prange = _51_1155}, t) -> begin
if top_level then begin
(let _132_404 = (let _132_403 = (let _132_402 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_132_402))
in (_132_403, [], Some (t)))
in (_132_404, def))
end else begin
((FStar_Util.Inl (id), [], Some (t)), def)
end
end
| FStar_Parser_AST.PatVar (id, _51_1167) -> begin
if top_level then begin
(let _132_407 = (let _132_406 = (let _132_405 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_132_405))
in (_132_406, [], None))
in (_132_407, def))
end else begin
((FStar_Util.Inl (id), [], None), def)
end
end
| _51_1171 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected let binding", p.FStar_Parser_AST.prange))))
end)
end)
end
end))))
in (
# 662 "FStar.Parser.ToSyntax.fst"
let _51_1200 = (FStar_List.fold_left (fun _51_1176 _51_1185 -> (match ((_51_1176, _51_1185)) with
| ((env, fnames, rec_bindings), ((f, _51_1179, _51_1181), _51_1184)) -> begin
(
# 664 "FStar.Parser.ToSyntax.fst"
let _51_1196 = (match (f) with
| FStar_Util.Inl (x) -> begin
(
# 666 "FStar.Parser.ToSyntax.fst"
let _51_1190 = (FStar_Parser_Env.push_bv env x)
in (match (_51_1190) with
| (env, xx) -> begin
(let _132_411 = (let _132_410 = (FStar_Syntax_Syntax.mk_binder xx)
in (_132_410)::rec_bindings)
in (env, FStar_Util.Inl (xx), _132_411))
end))
end
| FStar_Util.Inr (l) -> begin
(let _132_412 = (FStar_Parser_Env.push_top_level_rec_binding env l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in (_132_412, FStar_Util.Inr (l), rec_bindings))
end)
in (match (_51_1196) with
| (env, lbname, rec_bindings) -> begin
(env, (lbname)::fnames, rec_bindings)
end))
end)) (env, [], []) funs)
in (match (_51_1200) with
| (env', fnames, rec_bindings) -> begin
(
# 672 "FStar.Parser.ToSyntax.fst"
let fnames = (FStar_List.rev fnames)
in (
# 674 "FStar.Parser.ToSyntax.fst"
let desugar_one_def = (fun env lbname _51_1211 -> (match (_51_1211) with
| ((_51_1206, args, result_t), def) -> begin
(
# 675 "FStar.Parser.ToSyntax.fst"
let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _132_419 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed ((def, t))) _132_419 FStar_Parser_AST.Expr))
end)
in (
# 678 "FStar.Parser.ToSyntax.fst"
let def = (match (args) with
| [] -> begin
def
end
| _51_1218 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.un_curry_abs args def) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
end)
in (
# 681 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env def)
in (
# 682 "FStar.Parser.ToSyntax.fst"
let lbname = (match (lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl (x)
end
| FStar_Util.Inr (l) -> begin
(let _132_421 = (let _132_420 = (incr_delta_qualifier body)
in (FStar_Syntax_Syntax.lid_as_fv l _132_420 None))
in FStar_Util.Inr (_132_421))
end)
in (
# 685 "FStar.Parser.ToSyntax.fst"
let body = if is_rec then begin
(FStar_Syntax_Subst.close rec_bindings body)
end else begin
body
end
in (mk_lb (lbname, FStar_Syntax_Syntax.tun, body)))))))
end))
in (
# 687 "FStar.Parser.ToSyntax.fst"
let lbs = (FStar_List.map2 (desugar_one_def (if is_rec then begin
env'
end else begin
env
end)) fnames funs)
in (
# 688 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env' body)
in (let _132_424 = (let _132_423 = (let _132_422 = (FStar_Syntax_Subst.close rec_bindings body)
in ((is_rec, lbs), _132_422))
in FStar_Syntax_Syntax.Tm_let (_132_423))
in (FStar_All.pipe_left mk _132_424))))))
end))))
end))
in (
# 692 "FStar.Parser.ToSyntax.fst"
let ds_non_rec = (fun pat t1 t2 -> (
# 693 "FStar.Parser.ToSyntax.fst"
let t1 = (desugar_term env t1)
in (
# 694 "FStar.Parser.ToSyntax.fst"
let _51_1237 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_51_1237) with
| (env, binder, pat) -> begin
(match (binder) with
| LetBinder (l, t) -> begin
(
# 697 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env t2)
in (
# 698 "FStar.Parser.ToSyntax.fst"
let fv = (let _132_431 = (incr_delta_qualifier t1)
in (FStar_Syntax_Syntax.lid_as_fv l _132_431 None))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]), body))))))
end
| LocalBinder (x, _51_1246) -> begin
(
# 702 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env t2)
in (
# 703 "FStar.Parser.ToSyntax.fst"
let body = (match (pat) with
| (None) | (Some ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (_); FStar_Syntax_Syntax.ty = _; FStar_Syntax_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _132_436 = (let _132_435 = (let _132_434 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _132_433 = (let _132_432 = (FStar_Syntax_Util.branch (pat, None, body))
in (_132_432)::[])
in (_132_434, _132_433)))
in FStar_Syntax_Syntax.Tm_match (_132_435))
in (FStar_Syntax_Syntax.mk _132_436 None body.FStar_Syntax_Syntax.pos))
end)
in (let _132_441 = (let _132_440 = (let _132_439 = (let _132_438 = (let _132_437 = (FStar_Syntax_Syntax.mk_binder x)
in (_132_437)::[])
in (FStar_Syntax_Subst.close _132_438 body))
in ((false, ((mk_lb (FStar_Util.Inl (x), x.FStar_Syntax_Syntax.sort, t1)))::[]), _132_439))
in FStar_Syntax_Syntax.Tm_let (_132_440))
in (FStar_All.pipe_left mk _132_441))))
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
# 717 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (let _132_452 = (let _132_451 = (let _132_450 = (desugar_term env t1)
in (let _132_449 = (let _132_448 = (let _132_443 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (let _132_442 = (desugar_term env t2)
in (_132_443, None, _132_442)))
in (let _132_447 = (let _132_446 = (let _132_445 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (let _132_444 = (desugar_term env t3)
in (_132_445, None, _132_444)))
in (_132_446)::[])
in (_132_448)::_132_447))
in (_132_450, _132_449)))
in FStar_Syntax_Syntax.Tm_match (_132_451))
in (mk _132_452)))
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(
# 723 "FStar.Parser.ToSyntax.fst"
let r = top.FStar_Parser_AST.range
in (
# 724 "FStar.Parser.ToSyntax.fst"
let handler = (FStar_Parser_AST.mk_function branches r r)
in (
# 725 "FStar.Parser.ToSyntax.fst"
let body = (FStar_Parser_AST.mk_function ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatConst (FStar_Const.Const_unit)) r), None, e))::[]) r r)
in (
# 726 "FStar.Parser.ToSyntax.fst"
let a1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (FStar_Syntax_Const.try_with_lid)) r top.FStar_Parser_AST.level), body, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (
# 727 "FStar.Parser.ToSyntax.fst"
let a2 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((a1, handler, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (desugar_term env a2))))))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(
# 731 "FStar.Parser.ToSyntax.fst"
let desugar_branch = (fun _51_1286 -> (match (_51_1286) with
| (pat, wopt, b) -> begin
(
# 732 "FStar.Parser.ToSyntax.fst"
let _51_1289 = (desugar_match_pat env pat)
in (match (_51_1289) with
| (env, pat) -> begin
(
# 733 "FStar.Parser.ToSyntax.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _132_455 = (desugar_term env e)
in Some (_132_455))
end)
in (
# 736 "FStar.Parser.ToSyntax.fst"
let b = (desugar_term env b)
in (FStar_Syntax_Util.branch (pat, wopt, b))))
end))
end))
in (let _132_459 = (let _132_458 = (let _132_457 = (desugar_term env e)
in (let _132_456 = (FStar_List.map desugar_branch branches)
in (_132_457, _132_456)))
in FStar_Syntax_Syntax.Tm_match (_132_458))
in (FStar_All.pipe_left mk _132_459)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _132_463 = (let _132_462 = (let _132_461 = (desugar_term env e)
in (let _132_460 = (desugar_typ env t)
in (_132_461, _132_460, None)))
in FStar_Syntax_Syntax.Tm_ascribed (_132_462))
in (FStar_All.pipe_left mk _132_463))
end
| FStar_Parser_AST.Record (_51_1300, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected empty record", top.FStar_Parser_AST.range))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(
# 747 "FStar.Parser.ToSyntax.fst"
let _51_1311 = (FStar_List.hd fields)
in (match (_51_1311) with
| (f, _51_1310) -> begin
(
# 748 "FStar.Parser.ToSyntax.fst"
let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (
# 749 "FStar.Parser.ToSyntax.fst"
let _51_1317 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_51_1317) with
| (record, _51_1316) -> begin
(
# 750 "FStar.Parser.ToSyntax.fst"
let get_field = (fun xopt f -> (
# 751 "FStar.Parser.ToSyntax.fst"
let fn = f.FStar_Ident.ident
in (
# 752 "FStar.Parser.ToSyntax.fst"
let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _51_1325 -> (match (_51_1325) with
| (g, _51_1324) -> begin
(
# 753 "FStar.Parser.ToSyntax.fst"
let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_51_1329, e) -> begin
(let _132_471 = (qfn fn)
in (_132_471, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _132_474 = (let _132_473 = (let _132_472 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in (_132_472, top.FStar_Parser_AST.range))
in FStar_Syntax_Syntax.Error (_132_473))
in (Prims.raise _132_474))
end
| Some (x) -> begin
(let _132_475 = (qfn fn)
in (_132_475, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Project ((x, f))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end))))
in (
# 764 "FStar.Parser.ToSyntax.fst"
let recterm = (match (eopt) with
| None -> begin
(let _132_480 = (let _132_479 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _51_1341 -> (match (_51_1341) with
| (f, _51_1340) -> begin
(let _132_478 = (let _132_477 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _132_477))
in (_132_478, FStar_Parser_AST.Nothing))
end))))
in (record.FStar_Parser_Env.constrname, _132_479))
in FStar_Parser_AST.Construct (_132_480))
end
| Some (e) -> begin
(
# 771 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (
# 772 "FStar.Parser.ToSyntax.fst"
let xterm = (let _132_482 = (let _132_481 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_132_481))
in (FStar_Parser_AST.mk_term _132_482 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (
# 773 "FStar.Parser.ToSyntax.fst"
let record = (let _132_485 = (let _132_484 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _51_1349 -> (match (_51_1349) with
| (f, _51_1348) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _132_484))
in FStar_Parser_AST.Record (_132_485))
in FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar ((x, false))) x.FStar_Ident.idRange), e))::[], (FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level))))))
end)
in (
# 776 "FStar.Parser.ToSyntax.fst"
let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (
# 777 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _51_1365; FStar_Syntax_Syntax.pos = _51_1363; FStar_Syntax_Syntax.vars = _51_1361}, args); FStar_Syntax_Syntax.tk = _51_1359; FStar_Syntax_Syntax.pos = _51_1357; FStar_Syntax_Syntax.vars = _51_1355}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(
# 780 "FStar.Parser.ToSyntax.fst"
let e = (let _132_493 = (let _132_492 = (let _132_491 = (let _132_490 = (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos)
in (let _132_489 = (let _132_488 = (let _132_487 = (let _132_486 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _132_486))
in FStar_Syntax_Syntax.Record_ctor (_132_487))
in Some (_132_488))
in (FStar_Syntax_Syntax.fvar _132_490 FStar_Syntax_Syntax.Delta_constant _132_489)))
in (_132_491, args))
in FStar_Syntax_Syntax.Tm_app (_132_492))
in (FStar_All.pipe_left mk _132_493))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end
| _51_1379 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(
# 788 "FStar.Parser.ToSyntax.fst"
let _51_1386 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_projector_by_field_name env) f)
in (match (_51_1386) with
| (fieldname, is_rec) -> begin
(
# 789 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env e)
in (
# 790 "FStar.Parser.ToSyntax.fst"
let fn = (
# 791 "FStar.Parser.ToSyntax.fst"
let _51_1391 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_51_1391) with
| (ns, _51_1390) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (
# 793 "FStar.Parser.ToSyntax.fst"
let qual = if is_rec then begin
Some (FStar_Syntax_Syntax.Record_projector (fn))
end else begin
None
end
in (let _132_499 = (let _132_498 = (let _132_497 = (let _132_494 = (FStar_Ident.set_lid_range fieldname (FStar_Ident.range_of_lid f))
in (FStar_Syntax_Syntax.fvar _132_494 FStar_Syntax_Syntax.Delta_equational (Some (FStar_Syntax_Syntax.Record_projector (fn)))))
in (let _132_496 = (let _132_495 = (FStar_Syntax_Syntax.as_arg e)
in (_132_495)::[])
in (_132_497, _132_496)))
in FStar_Syntax_Syntax.Tm_app (_132_498))
in (FStar_All.pipe_left mk _132_499)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| _51_1401 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _51_1403 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_args : FStar_Parser_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun _51_1408 -> (match (_51_1408) with
| (a, imp) -> begin
(let _132_503 = (desugar_term env a)
in (arg_withimp_e imp _132_503))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r default_ok env t -> (
# 810 "FStar.Parser.ToSyntax.fst"
let fail = (fun msg -> (Prims.raise (FStar_Syntax_Syntax.Error ((msg, r)))))
in (
# 811 "FStar.Parser.ToSyntax.fst"
let is_requires = (fun _51_1420 -> (match (_51_1420) with
| (t, _51_1419) -> begin
(match ((let _132_511 = (unparen t)
in _132_511.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Requires (_51_1422) -> begin
true
end
| _51_1425 -> begin
false
end)
end))
in (
# 814 "FStar.Parser.ToSyntax.fst"
let is_ensures = (fun _51_1430 -> (match (_51_1430) with
| (t, _51_1429) -> begin
(match ((let _132_514 = (unparen t)
in _132_514.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ensures (_51_1432) -> begin
true
end
| _51_1435 -> begin
false
end)
end))
in (
# 817 "FStar.Parser.ToSyntax.fst"
let is_app = (fun head _51_1441 -> (match (_51_1441) with
| (t, _51_1440) -> begin
(match ((let _132_519 = (unparen t)
in _132_519.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _51_1445; FStar_Parser_AST.level = _51_1443}, _51_1450, _51_1452) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| _51_1456 -> begin
false
end)
end))
in (
# 820 "FStar.Parser.ToSyntax.fst"
let pre_process_comp_typ = (fun t -> (
# 821 "FStar.Parser.ToSyntax.fst"
let _51_1461 = (head_and_args t)
in (match (_51_1461) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(
# 824 "FStar.Parser.ToSyntax.fst"
let unit_tm = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (
# 825 "FStar.Parser.ToSyntax.fst"
let nil_pat = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr), FStar_Parser_AST.Nothing)
in (
# 826 "FStar.Parser.ToSyntax.fst"
let args = (match (args) with
| [] -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Not enough arguments to \'Lemma\'", t.FStar_Parser_AST.range))))
end
| ens::[] -> begin
(
# 829 "FStar.Parser.ToSyntax.fst"
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
# 834 "FStar.Parser.ToSyntax.fst"
let head = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_name env) lemma)
in (head, args)))))
end
| FStar_Parser_AST.Name (l) when (FStar_Parser_Env.is_effect_name env l) -> begin
(let _132_522 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_name env) l)
in (_132_522, args))
end
| FStar_Parser_AST.Name (l) when ((let _132_523 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _132_523 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(let _132_524 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in (_132_524, args))
end
| FStar_Parser_AST.Name (l) when ((let _132_525 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _132_525 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(let _132_526 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)
in (_132_526, args))
end
| FStar_Parser_AST.Name (l) when ((((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) && default_ok) -> begin
(let _132_527 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in (_132_527, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _51_1489 when default_ok -> begin
(let _132_528 = (FStar_Ident.set_lid_range env.FStar_Parser_Env.default_result_effect head.FStar_Parser_AST.range)
in (_132_528, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _51_1491 -> begin
(let _132_530 = (let _132_529 = (FStar_Parser_AST.term_to_string t)
in (FStar_Util.format1 "%s is not an effect" _132_529))
in (fail _132_530))
end)
end)))
in (
# 864 "FStar.Parser.ToSyntax.fst"
let _51_1494 = (pre_process_comp_typ t)
in (match (_51_1494) with
| (eff, args) -> begin
(
# 865 "FStar.Parser.ToSyntax.fst"
let _51_1495 = if ((FStar_List.length args) = 0) then begin
(let _132_532 = (let _132_531 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" _132_531))
in (fail _132_532))
end else begin
()
end
in (
# 867 "FStar.Parser.ToSyntax.fst"
let _51_1499 = (let _132_534 = (FStar_List.hd args)
in (let _132_533 = (FStar_List.tl args)
in (_132_534, _132_533)))
in (match (_51_1499) with
| (result_arg, rest) -> begin
(
# 868 "FStar.Parser.ToSyntax.fst"
let result_typ = (desugar_typ env (Prims.fst result_arg))
in (
# 869 "FStar.Parser.ToSyntax.fst"
let rest = (desugar_args env rest)
in (
# 870 "FStar.Parser.ToSyntax.fst"
let _51_1524 = (FStar_All.pipe_right rest (FStar_List.partition (fun _51_1505 -> (match (_51_1505) with
| (t, _51_1504) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _51_1511; FStar_Syntax_Syntax.pos = _51_1509; FStar_Syntax_Syntax.vars = _51_1507}, _51_1516::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| _51_1521 -> begin
false
end)
end))))
in (match (_51_1524) with
| (dec, rest) -> begin
(
# 876 "FStar.Parser.ToSyntax.fst"
let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _51_1528 -> (match (_51_1528) with
| (t, _51_1527) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_51_1530, (arg, _51_1533)::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| _51_1539 -> begin
(FStar_All.failwith "impos")
end)
end))))
in if ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid) && ((FStar_List.length decreases_clause) = 0)) then begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end else begin
if ((FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid) && ((FStar_List.length decreases_clause) = 0)) then begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end else begin
(
# 884 "FStar.Parser.ToSyntax.fst"
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
# 890 "FStar.Parser.ToSyntax.fst"
let rest = if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid) then begin
(match (rest) with
| req::ens::(pat, aq)::[] -> begin
(
# 894 "FStar.Parser.ToSyntax.fst"
let pat = (match (pat.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
(
# 896 "FStar.Parser.ToSyntax.fst"
let nil = (FStar_Syntax_Syntax.mk_Tm_uinst pat ((FStar_Syntax_Syntax.U_succ (FStar_Syntax_Syntax.U_zero))::[]))
in (
# 897 "FStar.Parser.ToSyntax.fst"
let pattern = (let _132_538 = (let _132_537 = (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _132_537 FStar_Syntax_Syntax.Delta_constant None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _132_538 ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app nil (((pattern, Some (FStar_Syntax_Syntax.imp_tag)))::[]) None pat.FStar_Syntax_Syntax.pos)))
end
| _51_1553 -> begin
pat
end)
in (let _132_542 = (let _132_541 = (let _132_540 = (let _132_539 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((pat, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)))) None pat.FStar_Syntax_Syntax.pos)
in (_132_539, aq))
in (_132_540)::[])
in (ens)::_132_541)
in (req)::_132_542))
end
| _51_1556 -> begin
rest
end)
end else begin
rest
end
in (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.effect_name = eff; FStar_Syntax_Syntax.result_typ = result_typ; FStar_Syntax_Syntax.effect_args = rest; FStar_Syntax_Syntax.flags = (FStar_List.append flags decreases_clause)})))
end
end)
end))))
end)))
end))))))))
and desugar_formula : env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env f -> (
# 910 "FStar.Parser.ToSyntax.fst"
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
| _51_1568 -> begin
None
end))
in (
# 917 "FStar.Parser.ToSyntax.fst"
let mk = (fun t -> (FStar_Syntax_Syntax.mk t None f.FStar_Parser_AST.range))
in (
# 918 "FStar.Parser.ToSyntax.fst"
let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (
# 919 "FStar.Parser.ToSyntax.fst"
let setpos = (fun t -> (
# 919 "FStar.Parser.ToSyntax.fst"
let _51_1575 = t
in {FStar_Syntax_Syntax.n = _51_1575.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _51_1575.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _51_1575.FStar_Syntax_Syntax.vars}))
in (
# 920 "FStar.Parser.ToSyntax.fst"
let desugar_quant = (fun q b pats body -> (
# 921 "FStar.Parser.ToSyntax.fst"
let tk = (desugar_binder env (
# 921 "FStar.Parser.ToSyntax.fst"
let _51_1582 = b
in {FStar_Parser_AST.b = _51_1582.FStar_Parser_AST.b; FStar_Parser_AST.brange = _51_1582.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _51_1582.FStar_Parser_AST.aqual}))
in (
# 922 "FStar.Parser.ToSyntax.fst"
let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _132_577 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _132_577)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(
# 925 "FStar.Parser.ToSyntax.fst"
let _51_1596 = (FStar_Parser_Env.push_bv env a)
in (match (_51_1596) with
| (env, a) -> begin
(
# 926 "FStar.Parser.ToSyntax.fst"
let a = (
# 926 "FStar.Parser.ToSyntax.fst"
let _51_1597 = a
in {FStar_Syntax_Syntax.ppname = _51_1597.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _51_1597.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (
# 927 "FStar.Parser.ToSyntax.fst"
let pats = (desugar_pats env pats)
in (
# 928 "FStar.Parser.ToSyntax.fst"
let body = (desugar_formula env body)
in (
# 929 "FStar.Parser.ToSyntax.fst"
let body = (match (pats) with
| [] -> begin
body
end
| _51_1604 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((body, FStar_Syntax_Syntax.Meta_pattern (pats)))))
end)
in (
# 932 "FStar.Parser.ToSyntax.fst"
let body = (let _132_580 = (let _132_579 = (let _132_578 = (FStar_Syntax_Syntax.mk_binder a)
in (_132_578)::[])
in (no_annot_abs _132_579 body))
in (FStar_All.pipe_left setpos _132_580))
in (let _132_586 = (let _132_585 = (let _132_584 = (let _132_581 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Syntax_Syntax.fvar _132_581 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (let _132_583 = (let _132_582 = (FStar_Syntax_Syntax.as_arg body)
in (_132_582)::[])
in (_132_584, _132_583)))
in FStar_Syntax_Syntax.Tm_app (_132_585))
in (FStar_All.pipe_left mk _132_586)))))))
end))
end
| _51_1608 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 937 "FStar.Parser.ToSyntax.fst"
let push_quant = (fun q binders pats body -> (match (binders) with
| b::b'::_rest -> begin
(
# 939 "FStar.Parser.ToSyntax.fst"
let rest = (b')::_rest
in (
# 940 "FStar.Parser.ToSyntax.fst"
let body = (let _132_601 = (q (rest, pats, body))
in (let _132_600 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _132_601 _132_600 FStar_Parser_AST.Formula)))
in (let _132_602 = (q ((b)::[], [], body))
in (FStar_Parser_AST.mk_term _132_602 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _51_1622 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _132_603 = (unparen f)
in _132_603.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(
# 946 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env f)
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((l, f.FStar_Syntax_Syntax.pos, p)))))))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall (_1::_2::_3, pats, body) -> begin
(
# 953 "FStar.Parser.ToSyntax.fst"
let binders = (_1)::(_2)::_3
in (let _132_605 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _132_605)))
end
| FStar_Parser_AST.QExists (_1::_2::_3, pats, body) -> begin
(
# 957 "FStar.Parser.ToSyntax.fst"
let binders = (_1)::(_2)::_3
in (let _132_607 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _132_607)))
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
| _51_1680 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (
# 972 "FStar.Parser.ToSyntax.fst"
let _51_1704 = (FStar_List.fold_left (fun _51_1685 b -> (match (_51_1685) with
| (env, out) -> begin
(
# 973 "FStar.Parser.ToSyntax.fst"
let tk = (desugar_binder env (
# 973 "FStar.Parser.ToSyntax.fst"
let _51_1687 = b
in {FStar_Parser_AST.b = _51_1687.FStar_Parser_AST.b; FStar_Parser_AST.brange = _51_1687.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _51_1687.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(
# 976 "FStar.Parser.ToSyntax.fst"
let _51_1696 = (FStar_Parser_Env.push_bv env a)
in (match (_51_1696) with
| (env, a) -> begin
(
# 977 "FStar.Parser.ToSyntax.fst"
let a = (
# 977 "FStar.Parser.ToSyntax.fst"
let _51_1697 = a
in {FStar_Syntax_Syntax.ppname = _51_1697.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _51_1697.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (env, ((a, (trans_aqual b.FStar_Parser_AST.aqual)))::out))
end))
end
| _51_1701 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected binder", b.FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_51_1704) with
| (env, tpars) -> begin
(env, (FStar_List.rev tpars))
end)))
and desugar_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(let _132_614 = (desugar_typ env t)
in (Some (x), _132_614))
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _132_615 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None x.FStar_Ident.idRange)
in (Some (x), _132_615))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _132_616 = (desugar_typ env t)
in (None, _132_616))
end
| FStar_Parser_AST.Variable (x) -> begin
(Some (x), FStar_Syntax_Syntax.tun)
end))

# 989 "FStar.Parser.ToSyntax.fst"
let mk_data_discriminators : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  FStar_Ident.lid  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun quals env t tps k datas -> (
# 990 "FStar.Parser.ToSyntax.fst"
let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_Env.iface) || env.FStar_Parser_Env.admitted_iface) then begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (
# 993 "FStar.Parser.ToSyntax.fst"
let binders = (let _132_632 = (let _132_631 = (FStar_Syntax_Util.arrow_formals k)
in (Prims.fst _132_631))
in (FStar_List.append tps _132_632))
in (
# 994 "FStar.Parser.ToSyntax.fst"
let p = (FStar_Ident.range_of_lid t)
in (
# 995 "FStar.Parser.ToSyntax.fst"
let _51_1731 = (FStar_Syntax_Util.args_of_binders binders)
in (match (_51_1731) with
| (binders, args) -> begin
(
# 996 "FStar.Parser.ToSyntax.fst"
let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _51_1735 -> (match (_51_1735) with
| (x, _51_1734) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
in (
# 997 "FStar.Parser.ToSyntax.fst"
let binders = (let _132_638 = (let _132_637 = (let _132_636 = (let _132_635 = (let _132_634 = (FStar_Syntax_Syntax.lid_as_fv t FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _132_634))
in (FStar_Syntax_Syntax.mk_Tm_app _132_635 args None p))
in (FStar_All.pipe_left FStar_Syntax_Syntax.null_binder _132_636))
in (_132_637)::[])
in (FStar_List.append imp_binders _132_638))
in (
# 998 "FStar.Parser.ToSyntax.fst"
let disc_type = (let _132_641 = (let _132_640 = (let _132_639 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _132_639))
in (FStar_Syntax_Syntax.mk_Total _132_640))
in (FStar_Syntax_Util.arrow binders _132_641))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (
# 1000 "FStar.Parser.ToSyntax.fst"
let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (let _132_644 = (let _132_643 = (quals ((FStar_Syntax_Syntax.Logic)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in (disc_name, [], disc_type, _132_643, (FStar_Ident.range_of_lid disc_name)))
in FStar_Syntax_Syntax.Sig_declare_typ (_132_644)))))))))
end))))))

# 1003 "FStar.Parser.ToSyntax.fst"
let mk_indexed_projectors : FStar_Syntax_Syntax.fv_qual  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun fvq refine_domain env tc lid inductive_tps imp_tps fields t -> (
# 1004 "FStar.Parser.ToSyntax.fst"
let p = (FStar_Ident.range_of_lid lid)
in (
# 1005 "FStar.Parser.ToSyntax.fst"
let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p))
in (
# 1006 "FStar.Parser.ToSyntax.fst"
let projectee = (fun ptyp -> (FStar_Syntax_Syntax.gen_bv "projectee" (Some (p)) ptyp))
in (
# 1007 "FStar.Parser.ToSyntax.fst"
let tps = (FStar_List.map2 (fun _51_1758 _51_1762 -> (match ((_51_1758, _51_1762)) with
| ((_51_1756, imp), (x, _51_1761)) -> begin
(x, imp)
end)) inductive_tps imp_tps)
in (
# 1008 "FStar.Parser.ToSyntax.fst"
let _51_1863 = (
# 1009 "FStar.Parser.ToSyntax.fst"
let _51_1766 = (FStar_Syntax_Util.head_and_args t)
in (match (_51_1766) with
| (head, args0) -> begin
(
# 1010 "FStar.Parser.ToSyntax.fst"
let args = (
# 1011 "FStar.Parser.ToSyntax.fst"
let rec arguments = (fun tps args -> (match ((tps, args)) with
| ([], _51_1772) -> begin
args
end
| (_51_1775, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Not enough arguments to type", (FStar_Ident.range_of_lid lid)))))
end
| ((_51_1780, Some (FStar_Syntax_Syntax.Implicit (_51_1782)))::tps', (_51_1789, Some (FStar_Syntax_Syntax.Implicit (_51_1791)))::args') -> begin
(arguments tps' args')
end
| ((_51_1799, Some (FStar_Syntax_Syntax.Implicit (_51_1801)))::tps', (_51_1809, _51_1811)::_51_1807) -> begin
(arguments tps' args)
end
| ((_51_1818, _51_1820)::_51_1816, (a, Some (FStar_Syntax_Syntax.Implicit (_51_1827)))::_51_1824) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected implicit annotation on argument", a.FStar_Syntax_Syntax.pos))))
end
| ((_51_1835, _51_1837)::tps', (_51_1842, _51_1844)::args') -> begin
(arguments tps' args')
end))
in (arguments inductive_tps args0))
in (
# 1020 "FStar.Parser.ToSyntax.fst"
let indices = (FStar_All.pipe_right args (FStar_List.map (fun _51_1849 -> (let _132_674 = (FStar_Syntax_Syntax.new_bv (Some (p)) FStar_Syntax_Syntax.tun)
in (FStar_All.pipe_right _132_674 FStar_Syntax_Syntax.mk_binder)))))
in (
# 1021 "FStar.Parser.ToSyntax.fst"
let arg_typ = (let _132_679 = (let _132_675 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _132_675))
in (let _132_678 = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _51_1854 -> (match (_51_1854) with
| (x, imp) -> begin
(let _132_677 = (FStar_Syntax_Syntax.bv_to_name x)
in (_132_677, imp))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app _132_679 _132_678 None p)))
in (
# 1023 "FStar.Parser.ToSyntax.fst"
let arg_binder = if (not (refine_domain)) then begin
(let _132_680 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder _132_680))
end else begin
(
# 1026 "FStar.Parser.ToSyntax.fst"
let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (
# 1027 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p)) arg_typ)
in (let _132_689 = (
# 1028 "FStar.Parser.ToSyntax.fst"
let _51_1858 = (projectee arg_typ)
in (let _132_688 = (let _132_687 = (let _132_686 = (let _132_685 = (let _132_681 = (FStar_Ident.set_lid_range disc_name p)
in (FStar_Syntax_Syntax.fvar _132_681 FStar_Syntax_Syntax.Delta_equational None))
in (let _132_684 = (let _132_683 = (let _132_682 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _132_682))
in (_132_683)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _132_685 _132_684 None p)))
in (FStar_Syntax_Util.b2t _132_686))
in (FStar_Syntax_Util.refine x _132_687))
in {FStar_Syntax_Syntax.ppname = _51_1858.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _51_1858.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _132_688}))
in (FStar_Syntax_Syntax.mk_binder _132_689))))
end
in (arg_binder, indices)))))
end))
in (match (_51_1863) with
| (arg_binder, indices) -> begin
(
# 1032 "FStar.Parser.ToSyntax.fst"
let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder))
in (
# 1033 "FStar.Parser.ToSyntax.fst"
let imp_binders = (let _132_691 = (FStar_All.pipe_right indices (FStar_List.map (fun _51_1868 -> (match (_51_1868) with
| (x, _51_1867) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
in (FStar_List.append imp_tps _132_691))
in (
# 1034 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (
# 1036 "FStar.Parser.ToSyntax.fst"
let arg = (FStar_Syntax_Util.arg_of_non_null_binder arg_binder)
in (
# 1038 "FStar.Parser.ToSyntax.fst"
let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _51_1876 -> (match (_51_1876) with
| (a, _51_1875) -> begin
(
# 1039 "FStar.Parser.ToSyntax.fst"
let _51_1880 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (_51_1880) with
| (field_name, _51_1879) -> begin
(
# 1040 "FStar.Parser.ToSyntax.fst"
let proj = (let _132_695 = (let _132_694 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.fv_to_tm _132_694))
in (FStar_Syntax_Syntax.mk_Tm_app _132_695 ((arg)::[]) None p))
in FStar_Syntax_Syntax.NT ((a, proj)))
end))
end))))
in (
# 1043 "FStar.Parser.ToSyntax.fst"
let ntps = (FStar_List.length tps)
in (
# 1044 "FStar.Parser.ToSyntax.fst"
let all_params = (FStar_List.append imp_tps fields)
in (let _132_731 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _51_1889 -> (match (_51_1889) with
| (x, _51_1888) -> begin
(
# 1047 "FStar.Parser.ToSyntax.fst"
let _51_1893 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_51_1893) with
| (field_name, _51_1892) -> begin
(
# 1048 "FStar.Parser.ToSyntax.fst"
let t = (let _132_699 = (let _132_698 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total _132_698))
in (FStar_Syntax_Util.arrow binders _132_699))
in (
# 1049 "FStar.Parser.ToSyntax.fst"
let only_decl = (((let _132_700 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _132_700)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _132_702 = (let _132_701 = (FStar_Parser_Env.current_module env)
in _132_701.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _132_702)))
in (
# 1053 "FStar.Parser.ToSyntax.fst"
let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (
# 1054 "FStar.Parser.ToSyntax.fst"
let quals = (fun q -> if only_decl then begin
(FStar_Syntax_Syntax.Assumption)::q
end else begin
q
end)
in (
# 1055 "FStar.Parser.ToSyntax.fst"
let quals = (quals ((FStar_Syntax_Syntax.Projector ((lid, x.FStar_Syntax_Syntax.ppname)))::[]))
in (
# 1056 "FStar.Parser.ToSyntax.fst"
let decl = FStar_Syntax_Syntax.Sig_declare_typ ((field_name, [], t, quals, (FStar_Ident.range_of_lid field_name)))
in if only_decl then begin
(decl)::[]
end else begin
(
# 1059 "FStar.Parser.ToSyntax.fst"
let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (
# 1060 "FStar.Parser.ToSyntax.fst"
let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _51_1905 -> (match (_51_1905) with
| (x, imp) -> begin
(
# 1061 "FStar.Parser.ToSyntax.fst"
let b = (FStar_Syntax_Syntax.is_implicit imp)
in if ((i + ntps) = j) then begin
(let _132_707 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in (_132_707, b))
end else begin
if (b && (j < ntps)) then begin
(let _132_711 = (let _132_710 = (let _132_709 = (let _132_708 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (_132_708, FStar_Syntax_Syntax.tun))
in FStar_Syntax_Syntax.Pat_dot_term (_132_709))
in (pos _132_710))
in (_132_711, b))
end else begin
(let _132_714 = (let _132_713 = (let _132_712 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_132_712))
in (pos _132_713))
in (_132_714, b))
end
end)
end))))
in (
# 1067 "FStar.Parser.ToSyntax.fst"
let pat = (let _132_719 = (let _132_717 = (let _132_716 = (let _132_715 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in (_132_715, arg_pats))
in FStar_Syntax_Syntax.Pat_cons (_132_716))
in (FStar_All.pipe_right _132_717 pos))
in (let _132_718 = (FStar_Syntax_Syntax.bv_to_name projection)
in (_132_719, None, _132_718)))
in (
# 1068 "FStar.Parser.ToSyntax.fst"
let body = (let _132_723 = (let _132_722 = (let _132_721 = (let _132_720 = (FStar_Syntax_Util.branch pat)
in (_132_720)::[])
in (arg_exp, _132_721))
in FStar_Syntax_Syntax.Tm_match (_132_722))
in (FStar_Syntax_Syntax.mk _132_723 None p))
in (
# 1069 "FStar.Parser.ToSyntax.fst"
let imp = (no_annot_abs binders body)
in (
# 1070 "FStar.Parser.ToSyntax.fst"
let lb = (let _132_725 = (let _132_724 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None)
in FStar_Util.Inr (_132_724))
in {FStar_Syntax_Syntax.lbname = _132_725; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = imp})
in (
# 1075 "FStar.Parser.ToSyntax.fst"
let impl = (let _132_730 = (let _132_729 = (let _132_728 = (let _132_727 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _132_727 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_132_728)::[])
in ((false, (lb)::[]), p, _132_729, quals))
in FStar_Syntax_Syntax.Sig_let (_132_730))
in if no_decl then begin
(impl)::[]
end else begin
(decl)::(impl)::[]
end)))))))
end))))))
end))
end))))
in (FStar_All.pipe_right _132_731 FStar_List.flatten)))))))))
end)))))))

# 1078 "FStar.Parser.ToSyntax.fst"
let mk_data_projectors : FStar_Parser_Env.env  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun env _51_1917 -> (match (_51_1917) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _51_1920, t, l, n, quals, _51_1926, _51_1928) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(
# 1081 "FStar.Parser.ToSyntax.fst"
let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _51_10 -> (match (_51_10) with
| FStar_Syntax_Syntax.RecordConstructor (_51_1933) -> begin
true
end
| _51_1936 -> begin
false
end)))) then begin
false
end else begin
(match ((FStar_Parser_Env.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > 1)
end
| _51_1940 -> begin
true
end)
end
in (
# 1087 "FStar.Parser.ToSyntax.fst"
let _51_1944 = (FStar_Syntax_Util.arrow_formals t)
in (match (_51_1944) with
| (formals, cod) -> begin
(match (formals) with
| [] -> begin
[]
end
| _51_1947 -> begin
(
# 1091 "FStar.Parser.ToSyntax.fst"
let qual = (match ((FStar_Util.find_map quals (fun _51_11 -> (match (_51_11) with
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((lid, fns)))
end
| _51_1952 -> begin
None
end)))) with
| None -> begin
FStar_Syntax_Syntax.Data_ctor
end
| Some (q) -> begin
q
end)
in (
# 1094 "FStar.Parser.ToSyntax.fst"
let _51_1959 = (FStar_Util.first_N n formals)
in (match (_51_1959) with
| (tps, rest) -> begin
(mk_indexed_projectors qual refine_domain env l lid inductive_tps tps rest cod)
end)))
end)
end)))
end
| _51_1961 -> begin
[]
end)
end))

# 1100 "FStar.Parser.ToSyntax.fst"
let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (
# 1101 "FStar.Parser.ToSyntax.fst"
let lb = (let _132_759 = (let _132_755 = (let _132_754 = (incr_delta_qualifier t)
in (FStar_Syntax_Syntax.lid_as_fv lid _132_754 None))
in FStar_Util.Inr (_132_755))
in (let _132_758 = (let _132_756 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars _132_756))
in (let _132_757 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = _132_759; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = _132_758; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _132_757})))
in FStar_Syntax_Syntax.Sig_let (((false, (lb)::[]), rng, lids, quals))))

# 1110 "FStar.Parser.ToSyntax.fst"
let rec desugar_tycon : FStar_Parser_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (
# 1111 "FStar.Parser.ToSyntax.fst"
let tycon_id = (fun _51_12 -> (match (_51_12) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (
# 1116 "FStar.Parser.ToSyntax.fst"
let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _132_773 = (let _132_772 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_132_772))
in (FStar_Parser_AST.mk_term _132_773 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| (FStar_Parser_AST.TAnnotated (a, _)) | (FStar_Parser_AST.TVariable (a)) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar (a)) a.FStar_Ident.idRange FStar_Parser_AST.Type)
end
| FStar_Parser_AST.NoName (t) -> begin
t
end))
in (
# 1122 "FStar.Parser.ToSyntax.fst"
let tot = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) rng FStar_Parser_AST.Expr)
in (
# 1123 "FStar.Parser.ToSyntax.fst"
let with_constructor_effect = (fun t -> (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((tot, t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level))
in (
# 1124 "FStar.Parser.ToSyntax.fst"
let apply_binders = (fun t binders -> (
# 1125 "FStar.Parser.ToSyntax.fst"
let imp_of_aqual = (fun b -> (match (b.FStar_Parser_AST.aqual) with
| Some (FStar_Parser_AST.Implicit) -> begin
FStar_Parser_AST.Hash
end
| _51_2035 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _132_786 = (let _132_785 = (let _132_784 = (binder_to_term b)
in (out, _132_784, (imp_of_aqual b)))
in FStar_Parser_AST.App (_132_785))
in (FStar_Parser_AST.mk_term _132_786 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (
# 1130 "FStar.Parser.ToSyntax.fst"
let tycon_record_as_variant = (fun _51_13 -> (match (_51_13) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(
# 1132 "FStar.Parser.ToSyntax.fst"
let constrName = (FStar_Ident.mk_ident ((Prims.strcat "Mk" id.FStar_Ident.idText), id.FStar_Ident.idRange))
in (
# 1133 "FStar.Parser.ToSyntax.fst"
let mfields = (FStar_List.map (fun _51_2048 -> (match (_51_2048) with
| (x, t) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated (((FStar_Syntax_Util.mangle_field_name x), t))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (
# 1134 "FStar.Parser.ToSyntax.fst"
let result = (let _132_792 = (let _132_791 = (let _132_790 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_132_790))
in (FStar_Parser_AST.mk_term _132_791 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _132_792 parms))
in (
# 1135 "FStar.Parser.ToSyntax.fst"
let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _132_794 = (FStar_All.pipe_right fields (FStar_List.map (fun _51_2055 -> (match (_51_2055) with
| (x, _51_2054) -> begin
(FStar_Parser_Env.qualify env x)
end))))
in (FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _132_794))))))
end
| _51_2057 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1139 "FStar.Parser.ToSyntax.fst"
let desugar_abstract_tc = (fun quals _env mutuals _51_14 -> (match (_51_14) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(
# 1141 "FStar.Parser.ToSyntax.fst"
let _51_2071 = (typars_of_binders _env binders)
in (match (_51_2071) with
| (_env', typars) -> begin
(
# 1142 "FStar.Parser.ToSyntax.fst"
let k = (match (kopt) with
| None -> begin
FStar_Syntax_Util.ktype
end
| Some (k) -> begin
(desugar_term _env' k)
end)
in (
# 1145 "FStar.Parser.ToSyntax.fst"
let tconstr = (let _132_805 = (let _132_804 = (let _132_803 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_132_803))
in (FStar_Parser_AST.mk_term _132_804 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _132_805 binders))
in (
# 1146 "FStar.Parser.ToSyntax.fst"
let qlid = (FStar_Parser_Env.qualify _env id)
in (
# 1147 "FStar.Parser.ToSyntax.fst"
let typars = (FStar_Syntax_Subst.close_binders typars)
in (
# 1148 "FStar.Parser.ToSyntax.fst"
let k = (FStar_Syntax_Subst.close typars k)
in (
# 1149 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_inductive_typ ((qlid, [], typars, k, mutuals, [], quals, rng))
in (
# 1150 "FStar.Parser.ToSyntax.fst"
let _env = (FStar_Parser_Env.push_top_level_rec_binding _env id FStar_Syntax_Syntax.Delta_constant)
in (
# 1151 "FStar.Parser.ToSyntax.fst"
let _env2 = (FStar_Parser_Env.push_top_level_rec_binding _env' id FStar_Syntax_Syntax.Delta_constant)
in (_env, _env2, se, tconstr)))))))))
end))
end
| _51_2084 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (
# 1154 "FStar.Parser.ToSyntax.fst"
let push_tparams = (fun env bs -> (
# 1155 "FStar.Parser.ToSyntax.fst"
let _51_2099 = (FStar_List.fold_left (fun _51_2090 _51_2093 -> (match ((_51_2090, _51_2093)) with
| ((env, tps), (x, imp)) -> begin
(
# 1156 "FStar.Parser.ToSyntax.fst"
let _51_2096 = (FStar_Parser_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (_51_2096) with
| (env, y) -> begin
(env, ((y, imp))::tps)
end))
end)) (env, []) bs)
in (match (_51_2099) with
| (env, bs) -> begin
(env, (FStar_List.rev bs))
end)))
in (match (tcs) with
| FStar_Parser_AST.TyconAbstract (_51_2101)::[] -> begin
(
# 1161 "FStar.Parser.ToSyntax.fst"
let tc = (FStar_List.hd tcs)
in (
# 1162 "FStar.Parser.ToSyntax.fst"
let _51_2112 = (desugar_abstract_tc quals env [] tc)
in (match (_51_2112) with
| (_51_2106, _51_2108, se, _51_2111) -> begin
(
# 1163 "FStar.Parser.ToSyntax.fst"
let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _51_2115, typars, k, [], [], quals, rng) -> begin
(
# 1165 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
quals
end else begin
(
# 1167 "FStar.Parser.ToSyntax.fst"
let _51_2124 = (let _132_813 = (FStar_Range.string_of_range rng)
in (let _132_812 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" _132_813 _132_812)))
in (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals)
end
in (
# 1170 "FStar.Parser.ToSyntax.fst"
let t = (match (typars) with
| [] -> begin
k
end
| _51_2129 -> begin
(let _132_816 = (let _132_815 = (let _132_814 = (FStar_Syntax_Syntax.mk_Total k)
in (typars, _132_814))
in FStar_Syntax_Syntax.Tm_arrow (_132_815))
in (FStar_Syntax_Syntax.mk _132_816 None rng))
end)
in FStar_Syntax_Syntax.Sig_declare_typ ((l, [], t, quals, rng))))
end
| _51_2132 -> begin
se
end)
in (
# 1175 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))
end)))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t)::[] -> begin
(
# 1180 "FStar.Parser.ToSyntax.fst"
let _51_2144 = (typars_of_binders env binders)
in (match (_51_2144) with
| (env', typars) -> begin
(
# 1181 "FStar.Parser.ToSyntax.fst"
let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _51_15 -> (match (_51_15) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| _51_2149 -> begin
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
# 1187 "FStar.Parser.ToSyntax.fst"
let t0 = t
in (
# 1188 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _51_16 -> (match (_51_16) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| _51_2157 -> begin
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
# 1193 "FStar.Parser.ToSyntax.fst"
let se = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Effect)) then begin
(
# 1195 "FStar.Parser.ToSyntax.fst"
let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (
# 1196 "FStar.Parser.ToSyntax.fst"
let typars = (FStar_Syntax_Subst.close_binders typars)
in (
# 1197 "FStar.Parser.ToSyntax.fst"
let c = (FStar_Syntax_Subst.close_comp typars c)
in (let _132_822 = (let _132_821 = (FStar_Parser_Env.qualify env id)
in (let _132_820 = (FStar_All.pipe_right quals (FStar_List.filter (fun _51_17 -> (match (_51_17) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| _51_2165 -> begin
true
end))))
in (_132_821, [], typars, c, _132_820, rng)))
in FStar_Syntax_Syntax.Sig_effect_abbrev (_132_822)))))
end else begin
(
# 1199 "FStar.Parser.ToSyntax.fst"
let t = (desugar_typ env' t)
in (
# 1200 "FStar.Parser.ToSyntax.fst"
let nm = (FStar_Parser_Env.qualify env id)
in (mk_typ_abbrev nm [] typars k t ((nm)::[]) quals rng)))
end
in (
# 1203 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[]))))))
end))
end
| FStar_Parser_AST.TyconRecord (_51_2171)::[] -> begin
(
# 1207 "FStar.Parser.ToSyntax.fst"
let trec = (FStar_List.hd tcs)
in (
# 1208 "FStar.Parser.ToSyntax.fst"
let _51_2177 = (tycon_record_as_variant trec)
in (match (_51_2177) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| _51_2181::_51_2179 -> begin
(
# 1212 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1213 "FStar.Parser.ToSyntax.fst"
let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_Env.qualify env) (tycon_id x))) tcs)
in (
# 1214 "FStar.Parser.ToSyntax.fst"
let rec collect_tcs = (fun quals et tc -> (
# 1215 "FStar.Parser.ToSyntax.fst"
let _51_2192 = et
in (match (_51_2192) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_51_2194) -> begin
(
# 1218 "FStar.Parser.ToSyntax.fst"
let trec = tc
in (
# 1219 "FStar.Parser.ToSyntax.fst"
let _51_2199 = (tycon_record_as_variant trec)
in (match (_51_2199) with
| (t, fs) -> begin
(collect_tcs ((FStar_Syntax_Syntax.RecordType (fs))::quals) (env, tcs) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(
# 1222 "FStar.Parser.ToSyntax.fst"
let _51_2211 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_51_2211) with
| (env, _51_2208, se, tconstr) -> begin
(env, (FStar_Util.Inl ((se, constructors, tconstr, quals)))::tcs)
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(
# 1225 "FStar.Parser.ToSyntax.fst"
let _51_2223 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_51_2223) with
| (env, _51_2220, se, tconstr) -> begin
(env, (FStar_Util.Inr ((se, t, quals)))::tcs)
end))
end
| _51_2225 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (
# 1228 "FStar.Parser.ToSyntax.fst"
let _51_2228 = (FStar_List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_51_2228) with
| (env, tcs) -> begin
(
# 1229 "FStar.Parser.ToSyntax.fst"
let tcs = (FStar_List.rev tcs)
in (
# 1230 "FStar.Parser.ToSyntax.fst"
let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _51_19 -> (match (_51_19) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, _51_2236, _51_2238, _51_2240, _51_2242), t, quals) -> begin
(
# 1232 "FStar.Parser.ToSyntax.fst"
let _51_2252 = (push_tparams env tpars)
in (match (_51_2252) with
| (env_tps, _51_2251) -> begin
(
# 1233 "FStar.Parser.ToSyntax.fst"
let t = (desugar_term env_tps t)
in (let _132_832 = (let _132_831 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in ([], _132_831))
in (_132_832)::[]))
end))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, _51_2260, tags, _51_2263), constrs, tconstr, quals) -> begin
(
# 1237 "FStar.Parser.ToSyntax.fst"
let tycon = (tname, tpars, k)
in (
# 1238 "FStar.Parser.ToSyntax.fst"
let _51_2274 = (push_tparams env tpars)
in (match (_51_2274) with
| (env_tps, tps) -> begin
(
# 1239 "FStar.Parser.ToSyntax.fst"
let data_tpars = (FStar_List.map (fun _51_2278 -> (match (_51_2278) with
| (x, _51_2277) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end)) tps)
in (
# 1240 "FStar.Parser.ToSyntax.fst"
let _51_2302 = (let _132_844 = (FStar_All.pipe_right constrs (FStar_List.map (fun _51_2283 -> (match (_51_2283) with
| (id, topt, of_notation) -> begin
(
# 1242 "FStar.Parser.ToSyntax.fst"
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
# 1250 "FStar.Parser.ToSyntax.fst"
let t = (let _132_836 = (FStar_Parser_Env.default_total env_tps)
in (let _132_835 = (close env_tps t)
in (desugar_term _132_836 _132_835)))
in (
# 1251 "FStar.Parser.ToSyntax.fst"
let name = (FStar_Parser_Env.qualify env id)
in (
# 1252 "FStar.Parser.ToSyntax.fst"
let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _51_18 -> (match (_51_18) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| _51_2297 -> begin
[]
end))))
in (
# 1255 "FStar.Parser.ToSyntax.fst"
let ntps = (FStar_List.length data_tpars)
in (let _132_843 = (let _132_842 = (let _132_841 = (let _132_840 = (let _132_839 = (let _132_838 = (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total _132_838))
in (FStar_Syntax_Util.arrow data_tpars _132_839))
in (name, univs, _132_840, tname, ntps, quals, mutuals, rng))
in FStar_Syntax_Syntax.Sig_datacon (_132_841))
in (tps, _132_842))
in (name, _132_843)))))))
end))))
in (FStar_All.pipe_left FStar_List.split _132_844))
in (match (_51_2302) with
| (constrNames, constrs) -> begin
(([], FStar_Syntax_Syntax.Sig_inductive_typ ((tname, univs, tpars, k, mutuals, constrNames, tags, rng))))::constrs
end)))
end)))
end
| _51_2304 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1260 "FStar.Parser.ToSyntax.fst"
let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (
# 1261 "FStar.Parser.ToSyntax.fst"
let bundle = (let _132_846 = (let _132_845 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _132_845, rng))
in FStar_Syntax_Syntax.Sig_bundle (_132_846))
in (
# 1262 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 bundle)
in (
# 1263 "FStar.Parser.ToSyntax.fst"
let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projectors env)))
in (
# 1264 "FStar.Parser.ToSyntax.fst"
let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _51_20 -> (match (_51_20) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, _51_2313, tps, k, _51_2317, constrs, quals, _51_2321) when ((FStar_List.length constrs) > 1) -> begin
(mk_data_discriminators quals env tname tps k constrs)
end
| _51_2325 -> begin
[]
end))))
in (
# 1268 "FStar.Parser.ToSyntax.fst"
let ops = (FStar_List.append discs data_ops)
in (
# 1269 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env ops)
in (env, (FStar_List.append ((bundle)::[]) ops)))))))))))
end)))))
end
| [] -> begin
(FStar_All.failwith "impossible")
end))))))))))

# 1274 "FStar.Parser.ToSyntax.fst"
let desugar_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.binder Prims.list) = (fun env binders -> (
# 1275 "FStar.Parser.ToSyntax.fst"
let _51_2349 = (FStar_List.fold_left (fun _51_2334 b -> (match (_51_2334) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| (Some (a), k) -> begin
(
# 1278 "FStar.Parser.ToSyntax.fst"
let _51_2342 = (FStar_Parser_Env.push_bv env a)
in (match (_51_2342) with
| (env, a) -> begin
(let _132_855 = (let _132_854 = (FStar_Syntax_Syntax.mk_binder (
# 1279 "FStar.Parser.ToSyntax.fst"
let _51_2343 = a
in {FStar_Syntax_Syntax.ppname = _51_2343.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _51_2343.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (_132_854)::binders)
in (env, _132_855))
end))
end
| _51_2346 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Missing name in binder", b.FStar_Parser_AST.brange))))
end)
end)) (env, []) binders)
in (match (_51_2349) with
| (env, binders) -> begin
(env, (FStar_List.rev binders))
end)))

# 1284 "FStar.Parser.ToSyntax.fst"
let rec desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(
# 1286 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_pragma (((trans_pragma p), d.FStar_Parser_AST.drange))
in (env, (se)::[]))
end
| FStar_Parser_AST.Open (lid) -> begin
(
# 1290 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_namespace env lid)
in (env, []))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(let _132_860 = (FStar_List.map trans_qual qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _132_860 tcs))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _132_862 = (let _132_861 = (desugar_term_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((isrec, lets, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Syntax_Subst.compress _132_861))
in _132_862.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let (lbs, _51_2369) -> begin
(
# 1299 "FStar.Parser.ToSyntax.fst"
let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (
# 1300 "FStar.Parser.ToSyntax.fst"
let quals = (match (quals) with
| _51_2377::_51_2375 -> begin
(FStar_List.map trans_qual quals)
end
| _51_2380 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _51_21 -> (match (_51_21) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (_51_2391); FStar_Syntax_Syntax.lbunivs = _51_2389; FStar_Syntax_Syntax.lbtyp = _51_2387; FStar_Syntax_Syntax.lbeff = _51_2385; FStar_Syntax_Syntax.lbdef = _51_2383} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _51_2401; FStar_Syntax_Syntax.lbtyp = _51_2399; FStar_Syntax_Syntax.lbeff = _51_2397; FStar_Syntax_Syntax.lbdef = _51_2395} -> begin
(FStar_Parser_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (
# 1305 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right lets (FStar_Util.for_some (fun _51_2409 -> (match (_51_2409) with
| (_51_2407, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end)))) then begin
(FStar_Syntax_Syntax.Logic)::quals
end else begin
quals
end
in (
# 1309 "FStar.Parser.ToSyntax.fst"
let s = (let _132_868 = (let _132_867 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (lbs, d.FStar_Parser_AST.drange, _132_867, quals))
in FStar_Syntax_Syntax.Sig_let (_132_868))
in (
# 1310 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env s)
in (env, (s)::[]))))))
end
| _51_2415 -> begin
(FStar_All.failwith "Desugaring a let did not produce a let")
end)
end
| FStar_Parser_AST.Main (t) -> begin
(
# 1316 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env t)
in (
# 1317 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, d.FStar_Parser_AST.drange))
in (env, (se)::[])))
end
| FStar_Parser_AST.Assume (atag, id, t) -> begin
(
# 1321 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env t)
in (let _132_872 = (let _132_871 = (let _132_870 = (let _132_869 = (FStar_Parser_Env.qualify env id)
in (_132_869, f, (FStar_Syntax_Syntax.Assumption)::[], d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Sig_assume (_132_870))
in (_132_871)::[])
in (env, _132_872)))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(
# 1325 "FStar.Parser.ToSyntax.fst"
let t = (let _132_873 = (close_fun env t)
in (desugar_term env _132_873))
in (
# 1326 "FStar.Parser.ToSyntax.fst"
let quals = if (env.FStar_Parser_Env.iface && env.FStar_Parser_Env.admitted_iface) then begin
(FStar_Parser_AST.Assumption)::quals
end else begin
quals
end
in (
# 1327 "FStar.Parser.ToSyntax.fst"
let se = (let _132_876 = (let _132_875 = (FStar_Parser_Env.qualify env id)
in (let _132_874 = (FStar_List.map trans_qual quals)
in (_132_875, [], t, _132_874, d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_declare_typ (_132_876))
in (
# 1328 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(
# 1332 "FStar.Parser.ToSyntax.fst"
let t = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (
# 1333 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env id)
in (
# 1334 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_datacon ((l, [], t, FStar_Syntax_Const.exn_lid, 0, (FStar_Syntax_Syntax.ExceptionConstructor)::[], (FStar_Syntax_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (
# 1335 "FStar.Parser.ToSyntax.fst"
let se' = FStar_Syntax_Syntax.Sig_bundle (((se)::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (
# 1336 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se')
in (
# 1337 "FStar.Parser.ToSyntax.fst"
let data_ops = (mk_data_projectors env ([], se))
in (
# 1338 "FStar.Parser.ToSyntax.fst"
let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (
# 1339 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops))))))))))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(
# 1343 "FStar.Parser.ToSyntax.fst"
let t = (desugar_term env term)
in (
# 1344 "FStar.Parser.ToSyntax.fst"
let t = (let _132_880 = (let _132_877 = (FStar_Syntax_Syntax.null_binder t)
in (_132_877)::[])
in (let _132_879 = (let _132_878 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _132_878))
in (FStar_Syntax_Util.arrow _132_880 _132_879)))
in (
# 1345 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env id)
in (
# 1346 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_datacon ((l, [], t, FStar_Syntax_Const.exn_lid, 0, (FStar_Syntax_Syntax.ExceptionConstructor)::[], (FStar_Syntax_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (
# 1347 "FStar.Parser.ToSyntax.fst"
let se' = FStar_Syntax_Syntax.Sig_bundle (((se)::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (
# 1348 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se')
in (
# 1349 "FStar.Parser.ToSyntax.fst"
let data_ops = (mk_data_projectors env ([], se))
in (
# 1350 "FStar.Parser.ToSyntax.fst"
let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (
# 1351 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops)))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(
# 1355 "FStar.Parser.ToSyntax.fst"
let _51_2468 = (desugar_binders env binders)
in (match (_51_2468) with
| (env_k, binders) -> begin
(
# 1356 "FStar.Parser.ToSyntax.fst"
let k = (desugar_term env_k k)
in (
# 1357 "FStar.Parser.ToSyntax.fst"
let name = (FStar_Parser_Env.qualify env id)
in (
# 1358 "FStar.Parser.ToSyntax.fst"
let se = (mk_typ_abbrev name [] binders FStar_Syntax_Syntax.tun k ((name)::[]) [] d.FStar_Parser_AST.drange)
in (
# 1359 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))))
end))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(
# 1363 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1364 "FStar.Parser.ToSyntax.fst"
let _51_2484 = (desugar_binders env eff_binders)
in (match (_51_2484) with
| (env, binders) -> begin
(
# 1365 "FStar.Parser.ToSyntax.fst"
let _51_2495 = (
# 1366 "FStar.Parser.ToSyntax.fst"
let _51_2487 = (head_and_args defn)
in (match (_51_2487) with
| (head, args) -> begin
(
# 1367 "FStar.Parser.ToSyntax.fst"
let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_defn env) l)
end
| _51_2491 -> begin
(let _132_885 = (let _132_884 = (let _132_883 = (let _132_882 = (let _132_881 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat "Effect " _132_881))
in (Prims.strcat _132_882 " not found"))
in (_132_883, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_132_884))
in (Prims.raise _132_885))
end)
in (let _132_886 = (desugar_args env args)
in (ed, _132_886)))
end))
in (match (_51_2495) with
| (ed, args) -> begin
(
# 1371 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_Syntax_Subst.close_binders binders)
in (
# 1372 "FStar.Parser.ToSyntax.fst"
let sub = (fun _51_2501 -> (match (_51_2501) with
| (_51_2499, x) -> begin
(
# 1373 "FStar.Parser.ToSyntax.fst"
let _51_2504 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (_51_2504) with
| (edb, x) -> begin
(
# 1374 "FStar.Parser.ToSyntax.fst"
let s = (FStar_Syntax_Util.subst_of_list edb args)
in (let _132_890 = (let _132_889 = (FStar_Syntax_Subst.subst s x)
in (FStar_Syntax_Subst.close binders _132_889))
in ([], _132_890)))
end))
end))
in (
# 1376 "FStar.Parser.ToSyntax.fst"
let ed = (let _132_907 = (FStar_List.map trans_qual quals)
in (let _132_906 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _132_905 = (let _132_891 = (sub ([], ed.FStar_Syntax_Syntax.signature))
in (Prims.snd _132_891))
in (let _132_904 = (sub ed.FStar_Syntax_Syntax.ret)
in (let _132_903 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (let _132_902 = (sub ed.FStar_Syntax_Syntax.bind_wlp)
in (let _132_901 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (let _132_900 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (let _132_899 = (sub ed.FStar_Syntax_Syntax.ite_wlp)
in (let _132_898 = (sub ed.FStar_Syntax_Syntax.wp_binop)
in (let _132_897 = (sub ed.FStar_Syntax_Syntax.wp_as_type)
in (let _132_896 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (let _132_895 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (let _132_894 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (let _132_893 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (let _132_892 = (sub ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _132_907; FStar_Syntax_Syntax.mname = _132_906; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = _132_905; FStar_Syntax_Syntax.ret = _132_904; FStar_Syntax_Syntax.bind_wp = _132_903; FStar_Syntax_Syntax.bind_wlp = _132_902; FStar_Syntax_Syntax.if_then_else = _132_901; FStar_Syntax_Syntax.ite_wp = _132_900; FStar_Syntax_Syntax.ite_wlp = _132_899; FStar_Syntax_Syntax.wp_binop = _132_898; FStar_Syntax_Syntax.wp_as_type = _132_897; FStar_Syntax_Syntax.close_wp = _132_896; FStar_Syntax_Syntax.assert_p = _132_895; FStar_Syntax_Syntax.assume_p = _132_894; FStar_Syntax_Syntax.null_wp = _132_893; FStar_Syntax_Syntax.trivial = _132_892}))))))))))))))))
in (
# 1396 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (
# 1397 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 se)
in (env, (se)::[]))))))
end))
end)))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls)) -> begin
(
# 1401 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1402 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.enter_monad_scope env eff_name)
in (
# 1403 "FStar.Parser.ToSyntax.fst"
let _51_2522 = (desugar_binders env eff_binders)
in (match (_51_2522) with
| (env, binders) -> begin
(
# 1404 "FStar.Parser.ToSyntax.fst"
let eff_k = (let _132_908 = (FStar_Parser_Env.default_total env)
in (desugar_term _132_908 eff_kind))
in (
# 1405 "FStar.Parser.ToSyntax.fst"
let _51_2533 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _51_2526 decl -> (match (_51_2526) with
| (env, out) -> begin
(
# 1406 "FStar.Parser.ToSyntax.fst"
let _51_2530 = (desugar_decl env decl)
in (match (_51_2530) with
| (env, ses) -> begin
(let _132_912 = (let _132_911 = (FStar_List.hd ses)
in (_132_911)::out)
in (env, _132_912))
end))
end)) (env, [])))
in (match (_51_2533) with
| (env, decls) -> begin
(
# 1408 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_Syntax_Subst.close_binders binders)
in (
# 1409 "FStar.Parser.ToSyntax.fst"
let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (
# 1410 "FStar.Parser.ToSyntax.fst"
let lookup = (fun s -> (
# 1411 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env (FStar_Ident.mk_ident (s, d.FStar_Parser_AST.drange)))
in (let _132_916 = (let _132_915 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) _132_915))
in ([], _132_916))))
in (
# 1413 "FStar.Parser.ToSyntax.fst"
let ed = (let _132_931 = (FStar_List.map trans_qual quals)
in (let _132_930 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _132_929 = (lookup "return")
in (let _132_928 = (lookup "bind_wp")
in (let _132_927 = (lookup "bind_wlp")
in (let _132_926 = (lookup "if_then_else")
in (let _132_925 = (lookup "ite_wp")
in (let _132_924 = (lookup "ite_wlp")
in (let _132_923 = (lookup "wp_binop")
in (let _132_922 = (lookup "wp_as_type")
in (let _132_921 = (lookup "close_wp")
in (let _132_920 = (lookup "assert_p")
in (let _132_919 = (lookup "assume_p")
in (let _132_918 = (lookup "null_wp")
in (let _132_917 = (lookup "trivial")
in {FStar_Syntax_Syntax.qualifiers = _132_931; FStar_Syntax_Syntax.mname = _132_930; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret = _132_929; FStar_Syntax_Syntax.bind_wp = _132_928; FStar_Syntax_Syntax.bind_wlp = _132_927; FStar_Syntax_Syntax.if_then_else = _132_926; FStar_Syntax_Syntax.ite_wp = _132_925; FStar_Syntax_Syntax.ite_wlp = _132_924; FStar_Syntax_Syntax.wp_binop = _132_923; FStar_Syntax_Syntax.wp_as_type = _132_922; FStar_Syntax_Syntax.close_wp = _132_921; FStar_Syntax_Syntax.assert_p = _132_920; FStar_Syntax_Syntax.assume_p = _132_919; FStar_Syntax_Syntax.null_wp = _132_918; FStar_Syntax_Syntax.trivial = _132_917})))))))))))))))
in (
# 1433 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (
# 1434 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 se)
in (env, (se)::[])))))))
end)))
end))))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(
# 1438 "FStar.Parser.ToSyntax.fst"
let lookup = (fun l -> (match ((FStar_Parser_Env.try_lookup_effect_name env l)) with
| None -> begin
(let _132_938 = (let _132_937 = (let _132_936 = (let _132_935 = (let _132_934 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat "Effect name " _132_934))
in (Prims.strcat _132_935 " not found"))
in (_132_936, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_132_937))
in (Prims.raise _132_938))
end
| Some (l) -> begin
l
end))
in (
# 1441 "FStar.Parser.ToSyntax.fst"
let src = (lookup l.FStar_Parser_AST.msource)
in (
# 1442 "FStar.Parser.ToSyntax.fst"
let dst = (lookup l.FStar_Parser_AST.mdest)
in (
# 1443 "FStar.Parser.ToSyntax.fst"
let lift = (let _132_939 = (desugar_term env l.FStar_Parser_AST.lift_op)
in ([], _132_939))
in (
# 1444 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect (({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift = lift}, d.FStar_Parser_AST.drange))
in (env, (se)::[]))))))
end))

# 1447 "FStar.Parser.ToSyntax.fst"
let desugar_decls : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _51_2557 d -> (match (_51_2557) with
| (env, sigelts) -> begin
(
# 1449 "FStar.Parser.ToSyntax.fst"
let _51_2561 = (desugar_decl env d)
in (match (_51_2561) with
| (env, se) -> begin
(env, (FStar_List.append sigelts se))
end))
end)) (env, []) decls))

# 1452 "FStar.Parser.ToSyntax.fst"
let open_prims_all : FStar_Parser_AST.decl Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.all_lid)) FStar_Range.dummyRange))::[]

# 1459 "FStar.Parser.ToSyntax.fst"
let desugar_modul_common : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (
# 1460 "FStar.Parser.ToSyntax.fst"
let open_ns = (fun mname d -> (
# 1461 "FStar.Parser.ToSyntax.fst"
let d = if ((FStar_List.length mname.FStar_Ident.ns) <> 0) then begin
(let _132_958 = (let _132_957 = (let _132_956 = (FStar_Ident.lid_of_ids mname.FStar_Ident.ns)
in FStar_Parser_AST.Open (_132_956))
in (FStar_Parser_AST.mk_decl _132_957 (FStar_Ident.range_of_lid mname)))
in (_132_958)::d)
end else begin
d
end
in d))
in (
# 1465 "FStar.Parser.ToSyntax.fst"
let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod) -> begin
(FStar_Parser_Env.finish_module_or_interface env prev_mod)
end)
in (
# 1468 "FStar.Parser.ToSyntax.fst"
let _51_2588 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _132_960 = (FStar_Parser_Env.prepare_module_or_interface true admitted env mname)
in (let _132_959 = (open_ns mname decls)
in (_132_960, mname, _132_959, true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _132_962 = (FStar_Parser_Env.prepare_module_or_interface false false env mname)
in (let _132_961 = (open_ns mname decls)
in (_132_962, mname, _132_961, false)))
end)
in (match (_51_2588) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(
# 1473 "FStar.Parser.ToSyntax.fst"
let _51_2591 = (desugar_decls env decls)
in (match (_51_2591) with
| (env, sigelts) -> begin
(
# 1474 "FStar.Parser.ToSyntax.fst"
let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in (env, modul, pop_when_done))
end))
end)))))

# 1482 "FStar.Parser.ToSyntax.fst"
let desugar_partial_modul : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (
# 1483 "FStar.Parser.ToSyntax.fst"
let m = if (FStar_ST.read FStar_Options.interactive_fsi) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface ((mname, decls, true))
end
| FStar_Parser_AST.Interface (mname, _51_2602, _51_2604) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (
# 1490 "FStar.Parser.ToSyntax.fst"
let _51_2612 = (desugar_modul_common curmod env m)
in (match (_51_2612) with
| (x, y, _51_2611) -> begin
(x, y)
end))))

# 1493 "FStar.Parser.ToSyntax.fst"
let desugar_modul : FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (
# 1494 "FStar.Parser.ToSyntax.fst"
let _51_2618 = (desugar_modul_common None env m)
in (match (_51_2618) with
| (env, modul, pop_when_done) -> begin
(
# 1495 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.finish_module_or_interface env modul)
in (
# 1496 "FStar.Parser.ToSyntax.fst"
let _51_2620 = if (FStar_Options.should_dump modul.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _132_973 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _132_973))
end else begin
()
end
in (let _132_974 = if pop_when_done then begin
(FStar_Parser_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end else begin
env
end
in (_132_974, modul))))
end)))

# 1500 "FStar.Parser.ToSyntax.fst"
let desugar_file : FStar_Parser_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (
# 1501 "FStar.Parser.ToSyntax.fst"
let _51_2633 = (FStar_List.fold_left (fun _51_2626 m -> (match (_51_2626) with
| (env, mods) -> begin
(
# 1502 "FStar.Parser.ToSyntax.fst"
let _51_2630 = (desugar_modul env m)
in (match (_51_2630) with
| (env, m) -> begin
(env, (m)::mods)
end))
end)) (env, []) f)
in (match (_51_2633) with
| (env, mods) -> begin
(env, (FStar_List.rev mods))
end)))

# 1506 "FStar.Parser.ToSyntax.fst"
let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Parser_Env.env  ->  FStar_Parser_Env.env = (fun m en -> (
# 1507 "FStar.Parser.ToSyntax.fst"
let _51_2638 = (FStar_Parser_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (_51_2638) with
| (en, pop_when_done) -> begin
(
# 1508 "FStar.Parser.ToSyntax.fst"
let en = (FStar_List.fold_left FStar_Parser_Env.push_sigelt (
# 1508 "FStar.Parser.ToSyntax.fst"
let _51_2639 = en
in {FStar_Parser_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_Parser_Env.modules = _51_2639.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _51_2639.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.sigaccum = _51_2639.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _51_2639.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _51_2639.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _51_2639.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _51_2639.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _51_2639.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _51_2639.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = _51_2639.FStar_Parser_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (
# 1509 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_Env.export_interface m.FStar_Syntax_Syntax.name env)
end else begin
env
end))
end)))




