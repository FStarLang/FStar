
open Prims
# 38 "FStar.Parser.ToSyntax.fst"
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

# 43 "FStar.Parser.ToSyntax.fst"
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

# 57 "FStar.Parser.ToSyntax.fst"
let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun _46_3 -> (match (_46_3) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end))

# 61 "FStar.Parser.ToSyntax.fst"
let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _46_4 -> (match (_46_4) with
| (FStar_Parser_AST.Hash) | (FStar_Parser_AST.FsTypApp) -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| _46_51 -> begin
None
end))

# 66 "FStar.Parser.ToSyntax.fst"
let arg_withimp_e = (fun imp t -> (t, (as_imp imp)))

# 68 "FStar.Parser.ToSyntax.fst"
let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
(t, Some (FStar_Syntax_Syntax.imp_tag))
end
| _46_58 -> begin
(t, None)
end))

# 72 "FStar.Parser.ToSyntax.fst"
let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_46_62) -> begin
true
end
| _46_65 -> begin
false
end)))))

# 77 "FStar.Parser.ToSyntax.fst"
let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _46_70 -> begin
t
end))

# 81 "FStar.Parser.ToSyntax.fst"
let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _125_21 = (let _125_20 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_125_20))
in (FStar_Parser_AST.mk_term _125_21 r FStar_Parser_AST.Kind)))

# 83 "FStar.Parser.ToSyntax.fst"
let rec delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (
# 86 "FStar.Parser.ToSyntax.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_46_75) -> begin
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

# 104 "FStar.Parser.ToSyntax.fst"
let incr_delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (
# 107 "FStar.Parser.ToSyntax.fst"
let d = (delta_qualifier t)
in (
# 108 "FStar.Parser.ToSyntax.fst"
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

# 113 "FStar.Parser.ToSyntax.fst"
let compile_op : Prims.int  ->  Prims.string  ->  Prims.string = (fun arity s -> (
# 116 "FStar.Parser.ToSyntax.fst"
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
| _46_170 -> begin
"UNKNOWN"
end))
in (
# 135 "FStar.Parser.ToSyntax.fst"
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

# 139 "FStar.Parser.ToSyntax.fst"
let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _125_53 = (let _125_52 = (let _125_51 = (let _125_50 = (compile_op n s)
in (_125_50, r))
in (FStar_Ident.mk_ident _125_51))
in (_125_52)::[])
in (FStar_All.pipe_right _125_53 FStar_Ident.lid_of_ids)))

# 141 "FStar.Parser.ToSyntax.fst"
let op_as_term : FStar_Parser_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.term Prims.option = (fun env arity rng s -> (
# 144 "FStar.Parser.ToSyntax.fst"
let r = (fun l dd -> (let _125_68 = (let _125_67 = (let _125_66 = (FStar_Ident.set_lid_range l rng)
in (FStar_Syntax_Syntax.lid_as_fv _125_66 dd None))
in (FStar_All.pipe_right _125_67 FStar_Syntax_Syntax.fv_to_tm))
in Some (_125_68)))
in (
# 145 "FStar.Parser.ToSyntax.fst"
let fallback = (fun _46_185 -> (match (()) with
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
| _46_213 -> begin
None
end)
end))
in (match ((let _125_71 = (compile_op_lid arity s rng)
in (FStar_Parser_Env.try_lookup_lid env _125_71))) with
| Some (t) -> begin
Some (t)
end
| _46_217 -> begin
(fallback ())
end))))

# 177 "FStar.Parser.ToSyntax.fst"
let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _125_78 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _125_78)))

# 181 "FStar.Parser.ToSyntax.fst"
let rec free_type_vars_b : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_46_226) -> begin
(env, [])
end
| FStar_Parser_AST.TVariable (x) -> begin
(
# 186 "FStar.Parser.ToSyntax.fst"
let _46_233 = (FStar_Parser_Env.push_bv env x)
in (match (_46_233) with
| (env, _46_232) -> begin
(env, (x)::[])
end))
end
| FStar_Parser_AST.Annotated (_46_235, term) -> begin
(let _125_85 = (free_type_vars env term)
in (env, _125_85))
end
| FStar_Parser_AST.TAnnotated (id, _46_241) -> begin
(
# 191 "FStar.Parser.ToSyntax.fst"
let _46_247 = (FStar_Parser_Env.push_bv env id)
in (match (_46_247) with
| (env, _46_246) -> begin
(env, [])
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _125_86 = (free_type_vars env t)
in (env, _125_86))
end))
and free_type_vars : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _125_89 = (unparen t)
in _125_89.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (_46_253) -> begin
(FStar_All.failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_Env.try_lookup_id env a)) with
| None -> begin
(a)::[]
end
| _46_259 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_46_289, ts) -> begin
(FStar_List.collect (fun _46_296 -> (match (_46_296) with
| (t, _46_295) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_46_298, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _46_305) -> begin
(let _125_92 = (free_type_vars env t1)
in (let _125_91 = (free_type_vars env t2)
in (FStar_List.append _125_92 _125_91)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(
# 221 "FStar.Parser.ToSyntax.fst"
let _46_314 = (free_type_vars_b env b)
in (match (_46_314) with
| (env, f) -> begin
(let _125_93 = (free_type_vars env t)
in (FStar_List.append f _125_93))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(
# 226 "FStar.Parser.ToSyntax.fst"
let _46_330 = (FStar_List.fold_left (fun _46_323 binder -> (match (_46_323) with
| (env, free) -> begin
(
# 227 "FStar.Parser.ToSyntax.fst"
let _46_327 = (free_type_vars_b env binder)
in (match (_46_327) with
| (env, f) -> begin
(env, (FStar_List.append f free))
end))
end)) (env, []) binders)
in (match (_46_330) with
| (env, free) -> begin
(let _125_96 = (free_type_vars env body)
in (FStar_List.append free _125_96))
end))
end
| FStar_Parser_AST.Project (t, _46_333) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
[]
end))

# 242 "FStar.Parser.ToSyntax.fst"
let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (
# 245 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun args t -> (match ((let _125_103 = (unparen t)
in _125_103.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _46_377 -> begin
(t, args)
end))
in (aux [] t)))

# 249 "FStar.Parser.ToSyntax.fst"
let close : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 252 "FStar.Parser.ToSyntax.fst"
let ftv = (let _125_108 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _125_108))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 255 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _125_112 = (let _125_111 = (let _125_110 = (tm_type x.FStar_Ident.idRange)
in (x, _125_110))
in FStar_Parser_AST.TAnnotated (_125_111))
in (FStar_Parser_AST.mk_binder _125_112 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 256 "FStar.Parser.ToSyntax.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))

# 257 "FStar.Parser.ToSyntax.fst"
let close_fun : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 260 "FStar.Parser.ToSyntax.fst"
let ftv = (let _125_117 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _125_117))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 263 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _125_121 = (let _125_120 = (let _125_119 = (tm_type x.FStar_Ident.idRange)
in (x, _125_119))
in FStar_Parser_AST.TAnnotated (_125_120))
in (FStar_Parser_AST.mk_binder _125_121 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 264 "FStar.Parser.ToSyntax.fst"
let t = (match ((let _125_122 = (unparen t)
in _125_122.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_46_390) -> begin
t
end
| _46_393 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level), t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end)
in (
# 267 "FStar.Parser.ToSyntax.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result)))
end))

# 268 "FStar.Parser.ToSyntax.fst"
let rec uncurry : FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term) = (fun bs t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (binders, t) -> begin
(uncurry (FStar_List.append bs binders) t)
end
| _46_403 -> begin
(bs, t)
end))

# 272 "FStar.Parser.ToSyntax.fst"
let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _46_407) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_46_413); FStar_Parser_AST.prange = _46_411}, _46_417) -> begin
true
end
| _46_421 -> begin
false
end))

# 277 "FStar.Parser.ToSyntax.fst"
let rec destruct_app_pattern : FStar_Parser_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 281 "FStar.Parser.ToSyntax.fst"
let _46_433 = (destruct_app_pattern env is_top_level p)
in (match (_46_433) with
| (name, args, _46_432) -> begin
(name, args, Some (t))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _46_438); FStar_Parser_AST.prange = _46_435}, args) when is_top_level -> begin
(let _125_136 = (let _125_135 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_125_135))
in (_125_136, args, None))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _46_449); FStar_Parser_AST.prange = _46_446}, args) -> begin
(FStar_Util.Inl (id), args, None)
end
| _46_457 -> begin
(FStar_All.failwith "Not an app pattern")
end))

# 288 "FStar.Parser.ToSyntax.fst"
type bnd =
| LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * FStar_Syntax_Syntax.term)

# 291 "FStar.Parser.ToSyntax.fst"
let is_LocalBinder = (fun _discr_ -> (match (_discr_) with
| LocalBinder (_) -> begin
true
end
| _ -> begin
false
end))

# 292 "FStar.Parser.ToSyntax.fst"
let is_LetBinder = (fun _discr_ -> (match (_discr_) with
| LetBinder (_) -> begin
true
end
| _ -> begin
false
end))

# 291 "FStar.Parser.ToSyntax.fst"
let ___LocalBinder____0 = (fun projectee -> (match (projectee) with
| LocalBinder (_46_460) -> begin
_46_460
end))

# 292 "FStar.Parser.ToSyntax.fst"
let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_46_463) -> begin
_46_463
end))

# 292 "FStar.Parser.ToSyntax.fst"
let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun _46_6 -> (match (_46_6) with
| LocalBinder (a, aq) -> begin
(a, aq)
end
| _46_470 -> begin
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
# 299 "FStar.Parser.ToSyntax.fst"
let _46_483 = (FStar_Parser_Env.push_bv env a)
in (match (_46_483) with
| (env, a) -> begin
(((
# 300 "FStar.Parser.ToSyntax.fst"
let _46_484 = a
in {FStar_Syntax_Syntax.ppname = _46_484.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _46_484.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}), (trans_aqual imp)), env)
end))
end))

# 300 "FStar.Parser.ToSyntax.fst"
type env_t =
FStar_Parser_Env.env

# 302 "FStar.Parser.ToSyntax.fst"
type lenv_t =
FStar_Syntax_Syntax.bv Prims.list

# 303 "FStar.Parser.ToSyntax.fst"
let mk_lb : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.letbinding = (fun _46_489 -> (match (_46_489) with
| (n, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))

# 305 "FStar.Parser.ToSyntax.fst"
let no_annot_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t None))

# 306 "FStar.Parser.ToSyntax.fst"
let rec desugar_data_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat) = (fun env p -> (
# 309 "FStar.Parser.ToSyntax.fst"
let check_linear_pattern_variables = (fun p -> (
# 310 "FStar.Parser.ToSyntax.fst"
let rec pat_vars = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_dot_term (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_constant (_)) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (_46_510, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out _46_518 -> (match (_46_518) with
| (p, _46_517) -> begin
(let _125_219 = (pat_vars p)
in (FStar_Util.set_union out _125_219))
end)) FStar_Syntax_Syntax.no_names))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj (hd::tl) -> begin
(
# 319 "FStar.Parser.ToSyntax.fst"
let xs = (pat_vars hd)
in if (not ((FStar_Util.for_all (fun p -> (
# 320 "FStar.Parser.ToSyntax.fst"
let ys = (pat_vars p)
in ((FStar_Util.set_is_subset_of xs ys) && (FStar_Util.set_is_subset_of ys xs)))) tl))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Disjunctive pattern binds different variables in each case", p.FStar_Syntax_Syntax.p))))
end else begin
xs
end)
end))
in (pat_vars p)))
in (
# 327 "FStar.Parser.ToSyntax.fst"
let resolvex = (fun l e x -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText))))) with
| Some (y) -> begin
(l, e, y)
end
| _46_536 -> begin
(
# 331 "FStar.Parser.ToSyntax.fst"
let _46_539 = (FStar_Parser_Env.push_bv e x)
in (match (_46_539) with
| (e, x) -> begin
((x)::l, e, x)
end))
end))
in (
# 333 "FStar.Parser.ToSyntax.fst"
let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun b -> (b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText))))) with
| Some (b) -> begin
(l, e, b)
end
| _46_548 -> begin
(
# 337 "FStar.Parser.ToSyntax.fst"
let _46_551 = (FStar_Parser_Env.push_bv e a)
in (match (_46_551) with
| (e, a) -> begin
((a)::l, e, a)
end))
end))
in (
# 339 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun loc env p -> (
# 340 "FStar.Parser.ToSyntax.fst"
let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Parser_AST.prange))
in (
# 341 "FStar.Parser.ToSyntax.fst"
let pos_r = (fun r q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r))
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.PatOr (p::ps) -> begin
(
# 345 "FStar.Parser.ToSyntax.fst"
let _46_573 = (aux loc env p)
in (match (_46_573) with
| (loc, env, var, p, _46_572) -> begin
(
# 346 "FStar.Parser.ToSyntax.fst"
let _46_590 = (FStar_List.fold_left (fun _46_577 p -> (match (_46_577) with
| (loc, env, ps) -> begin
(
# 347 "FStar.Parser.ToSyntax.fst"
let _46_586 = (aux loc env p)
in (match (_46_586) with
| (loc, env, _46_582, p, _46_585) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_46_590) with
| (loc, env, ps) -> begin
(
# 349 "FStar.Parser.ToSyntax.fst"
let pat = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in (loc, env, var, pat, false))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 353 "FStar.Parser.ToSyntax.fst"
let _46_601 = (aux loc env p)
in (match (_46_601) with
| (loc, env', binder, p, imp) -> begin
(
# 354 "FStar.Parser.ToSyntax.fst"
let binder = (match (binder) with
| LetBinder (_46_603) -> begin
(FStar_All.failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(
# 357 "FStar.Parser.ToSyntax.fst"
let t = (let _125_249 = (close_fun env t)
in (desugar_term env _125_249))
in LocalBinder (((
# 358 "FStar.Parser.ToSyntax.fst"
let _46_610 = x
in {FStar_Syntax_Syntax.ppname = _46_610.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _46_610.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), aq)))
end)
in (loc, env', binder, p, imp))
end))
end
| FStar_Parser_AST.PatWild -> begin
(
# 362 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _125_250 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in (loc, env, LocalBinder ((x, None)), _125_250, false)))
end
| FStar_Parser_AST.PatConst (c) -> begin
(
# 366 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _125_251 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in (loc, env, LocalBinder ((x, None)), _125_251, false)))
end
| (FStar_Parser_AST.PatTvar (x, aq)) | (FStar_Parser_AST.PatVar (x, aq)) -> begin
(
# 371 "FStar.Parser.ToSyntax.fst"
let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (
# 372 "FStar.Parser.ToSyntax.fst"
let aq = (trans_aqual aq)
in (
# 373 "FStar.Parser.ToSyntax.fst"
let _46_629 = (resolvex loc env x)
in (match (_46_629) with
| (loc, env, xbv) -> begin
(let _125_252 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in (loc, env, LocalBinder ((xbv, aq)), _125_252, imp))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(
# 377 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_datacon env) l)
in (
# 378 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _125_253 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, []))))
in (loc, env, LocalBinder ((x, None)), _125_253, false))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _46_635}, args) -> begin
(
# 382 "FStar.Parser.ToSyntax.fst"
let _46_657 = (FStar_List.fold_right (fun arg _46_646 -> (match (_46_646) with
| (loc, env, args) -> begin
(
# 383 "FStar.Parser.ToSyntax.fst"
let _46_653 = (aux loc env arg)
in (match (_46_653) with
| (loc, env, _46_650, arg, imp) -> begin
(loc, env, ((arg, imp))::args)
end))
end)) args (loc, env, []))
in (match (_46_657) with
| (loc, env, args) -> begin
(
# 385 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_datacon env) l)
in (
# 386 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _125_256 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _125_256, false))))
end))
end
| FStar_Parser_AST.PatApp (_46_661) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(
# 392 "FStar.Parser.ToSyntax.fst"
let _46_681 = (FStar_List.fold_right (fun pat _46_669 -> (match (_46_669) with
| (loc, env, pats) -> begin
(
# 393 "FStar.Parser.ToSyntax.fst"
let _46_677 = (aux loc env pat)
in (match (_46_677) with
| (loc, env, _46_673, pat, _46_676) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_46_681) with
| (loc, env, pats) -> begin
(
# 395 "FStar.Parser.ToSyntax.fst"
let pat = (let _125_269 = (let _125_268 = (let _125_264 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _125_264))
in (let _125_267 = (let _125_266 = (let _125_265 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_125_265, []))
in FStar_Syntax_Syntax.Pat_cons (_125_266))
in (FStar_All.pipe_left _125_268 _125_267)))
in (FStar_List.fold_right (fun hd tl -> (
# 396 "FStar.Parser.ToSyntax.fst"
let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (let _125_263 = (let _125_262 = (let _125_261 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_125_261, ((hd, false))::((tl, false))::[]))
in FStar_Syntax_Syntax.Pat_cons (_125_262))
in (FStar_All.pipe_left (pos_r r) _125_263)))) pats _125_269))
in (
# 399 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (loc, env, LocalBinder ((x, None)), pat, false)))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(
# 403 "FStar.Parser.ToSyntax.fst"
let _46_707 = (FStar_List.fold_left (fun _46_694 p -> (match (_46_694) with
| (loc, env, pats) -> begin
(
# 404 "FStar.Parser.ToSyntax.fst"
let _46_703 = (aux loc env p)
in (match (_46_703) with
| (loc, env, _46_699, pat, _46_702) -> begin
(loc, env, ((pat, false))::pats)
end))
end)) (loc, env, []) args)
in (match (_46_707) with
| (loc, env, args) -> begin
(
# 406 "FStar.Parser.ToSyntax.fst"
let args = (FStar_List.rev args)
in (
# 407 "FStar.Parser.ToSyntax.fst"
let l = if dep then begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end else begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end
in (
# 409 "FStar.Parser.ToSyntax.fst"
let constr = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (
# 410 "FStar.Parser.ToSyntax.fst"
let l = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| _46_714 -> begin
(FStar_All.failwith "impossible")
end)
in (
# 413 "FStar.Parser.ToSyntax.fst"
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
# 420 "FStar.Parser.ToSyntax.fst"
let _46_724 = (FStar_List.hd fields)
in (match (_46_724) with
| (f, _46_723) -> begin
(
# 421 "FStar.Parser.ToSyntax.fst"
let _46_728 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_46_728) with
| (record, _46_727) -> begin
(
# 422 "FStar.Parser.ToSyntax.fst"
let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _46_731 -> (match (_46_731) with
| (f, p) -> begin
(let _125_274 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.qualify_field_to_record env record) f)
in (_125_274, p))
end))))
in (
# 424 "FStar.Parser.ToSyntax.fst"
let args = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _46_736 -> (match (_46_736) with
| (f, _46_735) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _46_740 -> (match (_46_740) with
| (g, _46_739) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_46_743, p) -> begin
p
end)
end))))
in (
# 428 "FStar.Parser.ToSyntax.fst"
let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_Env.constrname)) p.FStar_Parser_AST.prange), args))) p.FStar_Parser_AST.prange)
in (
# 429 "FStar.Parser.ToSyntax.fst"
let _46_755 = (aux loc env app)
in (match (_46_755) with
| (env, e, b, p, _46_754) -> begin
(
# 430 "FStar.Parser.ToSyntax.fst"
let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(let _125_283 = (let _125_282 = (let _125_281 = (
# 431 "FStar.Parser.ToSyntax.fst"
let _46_760 = fv
in (let _125_280 = (let _125_279 = (let _125_278 = (let _125_277 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _125_277))
in FStar_Syntax_Syntax.Record_ctor (_125_278))
in Some (_125_279))
in {FStar_Syntax_Syntax.fv_name = _46_760.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = _46_760.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _125_280}))
in (_125_281, args))
in FStar_Syntax_Syntax.Pat_cons (_125_282))
in (FStar_All.pipe_left pos _125_283))
end
| _46_763 -> begin
p
end)
in (env, e, b, p, false))
end)))))
end))
end))
end))))
in (
# 435 "FStar.Parser.ToSyntax.fst"
let _46_772 = (aux [] env p)
in (match (_46_772) with
| (_46_766, env, b, p, _46_771) -> begin
(
# 436 "FStar.Parser.ToSyntax.fst"
let _46_773 = (let _125_284 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore _125_284))
in (env, b, p))
end)))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _46_780) -> begin
(let _125_290 = (let _125_289 = (let _125_288 = (FStar_Parser_Env.qualify env x)
in (_125_288, FStar_Syntax_Syntax.tun))
in LetBinder (_125_289))
in (env, _125_290, None))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _46_787); FStar_Parser_AST.prange = _46_784}, t) -> begin
(let _125_294 = (let _125_293 = (let _125_292 = (FStar_Parser_Env.qualify env x)
in (let _125_291 = (desugar_term env t)
in (_125_292, _125_291)))
in LetBinder (_125_293))
in (env, _125_294, None))
end
| _46_795 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern at the top-level", p.FStar_Parser_AST.prange))))
end)
end else begin
(
# 447 "FStar.Parser.ToSyntax.fst"
let _46_799 = (desugar_data_pat env p)
in (match (_46_799) with
| (env, binder, p) -> begin
(
# 448 "FStar.Parser.ToSyntax.fst"
let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| _46_807 -> begin
Some (p)
end)
in (env, binder, p))
end))
end)
and desugar_binding_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun _46_811 env pat -> (
# 457 "FStar.Parser.ToSyntax.fst"
let _46_819 = (desugar_data_pat env pat)
in (match (_46_819) with
| (env, _46_817, pat) -> begin
(env, pat)
end)))
and desugar_match_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (
# 463 "FStar.Parser.ToSyntax.fst"
let env = (
# 463 "FStar.Parser.ToSyntax.fst"
let _46_824 = env
in {FStar_Parser_Env.curmodule = _46_824.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _46_824.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _46_824.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.sigaccum = _46_824.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _46_824.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _46_824.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _46_824.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _46_824.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _46_824.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _46_824.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (
# 467 "FStar.Parser.ToSyntax.fst"
let env = (
# 467 "FStar.Parser.ToSyntax.fst"
let _46_829 = env
in {FStar_Parser_Env.curmodule = _46_829.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _46_829.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _46_829.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.sigaccum = _46_829.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _46_829.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _46_829.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _46_829.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _46_829.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _46_829.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _46_829.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (
# 471 "FStar.Parser.ToSyntax.fst"
let mk = (fun e -> (FStar_Syntax_Syntax.mk e None top.FStar_Parser_AST.range))
in (
# 472 "FStar.Parser.ToSyntax.fst"
let setpos = (fun e -> (
# 472 "FStar.Parser.ToSyntax.fst"
let _46_839 = e
in {FStar_Syntax_Syntax.n = _46_839.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _46_839.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _46_839.FStar_Syntax_Syntax.vars}))
in (match ((let _125_313 = (unparen top)
in _125_313.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (_46_843) -> begin
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
| FStar_Parser_AST.Op ("*", _46_863::_46_861::[]) when (let _125_314 = (op_as_term env 2 top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right _125_314 FStar_Option.isNone)) -> begin
(
# 490 "FStar.Parser.ToSyntax.fst"
let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", t1::t2::[]) -> begin
(
# 492 "FStar.Parser.ToSyntax.fst"
let rest = (flatten t2)
in (t1)::rest)
end
| _46_877 -> begin
(t)::[]
end))
in (
# 495 "FStar.Parser.ToSyntax.fst"
let targs = (let _125_320 = (let _125_317 = (unparen top)
in (flatten _125_317))
in (FStar_All.pipe_right _125_320 (FStar_List.map (fun t -> (let _125_319 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg _125_319))))))
in (
# 496 "FStar.Parser.ToSyntax.fst"
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
# 506 "FStar.Parser.ToSyntax.fst"
let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _125_324 = (desugar_term env t)
in (_125_324, None)))))
in (mk (FStar_Syntax_Syntax.Tm_app ((op, args)))))
end)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _46_898; FStar_Ident.ident = _46_896; FStar_Ident.nsstr = _46_894; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _46_907; FStar_Ident.ident = _46_905; FStar_Ident.nsstr = _46_903; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _46_916; FStar_Ident.ident = _46_914; FStar_Ident.nsstr = _46_912; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _46_925; FStar_Ident.ident = _46_923; FStar_Ident.nsstr = _46_921; FStar_Ident.str = "True"}) -> begin
(let _125_325 = (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _125_325 FStar_Syntax_Syntax.Delta_constant None))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _46_934; FStar_Ident.ident = _46_932; FStar_Ident.nsstr = _46_930; FStar_Ident.str = "False"}) -> begin
(let _125_326 = (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _125_326 FStar_Syntax_Syntax.Delta_constant None))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(let _125_327 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (FStar_All.pipe_left setpos _125_327))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(
# 521 "FStar.Parser.ToSyntax.fst"
let _46_949 = (match ((FStar_Parser_Env.try_lookup_datacon env l)) with
| None -> begin
(let _125_328 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (_125_328, false))
end
| Some (head) -> begin
(let _125_329 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in (_125_329, true))
end)
in (match (_46_949) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| _46_952 -> begin
(
# 527 "FStar.Parser.ToSyntax.fst"
let args = (FStar_List.map (fun _46_955 -> (match (_46_955) with
| (t, imp) -> begin
(
# 528 "FStar.Parser.ToSyntax.fst"
let te = (desugar_term env t)
in (arg_withimp_e imp te))
end)) args)
in (
# 530 "FStar.Parser.ToSyntax.fst"
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
# 537 "FStar.Parser.ToSyntax.fst"
let _46_983 = (FStar_List.fold_left (fun _46_966 b -> (match (_46_966) with
| (env, tparams, typs) -> begin
(
# 538 "FStar.Parser.ToSyntax.fst"
let _46_970 = (desugar_binder env b)
in (match (_46_970) with
| (xopt, t) -> begin
(
# 539 "FStar.Parser.ToSyntax.fst"
let _46_976 = (match (xopt) with
| None -> begin
(let _125_333 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (env, _125_333))
end
| Some (x) -> begin
(FStar_Parser_Env.push_bv env x)
end)
in (match (_46_976) with
| (env, x) -> begin
(let _125_337 = (let _125_336 = (let _125_335 = (let _125_334 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _125_334))
in (_125_335)::[])
in (FStar_List.append typs _125_336))
in (env, (FStar_List.append tparams ((((
# 543 "FStar.Parser.ToSyntax.fst"
let _46_977 = x
in {FStar_Syntax_Syntax.ppname = _46_977.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _46_977.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), None))::[])), _125_337))
end))
end))
end)) (env, [], []) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_46_983) with
| (env, _46_981, targs) -> begin
(
# 546 "FStar.Parser.ToSyntax.fst"
let tup = (let _125_338 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) _125_338))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app ((tup, targs)))))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(
# 550 "FStar.Parser.ToSyntax.fst"
let _46_991 = (uncurry binders t)
in (match (_46_991) with
| (bs, t) -> begin
(
# 551 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun env bs _46_8 -> (match (_46_8) with
| [] -> begin
(
# 553 "FStar.Parser.ToSyntax.fst"
let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (let _125_345 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos _125_345)))
end
| hd::tl -> begin
(
# 557 "FStar.Parser.ToSyntax.fst"
let mlenv = (FStar_Parser_Env.default_ml env)
in (
# 558 "FStar.Parser.ToSyntax.fst"
let bb = (desugar_binder mlenv hd)
in (
# 559 "FStar.Parser.ToSyntax.fst"
let _46_1005 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_46_1005) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_binder env b)) with
| (None, _46_1012) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(
# 568 "FStar.Parser.ToSyntax.fst"
let _46_1020 = (as_binder env None b)
in (match (_46_1020) with
| ((x, _46_1017), env) -> begin
(
# 569 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env f)
in (let _125_346 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos _125_346)))
end))
end)
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(
# 574 "FStar.Parser.ToSyntax.fst"
let _46_1040 = (FStar_List.fold_left (fun _46_1028 pat -> (match (_46_1028) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (_46_1031, t) -> begin
(let _125_350 = (let _125_349 = (free_type_vars env t)
in (FStar_List.append _125_349 ftvs))
in (env, _125_350))
end
| _46_1036 -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_46_1040) with
| (_46_1038, ftv) -> begin
(
# 578 "FStar.Parser.ToSyntax.fst"
let ftv = (sort_ftv ftv)
in (
# 579 "FStar.Parser.ToSyntax.fst"
let binders = (let _125_352 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar ((a, Some (FStar_Parser_AST.Implicit)))) top.FStar_Parser_AST.range))))
in (FStar_List.append _125_352 binders))
in (
# 588 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun env bs sc_pat_opt _46_9 -> (match (_46_9) with
| [] -> begin
(
# 590 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env body)
in (
# 591 "FStar.Parser.ToSyntax.fst"
let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(
# 593 "FStar.Parser.ToSyntax.fst"
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
# 599 "FStar.Parser.ToSyntax.fst"
let _46_1064 = (desugar_binding_pat env p)
in (match (_46_1064) with
| (env, b, pat) -> begin
(
# 600 "FStar.Parser.ToSyntax.fst"
let _46_1115 = (match (b) with
| LetBinder (_46_1066) -> begin
(FStar_All.failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(
# 603 "FStar.Parser.ToSyntax.fst"
let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _46_1074) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _125_365 = (let _125_364 = (FStar_Syntax_Syntax.bv_to_name x)
in (_125_364, p))
in Some (_125_365))
end
| (Some (p), Some (sc, p')) -> begin
(match ((sc.FStar_Syntax_Syntax.n, p'.FStar_Syntax_Syntax.v)) with
| (FStar_Syntax_Syntax.Tm_name (_46_1088), _46_1091) -> begin
(
# 609 "FStar.Parser.ToSyntax.fst"
let tup2 = (let _125_366 = (FStar_Syntax_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _125_366 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (
# 610 "FStar.Parser.ToSyntax.fst"
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
# 611 "FStar.Parser.ToSyntax.fst"
let p = (let _125_375 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tup2, ((p', false))::((p, false))::[]))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _125_375))
in Some ((sc, p)))))
end
| (FStar_Syntax_Syntax.Tm_app (_46_1097, args), FStar_Syntax_Syntax.Pat_cons (_46_1102, pats)) -> begin
(
# 614 "FStar.Parser.ToSyntax.fst"
let tupn = (let _125_376 = (FStar_Syntax_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _125_376 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (
# 615 "FStar.Parser.ToSyntax.fst"
let sc = (let _125_383 = (let _125_382 = (let _125_381 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (let _125_380 = (let _125_379 = (let _125_378 = (let _125_377 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _125_377))
in (_125_378)::[])
in (FStar_List.append args _125_379))
in (_125_381, _125_380)))
in FStar_Syntax_Syntax.Tm_app (_125_382))
in (mk _125_383))
in (
# 616 "FStar.Parser.ToSyntax.fst"
let p = (let _125_384 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tupn, (FStar_List.append pats (((p, false))::[]))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _125_384))
in Some ((sc, p)))))
end
| _46_1111 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((x, aq), sc_pat_opt))
end)
in (match (_46_1115) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _46_1119; FStar_Parser_AST.level = _46_1117}, phi, _46_1125) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(
# 627 "FStar.Parser.ToSyntax.fst"
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
| FStar_Parser_AST.App (_46_1130) -> begin
(
# 633 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun args e -> (match ((let _125_397 = (unparen e)
in _125_397.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(
# 635 "FStar.Parser.ToSyntax.fst"
let arg = (let _125_398 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _125_398))
in (aux ((arg)::args) e))
end
| _46_1142 -> begin
(
# 638 "FStar.Parser.ToSyntax.fst"
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
# 647 "FStar.Parser.ToSyntax.fst"
let ds_let_rec_or_app = (fun _46_1158 -> (match (()) with
| () -> begin
(
# 648 "FStar.Parser.ToSyntax.fst"
let bindings = ((pat, _snd))::_tl
in (
# 649 "FStar.Parser.ToSyntax.fst"
let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _46_1162 -> (match (_46_1162) with
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
| _46_1168 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _46_1173); FStar_Parser_AST.prange = _46_1170}, t) -> begin
if top_level then begin
(let _125_409 = (let _125_408 = (let _125_407 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_125_407))
in (_125_408, [], Some (t)))
in (_125_409, def))
end else begin
((FStar_Util.Inl (id), [], Some (t)), def)
end
end
| FStar_Parser_AST.PatVar (id, _46_1182) -> begin
if top_level then begin
(let _125_412 = (let _125_411 = (let _125_410 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_125_410))
in (_125_411, [], None))
in (_125_412, def))
end else begin
((FStar_Util.Inl (id), [], None), def)
end
end
| _46_1186 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected let binding", p.FStar_Parser_AST.prange))))
end)
end)
end
end))))
in (
# 666 "FStar.Parser.ToSyntax.fst"
let _46_1215 = (FStar_List.fold_left (fun _46_1191 _46_1200 -> (match ((_46_1191, _46_1200)) with
| ((env, fnames, rec_bindings), ((f, _46_1194, _46_1196), _46_1199)) -> begin
(
# 668 "FStar.Parser.ToSyntax.fst"
let _46_1211 = (match (f) with
| FStar_Util.Inl (x) -> begin
(
# 670 "FStar.Parser.ToSyntax.fst"
let _46_1205 = (FStar_Parser_Env.push_bv env x)
in (match (_46_1205) with
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
in (match (_46_1211) with
| (env, lbname, rec_bindings) -> begin
(env, (lbname)::fnames, rec_bindings)
end))
end)) (env, [], []) funs)
in (match (_46_1215) with
| (env', fnames, rec_bindings) -> begin
(
# 676 "FStar.Parser.ToSyntax.fst"
let fnames = (FStar_List.rev fnames)
in (
# 678 "FStar.Parser.ToSyntax.fst"
let desugar_one_def = (fun env lbname _46_1226 -> (match (_46_1226) with
| ((_46_1221, args, result_t), def) -> begin
(
# 679 "FStar.Parser.ToSyntax.fst"
let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _125_424 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed ((def, t))) _125_424 FStar_Parser_AST.Expr))
end)
in (
# 682 "FStar.Parser.ToSyntax.fst"
let def = (match (args) with
| [] -> begin
def
end
| _46_1233 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.un_curry_abs args def) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
end)
in (
# 685 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env def)
in (
# 686 "FStar.Parser.ToSyntax.fst"
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
# 689 "FStar.Parser.ToSyntax.fst"
let body = if is_rec then begin
(FStar_Syntax_Subst.close rec_bindings body)
end else begin
body
end
in (mk_lb (lbname, FStar_Syntax_Syntax.tun, body)))))))
end))
in (
# 691 "FStar.Parser.ToSyntax.fst"
let lbs = (FStar_List.map2 (desugar_one_def (if is_rec then begin
env'
end else begin
env
end)) fnames funs)
in (
# 692 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env' body)
in (let _125_429 = (let _125_428 = (let _125_427 = (FStar_Syntax_Subst.close rec_bindings body)
in ((is_rec, lbs), _125_427))
in FStar_Syntax_Syntax.Tm_let (_125_428))
in (FStar_All.pipe_left mk _125_429))))))
end))))
end))
in (
# 696 "FStar.Parser.ToSyntax.fst"
let ds_non_rec = (fun pat t1 t2 -> (
# 697 "FStar.Parser.ToSyntax.fst"
let t1 = (desugar_term env t1)
in (
# 698 "FStar.Parser.ToSyntax.fst"
let _46_1252 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_46_1252) with
| (env, binder, pat) -> begin
(match (binder) with
| LetBinder (l, t) -> begin
(
# 701 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env t2)
in (
# 702 "FStar.Parser.ToSyntax.fst"
let fv = (let _125_436 = (incr_delta_qualifier t1)
in (FStar_Syntax_Syntax.lid_as_fv l _125_436 None))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]), body))))))
end
| LocalBinder (x, _46_1261) -> begin
(
# 706 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env t2)
in (
# 707 "FStar.Parser.ToSyntax.fst"
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
# 721 "FStar.Parser.ToSyntax.fst"
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
# 727 "FStar.Parser.ToSyntax.fst"
let r = top.FStar_Parser_AST.range
in (
# 728 "FStar.Parser.ToSyntax.fst"
let handler = (FStar_Parser_AST.mk_function branches r r)
in (
# 729 "FStar.Parser.ToSyntax.fst"
let body = (FStar_Parser_AST.mk_function ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatConst (FStar_Const.Const_unit)) r), None, e))::[]) r r)
in (
# 730 "FStar.Parser.ToSyntax.fst"
let a1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (FStar_Syntax_Const.try_with_lid)) r top.FStar_Parser_AST.level), body, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (
# 731 "FStar.Parser.ToSyntax.fst"
let a2 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((a1, handler, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (desugar_term env a2))))))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(
# 735 "FStar.Parser.ToSyntax.fst"
let desugar_branch = (fun _46_1301 -> (match (_46_1301) with
| (pat, wopt, b) -> begin
(
# 736 "FStar.Parser.ToSyntax.fst"
let _46_1304 = (desugar_match_pat env pat)
in (match (_46_1304) with
| (env, pat) -> begin
(
# 737 "FStar.Parser.ToSyntax.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _125_460 = (desugar_term env e)
in Some (_125_460))
end)
in (
# 740 "FStar.Parser.ToSyntax.fst"
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
# 745 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.default_ml env)
in (
# 746 "FStar.Parser.ToSyntax.fst"
let c = (desugar_comp t.FStar_Parser_AST.range true env t)
in (
# 747 "FStar.Parser.ToSyntax.fst"
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
| FStar_Parser_AST.Record (_46_1318, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected empty record", top.FStar_Parser_AST.range))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(
# 756 "FStar.Parser.ToSyntax.fst"
let _46_1329 = (FStar_List.hd fields)
in (match (_46_1329) with
| (f, _46_1328) -> begin
(
# 757 "FStar.Parser.ToSyntax.fst"
let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (
# 758 "FStar.Parser.ToSyntax.fst"
let _46_1335 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_46_1335) with
| (record, _46_1334) -> begin
(
# 759 "FStar.Parser.ToSyntax.fst"
let get_field = (fun xopt f -> (
# 760 "FStar.Parser.ToSyntax.fst"
let fn = f.FStar_Ident.ident
in (
# 761 "FStar.Parser.ToSyntax.fst"
let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _46_1343 -> (match (_46_1343) with
| (g, _46_1342) -> begin
(
# 762 "FStar.Parser.ToSyntax.fst"
let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_46_1347, e) -> begin
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
# 773 "FStar.Parser.ToSyntax.fst"
let recterm = (match (eopt) with
| None -> begin
(let _125_484 = (let _125_483 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _46_1359 -> (match (_46_1359) with
| (f, _46_1358) -> begin
(let _125_482 = (let _125_481 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _125_481))
in (_125_482, FStar_Parser_AST.Nothing))
end))))
in (record.FStar_Parser_Env.constrname, _125_483))
in FStar_Parser_AST.Construct (_125_484))
end
| Some (e) -> begin
(
# 780 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (
# 781 "FStar.Parser.ToSyntax.fst"
let xterm = (let _125_486 = (let _125_485 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_125_485))
in (FStar_Parser_AST.mk_term _125_486 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (
# 782 "FStar.Parser.ToSyntax.fst"
let record = (let _125_489 = (let _125_488 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _46_1367 -> (match (_46_1367) with
| (f, _46_1366) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _125_488))
in FStar_Parser_AST.Record (_125_489))
in FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar ((x, None))) x.FStar_Ident.idRange), e))::[], (FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level))))))
end)
in (
# 785 "FStar.Parser.ToSyntax.fst"
let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (
# 786 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _46_1383; FStar_Syntax_Syntax.pos = _46_1381; FStar_Syntax_Syntax.vars = _46_1379}, args); FStar_Syntax_Syntax.tk = _46_1377; FStar_Syntax_Syntax.pos = _46_1375; FStar_Syntax_Syntax.vars = _46_1373}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(
# 789 "FStar.Parser.ToSyntax.fst"
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
| _46_1397 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(
# 797 "FStar.Parser.ToSyntax.fst"
let _46_1404 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_projector_by_field_name env) f)
in (match (_46_1404) with
| (fieldname, is_rec) -> begin
(
# 798 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env e)
in (
# 799 "FStar.Parser.ToSyntax.fst"
let fn = (
# 800 "FStar.Parser.ToSyntax.fst"
let _46_1409 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_46_1409) with
| (ns, _46_1408) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (
# 802 "FStar.Parser.ToSyntax.fst"
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
| _46_1419 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _46_1421 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_args : FStar_Parser_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun _46_1426 -> (match (_46_1426) with
| (a, imp) -> begin
(let _125_507 = (desugar_term env a)
in (arg_withimp_e imp _125_507))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r default_ok env t -> (
# 819 "FStar.Parser.ToSyntax.fst"
let fail = (fun msg -> (Prims.raise (FStar_Syntax_Syntax.Error ((msg, r)))))
in (
# 820 "FStar.Parser.ToSyntax.fst"
let is_requires = (fun _46_1438 -> (match (_46_1438) with
| (t, _46_1437) -> begin
(match ((let _125_515 = (unparen t)
in _125_515.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Requires (_46_1440) -> begin
true
end
| _46_1443 -> begin
false
end)
end))
in (
# 823 "FStar.Parser.ToSyntax.fst"
let is_ensures = (fun _46_1448 -> (match (_46_1448) with
| (t, _46_1447) -> begin
(match ((let _125_518 = (unparen t)
in _125_518.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ensures (_46_1450) -> begin
true
end
| _46_1453 -> begin
false
end)
end))
in (
# 826 "FStar.Parser.ToSyntax.fst"
let is_app = (fun head _46_1459 -> (match (_46_1459) with
| (t, _46_1458) -> begin
(match ((let _125_523 = (unparen t)
in _125_523.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _46_1463; FStar_Parser_AST.level = _46_1461}, _46_1468, _46_1470) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| _46_1474 -> begin
false
end)
end))
in (
# 829 "FStar.Parser.ToSyntax.fst"
let pre_process_comp_typ = (fun t -> (
# 830 "FStar.Parser.ToSyntax.fst"
let _46_1479 = (head_and_args t)
in (match (_46_1479) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(
# 833 "FStar.Parser.ToSyntax.fst"
let unit_tm = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (
# 834 "FStar.Parser.ToSyntax.fst"
let nil_pat = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr), FStar_Parser_AST.Nothing)
in (
# 835 "FStar.Parser.ToSyntax.fst"
let args = (match (args) with
| [] -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Not enough arguments to \'Lemma\'", t.FStar_Parser_AST.range))))
end
| ens::[] -> begin
(
# 838 "FStar.Parser.ToSyntax.fst"
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
# 843 "FStar.Parser.ToSyntax.fst"
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
| _46_1507 when default_ok -> begin
(let _125_532 = (FStar_Ident.set_lid_range env.FStar_Parser_Env.default_result_effect head.FStar_Parser_AST.range)
in (_125_532, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _46_1509 -> begin
(let _125_534 = (let _125_533 = (FStar_Parser_AST.term_to_string t)
in (FStar_Util.format1 "%s is not an effect" _125_533))
in (fail _125_534))
end)
end)))
in (
# 873 "FStar.Parser.ToSyntax.fst"
let _46_1512 = (pre_process_comp_typ t)
in (match (_46_1512) with
| (eff, args) -> begin
(
# 874 "FStar.Parser.ToSyntax.fst"
let _46_1513 = if ((FStar_List.length args) = 0) then begin
(let _125_536 = (let _125_535 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" _125_535))
in (fail _125_536))
end else begin
()
end
in (
# 876 "FStar.Parser.ToSyntax.fst"
let _46_1517 = (let _125_538 = (FStar_List.hd args)
in (let _125_537 = (FStar_List.tl args)
in (_125_538, _125_537)))
in (match (_46_1517) with
| (result_arg, rest) -> begin
(
# 877 "FStar.Parser.ToSyntax.fst"
let result_typ = (desugar_typ env (Prims.fst result_arg))
in (
# 878 "FStar.Parser.ToSyntax.fst"
let rest = (desugar_args env rest)
in (
# 879 "FStar.Parser.ToSyntax.fst"
let _46_1542 = (FStar_All.pipe_right rest (FStar_List.partition (fun _46_1523 -> (match (_46_1523) with
| (t, _46_1522) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _46_1529; FStar_Syntax_Syntax.pos = _46_1527; FStar_Syntax_Syntax.vars = _46_1525}, _46_1534::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| _46_1539 -> begin
false
end)
end))))
in (match (_46_1542) with
| (dec, rest) -> begin
(
# 885 "FStar.Parser.ToSyntax.fst"
let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _46_1546 -> (match (_46_1546) with
| (t, _46_1545) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_46_1548, (arg, _46_1551)::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| _46_1557 -> begin
(FStar_All.failwith "impos")
end)
end))))
in (
# 889 "FStar.Parser.ToSyntax.fst"
let no_additional_args = (((FStar_List.length decreases_clause) = 0) && ((FStar_List.length rest) = 0))
in if (no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid)) then begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end else begin
if (no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid)) then begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end else begin
(
# 897 "FStar.Parser.ToSyntax.fst"
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
# 903 "FStar.Parser.ToSyntax.fst"
let rest = if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid) then begin
(match (rest) with
| req::ens::(pat, aq)::[] -> begin
(
# 907 "FStar.Parser.ToSyntax.fst"
let pat = (match (pat.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
(
# 909 "FStar.Parser.ToSyntax.fst"
let nil = (FStar_Syntax_Syntax.mk_Tm_uinst pat ((FStar_Syntax_Syntax.U_succ (FStar_Syntax_Syntax.U_zero))::[]))
in (
# 910 "FStar.Parser.ToSyntax.fst"
let pattern = (let _125_542 = (let _125_541 = (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _125_541 FStar_Syntax_Syntax.Delta_constant None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _125_542 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app nil (((pattern, Some (FStar_Syntax_Syntax.imp_tag)))::[]) None pat.FStar_Syntax_Syntax.pos)))
end
| _46_1572 -> begin
pat
end)
in (let _125_546 = (let _125_545 = (let _125_544 = (let _125_543 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((pat, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)))) None pat.FStar_Syntax_Syntax.pos)
in (_125_543, aq))
in (_125_544)::[])
in (ens)::_125_545)
in (req)::_125_546))
end
| _46_1575 -> begin
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
# 923 "FStar.Parser.ToSyntax.fst"
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
| _46_1587 -> begin
None
end))
in (
# 930 "FStar.Parser.ToSyntax.fst"
let mk = (fun t -> (FStar_Syntax_Syntax.mk t None f.FStar_Parser_AST.range))
in (
# 931 "FStar.Parser.ToSyntax.fst"
let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (
# 932 "FStar.Parser.ToSyntax.fst"
let setpos = (fun t -> (
# 932 "FStar.Parser.ToSyntax.fst"
let _46_1594 = t
in {FStar_Syntax_Syntax.n = _46_1594.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _46_1594.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _46_1594.FStar_Syntax_Syntax.vars}))
in (
# 933 "FStar.Parser.ToSyntax.fst"
let desugar_quant = (fun q b pats body -> (
# 934 "FStar.Parser.ToSyntax.fst"
let tk = (desugar_binder env (
# 934 "FStar.Parser.ToSyntax.fst"
let _46_1601 = b
in {FStar_Parser_AST.b = _46_1601.FStar_Parser_AST.b; FStar_Parser_AST.brange = _46_1601.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _46_1601.FStar_Parser_AST.aqual}))
in (
# 935 "FStar.Parser.ToSyntax.fst"
let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _125_581 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _125_581)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(
# 938 "FStar.Parser.ToSyntax.fst"
let _46_1615 = (FStar_Parser_Env.push_bv env a)
in (match (_46_1615) with
| (env, a) -> begin
(
# 939 "FStar.Parser.ToSyntax.fst"
let a = (
# 939 "FStar.Parser.ToSyntax.fst"
let _46_1616 = a
in {FStar_Syntax_Syntax.ppname = _46_1616.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _46_1616.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (
# 940 "FStar.Parser.ToSyntax.fst"
let pats = (desugar_pats env pats)
in (
# 941 "FStar.Parser.ToSyntax.fst"
let body = (desugar_formula env body)
in (
# 942 "FStar.Parser.ToSyntax.fst"
let body = (match (pats) with
| [] -> begin
body
end
| _46_1623 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((body, FStar_Syntax_Syntax.Meta_pattern (pats)))))
end)
in (
# 945 "FStar.Parser.ToSyntax.fst"
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
| _46_1627 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 950 "FStar.Parser.ToSyntax.fst"
let push_quant = (fun q binders pats body -> (match (binders) with
| b::b'::_rest -> begin
(
# 952 "FStar.Parser.ToSyntax.fst"
let rest = (b')::_rest
in (
# 953 "FStar.Parser.ToSyntax.fst"
let body = (let _125_605 = (q (rest, pats, body))
in (let _125_604 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _125_605 _125_604 FStar_Parser_AST.Formula)))
in (let _125_606 = (q ((b)::[], [], body))
in (FStar_Parser_AST.mk_term _125_606 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _46_1641 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _125_607 = (unparen f)
in _125_607.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(
# 959 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env f)
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((l, f.FStar_Syntax_Syntax.pos, p)))))))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall (_1::_2::_3, pats, body) -> begin
(
# 966 "FStar.Parser.ToSyntax.fst"
let binders = (_1)::(_2)::_3
in (let _125_609 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _125_609)))
end
| FStar_Parser_AST.QExists (_1::_2::_3, pats, body) -> begin
(
# 970 "FStar.Parser.ToSyntax.fst"
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
| _46_1699 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (
# 985 "FStar.Parser.ToSyntax.fst"
let _46_1723 = (FStar_List.fold_left (fun _46_1704 b -> (match (_46_1704) with
| (env, out) -> begin
(
# 986 "FStar.Parser.ToSyntax.fst"
let tk = (desugar_binder env (
# 986 "FStar.Parser.ToSyntax.fst"
let _46_1706 = b
in {FStar_Parser_AST.b = _46_1706.FStar_Parser_AST.b; FStar_Parser_AST.brange = _46_1706.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _46_1706.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(
# 989 "FStar.Parser.ToSyntax.fst"
let _46_1715 = (FStar_Parser_Env.push_bv env a)
in (match (_46_1715) with
| (env, a) -> begin
(
# 990 "FStar.Parser.ToSyntax.fst"
let a = (
# 990 "FStar.Parser.ToSyntax.fst"
let _46_1716 = a
in {FStar_Syntax_Syntax.ppname = _46_1716.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _46_1716.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (env, ((a, (trans_aqual b.FStar_Parser_AST.aqual)))::out))
end))
end
| _46_1720 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected binder", b.FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_46_1723) with
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

# 1000 "FStar.Parser.ToSyntax.fst"
let mk_data_discriminators : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  FStar_Ident.lid  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun quals env t tps k datas -> (
# 1003 "FStar.Parser.ToSyntax.fst"
let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_Env.iface) || env.FStar_Parser_Env.admitted_iface) then begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (
# 1006 "FStar.Parser.ToSyntax.fst"
let binders = (let _125_636 = (let _125_635 = (FStar_Syntax_Util.arrow_formals k)
in (Prims.fst _125_635))
in (FStar_List.append tps _125_636))
in (
# 1007 "FStar.Parser.ToSyntax.fst"
let p = (FStar_Ident.range_of_lid t)
in (
# 1008 "FStar.Parser.ToSyntax.fst"
let _46_1750 = (FStar_Syntax_Util.args_of_binders binders)
in (match (_46_1750) with
| (binders, args) -> begin
(
# 1009 "FStar.Parser.ToSyntax.fst"
let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _46_1754 -> (match (_46_1754) with
| (x, _46_1753) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
in (
# 1010 "FStar.Parser.ToSyntax.fst"
let binders = (let _125_642 = (let _125_641 = (let _125_640 = (let _125_639 = (let _125_638 = (FStar_Syntax_Syntax.lid_as_fv t FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _125_638))
in (FStar_Syntax_Syntax.mk_Tm_app _125_639 args None p))
in (FStar_All.pipe_left FStar_Syntax_Syntax.null_binder _125_640))
in (_125_641)::[])
in (FStar_List.append imp_binders _125_642))
in (
# 1011 "FStar.Parser.ToSyntax.fst"
let disc_type = (let _125_645 = (let _125_644 = (let _125_643 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _125_643))
in (FStar_Syntax_Syntax.mk_Total _125_644))
in (FStar_Syntax_Util.arrow binders _125_645))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (
# 1013 "FStar.Parser.ToSyntax.fst"
let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (let _125_648 = (let _125_647 = (quals ((FStar_Syntax_Syntax.Logic)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in (disc_name, [], disc_type, _125_647, (FStar_Ident.range_of_lid disc_name)))
in FStar_Syntax_Syntax.Sig_declare_typ (_125_648)))))))))
end))))))

# 1014 "FStar.Parser.ToSyntax.fst"
let mk_indexed_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq refine_domain env tc lid inductive_tps imp_tps fields t -> (
# 1017 "FStar.Parser.ToSyntax.fst"
let p = (FStar_Ident.range_of_lid lid)
in (
# 1018 "FStar.Parser.ToSyntax.fst"
let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p))
in (
# 1019 "FStar.Parser.ToSyntax.fst"
let projectee = (fun ptyp -> (FStar_Syntax_Syntax.gen_bv "projectee" (Some (p)) ptyp))
in (
# 1020 "FStar.Parser.ToSyntax.fst"
let tps = (FStar_List.map2 (fun _46_1778 _46_1782 -> (match ((_46_1778, _46_1782)) with
| ((_46_1776, imp), (x, _46_1781)) -> begin
(x, imp)
end)) inductive_tps imp_tps)
in (
# 1021 "FStar.Parser.ToSyntax.fst"
let _46_1883 = (
# 1022 "FStar.Parser.ToSyntax.fst"
let _46_1786 = (FStar_Syntax_Util.head_and_args t)
in (match (_46_1786) with
| (head, args0) -> begin
(
# 1023 "FStar.Parser.ToSyntax.fst"
let args = (
# 1024 "FStar.Parser.ToSyntax.fst"
let rec arguments = (fun tps args -> (match ((tps, args)) with
| ([], _46_1792) -> begin
args
end
| (_46_1795, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Not enough arguments to type", (FStar_Ident.range_of_lid lid)))))
end
| ((_46_1800, Some (FStar_Syntax_Syntax.Implicit (_46_1802)))::tps', (_46_1809, Some (FStar_Syntax_Syntax.Implicit (_46_1811)))::args') -> begin
(arguments tps' args')
end
| ((_46_1819, Some (FStar_Syntax_Syntax.Implicit (_46_1821)))::tps', (_46_1829, _46_1831)::_46_1827) -> begin
(arguments tps' args)
end
| ((_46_1838, _46_1840)::_46_1836, (a, Some (FStar_Syntax_Syntax.Implicit (_46_1847)))::_46_1844) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected implicit annotation on argument", a.FStar_Syntax_Syntax.pos))))
end
| ((_46_1855, _46_1857)::tps', (_46_1862, _46_1864)::args') -> begin
(arguments tps' args')
end))
in (arguments inductive_tps args0))
in (
# 1033 "FStar.Parser.ToSyntax.fst"
let indices = (FStar_All.pipe_right args (FStar_List.map (fun _46_1869 -> (let _125_680 = (FStar_Syntax_Syntax.new_bv (Some (p)) FStar_Syntax_Syntax.tun)
in (FStar_All.pipe_right _125_680 FStar_Syntax_Syntax.mk_binder)))))
in (
# 1034 "FStar.Parser.ToSyntax.fst"
let arg_typ = (let _125_685 = (let _125_681 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _125_681))
in (let _125_684 = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _46_1874 -> (match (_46_1874) with
| (x, imp) -> begin
(let _125_683 = (FStar_Syntax_Syntax.bv_to_name x)
in (_125_683, imp))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app _125_685 _125_684 None p)))
in (
# 1036 "FStar.Parser.ToSyntax.fst"
let arg_binder = if (not (refine_domain)) then begin
(let _125_686 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder _125_686))
end else begin
(
# 1039 "FStar.Parser.ToSyntax.fst"
let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (
# 1040 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p)) arg_typ)
in (let _125_695 = (
# 1041 "FStar.Parser.ToSyntax.fst"
let _46_1878 = (projectee arg_typ)
in (let _125_694 = (let _125_693 = (let _125_692 = (let _125_691 = (let _125_687 = (FStar_Ident.set_lid_range disc_name p)
in (FStar_Syntax_Syntax.fvar _125_687 FStar_Syntax_Syntax.Delta_equational None))
in (let _125_690 = (let _125_689 = (let _125_688 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _125_688))
in (_125_689)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _125_691 _125_690 None p)))
in (FStar_Syntax_Util.b2t _125_692))
in (FStar_Syntax_Util.refine x _125_693))
in {FStar_Syntax_Syntax.ppname = _46_1878.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _46_1878.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _125_694}))
in (FStar_Syntax_Syntax.mk_binder _125_695))))
end
in (arg_binder, indices)))))
end))
in (match (_46_1883) with
| (arg_binder, indices) -> begin
(
# 1045 "FStar.Parser.ToSyntax.fst"
let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder))
in (
# 1046 "FStar.Parser.ToSyntax.fst"
let imp_binders = (let _125_697 = (FStar_All.pipe_right indices (FStar_List.map (fun _46_1888 -> (match (_46_1888) with
| (x, _46_1887) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
in (FStar_List.append imp_tps _125_697))
in (
# 1047 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (
# 1049 "FStar.Parser.ToSyntax.fst"
let arg = (FStar_Syntax_Util.arg_of_non_null_binder arg_binder)
in (
# 1051 "FStar.Parser.ToSyntax.fst"
let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _46_1896 -> (match (_46_1896) with
| (a, _46_1895) -> begin
(
# 1052 "FStar.Parser.ToSyntax.fst"
let _46_1900 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (_46_1900) with
| (field_name, _46_1899) -> begin
(
# 1053 "FStar.Parser.ToSyntax.fst"
let proj = (let _125_701 = (let _125_700 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.fv_to_tm _125_700))
in (FStar_Syntax_Syntax.mk_Tm_app _125_701 ((arg)::[]) None p))
in FStar_Syntax_Syntax.NT ((a, proj)))
end))
end))))
in (
# 1056 "FStar.Parser.ToSyntax.fst"
let ntps = (FStar_List.length tps)
in (
# 1057 "FStar.Parser.ToSyntax.fst"
let all_params = (FStar_List.append imp_tps fields)
in (let _125_737 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _46_1909 -> (match (_46_1909) with
| (x, _46_1908) -> begin
(
# 1060 "FStar.Parser.ToSyntax.fst"
let _46_1913 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_46_1913) with
| (field_name, _46_1912) -> begin
(
# 1061 "FStar.Parser.ToSyntax.fst"
let t = (let _125_705 = (let _125_704 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total _125_704))
in (FStar_Syntax_Util.arrow binders _125_705))
in (
# 1062 "FStar.Parser.ToSyntax.fst"
let only_decl = (((let _125_706 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _125_706)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _125_708 = (let _125_707 = (FStar_Parser_Env.current_module env)
in _125_707.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _125_708)))
in (
# 1066 "FStar.Parser.ToSyntax.fst"
let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (
# 1067 "FStar.Parser.ToSyntax.fst"
let quals = (fun q -> if only_decl then begin
(FStar_Syntax_Syntax.Assumption)::q
end else begin
q
end)
in (
# 1068 "FStar.Parser.ToSyntax.fst"
let quals = (quals ((FStar_Syntax_Syntax.Projector ((lid, x.FStar_Syntax_Syntax.ppname)))::iquals))
in (
# 1069 "FStar.Parser.ToSyntax.fst"
let decl = FStar_Syntax_Syntax.Sig_declare_typ ((field_name, [], t, quals, (FStar_Ident.range_of_lid field_name)))
in if only_decl then begin
(decl)::[]
end else begin
(
# 1072 "FStar.Parser.ToSyntax.fst"
let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (
# 1073 "FStar.Parser.ToSyntax.fst"
let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _46_1925 -> (match (_46_1925) with
| (x, imp) -> begin
(
# 1074 "FStar.Parser.ToSyntax.fst"
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
# 1080 "FStar.Parser.ToSyntax.fst"
let pat = (let _125_725 = (let _125_723 = (let _125_722 = (let _125_721 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in (_125_721, arg_pats))
in FStar_Syntax_Syntax.Pat_cons (_125_722))
in (FStar_All.pipe_right _125_723 pos))
in (let _125_724 = (FStar_Syntax_Syntax.bv_to_name projection)
in (_125_725, None, _125_724)))
in (
# 1081 "FStar.Parser.ToSyntax.fst"
let body = (let _125_729 = (let _125_728 = (let _125_727 = (let _125_726 = (FStar_Syntax_Util.branch pat)
in (_125_726)::[])
in (arg_exp, _125_727))
in FStar_Syntax_Syntax.Tm_match (_125_728))
in (FStar_Syntax_Syntax.mk _125_729 None p))
in (
# 1082 "FStar.Parser.ToSyntax.fst"
let imp = (no_annot_abs binders body)
in (
# 1083 "FStar.Parser.ToSyntax.fst"
let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end else begin
FStar_Syntax_Syntax.Delta_equational
end
in (
# 1086 "FStar.Parser.ToSyntax.fst"
let lb = (let _125_731 = (let _125_730 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (_125_730))
in {FStar_Syntax_Syntax.lbname = _125_731; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = imp})
in (
# 1091 "FStar.Parser.ToSyntax.fst"
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

# 1092 "FStar.Parser.ToSyntax.fst"
let mk_data_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env _46_1939 -> (match (_46_1939) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _46_1942, t, l, n, quals, _46_1948, _46_1950) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(
# 1097 "FStar.Parser.ToSyntax.fst"
let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _46_10 -> (match (_46_10) with
| FStar_Syntax_Syntax.RecordConstructor (_46_1955) -> begin
true
end
| _46_1958 -> begin
false
end)))) then begin
false
end else begin
(match ((FStar_Parser_Env.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > 1)
end
| _46_1962 -> begin
true
end)
end
in (
# 1103 "FStar.Parser.ToSyntax.fst"
let _46_1966 = (FStar_Syntax_Util.arrow_formals t)
in (match (_46_1966) with
| (formals, cod) -> begin
(match (formals) with
| [] -> begin
[]
end
| _46_1969 -> begin
(
# 1107 "FStar.Parser.ToSyntax.fst"
let fv_qual = (match ((FStar_Util.find_map quals (fun _46_11 -> (match (_46_11) with
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((lid, fns)))
end
| _46_1974 -> begin
None
end)))) with
| None -> begin
FStar_Syntax_Syntax.Data_ctor
end
| Some (q) -> begin
q
end)
in (
# 1110 "FStar.Parser.ToSyntax.fst"
let iquals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract iquals) then begin
(FStar_Syntax_Syntax.Private)::iquals
end else begin
iquals
end
in (
# 1113 "FStar.Parser.ToSyntax.fst"
let _46_1982 = (FStar_Util.first_N n formals)
in (match (_46_1982) with
| (tps, rest) -> begin
(mk_indexed_projectors iquals fv_qual refine_domain env l lid inductive_tps tps rest cod)
end))))
end)
end)))
end
| _46_1984 -> begin
[]
end)
end))

# 1117 "FStar.Parser.ToSyntax.fst"
let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (
# 1120 "FStar.Parser.ToSyntax.fst"
let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _125_762 = (incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (_125_762))
end else begin
(incr_delta_qualifier t)
end
in (
# 1123 "FStar.Parser.ToSyntax.fst"
let lb = (let _125_767 = (let _125_763 = (FStar_Syntax_Syntax.lid_as_fv lid dd None)
in FStar_Util.Inr (_125_763))
in (let _125_766 = (let _125_764 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars _125_764))
in (let _125_765 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = _125_767; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = _125_766; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _125_765})))
in FStar_Syntax_Syntax.Sig_let (((false, (lb)::[]), rng, lids, quals)))))

# 1130 "FStar.Parser.ToSyntax.fst"
let rec desugar_tycon : FStar_Parser_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (
# 1133 "FStar.Parser.ToSyntax.fst"
let tycon_id = (fun _46_12 -> (match (_46_12) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (
# 1138 "FStar.Parser.ToSyntax.fst"
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
# 1144 "FStar.Parser.ToSyntax.fst"
let tot = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) rng FStar_Parser_AST.Expr)
in (
# 1145 "FStar.Parser.ToSyntax.fst"
let with_constructor_effect = (fun t -> (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((tot, t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level))
in (
# 1146 "FStar.Parser.ToSyntax.fst"
let apply_binders = (fun t binders -> (
# 1147 "FStar.Parser.ToSyntax.fst"
let imp_of_aqual = (fun b -> (match (b.FStar_Parser_AST.aqual) with
| Some (FStar_Parser_AST.Implicit) -> begin
FStar_Parser_AST.Hash
end
| _46_2059 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _125_794 = (let _125_793 = (let _125_792 = (binder_to_term b)
in (out, _125_792, (imp_of_aqual b)))
in FStar_Parser_AST.App (_125_793))
in (FStar_Parser_AST.mk_term _125_794 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (
# 1152 "FStar.Parser.ToSyntax.fst"
let tycon_record_as_variant = (fun _46_13 -> (match (_46_13) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(
# 1154 "FStar.Parser.ToSyntax.fst"
let constrName = (FStar_Ident.mk_ident ((Prims.strcat "Mk" id.FStar_Ident.idText), id.FStar_Ident.idRange))
in (
# 1155 "FStar.Parser.ToSyntax.fst"
let mfields = (FStar_List.map (fun _46_2072 -> (match (_46_2072) with
| (x, t) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated (((FStar_Syntax_Util.mangle_field_name x), t))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (
# 1156 "FStar.Parser.ToSyntax.fst"
let result = (let _125_800 = (let _125_799 = (let _125_798 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_125_798))
in (FStar_Parser_AST.mk_term _125_799 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _125_800 parms))
in (
# 1157 "FStar.Parser.ToSyntax.fst"
let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _125_802 = (FStar_All.pipe_right fields (FStar_List.map (fun _46_2079 -> (match (_46_2079) with
| (x, _46_2078) -> begin
(FStar_Parser_Env.qualify env x)
end))))
in (FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _125_802))))))
end
| _46_2081 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1161 "FStar.Parser.ToSyntax.fst"
let desugar_abstract_tc = (fun quals _env mutuals _46_14 -> (match (_46_14) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(
# 1163 "FStar.Parser.ToSyntax.fst"
let _46_2095 = (typars_of_binders _env binders)
in (match (_46_2095) with
| (_env', typars) -> begin
(
# 1164 "FStar.Parser.ToSyntax.fst"
let k = (match (kopt) with
| None -> begin
FStar_Syntax_Util.ktype
end
| Some (k) -> begin
(desugar_term _env' k)
end)
in (
# 1167 "FStar.Parser.ToSyntax.fst"
let tconstr = (let _125_813 = (let _125_812 = (let _125_811 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_125_811))
in (FStar_Parser_AST.mk_term _125_812 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _125_813 binders))
in (
# 1168 "FStar.Parser.ToSyntax.fst"
let qlid = (FStar_Parser_Env.qualify _env id)
in (
# 1169 "FStar.Parser.ToSyntax.fst"
let typars = (FStar_Syntax_Subst.close_binders typars)
in (
# 1170 "FStar.Parser.ToSyntax.fst"
let k = (FStar_Syntax_Subst.close typars k)
in (
# 1171 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_inductive_typ ((qlid, [], typars, k, mutuals, [], quals, rng))
in (
# 1172 "FStar.Parser.ToSyntax.fst"
let _env = (FStar_Parser_Env.push_top_level_rec_binding _env id FStar_Syntax_Syntax.Delta_constant)
in (
# 1173 "FStar.Parser.ToSyntax.fst"
let _env2 = (FStar_Parser_Env.push_top_level_rec_binding _env' id FStar_Syntax_Syntax.Delta_constant)
in (_env, _env2, se, tconstr)))))))))
end))
end
| _46_2108 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (
# 1176 "FStar.Parser.ToSyntax.fst"
let push_tparams = (fun env bs -> (
# 1177 "FStar.Parser.ToSyntax.fst"
let _46_2123 = (FStar_List.fold_left (fun _46_2114 _46_2117 -> (match ((_46_2114, _46_2117)) with
| ((env, tps), (x, imp)) -> begin
(
# 1178 "FStar.Parser.ToSyntax.fst"
let _46_2120 = (FStar_Parser_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (_46_2120) with
| (env, y) -> begin
(env, ((y, imp))::tps)
end))
end)) (env, []) bs)
in (match (_46_2123) with
| (env, bs) -> begin
(env, (FStar_List.rev bs))
end)))
in (match (tcs) with
| FStar_Parser_AST.TyconAbstract (_46_2125)::[] -> begin
(
# 1183 "FStar.Parser.ToSyntax.fst"
let tc = (FStar_List.hd tcs)
in (
# 1184 "FStar.Parser.ToSyntax.fst"
let _46_2136 = (desugar_abstract_tc quals env [] tc)
in (match (_46_2136) with
| (_46_2130, _46_2132, se, _46_2135) -> begin
(
# 1185 "FStar.Parser.ToSyntax.fst"
let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _46_2139, typars, k, [], [], quals, rng) -> begin
(
# 1187 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
quals
end else begin
(
# 1189 "FStar.Parser.ToSyntax.fst"
let _46_2148 = (let _125_821 = (FStar_Range.string_of_range rng)
in (let _125_820 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" _125_821 _125_820)))
in (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals)
end
in (
# 1192 "FStar.Parser.ToSyntax.fst"
let t = (match (typars) with
| [] -> begin
k
end
| _46_2153 -> begin
(let _125_824 = (let _125_823 = (let _125_822 = (FStar_Syntax_Syntax.mk_Total k)
in (typars, _125_822))
in FStar_Syntax_Syntax.Tm_arrow (_125_823))
in (FStar_Syntax_Syntax.mk _125_824 None rng))
end)
in FStar_Syntax_Syntax.Sig_declare_typ ((l, [], t, quals, rng))))
end
| _46_2156 -> begin
se
end)
in (
# 1197 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))
end)))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t)::[] -> begin
(
# 1202 "FStar.Parser.ToSyntax.fst"
let _46_2168 = (typars_of_binders env binders)
in (match (_46_2168) with
| (env', typars) -> begin
(
# 1203 "FStar.Parser.ToSyntax.fst"
let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _46_15 -> (match (_46_15) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| _46_2173 -> begin
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
# 1209 "FStar.Parser.ToSyntax.fst"
let t0 = t
in (
# 1210 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _46_16 -> (match (_46_16) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| _46_2181 -> begin
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
# 1215 "FStar.Parser.ToSyntax.fst"
let se = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Effect)) then begin
(
# 1217 "FStar.Parser.ToSyntax.fst"
let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (
# 1218 "FStar.Parser.ToSyntax.fst"
let typars = (FStar_Syntax_Subst.close_binders typars)
in (
# 1219 "FStar.Parser.ToSyntax.fst"
let c = (FStar_Syntax_Subst.close_comp typars c)
in (let _125_830 = (let _125_829 = (FStar_Parser_Env.qualify env id)
in (let _125_828 = (FStar_All.pipe_right quals (FStar_List.filter (fun _46_17 -> (match (_46_17) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| _46_2189 -> begin
true
end))))
in (_125_829, [], typars, c, _125_828, rng)))
in FStar_Syntax_Syntax.Sig_effect_abbrev (_125_830)))))
end else begin
(
# 1221 "FStar.Parser.ToSyntax.fst"
let t = (desugar_typ env' t)
in (
# 1222 "FStar.Parser.ToSyntax.fst"
let nm = (FStar_Parser_Env.qualify env id)
in (mk_typ_abbrev nm [] typars k t ((nm)::[]) quals rng)))
end
in (
# 1225 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[]))))))
end))
end
| FStar_Parser_AST.TyconRecord (_46_2195)::[] -> begin
(
# 1229 "FStar.Parser.ToSyntax.fst"
let trec = (FStar_List.hd tcs)
in (
# 1230 "FStar.Parser.ToSyntax.fst"
let _46_2201 = (tycon_record_as_variant trec)
in (match (_46_2201) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| _46_2205::_46_2203 -> begin
(
# 1234 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1235 "FStar.Parser.ToSyntax.fst"
let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_Env.qualify env) (tycon_id x))) tcs)
in (
# 1236 "FStar.Parser.ToSyntax.fst"
let rec collect_tcs = (fun quals et tc -> (
# 1237 "FStar.Parser.ToSyntax.fst"
let _46_2216 = et
in (match (_46_2216) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_46_2218) -> begin
(
# 1240 "FStar.Parser.ToSyntax.fst"
let trec = tc
in (
# 1241 "FStar.Parser.ToSyntax.fst"
let _46_2223 = (tycon_record_as_variant trec)
in (match (_46_2223) with
| (t, fs) -> begin
(collect_tcs ((FStar_Syntax_Syntax.RecordType (fs))::quals) (env, tcs) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(
# 1244 "FStar.Parser.ToSyntax.fst"
let _46_2235 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_46_2235) with
| (env, _46_2232, se, tconstr) -> begin
(env, (FStar_Util.Inl ((se, constructors, tconstr, quals)))::tcs)
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(
# 1247 "FStar.Parser.ToSyntax.fst"
let _46_2247 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_46_2247) with
| (env, _46_2244, se, tconstr) -> begin
(env, (FStar_Util.Inr ((se, t, quals)))::tcs)
end))
end
| _46_2249 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (
# 1250 "FStar.Parser.ToSyntax.fst"
let _46_2252 = (FStar_List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_46_2252) with
| (env, tcs) -> begin
(
# 1251 "FStar.Parser.ToSyntax.fst"
let tcs = (FStar_List.rev tcs)
in (
# 1252 "FStar.Parser.ToSyntax.fst"
let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _46_19 -> (match (_46_19) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, _46_2260, _46_2262, _46_2264, _46_2266), t, quals) -> begin
(
# 1254 "FStar.Parser.ToSyntax.fst"
let _46_2276 = (push_tparams env tpars)
in (match (_46_2276) with
| (env_tps, _46_2275) -> begin
(
# 1255 "FStar.Parser.ToSyntax.fst"
let t = (desugar_term env_tps t)
in (let _125_840 = (let _125_839 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in ([], _125_839))
in (_125_840)::[]))
end))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, _46_2284, tags, _46_2287), constrs, tconstr, quals) -> begin
(
# 1259 "FStar.Parser.ToSyntax.fst"
let tycon = (tname, tpars, k)
in (
# 1260 "FStar.Parser.ToSyntax.fst"
let _46_2298 = (push_tparams env tpars)
in (match (_46_2298) with
| (env_tps, tps) -> begin
(
# 1261 "FStar.Parser.ToSyntax.fst"
let data_tpars = (FStar_List.map (fun _46_2302 -> (match (_46_2302) with
| (x, _46_2301) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end)) tps)
in (
# 1262 "FStar.Parser.ToSyntax.fst"
let _46_2326 = (let _125_852 = (FStar_All.pipe_right constrs (FStar_List.map (fun _46_2307 -> (match (_46_2307) with
| (id, topt, of_notation) -> begin
(
# 1264 "FStar.Parser.ToSyntax.fst"
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
# 1272 "FStar.Parser.ToSyntax.fst"
let t = (let _125_844 = (FStar_Parser_Env.default_total env_tps)
in (let _125_843 = (close env_tps t)
in (desugar_term _125_844 _125_843)))
in (
# 1273 "FStar.Parser.ToSyntax.fst"
let name = (FStar_Parser_Env.qualify env id)
in (
# 1274 "FStar.Parser.ToSyntax.fst"
let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _46_18 -> (match (_46_18) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| _46_2321 -> begin
[]
end))))
in (
# 1277 "FStar.Parser.ToSyntax.fst"
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
in (match (_46_2326) with
| (constrNames, constrs) -> begin
(([], FStar_Syntax_Syntax.Sig_inductive_typ ((tname, univs, tpars, k, mutuals, constrNames, tags, rng))))::constrs
end)))
end)))
end
| _46_2328 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1282 "FStar.Parser.ToSyntax.fst"
let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (
# 1283 "FStar.Parser.ToSyntax.fst"
let bundle = (let _125_854 = (let _125_853 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _125_853, rng))
in FStar_Syntax_Syntax.Sig_bundle (_125_854))
in (
# 1284 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 bundle)
in (
# 1285 "FStar.Parser.ToSyntax.fst"
let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projectors quals env)))
in (
# 1286 "FStar.Parser.ToSyntax.fst"
let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _46_20 -> (match (_46_20) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, _46_2337, tps, k, _46_2341, constrs, quals, _46_2345) when ((FStar_List.length constrs) > 1) -> begin
(
# 1288 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract quals) then begin
(FStar_Syntax_Syntax.Private)::quals
end else begin
quals
end
in (mk_data_discriminators quals env tname tps k constrs))
end
| _46_2350 -> begin
[]
end))))
in (
# 1293 "FStar.Parser.ToSyntax.fst"
let ops = (FStar_List.append discs data_ops)
in (
# 1294 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env ops)
in (env, (FStar_List.append ((bundle)::[]) ops)))))))))))
end)))))
end
| [] -> begin
(FStar_All.failwith "impossible")
end))))))))))

# 1297 "FStar.Parser.ToSyntax.fst"
let desugar_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.binder Prims.list) = (fun env binders -> (
# 1300 "FStar.Parser.ToSyntax.fst"
let _46_2374 = (FStar_List.fold_left (fun _46_2359 b -> (match (_46_2359) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| (Some (a), k) -> begin
(
# 1303 "FStar.Parser.ToSyntax.fst"
let _46_2367 = (FStar_Parser_Env.push_bv env a)
in (match (_46_2367) with
| (env, a) -> begin
(let _125_863 = (let _125_862 = (FStar_Syntax_Syntax.mk_binder (
# 1304 "FStar.Parser.ToSyntax.fst"
let _46_2368 = a
in {FStar_Syntax_Syntax.ppname = _46_2368.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _46_2368.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (_125_862)::binders)
in (env, _125_863))
end))
end
| _46_2371 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Missing name in binder", b.FStar_Parser_AST.brange))))
end)
end)) (env, []) binders)
in (match (_46_2374) with
| (env, binders) -> begin
(env, (FStar_List.rev binders))
end)))

# 1307 "FStar.Parser.ToSyntax.fst"
let rec desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(
# 1311 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_pragma (((trans_pragma p), d.FStar_Parser_AST.drange))
in (env, (se)::[]))
end
| FStar_Parser_AST.Open (lid) -> begin
(
# 1315 "FStar.Parser.ToSyntax.fst"
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
| FStar_Syntax_Syntax.Tm_let (lbs, _46_2394) -> begin
(
# 1324 "FStar.Parser.ToSyntax.fst"
let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (
# 1325 "FStar.Parser.ToSyntax.fst"
let quals = (match (quals) with
| _46_2402::_46_2400 -> begin
(FStar_List.map trans_qual quals)
end
| _46_2405 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _46_21 -> (match (_46_21) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (_46_2416); FStar_Syntax_Syntax.lbunivs = _46_2414; FStar_Syntax_Syntax.lbtyp = _46_2412; FStar_Syntax_Syntax.lbeff = _46_2410; FStar_Syntax_Syntax.lbdef = _46_2408} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _46_2426; FStar_Syntax_Syntax.lbtyp = _46_2424; FStar_Syntax_Syntax.lbeff = _46_2422; FStar_Syntax_Syntax.lbdef = _46_2420} -> begin
(FStar_Parser_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (
# 1330 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right lets (FStar_Util.for_some (fun _46_2434 -> (match (_46_2434) with
| (_46_2432, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end)))) then begin
(FStar_Syntax_Syntax.Logic)::quals
end else begin
quals
end
in (
# 1334 "FStar.Parser.ToSyntax.fst"
let lbs = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _125_875 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 1336 "FStar.Parser.ToSyntax.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 1337 "FStar.Parser.ToSyntax.fst"
let _46_2438 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((
# 1337 "FStar.Parser.ToSyntax.fst"
let _46_2440 = fv
in {FStar_Syntax_Syntax.fv_name = _46_2440.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = _46_2440.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = _46_2438.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _46_2438.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _46_2438.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _46_2438.FStar_Syntax_Syntax.lbdef})))))
in ((Prims.fst lbs), _125_875))
end else begin
lbs
end
in (
# 1339 "FStar.Parser.ToSyntax.fst"
let s = (let _125_878 = (let _125_877 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (lbs, d.FStar_Parser_AST.drange, _125_877, quals))
in FStar_Syntax_Syntax.Sig_let (_125_878))
in (
# 1340 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env s)
in (env, (s)::[])))))))
end
| _46_2447 -> begin
(FStar_All.failwith "Desugaring a let did not produce a let")
end)
end
| FStar_Parser_AST.Main (t) -> begin
(
# 1346 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env t)
in (
# 1347 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, d.FStar_Parser_AST.drange))
in (env, (se)::[])))
end
| FStar_Parser_AST.Assume (atag, id, t) -> begin
(
# 1351 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env t)
in (let _125_882 = (let _125_881 = (let _125_880 = (let _125_879 = (FStar_Parser_Env.qualify env id)
in (_125_879, f, (FStar_Syntax_Syntax.Assumption)::[], d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Sig_assume (_125_880))
in (_125_881)::[])
in (env, _125_882)))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(
# 1355 "FStar.Parser.ToSyntax.fst"
let t = (let _125_883 = (close_fun env t)
in (desugar_term env _125_883))
in (
# 1356 "FStar.Parser.ToSyntax.fst"
let quals = if (env.FStar_Parser_Env.iface && env.FStar_Parser_Env.admitted_iface) then begin
(FStar_Parser_AST.Assumption)::quals
end else begin
quals
end
in (
# 1357 "FStar.Parser.ToSyntax.fst"
let se = (let _125_886 = (let _125_885 = (FStar_Parser_Env.qualify env id)
in (let _125_884 = (FStar_List.map trans_qual quals)
in (_125_885, [], t, _125_884, d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_declare_typ (_125_886))
in (
# 1358 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(
# 1362 "FStar.Parser.ToSyntax.fst"
let t = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (
# 1363 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env id)
in (
# 1364 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_datacon ((l, [], t, FStar_Syntax_Const.exn_lid, 0, (FStar_Syntax_Syntax.ExceptionConstructor)::[], (FStar_Syntax_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (
# 1365 "FStar.Parser.ToSyntax.fst"
let se' = FStar_Syntax_Syntax.Sig_bundle (((se)::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (
# 1366 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se')
in (
# 1367 "FStar.Parser.ToSyntax.fst"
let data_ops = (mk_data_projectors [] env ([], se))
in (
# 1368 "FStar.Parser.ToSyntax.fst"
let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (
# 1369 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops))))))))))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(
# 1373 "FStar.Parser.ToSyntax.fst"
let t = (desugar_term env term)
in (
# 1374 "FStar.Parser.ToSyntax.fst"
let t = (let _125_890 = (let _125_887 = (FStar_Syntax_Syntax.null_binder t)
in (_125_887)::[])
in (let _125_889 = (let _125_888 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _125_888))
in (FStar_Syntax_Util.arrow _125_890 _125_889)))
in (
# 1375 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env id)
in (
# 1376 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_datacon ((l, [], t, FStar_Syntax_Const.exn_lid, 0, (FStar_Syntax_Syntax.ExceptionConstructor)::[], (FStar_Syntax_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (
# 1377 "FStar.Parser.ToSyntax.fst"
let se' = FStar_Syntax_Syntax.Sig_bundle (((se)::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (
# 1378 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se')
in (
# 1379 "FStar.Parser.ToSyntax.fst"
let data_ops = (mk_data_projectors [] env ([], se))
in (
# 1380 "FStar.Parser.ToSyntax.fst"
let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (
# 1381 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops)))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(
# 1385 "FStar.Parser.ToSyntax.fst"
let _46_2500 = (desugar_binders env binders)
in (match (_46_2500) with
| (env_k, binders) -> begin
(
# 1386 "FStar.Parser.ToSyntax.fst"
let k = (desugar_term env_k k)
in (
# 1387 "FStar.Parser.ToSyntax.fst"
let name = (FStar_Parser_Env.qualify env id)
in (
# 1388 "FStar.Parser.ToSyntax.fst"
let se = (mk_typ_abbrev name [] binders FStar_Syntax_Syntax.tun k ((name)::[]) [] d.FStar_Parser_AST.drange)
in (
# 1389 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))))
end))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(
# 1393 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1394 "FStar.Parser.ToSyntax.fst"
let _46_2516 = (desugar_binders env eff_binders)
in (match (_46_2516) with
| (env, binders) -> begin
(
# 1395 "FStar.Parser.ToSyntax.fst"
let _46_2527 = (
# 1396 "FStar.Parser.ToSyntax.fst"
let _46_2519 = (head_and_args defn)
in (match (_46_2519) with
| (head, args) -> begin
(
# 1397 "FStar.Parser.ToSyntax.fst"
let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_defn env) l)
end
| _46_2523 -> begin
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
in (match (_46_2527) with
| (ed, args) -> begin
(
# 1401 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_Syntax_Subst.close_binders binders)
in (
# 1402 "FStar.Parser.ToSyntax.fst"
let sub = (fun _46_2533 -> (match (_46_2533) with
| (_46_2531, x) -> begin
(
# 1403 "FStar.Parser.ToSyntax.fst"
let _46_2536 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (_46_2536) with
| (edb, x) -> begin
(
# 1404 "FStar.Parser.ToSyntax.fst"
let s = (FStar_Syntax_Util.subst_of_list edb args)
in (let _125_900 = (let _125_899 = (FStar_Syntax_Subst.subst s x)
in (FStar_Syntax_Subst.close binders _125_899))
in ([], _125_900)))
end))
end))
in (
# 1406 "FStar.Parser.ToSyntax.fst"
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
# 1426 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (
# 1427 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 se)
in (env, (se)::[]))))))
end))
end)))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls)) -> begin
(
# 1431 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1432 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.enter_monad_scope env eff_name)
in (
# 1433 "FStar.Parser.ToSyntax.fst"
let _46_2554 = (desugar_binders env eff_binders)
in (match (_46_2554) with
| (env, binders) -> begin
(
# 1434 "FStar.Parser.ToSyntax.fst"
let eff_k = (let _125_918 = (FStar_Parser_Env.default_total env)
in (desugar_term _125_918 eff_kind))
in (
# 1435 "FStar.Parser.ToSyntax.fst"
let _46_2565 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _46_2558 decl -> (match (_46_2558) with
| (env, out) -> begin
(
# 1436 "FStar.Parser.ToSyntax.fst"
let _46_2562 = (desugar_decl env decl)
in (match (_46_2562) with
| (env, ses) -> begin
(let _125_922 = (let _125_921 = (FStar_List.hd ses)
in (_125_921)::out)
in (env, _125_922))
end))
end)) (env, [])))
in (match (_46_2565) with
| (env, decls) -> begin
(
# 1438 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_Syntax_Subst.close_binders binders)
in (
# 1439 "FStar.Parser.ToSyntax.fst"
let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (
# 1440 "FStar.Parser.ToSyntax.fst"
let lookup = (fun s -> (
# 1441 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env (FStar_Ident.mk_ident (s, d.FStar_Parser_AST.drange)))
in (let _125_926 = (let _125_925 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) _125_925))
in ([], _125_926))))
in (
# 1443 "FStar.Parser.ToSyntax.fst"
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
# 1463 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (
# 1464 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 se)
in (env, (se)::[])))))))
end)))
end))))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(
# 1468 "FStar.Parser.ToSyntax.fst"
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
# 1471 "FStar.Parser.ToSyntax.fst"
let src = (lookup l.FStar_Parser_AST.msource)
in (
# 1472 "FStar.Parser.ToSyntax.fst"
let dst = (lookup l.FStar_Parser_AST.mdest)
in (
# 1473 "FStar.Parser.ToSyntax.fst"
let lift = (let _125_949 = (desugar_term env l.FStar_Parser_AST.lift_op)
in ([], _125_949))
in (
# 1474 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect (({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift = lift}, d.FStar_Parser_AST.drange))
in (env, (se)::[]))))))
end))

# 1475 "FStar.Parser.ToSyntax.fst"
let desugar_decls : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _46_2589 d -> (match (_46_2589) with
| (env, sigelts) -> begin
(
# 1479 "FStar.Parser.ToSyntax.fst"
let _46_2593 = (desugar_decl env d)
in (match (_46_2593) with
| (env, se) -> begin
(env, (FStar_List.append sigelts se))
end))
end)) (env, []) decls))

# 1480 "FStar.Parser.ToSyntax.fst"
let open_prims_all : FStar_Parser_AST.decl Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.all_lid)) FStar_Range.dummyRange))::[]

# 1484 "FStar.Parser.ToSyntax.fst"
let desugar_modul_common : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (
# 1490 "FStar.Parser.ToSyntax.fst"
let open_ns = (fun mname d -> (
# 1491 "FStar.Parser.ToSyntax.fst"
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
# 1495 "FStar.Parser.ToSyntax.fst"
let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod) -> begin
(FStar_Parser_Env.finish_module_or_interface env prev_mod)
end)
in (
# 1498 "FStar.Parser.ToSyntax.fst"
let _46_2620 = (match (m) with
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
in (match (_46_2620) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(
# 1503 "FStar.Parser.ToSyntax.fst"
let _46_2623 = (desugar_decls env decls)
in (match (_46_2623) with
| (env, sigelts) -> begin
(
# 1504 "FStar.Parser.ToSyntax.fst"
let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in (env, modul, pop_when_done))
end))
end)))))

# 1510 "FStar.Parser.ToSyntax.fst"
let desugar_partial_modul : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (
# 1513 "FStar.Parser.ToSyntax.fst"
let m = if (FStar_ST.read FStar_Options.interactive_fsi) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface ((mname, decls, true))
end
| FStar_Parser_AST.Interface (mname, _46_2634, _46_2636) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (
# 1520 "FStar.Parser.ToSyntax.fst"
let _46_2644 = (desugar_modul_common curmod env m)
in (match (_46_2644) with
| (x, y, _46_2643) -> begin
(x, y)
end))))

# 1521 "FStar.Parser.ToSyntax.fst"
let desugar_modul : FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (
# 1524 "FStar.Parser.ToSyntax.fst"
let _46_2650 = (desugar_modul_common None env m)
in (match (_46_2650) with
| (env, modul, pop_when_done) -> begin
(
# 1525 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.finish_module_or_interface env modul)
in (
# 1526 "FStar.Parser.ToSyntax.fst"
let _46_2652 = if (FStar_Options.should_dump modul.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
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

# 1528 "FStar.Parser.ToSyntax.fst"
let desugar_file : FStar_Parser_Env.env  ->  FStar_Parser_AST.file  ->  Prims.bool  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f needs_interleaving -> (
# 1531 "FStar.Parser.ToSyntax.fst"
let _46_2667 = (FStar_List.fold_left (fun _46_2659 m -> (match (_46_2659) with
| (env, mods) -> begin
(
# 1532 "FStar.Parser.ToSyntax.fst"
let m = if needs_interleaving then begin
(FStar_Parser_Interleave.interleave_modul m)
end else begin
m
end
in (
# 1533 "FStar.Parser.ToSyntax.fst"
let _46_2664 = (desugar_modul env m)
in (match (_46_2664) with
| (env, m) -> begin
(env, (m)::mods)
end)))
end)) (env, []) f)
in (match (_46_2667) with
| (env, mods) -> begin
(env, (FStar_List.rev mods))
end)))

# 1535 "FStar.Parser.ToSyntax.fst"
let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Parser_Env.env  ->  FStar_Parser_Env.env = (fun m en -> (
# 1538 "FStar.Parser.ToSyntax.fst"
let _46_2672 = (FStar_Parser_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (_46_2672) with
| (en, pop_when_done) -> begin
(
# 1539 "FStar.Parser.ToSyntax.fst"
let en = (FStar_List.fold_left FStar_Parser_Env.push_sigelt (
# 1539 "FStar.Parser.ToSyntax.fst"
let _46_2673 = en
in {FStar_Parser_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_Parser_Env.modules = _46_2673.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _46_2673.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.sigaccum = _46_2673.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _46_2673.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _46_2673.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _46_2673.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _46_2673.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _46_2673.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _46_2673.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = _46_2673.FStar_Parser_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (
# 1540 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_Env.export_interface m.FStar_Syntax_Syntax.name env)
end else begin
env
end))
end)))




