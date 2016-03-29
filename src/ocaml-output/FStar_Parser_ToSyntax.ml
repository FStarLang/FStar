
open Prims
# 40 "FStar.Parser.ToSyntax.fst"
let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _52_1 -> (match (_52_1) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Syntax_Syntax.Equality)
end
| _52_28 -> begin
None
end))

# 45 "FStar.Parser.ToSyntax.fst"
let trans_qual : FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun _52_2 -> (match (_52_2) with
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
let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun _52_3 -> (match (_52_3) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end))

# 63 "FStar.Parser.ToSyntax.fst"
let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _52_4 -> (match (_52_4) with
| (FStar_Parser_AST.Hash) | (FStar_Parser_AST.FsTypApp) -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| _52_51 -> begin
None
end))

# 67 "FStar.Parser.ToSyntax.fst"
let arg_withimp_e = (fun imp t -> (t, (as_imp imp)))

# 69 "FStar.Parser.ToSyntax.fst"
let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
(t, Some (FStar_Syntax_Syntax.imp_tag))
end
| _52_58 -> begin
(t, None)
end))

# 74 "FStar.Parser.ToSyntax.fst"
let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_52_62) -> begin
true
end
| _52_65 -> begin
false
end)))))

# 79 "FStar.Parser.ToSyntax.fst"
let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _52_70 -> begin
t
end))

# 83 "FStar.Parser.ToSyntax.fst"
let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _137_21 = (let _137_20 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_137_20))
in (FStar_Parser_AST.mk_term _137_21 r FStar_Parser_AST.Kind)))

# 85 "FStar.Parser.ToSyntax.fst"
let rec delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (
# 86 "FStar.Parser.ToSyntax.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_52_75) -> begin
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

# 115 "FStar.Parser.ToSyntax.fst"
let compile_op : Prims.int  ->  Prims.string  ->  Prims.string = (fun arity s -> (
# 116 "FStar.Parser.ToSyntax.fst"
let name_of_char = (fun _52_5 -> (match (_52_5) with
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
| _52_170 -> begin
"UNKNOWN"
end))
in (
# 135 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _137_41 = (let _137_39 = (FStar_Util.char_at s i)
in (name_of_char _137_39))
in (let _137_40 = (aux (i + 1))
in (_137_41)::_137_40))
end)
in (let _137_43 = (let _137_42 = (aux 0)
in (FStar_String.concat "_" _137_42))
in (Prims.strcat "op_" _137_43)))))

# 141 "FStar.Parser.ToSyntax.fst"
let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _137_53 = (let _137_52 = (let _137_51 = (let _137_50 = (compile_op n s)
in (_137_50, r))
in (FStar_Ident.mk_ident _137_51))
in (_137_52)::[])
in (FStar_All.pipe_right _137_53 FStar_Ident.lid_of_ids)))

# 143 "FStar.Parser.ToSyntax.fst"
let op_as_term : FStar_Parser_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.term Prims.option = (fun env arity rng s -> (
# 144 "FStar.Parser.ToSyntax.fst"
let r = (fun l dd -> (let _137_68 = (let _137_67 = (let _137_66 = (FStar_Ident.set_lid_range l rng)
in (FStar_Syntax_Syntax.lid_as_fv _137_66 dd None))
in (FStar_All.pipe_right _137_67 FStar_Syntax_Syntax.fv_to_tm))
in Some (_137_68)))
in (
# 145 "FStar.Parser.ToSyntax.fst"
let fallback = (fun _52_185 -> (match (()) with
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
| _52_213 -> begin
None
end)
end))
in (match ((let _137_71 = (compile_op_lid arity s rng)
in (FStar_Parser_Env.try_lookup_lid env _137_71))) with
| Some (t) -> begin
Some (t)
end
| _52_217 -> begin
(fallback ())
end))))

# 179 "FStar.Parser.ToSyntax.fst"
let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _137_78 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _137_78)))

# 183 "FStar.Parser.ToSyntax.fst"
let rec free_type_vars_b : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_52_226) -> begin
(env, [])
end
| FStar_Parser_AST.TVariable (x) -> begin
(
# 186 "FStar.Parser.ToSyntax.fst"
let _52_233 = (FStar_Parser_Env.push_bv env x)
in (match (_52_233) with
| (env, _52_232) -> begin
(env, (x)::[])
end))
end
| FStar_Parser_AST.Annotated (_52_235, term) -> begin
(let _137_85 = (free_type_vars env term)
in (env, _137_85))
end
| FStar_Parser_AST.TAnnotated (id, _52_241) -> begin
(
# 191 "FStar.Parser.ToSyntax.fst"
let _52_247 = (FStar_Parser_Env.push_bv env id)
in (match (_52_247) with
| (env, _52_246) -> begin
(env, [])
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _137_86 = (free_type_vars env t)
in (env, _137_86))
end))
and free_type_vars : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _137_89 = (unparen t)
in _137_89.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (_52_253) -> begin
(FStar_All.failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_Env.try_lookup_id env a)) with
| None -> begin
(a)::[]
end
| _52_259 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_52_289, ts) -> begin
(FStar_List.collect (fun _52_296 -> (match (_52_296) with
| (t, _52_295) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_52_298, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _52_305) -> begin
(let _137_92 = (free_type_vars env t1)
in (let _137_91 = (free_type_vars env t2)
in (FStar_List.append _137_92 _137_91)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(
# 221 "FStar.Parser.ToSyntax.fst"
let _52_314 = (free_type_vars_b env b)
in (match (_52_314) with
| (env, f) -> begin
(let _137_93 = (free_type_vars env t)
in (FStar_List.append f _137_93))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(
# 226 "FStar.Parser.ToSyntax.fst"
let _52_330 = (FStar_List.fold_left (fun _52_323 binder -> (match (_52_323) with
| (env, free) -> begin
(
# 227 "FStar.Parser.ToSyntax.fst"
let _52_327 = (free_type_vars_b env binder)
in (match (_52_327) with
| (env, f) -> begin
(env, (FStar_List.append f free))
end))
end)) (env, []) binders)
in (match (_52_330) with
| (env, free) -> begin
(let _137_96 = (free_type_vars env body)
in (FStar_List.append free _137_96))
end))
end
| FStar_Parser_AST.Project (t, _52_333) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
[]
end))

# 244 "FStar.Parser.ToSyntax.fst"
let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (
# 245 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun args t -> (match ((let _137_103 = (unparen t)
in _137_103.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _52_377 -> begin
(t, args)
end))
in (aux [] t)))

# 251 "FStar.Parser.ToSyntax.fst"
let close : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 252 "FStar.Parser.ToSyntax.fst"
let ftv = (let _137_108 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _137_108))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 255 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _137_112 = (let _137_111 = (let _137_110 = (tm_type x.FStar_Ident.idRange)
in (x, _137_110))
in FStar_Parser_AST.TAnnotated (_137_111))
in (FStar_Parser_AST.mk_binder _137_112 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 256 "FStar.Parser.ToSyntax.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))

# 259 "FStar.Parser.ToSyntax.fst"
let close_fun : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 260 "FStar.Parser.ToSyntax.fst"
let ftv = (let _137_117 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _137_117))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 263 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _137_121 = (let _137_120 = (let _137_119 = (tm_type x.FStar_Ident.idRange)
in (x, _137_119))
in FStar_Parser_AST.TAnnotated (_137_120))
in (FStar_Parser_AST.mk_binder _137_121 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 264 "FStar.Parser.ToSyntax.fst"
let t = (match ((let _137_122 = (unparen t)
in _137_122.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_52_390) -> begin
t
end
| _52_393 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level), t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end)
in (
# 267 "FStar.Parser.ToSyntax.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result)))
end))

# 270 "FStar.Parser.ToSyntax.fst"
let rec uncurry : FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term) = (fun bs t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (binders, t) -> begin
(uncurry (FStar_List.append bs binders) t)
end
| _52_403 -> begin
(bs, t)
end))

# 274 "FStar.Parser.ToSyntax.fst"
let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _52_407) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_52_413); FStar_Parser_AST.prange = _52_411}, _52_417) -> begin
true
end
| _52_421 -> begin
false
end))

# 279 "FStar.Parser.ToSyntax.fst"
let rec destruct_app_pattern : FStar_Parser_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 281 "FStar.Parser.ToSyntax.fst"
let _52_433 = (destruct_app_pattern env is_top_level p)
in (match (_52_433) with
| (name, args, _52_432) -> begin
(name, args, Some (t))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _52_438); FStar_Parser_AST.prange = _52_435}, args) when is_top_level -> begin
(let _137_136 = (let _137_135 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_137_135))
in (_137_136, args, None))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _52_449); FStar_Parser_AST.prange = _52_446}, args) -> begin
(FStar_Util.Inl (id), args, None)
end
| _52_457 -> begin
(FStar_All.failwith "Not an app pattern")
end))

# 290 "FStar.Parser.ToSyntax.fst"
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
| LocalBinder (_52_460) -> begin
_52_460
end))

# 292 "FStar.Parser.ToSyntax.fst"
let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_52_463) -> begin
_52_463
end))

# 293 "FStar.Parser.ToSyntax.fst"
let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun _52_6 -> (match (_52_6) with
| LocalBinder (a, aq) -> begin
(a, aq)
end
| _52_470 -> begin
(FStar_All.failwith "Impossible")
end))

# 296 "FStar.Parser.ToSyntax.fst"
let as_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_Parser_Env.env) = (fun env imp _52_7 -> (match (_52_7) with
| (None, k) -> begin
(let _137_173 = (FStar_Syntax_Syntax.null_binder k)
in (_137_173, env))
end
| (Some (a), k) -> begin
(
# 299 "FStar.Parser.ToSyntax.fst"
let _52_483 = (FStar_Parser_Env.push_bv env a)
in (match (_52_483) with
| (env, a) -> begin
(((
# 300 "FStar.Parser.ToSyntax.fst"
let _52_484 = a
in {FStar_Syntax_Syntax.ppname = _52_484.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_484.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}), (trans_aqual imp)), env)
end))
end))

# 302 "FStar.Parser.ToSyntax.fst"
type env_t =
FStar_Parser_Env.env

# 303 "FStar.Parser.ToSyntax.fst"
type lenv_t =
FStar_Syntax_Syntax.bv Prims.list

# 305 "FStar.Parser.ToSyntax.fst"
let mk_lb : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.letbinding = (fun _52_489 -> (match (_52_489) with
| (n, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))

# 306 "FStar.Parser.ToSyntax.fst"
let no_annot_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t None))

# 308 "FStar.Parser.ToSyntax.fst"
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
| FStar_Syntax_Syntax.Pat_cons (_52_510, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out _52_518 -> (match (_52_518) with
| (p, _52_517) -> begin
(let _137_219 = (pat_vars p)
in (FStar_Util.set_union out _137_219))
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
| _52_536 -> begin
(
# 331 "FStar.Parser.ToSyntax.fst"
let _52_539 = (FStar_Parser_Env.push_bv e x)
in (match (_52_539) with
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
| _52_548 -> begin
(
# 337 "FStar.Parser.ToSyntax.fst"
let _52_551 = (FStar_Parser_Env.push_bv e a)
in (match (_52_551) with
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
let _52_573 = (aux loc env p)
in (match (_52_573) with
| (loc, env, var, p, _52_572) -> begin
(
# 346 "FStar.Parser.ToSyntax.fst"
let _52_590 = (FStar_List.fold_left (fun _52_577 p -> (match (_52_577) with
| (loc, env, ps) -> begin
(
# 347 "FStar.Parser.ToSyntax.fst"
let _52_586 = (aux loc env p)
in (match (_52_586) with
| (loc, env, _52_582, p, _52_585) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_52_590) with
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
let _52_601 = (aux loc env p)
in (match (_52_601) with
| (loc, env', binder, p, imp) -> begin
(
# 354 "FStar.Parser.ToSyntax.fst"
let binder = (match (binder) with
| LetBinder (_52_603) -> begin
(FStar_All.failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(
# 357 "FStar.Parser.ToSyntax.fst"
let t = (let _137_249 = (close_fun env t)
in (desugar_term env _137_249))
in LocalBinder (((
# 358 "FStar.Parser.ToSyntax.fst"
let _52_610 = x
in {FStar_Syntax_Syntax.ppname = _52_610.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_610.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), aq)))
end)
in (loc, env', binder, p, imp))
end))
end
| FStar_Parser_AST.PatWild -> begin
(
# 362 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _137_250 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in (loc, env, LocalBinder ((x, None)), _137_250, false)))
end
| FStar_Parser_AST.PatConst (c) -> begin
(
# 366 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _137_251 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in (loc, env, LocalBinder ((x, None)), _137_251, false)))
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
let _52_629 = (resolvex loc env x)
in (match (_52_629) with
| (loc, env, xbv) -> begin
(let _137_252 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in (loc, env, LocalBinder ((xbv, aq)), _137_252, imp))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(
# 377 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_datacon env) l)
in (
# 378 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _137_253 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, []))))
in (loc, env, LocalBinder ((x, None)), _137_253, false))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _52_635}, args) -> begin
(
# 382 "FStar.Parser.ToSyntax.fst"
let _52_657 = (FStar_List.fold_right (fun arg _52_646 -> (match (_52_646) with
| (loc, env, args) -> begin
(
# 383 "FStar.Parser.ToSyntax.fst"
let _52_653 = (aux loc env arg)
in (match (_52_653) with
| (loc, env, _52_650, arg, imp) -> begin
(loc, env, ((arg, imp))::args)
end))
end)) args (loc, env, []))
in (match (_52_657) with
| (loc, env, args) -> begin
(
# 385 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_datacon env) l)
in (
# 386 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _137_256 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _137_256, false))))
end))
end
| FStar_Parser_AST.PatApp (_52_661) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(
# 392 "FStar.Parser.ToSyntax.fst"
let _52_681 = (FStar_List.fold_right (fun pat _52_669 -> (match (_52_669) with
| (loc, env, pats) -> begin
(
# 393 "FStar.Parser.ToSyntax.fst"
let _52_677 = (aux loc env pat)
in (match (_52_677) with
| (loc, env, _52_673, pat, _52_676) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_52_681) with
| (loc, env, pats) -> begin
(
# 395 "FStar.Parser.ToSyntax.fst"
let pat = (let _137_269 = (let _137_268 = (let _137_264 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _137_264))
in (let _137_267 = (let _137_266 = (let _137_265 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_137_265, []))
in FStar_Syntax_Syntax.Pat_cons (_137_266))
in (FStar_All.pipe_left _137_268 _137_267)))
in (FStar_List.fold_right (fun hd tl -> (
# 396 "FStar.Parser.ToSyntax.fst"
let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (let _137_263 = (let _137_262 = (let _137_261 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_137_261, ((hd, false))::((tl, false))::[]))
in FStar_Syntax_Syntax.Pat_cons (_137_262))
in (FStar_All.pipe_left (pos_r r) _137_263)))) pats _137_269))
in (
# 399 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (loc, env, LocalBinder ((x, None)), pat, false)))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(
# 403 "FStar.Parser.ToSyntax.fst"
let _52_707 = (FStar_List.fold_left (fun _52_694 p -> (match (_52_694) with
| (loc, env, pats) -> begin
(
# 404 "FStar.Parser.ToSyntax.fst"
let _52_703 = (aux loc env p)
in (match (_52_703) with
| (loc, env, _52_699, pat, _52_702) -> begin
(loc, env, ((pat, false))::pats)
end))
end)) (loc, env, []) args)
in (match (_52_707) with
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
| _52_714 -> begin
(FStar_All.failwith "impossible")
end)
in (
# 413 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _137_272 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _137_272, false)))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(
# 420 "FStar.Parser.ToSyntax.fst"
let _52_724 = (FStar_List.hd fields)
in (match (_52_724) with
| (f, _52_723) -> begin
(
# 421 "FStar.Parser.ToSyntax.fst"
let _52_728 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_52_728) with
| (record, _52_727) -> begin
(
# 422 "FStar.Parser.ToSyntax.fst"
let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _52_731 -> (match (_52_731) with
| (f, p) -> begin
(let _137_274 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.qualify_field_to_record env record) f)
in (_137_274, p))
end))))
in (
# 424 "FStar.Parser.ToSyntax.fst"
let args = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _52_736 -> (match (_52_736) with
| (f, _52_735) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _52_740 -> (match (_52_740) with
| (g, _52_739) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_52_743, p) -> begin
p
end)
end))))
in (
# 428 "FStar.Parser.ToSyntax.fst"
let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_Env.constrname)) p.FStar_Parser_AST.prange), args))) p.FStar_Parser_AST.prange)
in (
# 429 "FStar.Parser.ToSyntax.fst"
let _52_755 = (aux loc env app)
in (match (_52_755) with
| (env, e, b, p, _52_754) -> begin
(
# 430 "FStar.Parser.ToSyntax.fst"
let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(let _137_283 = (let _137_282 = (let _137_281 = (
# 431 "FStar.Parser.ToSyntax.fst"
let _52_760 = fv
in (let _137_280 = (let _137_279 = (let _137_278 = (let _137_277 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _137_277))
in FStar_Syntax_Syntax.Record_ctor (_137_278))
in Some (_137_279))
in {FStar_Syntax_Syntax.fv_name = _52_760.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = _52_760.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _137_280}))
in (_137_281, args))
in FStar_Syntax_Syntax.Pat_cons (_137_282))
in (FStar_All.pipe_left pos _137_283))
end
| _52_763 -> begin
p
end)
in (env, e, b, p, false))
end)))))
end))
end))
end))))
in (
# 435 "FStar.Parser.ToSyntax.fst"
let _52_772 = (aux [] env p)
in (match (_52_772) with
| (_52_766, env, b, p, _52_771) -> begin
(
# 436 "FStar.Parser.ToSyntax.fst"
let _52_773 = (let _137_284 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore _137_284))
in (env, b, p))
end)))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _52_780) -> begin
(let _137_290 = (let _137_289 = (let _137_288 = (FStar_Parser_Env.qualify env x)
in (_137_288, FStar_Syntax_Syntax.tun))
in LetBinder (_137_289))
in (env, _137_290, None))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _52_787); FStar_Parser_AST.prange = _52_784}, t) -> begin
(let _137_294 = (let _137_293 = (let _137_292 = (FStar_Parser_Env.qualify env x)
in (let _137_291 = (desugar_term env t)
in (_137_292, _137_291)))
in LetBinder (_137_293))
in (env, _137_294, None))
end
| _52_795 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern at the top-level", p.FStar_Parser_AST.prange))))
end)
end else begin
(
# 447 "FStar.Parser.ToSyntax.fst"
let _52_799 = (desugar_data_pat env p)
in (match (_52_799) with
| (env, binder, p) -> begin
(
# 448 "FStar.Parser.ToSyntax.fst"
let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| _52_807 -> begin
Some (p)
end)
in (env, binder, p))
end))
end)
and desugar_binding_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun _52_811 env pat -> (
# 457 "FStar.Parser.ToSyntax.fst"
let _52_819 = (desugar_data_pat env pat)
in (match (_52_819) with
| (env, _52_817, pat) -> begin
(env, pat)
end)))
and desugar_match_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (
# 463 "FStar.Parser.ToSyntax.fst"
let env = (
# 463 "FStar.Parser.ToSyntax.fst"
let _52_824 = env
in {FStar_Parser_Env.curmodule = _52_824.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _52_824.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _52_824.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.sigaccum = _52_824.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _52_824.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _52_824.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _52_824.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _52_824.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _52_824.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _52_824.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (
# 467 "FStar.Parser.ToSyntax.fst"
let env = (
# 467 "FStar.Parser.ToSyntax.fst"
let _52_829 = env
in {FStar_Parser_Env.curmodule = _52_829.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _52_829.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _52_829.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.sigaccum = _52_829.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _52_829.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _52_829.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _52_829.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _52_829.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _52_829.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _52_829.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (
# 471 "FStar.Parser.ToSyntax.fst"
let mk = (fun e -> (FStar_Syntax_Syntax.mk e None top.FStar_Parser_AST.range))
in (
# 472 "FStar.Parser.ToSyntax.fst"
let setpos = (fun e -> (
# 472 "FStar.Parser.ToSyntax.fst"
let _52_839 = e
in {FStar_Syntax_Syntax.n = _52_839.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _52_839.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _52_839.FStar_Syntax_Syntax.vars}))
in (match ((let _137_313 = (unparen top)
in _137_313.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (_52_843) -> begin
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
| FStar_Parser_AST.Op ("*", _52_863::_52_861::[]) when (let _137_314 = (op_as_term env 2 top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right _137_314 FStar_Option.isNone)) -> begin
(
# 490 "FStar.Parser.ToSyntax.fst"
let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", t1::t2::[]) -> begin
(
# 492 "FStar.Parser.ToSyntax.fst"
let rest = (flatten t2)
in (t1)::rest)
end
| _52_877 -> begin
(t)::[]
end))
in (
# 495 "FStar.Parser.ToSyntax.fst"
let targs = (let _137_320 = (let _137_317 = (unparen top)
in (flatten _137_317))
in (FStar_All.pipe_right _137_320 (FStar_List.map (fun t -> (let _137_319 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg _137_319))))))
in (
# 496 "FStar.Parser.ToSyntax.fst"
let tup = (let _137_321 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) _137_321))
in (mk (FStar_Syntax_Syntax.Tm_app ((tup, targs)))))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _137_322 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) a)
in (FStar_All.pipe_left setpos _137_322))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Unexpected operator: " s), top.FStar_Parser_AST.range))))
end
| Some (op) -> begin
(
# 506 "FStar.Parser.ToSyntax.fst"
let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _137_324 = (desugar_term env t)
in (_137_324, None)))))
in (mk (FStar_Syntax_Syntax.Tm_app ((op, args)))))
end)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _52_898; FStar_Ident.ident = _52_896; FStar_Ident.nsstr = _52_894; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _52_907; FStar_Ident.ident = _52_905; FStar_Ident.nsstr = _52_903; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _52_916; FStar_Ident.ident = _52_914; FStar_Ident.nsstr = _52_912; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _52_925; FStar_Ident.ident = _52_923; FStar_Ident.nsstr = _52_921; FStar_Ident.str = "True"}) -> begin
(let _137_325 = (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _137_325 FStar_Syntax_Syntax.Delta_constant None))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _52_934; FStar_Ident.ident = _52_932; FStar_Ident.nsstr = _52_930; FStar_Ident.str = "False"}) -> begin
(let _137_326 = (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _137_326 FStar_Syntax_Syntax.Delta_constant None))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(let _137_327 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (FStar_All.pipe_left setpos _137_327))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(
# 521 "FStar.Parser.ToSyntax.fst"
let _52_949 = (match ((FStar_Parser_Env.try_lookup_datacon env l)) with
| None -> begin
(let _137_328 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (_137_328, false))
end
| Some (head) -> begin
(let _137_329 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in (_137_329, true))
end)
in (match (_52_949) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| _52_952 -> begin
(
# 527 "FStar.Parser.ToSyntax.fst"
let args = (FStar_List.map (fun _52_955 -> (match (_52_955) with
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
let _52_983 = (FStar_List.fold_left (fun _52_966 b -> (match (_52_966) with
| (env, tparams, typs) -> begin
(
# 538 "FStar.Parser.ToSyntax.fst"
let _52_970 = (desugar_binder env b)
in (match (_52_970) with
| (xopt, t) -> begin
(
# 539 "FStar.Parser.ToSyntax.fst"
let _52_976 = (match (xopt) with
| None -> begin
(let _137_333 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (env, _137_333))
end
| Some (x) -> begin
(FStar_Parser_Env.push_bv env x)
end)
in (match (_52_976) with
| (env, x) -> begin
(let _137_337 = (let _137_336 = (let _137_335 = (let _137_334 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _137_334))
in (_137_335)::[])
in (FStar_List.append typs _137_336))
in (env, (FStar_List.append tparams ((((
# 543 "FStar.Parser.ToSyntax.fst"
let _52_977 = x
in {FStar_Syntax_Syntax.ppname = _52_977.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_977.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), None))::[])), _137_337))
end))
end))
end)) (env, [], []) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_52_983) with
| (env, _52_981, targs) -> begin
(
# 546 "FStar.Parser.ToSyntax.fst"
let tup = (let _137_338 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) _137_338))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app ((tup, targs)))))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(
# 550 "FStar.Parser.ToSyntax.fst"
let _52_991 = (uncurry binders t)
in (match (_52_991) with
| (bs, t) -> begin
(
# 551 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun env bs _52_8 -> (match (_52_8) with
| [] -> begin
(
# 553 "FStar.Parser.ToSyntax.fst"
let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (let _137_345 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos _137_345)))
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
let _52_1005 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_52_1005) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_binder env b)) with
| (None, _52_1012) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(
# 568 "FStar.Parser.ToSyntax.fst"
let _52_1020 = (as_binder env None b)
in (match (_52_1020) with
| ((x, _52_1017), env) -> begin
(
# 569 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env f)
in (let _137_346 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos _137_346)))
end))
end)
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(
# 574 "FStar.Parser.ToSyntax.fst"
let _52_1040 = (FStar_List.fold_left (fun _52_1028 pat -> (match (_52_1028) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (_52_1031, t) -> begin
(let _137_350 = (let _137_349 = (free_type_vars env t)
in (FStar_List.append _137_349 ftvs))
in (env, _137_350))
end
| _52_1036 -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_52_1040) with
| (_52_1038, ftv) -> begin
(
# 578 "FStar.Parser.ToSyntax.fst"
let ftv = (sort_ftv ftv)
in (
# 579 "FStar.Parser.ToSyntax.fst"
let binders = (let _137_352 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar ((a, Some (FStar_Parser_AST.Implicit)))) top.FStar_Parser_AST.range))))
in (FStar_List.append _137_352 binders))
in (
# 588 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun env bs sc_pat_opt _52_9 -> (match (_52_9) with
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
let body = (let _137_362 = (let _137_361 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right _137_361 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close _137_362 body))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((sc, ((pat, None, body))::[]))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (let _137_363 = (no_annot_abs (FStar_List.rev bs) body)
in (setpos _137_363))))
end
| p::rest -> begin
(
# 599 "FStar.Parser.ToSyntax.fst"
let _52_1064 = (desugar_binding_pat env p)
in (match (_52_1064) with
| (env, b, pat) -> begin
(
# 600 "FStar.Parser.ToSyntax.fst"
let _52_1115 = (match (b) with
| LetBinder (_52_1066) -> begin
(FStar_All.failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(
# 603 "FStar.Parser.ToSyntax.fst"
let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _52_1074) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _137_365 = (let _137_364 = (FStar_Syntax_Syntax.bv_to_name x)
in (_137_364, p))
in Some (_137_365))
end
| (Some (p), Some (sc, p')) -> begin
(match ((sc.FStar_Syntax_Syntax.n, p'.FStar_Syntax_Syntax.v)) with
| (FStar_Syntax_Syntax.Tm_name (_52_1088), _52_1091) -> begin
(
# 609 "FStar.Parser.ToSyntax.fst"
let tup2 = (let _137_366 = (FStar_Syntax_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _137_366 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (
# 610 "FStar.Parser.ToSyntax.fst"
let sc = (let _137_374 = (let _137_373 = (let _137_372 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (let _137_371 = (let _137_370 = (FStar_Syntax_Syntax.as_arg sc)
in (let _137_369 = (let _137_368 = (let _137_367 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _137_367))
in (_137_368)::[])
in (_137_370)::_137_369))
in (_137_372, _137_371)))
in FStar_Syntax_Syntax.Tm_app (_137_373))
in (FStar_Syntax_Syntax.mk _137_374 None top.FStar_Parser_AST.range))
in (
# 611 "FStar.Parser.ToSyntax.fst"
let p = (let _137_375 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tup2, ((p', false))::((p, false))::[]))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _137_375))
in Some ((sc, p)))))
end
| (FStar_Syntax_Syntax.Tm_app (_52_1097, args), FStar_Syntax_Syntax.Pat_cons (_52_1102, pats)) -> begin
(
# 614 "FStar.Parser.ToSyntax.fst"
let tupn = (let _137_376 = (FStar_Syntax_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _137_376 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (
# 615 "FStar.Parser.ToSyntax.fst"
let sc = (let _137_383 = (let _137_382 = (let _137_381 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (let _137_380 = (let _137_379 = (let _137_378 = (let _137_377 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _137_377))
in (_137_378)::[])
in (FStar_List.append args _137_379))
in (_137_381, _137_380)))
in FStar_Syntax_Syntax.Tm_app (_137_382))
in (mk _137_383))
in (
# 616 "FStar.Parser.ToSyntax.fst"
let p = (let _137_384 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tupn, (FStar_List.append pats (((p, false))::[]))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _137_384))
in Some ((sc, p)))))
end
| _52_1111 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((x, aq), sc_pat_opt))
end)
in (match (_52_1115) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _52_1119; FStar_Parser_AST.level = _52_1117}, phi, _52_1125) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(
# 627 "FStar.Parser.ToSyntax.fst"
let phi = (desugar_formula env phi)
in (let _137_392 = (let _137_391 = (let _137_390 = (FStar_Syntax_Syntax.fvar a FStar_Syntax_Syntax.Delta_equational None)
in (let _137_389 = (let _137_388 = (FStar_Syntax_Syntax.as_arg phi)
in (let _137_387 = (let _137_386 = (let _137_385 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _137_385))
in (_137_386)::[])
in (_137_388)::_137_387))
in (_137_390, _137_389)))
in FStar_Syntax_Syntax.Tm_app (_137_391))
in (mk _137_392)))
end
| FStar_Parser_AST.App (_52_1130) -> begin
(
# 633 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun args e -> (match ((let _137_397 = (unparen e)
in _137_397.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(
# 635 "FStar.Parser.ToSyntax.fst"
let arg = (let _137_398 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _137_398))
in (aux ((arg)::args) e))
end
| _52_1142 -> begin
(
# 638 "FStar.Parser.ToSyntax.fst"
let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app ((head, args)))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _137_401 = (let _137_400 = (let _137_399 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range), t1))::[], t2))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in (_137_399, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))
in FStar_Syntax_Syntax.Tm_meta (_137_400))
in (mk _137_401))
end
| FStar_Parser_AST.Let (is_rec, (pat, _snd)::_tl, body) -> begin
(
# 647 "FStar.Parser.ToSyntax.fst"
let ds_let_rec_or_app = (fun _52_1158 -> (match (()) with
| () -> begin
(
# 648 "FStar.Parser.ToSyntax.fst"
let bindings = ((pat, _snd))::_tl
in (
# 649 "FStar.Parser.ToSyntax.fst"
let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _52_1162 -> (match (_52_1162) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _137_405 = (destruct_app_pattern env top_level p)
in (_137_405, def))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _137_406 = (destruct_app_pattern env top_level p)
in (_137_406, def))
end
| _52_1168 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _52_1173); FStar_Parser_AST.prange = _52_1170}, t) -> begin
if top_level then begin
(let _137_409 = (let _137_408 = (let _137_407 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_137_407))
in (_137_408, [], Some (t)))
in (_137_409, def))
end else begin
((FStar_Util.Inl (id), [], Some (t)), def)
end
end
| FStar_Parser_AST.PatVar (id, _52_1182) -> begin
if top_level then begin
(let _137_412 = (let _137_411 = (let _137_410 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_137_410))
in (_137_411, [], None))
in (_137_412, def))
end else begin
((FStar_Util.Inl (id), [], None), def)
end
end
| _52_1186 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected let binding", p.FStar_Parser_AST.prange))))
end)
end)
end
end))))
in (
# 666 "FStar.Parser.ToSyntax.fst"
let _52_1215 = (FStar_List.fold_left (fun _52_1191 _52_1200 -> (match ((_52_1191, _52_1200)) with
| ((env, fnames, rec_bindings), ((f, _52_1194, _52_1196), _52_1199)) -> begin
(
# 668 "FStar.Parser.ToSyntax.fst"
let _52_1211 = (match (f) with
| FStar_Util.Inl (x) -> begin
(
# 670 "FStar.Parser.ToSyntax.fst"
let _52_1205 = (FStar_Parser_Env.push_bv env x)
in (match (_52_1205) with
| (env, xx) -> begin
(let _137_416 = (let _137_415 = (FStar_Syntax_Syntax.mk_binder xx)
in (_137_415)::rec_bindings)
in (env, FStar_Util.Inl (xx), _137_416))
end))
end
| FStar_Util.Inr (l) -> begin
(let _137_417 = (FStar_Parser_Env.push_top_level_rec_binding env l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in (_137_417, FStar_Util.Inr (l), rec_bindings))
end)
in (match (_52_1211) with
| (env, lbname, rec_bindings) -> begin
(env, (lbname)::fnames, rec_bindings)
end))
end)) (env, [], []) funs)
in (match (_52_1215) with
| (env', fnames, rec_bindings) -> begin
(
# 676 "FStar.Parser.ToSyntax.fst"
let fnames = (FStar_List.rev fnames)
in (
# 678 "FStar.Parser.ToSyntax.fst"
let desugar_one_def = (fun env lbname _52_1226 -> (match (_52_1226) with
| ((_52_1221, args, result_t), def) -> begin
(
# 679 "FStar.Parser.ToSyntax.fst"
let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _137_424 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed ((def, t))) _137_424 FStar_Parser_AST.Expr))
end)
in (
# 682 "FStar.Parser.ToSyntax.fst"
let def = (match (args) with
| [] -> begin
def
end
| _52_1233 -> begin
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
(let _137_426 = (let _137_425 = (incr_delta_qualifier body)
in (FStar_Syntax_Syntax.lid_as_fv l _137_425 None))
in FStar_Util.Inr (_137_426))
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
in (let _137_429 = (let _137_428 = (let _137_427 = (FStar_Syntax_Subst.close rec_bindings body)
in ((is_rec, lbs), _137_427))
in FStar_Syntax_Syntax.Tm_let (_137_428))
in (FStar_All.pipe_left mk _137_429))))))
end))))
end))
in (
# 696 "FStar.Parser.ToSyntax.fst"
let ds_non_rec = (fun pat t1 t2 -> (
# 697 "FStar.Parser.ToSyntax.fst"
let t1 = (desugar_term env t1)
in (
# 698 "FStar.Parser.ToSyntax.fst"
let _52_1252 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_52_1252) with
| (env, binder, pat) -> begin
(match (binder) with
| LetBinder (l, t) -> begin
(
# 701 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env t2)
in (
# 702 "FStar.Parser.ToSyntax.fst"
let fv = (let _137_436 = (incr_delta_qualifier t1)
in (FStar_Syntax_Syntax.lid_as_fv l _137_436 None))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]), body))))))
end
| LocalBinder (x, _52_1261) -> begin
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
(let _137_441 = (let _137_440 = (let _137_439 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _137_438 = (let _137_437 = (FStar_Syntax_Util.branch (pat, None, body))
in (_137_437)::[])
in (_137_439, _137_438)))
in FStar_Syntax_Syntax.Tm_match (_137_440))
in (FStar_Syntax_Syntax.mk _137_441 None body.FStar_Syntax_Syntax.pos))
end)
in (let _137_446 = (let _137_445 = (let _137_444 = (let _137_443 = (let _137_442 = (FStar_Syntax_Syntax.mk_binder x)
in (_137_442)::[])
in (FStar_Syntax_Subst.close _137_443 body))
in ((false, ((mk_lb (FStar_Util.Inl (x), x.FStar_Syntax_Syntax.sort, t1)))::[]), _137_444))
in FStar_Syntax_Syntax.Tm_let (_137_445))
in (FStar_All.pipe_left mk _137_446))))
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
in (let _137_457 = (let _137_456 = (let _137_455 = (desugar_term env t1)
in (let _137_454 = (let _137_453 = (let _137_448 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (let _137_447 = (desugar_term env t2)
in (_137_448, None, _137_447)))
in (let _137_452 = (let _137_451 = (let _137_450 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (let _137_449 = (desugar_term env t3)
in (_137_450, None, _137_449)))
in (_137_451)::[])
in (_137_453)::_137_452))
in (_137_455, _137_454)))
in FStar_Syntax_Syntax.Tm_match (_137_456))
in (mk _137_457)))
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
let desugar_branch = (fun _52_1301 -> (match (_52_1301) with
| (pat, wopt, b) -> begin
(
# 736 "FStar.Parser.ToSyntax.fst"
let _52_1304 = (desugar_match_pat env pat)
in (match (_52_1304) with
| (env, pat) -> begin
(
# 737 "FStar.Parser.ToSyntax.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _137_460 = (desugar_term env e)
in Some (_137_460))
end)
in (
# 740 "FStar.Parser.ToSyntax.fst"
let b = (desugar_term env b)
in (FStar_Syntax_Util.branch (pat, wopt, b))))
end))
end))
in (let _137_464 = (let _137_463 = (let _137_462 = (desugar_term env e)
in (let _137_461 = (FStar_List.map desugar_branch branches)
in (_137_462, _137_461)))
in FStar_Syntax_Syntax.Tm_match (_137_463))
in (FStar_All.pipe_left mk _137_464)))
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
in (let _137_467 = (let _137_466 = (let _137_465 = (desugar_term env e)
in (_137_465, annot, None))
in FStar_Syntax_Syntax.Tm_ascribed (_137_466))
in (FStar_All.pipe_left mk _137_467)))))
end
| FStar_Parser_AST.Record (_52_1318, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected empty record", top.FStar_Parser_AST.range))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(
# 756 "FStar.Parser.ToSyntax.fst"
let _52_1329 = (FStar_List.hd fields)
in (match (_52_1329) with
| (f, _52_1328) -> begin
(
# 757 "FStar.Parser.ToSyntax.fst"
let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (
# 758 "FStar.Parser.ToSyntax.fst"
let _52_1335 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_52_1335) with
| (record, _52_1334) -> begin
(
# 759 "FStar.Parser.ToSyntax.fst"
let get_field = (fun xopt f -> (
# 760 "FStar.Parser.ToSyntax.fst"
let fn = f.FStar_Ident.ident
in (
# 761 "FStar.Parser.ToSyntax.fst"
let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _52_1343 -> (match (_52_1343) with
| (g, _52_1342) -> begin
(
# 762 "FStar.Parser.ToSyntax.fst"
let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_52_1347, e) -> begin
(let _137_475 = (qfn fn)
in (_137_475, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _137_478 = (let _137_477 = (let _137_476 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in (_137_476, top.FStar_Parser_AST.range))
in FStar_Syntax_Syntax.Error (_137_477))
in (Prims.raise _137_478))
end
| Some (x) -> begin
(let _137_479 = (qfn fn)
in (_137_479, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Project ((x, f))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end))))
in (
# 773 "FStar.Parser.ToSyntax.fst"
let recterm = (match (eopt) with
| None -> begin
(let _137_484 = (let _137_483 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _52_1359 -> (match (_52_1359) with
| (f, _52_1358) -> begin
(let _137_482 = (let _137_481 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _137_481))
in (_137_482, FStar_Parser_AST.Nothing))
end))))
in (record.FStar_Parser_Env.constrname, _137_483))
in FStar_Parser_AST.Construct (_137_484))
end
| Some (e) -> begin
(
# 780 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (
# 781 "FStar.Parser.ToSyntax.fst"
let xterm = (let _137_486 = (let _137_485 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_137_485))
in (FStar_Parser_AST.mk_term _137_486 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (
# 782 "FStar.Parser.ToSyntax.fst"
let record = (let _137_489 = (let _137_488 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _52_1367 -> (match (_52_1367) with
| (f, _52_1366) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _137_488))
in FStar_Parser_AST.Record (_137_489))
in FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar ((x, None))) x.FStar_Ident.idRange), e))::[], (FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level))))))
end)
in (
# 785 "FStar.Parser.ToSyntax.fst"
let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (
# 786 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _52_1383; FStar_Syntax_Syntax.pos = _52_1381; FStar_Syntax_Syntax.vars = _52_1379}, args); FStar_Syntax_Syntax.tk = _52_1377; FStar_Syntax_Syntax.pos = _52_1375; FStar_Syntax_Syntax.vars = _52_1373}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(
# 789 "FStar.Parser.ToSyntax.fst"
let e = (let _137_497 = (let _137_496 = (let _137_495 = (let _137_494 = (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos)
in (let _137_493 = (let _137_492 = (let _137_491 = (let _137_490 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _137_490))
in FStar_Syntax_Syntax.Record_ctor (_137_491))
in Some (_137_492))
in (FStar_Syntax_Syntax.fvar _137_494 FStar_Syntax_Syntax.Delta_constant _137_493)))
in (_137_495, args))
in FStar_Syntax_Syntax.Tm_app (_137_496))
in (FStar_All.pipe_left mk _137_497))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end
| _52_1397 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(
# 797 "FStar.Parser.ToSyntax.fst"
let _52_1404 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_projector_by_field_name env) f)
in (match (_52_1404) with
| (fieldname, is_rec) -> begin
(
# 798 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env e)
in (
# 799 "FStar.Parser.ToSyntax.fst"
let fn = (
# 800 "FStar.Parser.ToSyntax.fst"
let _52_1409 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_52_1409) with
| (ns, _52_1408) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (
# 802 "FStar.Parser.ToSyntax.fst"
let qual = if is_rec then begin
Some (FStar_Syntax_Syntax.Record_projector (fn))
end else begin
None
end
in (let _137_503 = (let _137_502 = (let _137_501 = (let _137_498 = (FStar_Ident.set_lid_range fieldname (FStar_Ident.range_of_lid f))
in (FStar_Syntax_Syntax.fvar _137_498 FStar_Syntax_Syntax.Delta_equational qual))
in (let _137_500 = (let _137_499 = (FStar_Syntax_Syntax.as_arg e)
in (_137_499)::[])
in (_137_501, _137_500)))
in FStar_Syntax_Syntax.Tm_app (_137_502))
in (FStar_All.pipe_left mk _137_503)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| _52_1419 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _52_1421 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_args : FStar_Parser_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun _52_1426 -> (match (_52_1426) with
| (a, imp) -> begin
(let _137_507 = (desugar_term env a)
in (arg_withimp_e imp _137_507))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r default_ok env t -> (
# 819 "FStar.Parser.ToSyntax.fst"
let fail = (fun msg -> (Prims.raise (FStar_Syntax_Syntax.Error ((msg, r)))))
in (
# 820 "FStar.Parser.ToSyntax.fst"
let is_requires = (fun _52_1438 -> (match (_52_1438) with
| (t, _52_1437) -> begin
(match ((let _137_515 = (unparen t)
in _137_515.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Requires (_52_1440) -> begin
true
end
| _52_1443 -> begin
false
end)
end))
in (
# 823 "FStar.Parser.ToSyntax.fst"
let is_ensures = (fun _52_1448 -> (match (_52_1448) with
| (t, _52_1447) -> begin
(match ((let _137_518 = (unparen t)
in _137_518.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ensures (_52_1450) -> begin
true
end
| _52_1453 -> begin
false
end)
end))
in (
# 826 "FStar.Parser.ToSyntax.fst"
let is_app = (fun head _52_1459 -> (match (_52_1459) with
| (t, _52_1458) -> begin
(match ((let _137_523 = (unparen t)
in _137_523.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _52_1463; FStar_Parser_AST.level = _52_1461}, _52_1468, _52_1470) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| _52_1474 -> begin
false
end)
end))
in (
# 829 "FStar.Parser.ToSyntax.fst"
let pre_process_comp_typ = (fun t -> (
# 830 "FStar.Parser.ToSyntax.fst"
let _52_1479 = (head_and_args t)
in (match (_52_1479) with
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
(let _137_526 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_name env) l)
in (_137_526, args))
end
| FStar_Parser_AST.Name (l) when ((let _137_527 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _137_527 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(let _137_528 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in (_137_528, args))
end
| FStar_Parser_AST.Name (l) when ((let _137_529 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _137_529 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(let _137_530 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)
in (_137_530, args))
end
| FStar_Parser_AST.Name (l) when ((((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) && default_ok) -> begin
(let _137_531 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in (_137_531, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _52_1507 when default_ok -> begin
(let _137_532 = (FStar_Ident.set_lid_range env.FStar_Parser_Env.default_result_effect head.FStar_Parser_AST.range)
in (_137_532, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _52_1509 -> begin
(let _137_534 = (let _137_533 = (FStar_Parser_AST.term_to_string t)
in (FStar_Util.format1 "%s is not an effect" _137_533))
in (fail _137_534))
end)
end)))
in (
# 873 "FStar.Parser.ToSyntax.fst"
let _52_1512 = (pre_process_comp_typ t)
in (match (_52_1512) with
| (eff, args) -> begin
(
# 874 "FStar.Parser.ToSyntax.fst"
let _52_1513 = if ((FStar_List.length args) = 0) then begin
(let _137_536 = (let _137_535 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" _137_535))
in (fail _137_536))
end else begin
()
end
in (
# 876 "FStar.Parser.ToSyntax.fst"
let _52_1517 = (let _137_538 = (FStar_List.hd args)
in (let _137_537 = (FStar_List.tl args)
in (_137_538, _137_537)))
in (match (_52_1517) with
| (result_arg, rest) -> begin
(
# 877 "FStar.Parser.ToSyntax.fst"
let result_typ = (desugar_typ env (Prims.fst result_arg))
in (
# 878 "FStar.Parser.ToSyntax.fst"
let rest = (desugar_args env rest)
in (
# 879 "FStar.Parser.ToSyntax.fst"
let _52_1542 = (FStar_All.pipe_right rest (FStar_List.partition (fun _52_1523 -> (match (_52_1523) with
| (t, _52_1522) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _52_1529; FStar_Syntax_Syntax.pos = _52_1527; FStar_Syntax_Syntax.vars = _52_1525}, _52_1534::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| _52_1539 -> begin
false
end)
end))))
in (match (_52_1542) with
| (dec, rest) -> begin
(
# 885 "FStar.Parser.ToSyntax.fst"
let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _52_1546 -> (match (_52_1546) with
| (t, _52_1545) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_52_1548, (arg, _52_1551)::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| _52_1557 -> begin
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
let pattern = (let _137_542 = (let _137_541 = (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _137_541 FStar_Syntax_Syntax.Delta_constant None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _137_542 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app nil (((pattern, Some (FStar_Syntax_Syntax.imp_tag)))::[]) None pat.FStar_Syntax_Syntax.pos)))
end
| _52_1572 -> begin
pat
end)
in (let _137_546 = (let _137_545 = (let _137_544 = (let _137_543 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((pat, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)))) None pat.FStar_Syntax_Syntax.pos)
in (_137_543, aq))
in (_137_544)::[])
in (ens)::_137_545)
in (req)::_137_546))
end
| _52_1575 -> begin
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
| _52_1587 -> begin
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
let _52_1594 = t
in {FStar_Syntax_Syntax.n = _52_1594.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _52_1594.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _52_1594.FStar_Syntax_Syntax.vars}))
in (
# 933 "FStar.Parser.ToSyntax.fst"
let desugar_quant = (fun q b pats body -> (
# 934 "FStar.Parser.ToSyntax.fst"
let tk = (desugar_binder env (
# 934 "FStar.Parser.ToSyntax.fst"
let _52_1601 = b
in {FStar_Parser_AST.b = _52_1601.FStar_Parser_AST.b; FStar_Parser_AST.brange = _52_1601.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _52_1601.FStar_Parser_AST.aqual}))
in (
# 935 "FStar.Parser.ToSyntax.fst"
let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _137_581 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _137_581)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(
# 938 "FStar.Parser.ToSyntax.fst"
let _52_1615 = (FStar_Parser_Env.push_bv env a)
in (match (_52_1615) with
| (env, a) -> begin
(
# 939 "FStar.Parser.ToSyntax.fst"
let a = (
# 939 "FStar.Parser.ToSyntax.fst"
let _52_1616 = a
in {FStar_Syntax_Syntax.ppname = _52_1616.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_1616.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
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
| _52_1623 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((body, FStar_Syntax_Syntax.Meta_pattern (pats)))))
end)
in (
# 945 "FStar.Parser.ToSyntax.fst"
let body = (let _137_584 = (let _137_583 = (let _137_582 = (FStar_Syntax_Syntax.mk_binder a)
in (_137_582)::[])
in (no_annot_abs _137_583 body))
in (FStar_All.pipe_left setpos _137_584))
in (let _137_590 = (let _137_589 = (let _137_588 = (let _137_585 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Syntax_Syntax.fvar _137_585 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (let _137_587 = (let _137_586 = (FStar_Syntax_Syntax.as_arg body)
in (_137_586)::[])
in (_137_588, _137_587)))
in FStar_Syntax_Syntax.Tm_app (_137_589))
in (FStar_All.pipe_left mk _137_590)))))))
end))
end
| _52_1627 -> begin
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
let body = (let _137_605 = (q (rest, pats, body))
in (let _137_604 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _137_605 _137_604 FStar_Parser_AST.Formula)))
in (let _137_606 = (q ((b)::[], [], body))
in (FStar_Parser_AST.mk_term _137_606 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _52_1641 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _137_607 = (unparen f)
in _137_607.FStar_Parser_AST.tm)) with
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
in (let _137_609 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _137_609)))
end
| FStar_Parser_AST.QExists (_1::_2::_3, pats, body) -> begin
(
# 970 "FStar.Parser.ToSyntax.fst"
let binders = (_1)::(_2)::_3
in (let _137_611 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _137_611)))
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
| _52_1699 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (
# 985 "FStar.Parser.ToSyntax.fst"
let _52_1723 = (FStar_List.fold_left (fun _52_1704 b -> (match (_52_1704) with
| (env, out) -> begin
(
# 986 "FStar.Parser.ToSyntax.fst"
let tk = (desugar_binder env (
# 986 "FStar.Parser.ToSyntax.fst"
let _52_1706 = b
in {FStar_Parser_AST.b = _52_1706.FStar_Parser_AST.b; FStar_Parser_AST.brange = _52_1706.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _52_1706.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(
# 989 "FStar.Parser.ToSyntax.fst"
let _52_1715 = (FStar_Parser_Env.push_bv env a)
in (match (_52_1715) with
| (env, a) -> begin
(
# 990 "FStar.Parser.ToSyntax.fst"
let a = (
# 990 "FStar.Parser.ToSyntax.fst"
let _52_1716 = a
in {FStar_Syntax_Syntax.ppname = _52_1716.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_1716.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (env, ((a, (trans_aqual b.FStar_Parser_AST.aqual)))::out))
end))
end
| _52_1720 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected binder", b.FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_52_1723) with
| (env, tpars) -> begin
(env, (FStar_List.rev tpars))
end)))
and desugar_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(let _137_618 = (desugar_typ env t)
in (Some (x), _137_618))
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _137_619 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None x.FStar_Ident.idRange)
in (Some (x), _137_619))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _137_620 = (desugar_typ env t)
in (None, _137_620))
end
| FStar_Parser_AST.Variable (x) -> begin
(Some (x), FStar_Syntax_Syntax.tun)
end))

# 1002 "FStar.Parser.ToSyntax.fst"
let mk_data_discriminators : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  FStar_Ident.lid  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun quals env t tps k datas -> (
# 1003 "FStar.Parser.ToSyntax.fst"
let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_Env.iface) || env.FStar_Parser_Env.admitted_iface) then begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (
# 1006 "FStar.Parser.ToSyntax.fst"
let binders = (let _137_636 = (let _137_635 = (FStar_Syntax_Util.arrow_formals k)
in (Prims.fst _137_635))
in (FStar_List.append tps _137_636))
in (
# 1007 "FStar.Parser.ToSyntax.fst"
let p = (FStar_Ident.range_of_lid t)
in (
# 1008 "FStar.Parser.ToSyntax.fst"
let _52_1750 = (FStar_Syntax_Util.args_of_binders binders)
in (match (_52_1750) with
| (binders, args) -> begin
(
# 1009 "FStar.Parser.ToSyntax.fst"
let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _52_1754 -> (match (_52_1754) with
| (x, _52_1753) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
in (
# 1010 "FStar.Parser.ToSyntax.fst"
let binders = (let _137_642 = (let _137_641 = (let _137_640 = (let _137_639 = (let _137_638 = (FStar_Syntax_Syntax.lid_as_fv t FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _137_638))
in (FStar_Syntax_Syntax.mk_Tm_app _137_639 args None p))
in (FStar_All.pipe_left FStar_Syntax_Syntax.null_binder _137_640))
in (_137_641)::[])
in (FStar_List.append imp_binders _137_642))
in (
# 1011 "FStar.Parser.ToSyntax.fst"
let disc_type = (let _137_645 = (let _137_644 = (let _137_643 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _137_643))
in (FStar_Syntax_Syntax.mk_Total _137_644))
in (FStar_Syntax_Util.arrow binders _137_645))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (
# 1013 "FStar.Parser.ToSyntax.fst"
let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (let _137_648 = (let _137_647 = (quals ((FStar_Syntax_Syntax.Logic)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in (disc_name, [], disc_type, _137_647, (FStar_Ident.range_of_lid disc_name)))
in FStar_Syntax_Syntax.Sig_declare_typ (_137_648)))))))))
end))))))

# 1016 "FStar.Parser.ToSyntax.fst"
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
let tps = (FStar_List.map2 (fun _52_1778 _52_1782 -> (match ((_52_1778, _52_1782)) with
| ((_52_1776, imp), (x, _52_1781)) -> begin
(x, imp)
end)) inductive_tps imp_tps)
in (
# 1021 "FStar.Parser.ToSyntax.fst"
let _52_1883 = (
# 1022 "FStar.Parser.ToSyntax.fst"
let _52_1786 = (FStar_Syntax_Util.head_and_args t)
in (match (_52_1786) with
| (head, args0) -> begin
(
# 1023 "FStar.Parser.ToSyntax.fst"
let args = (
# 1024 "FStar.Parser.ToSyntax.fst"
let rec arguments = (fun tps args -> (match ((tps, args)) with
| ([], _52_1792) -> begin
args
end
| (_52_1795, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Not enough arguments to type", (FStar_Ident.range_of_lid lid)))))
end
| ((_52_1800, Some (FStar_Syntax_Syntax.Implicit (_52_1802)))::tps', (_52_1809, Some (FStar_Syntax_Syntax.Implicit (_52_1811)))::args') -> begin
(arguments tps' args')
end
| ((_52_1819, Some (FStar_Syntax_Syntax.Implicit (_52_1821)))::tps', (_52_1829, _52_1831)::_52_1827) -> begin
(arguments tps' args)
end
| ((_52_1838, _52_1840)::_52_1836, (a, Some (FStar_Syntax_Syntax.Implicit (_52_1847)))::_52_1844) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected implicit annotation on argument", a.FStar_Syntax_Syntax.pos))))
end
| ((_52_1855, _52_1857)::tps', (_52_1862, _52_1864)::args') -> begin
(arguments tps' args')
end))
in (arguments inductive_tps args0))
in (
# 1033 "FStar.Parser.ToSyntax.fst"
let indices = (FStar_All.pipe_right args (FStar_List.map (fun _52_1869 -> (let _137_680 = (FStar_Syntax_Syntax.new_bv (Some (p)) FStar_Syntax_Syntax.tun)
in (FStar_All.pipe_right _137_680 FStar_Syntax_Syntax.mk_binder)))))
in (
# 1034 "FStar.Parser.ToSyntax.fst"
let arg_typ = (let _137_685 = (let _137_681 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _137_681))
in (let _137_684 = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _52_1874 -> (match (_52_1874) with
| (x, imp) -> begin
(let _137_683 = (FStar_Syntax_Syntax.bv_to_name x)
in (_137_683, imp))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app _137_685 _137_684 None p)))
in (
# 1036 "FStar.Parser.ToSyntax.fst"
let arg_binder = if (not (refine_domain)) then begin
(let _137_686 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder _137_686))
end else begin
(
# 1039 "FStar.Parser.ToSyntax.fst"
let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (
# 1040 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p)) arg_typ)
in (let _137_695 = (
# 1041 "FStar.Parser.ToSyntax.fst"
let _52_1878 = (projectee arg_typ)
in (let _137_694 = (let _137_693 = (let _137_692 = (let _137_691 = (let _137_687 = (FStar_Ident.set_lid_range disc_name p)
in (FStar_Syntax_Syntax.fvar _137_687 FStar_Syntax_Syntax.Delta_equational None))
in (let _137_690 = (let _137_689 = (let _137_688 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _137_688))
in (_137_689)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _137_691 _137_690 None p)))
in (FStar_Syntax_Util.b2t _137_692))
in (FStar_Syntax_Util.refine x _137_693))
in {FStar_Syntax_Syntax.ppname = _52_1878.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_1878.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _137_694}))
in (FStar_Syntax_Syntax.mk_binder _137_695))))
end
in (arg_binder, indices)))))
end))
in (match (_52_1883) with
| (arg_binder, indices) -> begin
(
# 1045 "FStar.Parser.ToSyntax.fst"
let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder))
in (
# 1046 "FStar.Parser.ToSyntax.fst"
let imp_binders = (let _137_697 = (FStar_All.pipe_right indices (FStar_List.map (fun _52_1888 -> (match (_52_1888) with
| (x, _52_1887) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
in (FStar_List.append imp_tps _137_697))
in (
# 1047 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (
# 1049 "FStar.Parser.ToSyntax.fst"
let arg = (FStar_Syntax_Util.arg_of_non_null_binder arg_binder)
in (
# 1051 "FStar.Parser.ToSyntax.fst"
let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _52_1896 -> (match (_52_1896) with
| (a, _52_1895) -> begin
(
# 1052 "FStar.Parser.ToSyntax.fst"
let _52_1900 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (_52_1900) with
| (field_name, _52_1899) -> begin
(
# 1053 "FStar.Parser.ToSyntax.fst"
let proj = (let _137_701 = (let _137_700 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.fv_to_tm _137_700))
in (FStar_Syntax_Syntax.mk_Tm_app _137_701 ((arg)::[]) None p))
in FStar_Syntax_Syntax.NT ((a, proj)))
end))
end))))
in (
# 1056 "FStar.Parser.ToSyntax.fst"
let ntps = (FStar_List.length tps)
in (
# 1057 "FStar.Parser.ToSyntax.fst"
let all_params = (FStar_List.append imp_tps fields)
in (let _137_737 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _52_1909 -> (match (_52_1909) with
| (x, _52_1908) -> begin
(
# 1060 "FStar.Parser.ToSyntax.fst"
let _52_1913 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_52_1913) with
| (field_name, _52_1912) -> begin
(
# 1061 "FStar.Parser.ToSyntax.fst"
let t = (let _137_705 = (let _137_704 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total _137_704))
in (FStar_Syntax_Util.arrow binders _137_705))
in (
# 1062 "FStar.Parser.ToSyntax.fst"
let only_decl = (((let _137_706 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _137_706)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _137_708 = (let _137_707 = (FStar_Parser_Env.current_module env)
in _137_707.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _137_708)))
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
let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _52_1925 -> (match (_52_1925) with
| (x, imp) -> begin
(
# 1074 "FStar.Parser.ToSyntax.fst"
let b = (FStar_Syntax_Syntax.is_implicit imp)
in if ((i + ntps) = j) then begin
(let _137_713 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in (_137_713, b))
end else begin
if (b && (j < ntps)) then begin
(let _137_717 = (let _137_716 = (let _137_715 = (let _137_714 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (_137_714, FStar_Syntax_Syntax.tun))
in FStar_Syntax_Syntax.Pat_dot_term (_137_715))
in (pos _137_716))
in (_137_717, b))
end else begin
(let _137_720 = (let _137_719 = (let _137_718 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_137_718))
in (pos _137_719))
in (_137_720, b))
end
end)
end))))
in (
# 1080 "FStar.Parser.ToSyntax.fst"
let pat = (let _137_725 = (let _137_723 = (let _137_722 = (let _137_721 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in (_137_721, arg_pats))
in FStar_Syntax_Syntax.Pat_cons (_137_722))
in (FStar_All.pipe_right _137_723 pos))
in (let _137_724 = (FStar_Syntax_Syntax.bv_to_name projection)
in (_137_725, None, _137_724)))
in (
# 1081 "FStar.Parser.ToSyntax.fst"
let body = (let _137_729 = (let _137_728 = (let _137_727 = (let _137_726 = (FStar_Syntax_Util.branch pat)
in (_137_726)::[])
in (arg_exp, _137_727))
in FStar_Syntax_Syntax.Tm_match (_137_728))
in (FStar_Syntax_Syntax.mk _137_729 None p))
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
let lb = (let _137_731 = (let _137_730 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (_137_730))
in {FStar_Syntax_Syntax.lbname = _137_731; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = imp})
in (
# 1091 "FStar.Parser.ToSyntax.fst"
let impl = (let _137_736 = (let _137_735 = (let _137_734 = (let _137_733 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _137_733 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_137_734)::[])
in ((false, (lb)::[]), p, _137_735, quals))
in FStar_Syntax_Syntax.Sig_let (_137_736))
in if no_decl then begin
(impl)::[]
end else begin
(decl)::(impl)::[]
end))))))))
end))))))
end))
end))))
in (FStar_All.pipe_right _137_737 FStar_List.flatten)))))))))
end)))))))

# 1094 "FStar.Parser.ToSyntax.fst"
let mk_data_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env _52_1939 -> (match (_52_1939) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _52_1942, t, l, n, quals, _52_1948, _52_1950) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(
# 1097 "FStar.Parser.ToSyntax.fst"
let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _52_10 -> (match (_52_10) with
| FStar_Syntax_Syntax.RecordConstructor (_52_1955) -> begin
true
end
| _52_1958 -> begin
false
end)))) then begin
false
end else begin
(match ((FStar_Parser_Env.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > 1)
end
| _52_1962 -> begin
true
end)
end
in (
# 1103 "FStar.Parser.ToSyntax.fst"
let _52_1966 = (FStar_Syntax_Util.arrow_formals t)
in (match (_52_1966) with
| (formals, cod) -> begin
(match (formals) with
| [] -> begin
[]
end
| _52_1969 -> begin
(
# 1107 "FStar.Parser.ToSyntax.fst"
let fv_qual = (match ((FStar_Util.find_map quals (fun _52_11 -> (match (_52_11) with
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((lid, fns)))
end
| _52_1974 -> begin
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
let _52_1982 = (FStar_Util.first_N n formals)
in (match (_52_1982) with
| (tps, rest) -> begin
(mk_indexed_projectors iquals fv_qual refine_domain env l lid inductive_tps tps rest cod)
end))))
end)
end)))
end
| _52_1984 -> begin
[]
end)
end))

# 1119 "FStar.Parser.ToSyntax.fst"
let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (
# 1120 "FStar.Parser.ToSyntax.fst"
let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _137_762 = (incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (_137_762))
end else begin
(incr_delta_qualifier t)
end
in (
# 1123 "FStar.Parser.ToSyntax.fst"
let lb = (let _137_767 = (let _137_763 = (FStar_Syntax_Syntax.lid_as_fv lid dd None)
in FStar_Util.Inr (_137_763))
in (let _137_766 = (let _137_764 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars _137_764))
in (let _137_765 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = _137_767; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = _137_766; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _137_765})))
in FStar_Syntax_Syntax.Sig_let (((false, (lb)::[]), rng, lids, quals)))))

# 1132 "FStar.Parser.ToSyntax.fst"
let rec desugar_tycon : FStar_Parser_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (
# 1133 "FStar.Parser.ToSyntax.fst"
let tycon_id = (fun _52_12 -> (match (_52_12) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (
# 1138 "FStar.Parser.ToSyntax.fst"
let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _137_781 = (let _137_780 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_137_780))
in (FStar_Parser_AST.mk_term _137_781 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
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
| _52_2059 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _137_794 = (let _137_793 = (let _137_792 = (binder_to_term b)
in (out, _137_792, (imp_of_aqual b)))
in FStar_Parser_AST.App (_137_793))
in (FStar_Parser_AST.mk_term _137_794 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (
# 1152 "FStar.Parser.ToSyntax.fst"
let tycon_record_as_variant = (fun _52_13 -> (match (_52_13) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(
# 1154 "FStar.Parser.ToSyntax.fst"
let constrName = (FStar_Ident.mk_ident ((Prims.strcat "Mk" id.FStar_Ident.idText), id.FStar_Ident.idRange))
in (
# 1155 "FStar.Parser.ToSyntax.fst"
let mfields = (FStar_List.map (fun _52_2072 -> (match (_52_2072) with
| (x, t) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated (((FStar_Syntax_Util.mangle_field_name x), t))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (
# 1156 "FStar.Parser.ToSyntax.fst"
let result = (let _137_800 = (let _137_799 = (let _137_798 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_137_798))
in (FStar_Parser_AST.mk_term _137_799 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _137_800 parms))
in (
# 1157 "FStar.Parser.ToSyntax.fst"
let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _137_802 = (FStar_All.pipe_right fields (FStar_List.map (fun _52_2079 -> (match (_52_2079) with
| (x, _52_2078) -> begin
(FStar_Parser_Env.qualify env x)
end))))
in (FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _137_802))))))
end
| _52_2081 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1161 "FStar.Parser.ToSyntax.fst"
let desugar_abstract_tc = (fun quals _env mutuals _52_14 -> (match (_52_14) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(
# 1163 "FStar.Parser.ToSyntax.fst"
let _52_2095 = (typars_of_binders _env binders)
in (match (_52_2095) with
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
let tconstr = (let _137_813 = (let _137_812 = (let _137_811 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_137_811))
in (FStar_Parser_AST.mk_term _137_812 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _137_813 binders))
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
| _52_2108 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (
# 1176 "FStar.Parser.ToSyntax.fst"
let push_tparams = (fun env bs -> (
# 1177 "FStar.Parser.ToSyntax.fst"
let _52_2123 = (FStar_List.fold_left (fun _52_2114 _52_2117 -> (match ((_52_2114, _52_2117)) with
| ((env, tps), (x, imp)) -> begin
(
# 1178 "FStar.Parser.ToSyntax.fst"
let _52_2120 = (FStar_Parser_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (_52_2120) with
| (env, y) -> begin
(env, ((y, imp))::tps)
end))
end)) (env, []) bs)
in (match (_52_2123) with
| (env, bs) -> begin
(env, (FStar_List.rev bs))
end)))
in (match (tcs) with
| FStar_Parser_AST.TyconAbstract (_52_2125)::[] -> begin
(
# 1183 "FStar.Parser.ToSyntax.fst"
let tc = (FStar_List.hd tcs)
in (
# 1184 "FStar.Parser.ToSyntax.fst"
let _52_2136 = (desugar_abstract_tc quals env [] tc)
in (match (_52_2136) with
| (_52_2130, _52_2132, se, _52_2135) -> begin
(
# 1185 "FStar.Parser.ToSyntax.fst"
let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _52_2139, typars, k, [], [], quals, rng) -> begin
(
# 1187 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
quals
end else begin
(
# 1189 "FStar.Parser.ToSyntax.fst"
let _52_2148 = (let _137_821 = (FStar_Range.string_of_range rng)
in (let _137_820 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" _137_821 _137_820)))
in (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals)
end
in (
# 1192 "FStar.Parser.ToSyntax.fst"
let t = (match (typars) with
| [] -> begin
k
end
| _52_2153 -> begin
(let _137_824 = (let _137_823 = (let _137_822 = (FStar_Syntax_Syntax.mk_Total k)
in (typars, _137_822))
in FStar_Syntax_Syntax.Tm_arrow (_137_823))
in (FStar_Syntax_Syntax.mk _137_824 None rng))
end)
in FStar_Syntax_Syntax.Sig_declare_typ ((l, [], t, quals, rng))))
end
| _52_2156 -> begin
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
let _52_2168 = (typars_of_binders env binders)
in (match (_52_2168) with
| (env', typars) -> begin
(
# 1203 "FStar.Parser.ToSyntax.fst"
let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _52_15 -> (match (_52_15) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| _52_2173 -> begin
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
let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _52_16 -> (match (_52_16) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| _52_2181 -> begin
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
in (let _137_830 = (let _137_829 = (FStar_Parser_Env.qualify env id)
in (let _137_828 = (FStar_All.pipe_right quals (FStar_List.filter (fun _52_17 -> (match (_52_17) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| _52_2189 -> begin
true
end))))
in (_137_829, [], typars, c, _137_828, rng)))
in FStar_Syntax_Syntax.Sig_effect_abbrev (_137_830)))))
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
| FStar_Parser_AST.TyconRecord (_52_2195)::[] -> begin
(
# 1229 "FStar.Parser.ToSyntax.fst"
let trec = (FStar_List.hd tcs)
in (
# 1230 "FStar.Parser.ToSyntax.fst"
let _52_2201 = (tycon_record_as_variant trec)
in (match (_52_2201) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| _52_2205::_52_2203 -> begin
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
let _52_2216 = et
in (match (_52_2216) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_52_2218) -> begin
(
# 1240 "FStar.Parser.ToSyntax.fst"
let trec = tc
in (
# 1241 "FStar.Parser.ToSyntax.fst"
let _52_2223 = (tycon_record_as_variant trec)
in (match (_52_2223) with
| (t, fs) -> begin
(collect_tcs ((FStar_Syntax_Syntax.RecordType (fs))::quals) (env, tcs) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(
# 1244 "FStar.Parser.ToSyntax.fst"
let _52_2235 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_52_2235) with
| (env, _52_2232, se, tconstr) -> begin
(env, (FStar_Util.Inl ((se, constructors, tconstr, quals)))::tcs)
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(
# 1247 "FStar.Parser.ToSyntax.fst"
let _52_2247 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_52_2247) with
| (env, _52_2244, se, tconstr) -> begin
(env, (FStar_Util.Inr ((se, t, quals)))::tcs)
end))
end
| _52_2249 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (
# 1250 "FStar.Parser.ToSyntax.fst"
let _52_2252 = (FStar_List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_52_2252) with
| (env, tcs) -> begin
(
# 1251 "FStar.Parser.ToSyntax.fst"
let tcs = (FStar_List.rev tcs)
in (
# 1252 "FStar.Parser.ToSyntax.fst"
let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _52_19 -> (match (_52_19) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, _52_2260, _52_2262, _52_2264, _52_2266), t, quals) -> begin
(
# 1254 "FStar.Parser.ToSyntax.fst"
let _52_2276 = (push_tparams env tpars)
in (match (_52_2276) with
| (env_tps, _52_2275) -> begin
(
# 1255 "FStar.Parser.ToSyntax.fst"
let t = (desugar_term env_tps t)
in (let _137_840 = (let _137_839 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in ([], _137_839))
in (_137_840)::[]))
end))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, _52_2284, tags, _52_2287), constrs, tconstr, quals) -> begin
(
# 1259 "FStar.Parser.ToSyntax.fst"
let tycon = (tname, tpars, k)
in (
# 1260 "FStar.Parser.ToSyntax.fst"
let _52_2298 = (push_tparams env tpars)
in (match (_52_2298) with
| (env_tps, tps) -> begin
(
# 1261 "FStar.Parser.ToSyntax.fst"
let data_tpars = (FStar_List.map (fun _52_2302 -> (match (_52_2302) with
| (x, _52_2301) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end)) tps)
in (
# 1262 "FStar.Parser.ToSyntax.fst"
let _52_2326 = (let _137_852 = (FStar_All.pipe_right constrs (FStar_List.map (fun _52_2307 -> (match (_52_2307) with
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
let t = (let _137_844 = (FStar_Parser_Env.default_total env_tps)
in (let _137_843 = (close env_tps t)
in (desugar_term _137_844 _137_843)))
in (
# 1273 "FStar.Parser.ToSyntax.fst"
let name = (FStar_Parser_Env.qualify env id)
in (
# 1274 "FStar.Parser.ToSyntax.fst"
let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _52_18 -> (match (_52_18) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| _52_2321 -> begin
[]
end))))
in (
# 1277 "FStar.Parser.ToSyntax.fst"
let ntps = (FStar_List.length data_tpars)
in (let _137_851 = (let _137_850 = (let _137_849 = (let _137_848 = (let _137_847 = (let _137_846 = (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total _137_846))
in (FStar_Syntax_Util.arrow data_tpars _137_847))
in (name, univs, _137_848, tname, ntps, quals, mutuals, rng))
in FStar_Syntax_Syntax.Sig_datacon (_137_849))
in (tps, _137_850))
in (name, _137_851)))))))
end))))
in (FStar_All.pipe_left FStar_List.split _137_852))
in (match (_52_2326) with
| (constrNames, constrs) -> begin
(([], FStar_Syntax_Syntax.Sig_inductive_typ ((tname, univs, tpars, k, mutuals, constrNames, tags, rng))))::constrs
end)))
end)))
end
| _52_2328 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1282 "FStar.Parser.ToSyntax.fst"
let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (
# 1283 "FStar.Parser.ToSyntax.fst"
let bundle = (let _137_854 = (let _137_853 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _137_853, rng))
in FStar_Syntax_Syntax.Sig_bundle (_137_854))
in (
# 1284 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 bundle)
in (
# 1285 "FStar.Parser.ToSyntax.fst"
let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projectors quals env)))
in (
# 1286 "FStar.Parser.ToSyntax.fst"
let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _52_20 -> (match (_52_20) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, _52_2337, tps, k, _52_2341, constrs, quals, _52_2345) when ((FStar_List.length constrs) > 1) -> begin
(
# 1288 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract quals) then begin
(FStar_Syntax_Syntax.Private)::quals
end else begin
quals
end
in (mk_data_discriminators quals env tname tps k constrs))
end
| _52_2350 -> begin
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

# 1299 "FStar.Parser.ToSyntax.fst"
let desugar_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.binder Prims.list) = (fun env binders -> (
# 1300 "FStar.Parser.ToSyntax.fst"
let _52_2374 = (FStar_List.fold_left (fun _52_2359 b -> (match (_52_2359) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| (Some (a), k) -> begin
(
# 1303 "FStar.Parser.ToSyntax.fst"
let _52_2367 = (FStar_Parser_Env.push_bv env a)
in (match (_52_2367) with
| (env, a) -> begin
(let _137_863 = (let _137_862 = (FStar_Syntax_Syntax.mk_binder (
# 1304 "FStar.Parser.ToSyntax.fst"
let _52_2368 = a
in {FStar_Syntax_Syntax.ppname = _52_2368.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_2368.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (_137_862)::binders)
in (env, _137_863))
end))
end
| _52_2371 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Missing name in binder", b.FStar_Parser_AST.brange))))
end)
end)) (env, []) binders)
in (match (_52_2374) with
| (env, binders) -> begin
(env, (FStar_List.rev binders))
end)))

# 1309 "FStar.Parser.ToSyntax.fst"
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
(let _137_868 = (FStar_List.map trans_qual qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _137_868 tcs))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _137_870 = (let _137_869 = (desugar_term_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((isrec, lets, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Syntax_Subst.compress _137_869))
in _137_870.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let (lbs, _52_2394) -> begin
(
# 1324 "FStar.Parser.ToSyntax.fst"
let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (
# 1325 "FStar.Parser.ToSyntax.fst"
let quals = (match (quals) with
| _52_2402::_52_2400 -> begin
(FStar_List.map trans_qual quals)
end
| _52_2405 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _52_21 -> (match (_52_21) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (_52_2416); FStar_Syntax_Syntax.lbunivs = _52_2414; FStar_Syntax_Syntax.lbtyp = _52_2412; FStar_Syntax_Syntax.lbeff = _52_2410; FStar_Syntax_Syntax.lbdef = _52_2408} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _52_2426; FStar_Syntax_Syntax.lbtyp = _52_2424; FStar_Syntax_Syntax.lbeff = _52_2422; FStar_Syntax_Syntax.lbdef = _52_2420} -> begin
(FStar_Parser_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (
# 1330 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right lets (FStar_Util.for_some (fun _52_2434 -> (match (_52_2434) with
| (_52_2432, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end)))) then begin
(FStar_Syntax_Syntax.Logic)::quals
end else begin
quals
end
in (
# 1334 "FStar.Parser.ToSyntax.fst"
let lbs = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _137_875 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 1336 "FStar.Parser.ToSyntax.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 1337 "FStar.Parser.ToSyntax.fst"
let _52_2438 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((
# 1337 "FStar.Parser.ToSyntax.fst"
let _52_2440 = fv
in {FStar_Syntax_Syntax.fv_name = _52_2440.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = _52_2440.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = _52_2438.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _52_2438.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _52_2438.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _52_2438.FStar_Syntax_Syntax.lbdef})))))
in ((Prims.fst lbs), _137_875))
end else begin
lbs
end
in (
# 1339 "FStar.Parser.ToSyntax.fst"
let s = (let _137_878 = (let _137_877 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (lbs, d.FStar_Parser_AST.drange, _137_877, quals))
in FStar_Syntax_Syntax.Sig_let (_137_878))
in (
# 1340 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env s)
in (env, (s)::[])))))))
end
| _52_2447 -> begin
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
in (let _137_882 = (let _137_881 = (let _137_880 = (let _137_879 = (FStar_Parser_Env.qualify env id)
in (_137_879, f, (FStar_Syntax_Syntax.Assumption)::[], d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Sig_assume (_137_880))
in (_137_881)::[])
in (env, _137_882)))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(
# 1355 "FStar.Parser.ToSyntax.fst"
let t = (let _137_883 = (close_fun env t)
in (desugar_term env _137_883))
in (
# 1356 "FStar.Parser.ToSyntax.fst"
let quals = if (env.FStar_Parser_Env.iface && env.FStar_Parser_Env.admitted_iface) then begin
(FStar_Parser_AST.Assumption)::quals
end else begin
quals
end
in (
# 1357 "FStar.Parser.ToSyntax.fst"
let se = (let _137_886 = (let _137_885 = (FStar_Parser_Env.qualify env id)
in (let _137_884 = (FStar_List.map trans_qual quals)
in (_137_885, [], t, _137_884, d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_declare_typ (_137_886))
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
let t = (let _137_890 = (let _137_887 = (FStar_Syntax_Syntax.null_binder t)
in (_137_887)::[])
in (let _137_889 = (let _137_888 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _137_888))
in (FStar_Syntax_Util.arrow _137_890 _137_889)))
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
let _52_2500 = (desugar_binders env binders)
in (match (_52_2500) with
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
let _52_2516 = (desugar_binders env eff_binders)
in (match (_52_2516) with
| (env, binders) -> begin
(
# 1395 "FStar.Parser.ToSyntax.fst"
let _52_2527 = (
# 1396 "FStar.Parser.ToSyntax.fst"
let _52_2519 = (head_and_args defn)
in (match (_52_2519) with
| (head, args) -> begin
(
# 1397 "FStar.Parser.ToSyntax.fst"
let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_defn env) l)
end
| _52_2523 -> begin
(let _137_895 = (let _137_894 = (let _137_893 = (let _137_892 = (let _137_891 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat "Effect " _137_891))
in (Prims.strcat _137_892 " not found"))
in (_137_893, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_137_894))
in (Prims.raise _137_895))
end)
in (let _137_896 = (desugar_args env args)
in (ed, _137_896)))
end))
in (match (_52_2527) with
| (ed, args) -> begin
(
# 1401 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_Syntax_Subst.close_binders binders)
in (
# 1402 "FStar.Parser.ToSyntax.fst"
let sub = (fun _52_2533 -> (match (_52_2533) with
| (_52_2531, x) -> begin
(
# 1403 "FStar.Parser.ToSyntax.fst"
let _52_2536 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (_52_2536) with
| (edb, x) -> begin
(
# 1404 "FStar.Parser.ToSyntax.fst"
let s = (FStar_Syntax_Util.subst_of_list edb args)
in (let _137_900 = (let _137_899 = (FStar_Syntax_Subst.subst s x)
in (FStar_Syntax_Subst.close binders _137_899))
in ([], _137_900)))
end))
end))
in (
# 1406 "FStar.Parser.ToSyntax.fst"
let ed = (let _137_917 = (FStar_List.map trans_qual quals)
in (let _137_916 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _137_915 = (let _137_901 = (sub ([], ed.FStar_Syntax_Syntax.signature))
in (Prims.snd _137_901))
in (let _137_914 = (sub ed.FStar_Syntax_Syntax.ret)
in (let _137_913 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (let _137_912 = (sub ed.FStar_Syntax_Syntax.bind_wlp)
in (let _137_911 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (let _137_910 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (let _137_909 = (sub ed.FStar_Syntax_Syntax.ite_wlp)
in (let _137_908 = (sub ed.FStar_Syntax_Syntax.wp_binop)
in (let _137_907 = (sub ed.FStar_Syntax_Syntax.wp_as_type)
in (let _137_906 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (let _137_905 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (let _137_904 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (let _137_903 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (let _137_902 = (sub ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _137_917; FStar_Syntax_Syntax.mname = _137_916; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = _137_915; FStar_Syntax_Syntax.ret = _137_914; FStar_Syntax_Syntax.bind_wp = _137_913; FStar_Syntax_Syntax.bind_wlp = _137_912; FStar_Syntax_Syntax.if_then_else = _137_911; FStar_Syntax_Syntax.ite_wp = _137_910; FStar_Syntax_Syntax.ite_wlp = _137_909; FStar_Syntax_Syntax.wp_binop = _137_908; FStar_Syntax_Syntax.wp_as_type = _137_907; FStar_Syntax_Syntax.close_wp = _137_906; FStar_Syntax_Syntax.assert_p = _137_905; FStar_Syntax_Syntax.assume_p = _137_904; FStar_Syntax_Syntax.null_wp = _137_903; FStar_Syntax_Syntax.trivial = _137_902}))))))))))))))))
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
let _52_2554 = (desugar_binders env eff_binders)
in (match (_52_2554) with
| (env, binders) -> begin
(
# 1434 "FStar.Parser.ToSyntax.fst"
let eff_k = (let _137_918 = (FStar_Parser_Env.default_total env)
in (desugar_term _137_918 eff_kind))
in (
# 1435 "FStar.Parser.ToSyntax.fst"
let _52_2565 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _52_2558 decl -> (match (_52_2558) with
| (env, out) -> begin
(
# 1436 "FStar.Parser.ToSyntax.fst"
let _52_2562 = (desugar_decl env decl)
in (match (_52_2562) with
| (env, ses) -> begin
(let _137_922 = (let _137_921 = (FStar_List.hd ses)
in (_137_921)::out)
in (env, _137_922))
end))
end)) (env, [])))
in (match (_52_2565) with
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
in (let _137_926 = (let _137_925 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) _137_925))
in ([], _137_926))))
in (
# 1443 "FStar.Parser.ToSyntax.fst"
let ed = (let _137_941 = (FStar_List.map trans_qual quals)
in (let _137_940 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _137_939 = (lookup "return")
in (let _137_938 = (lookup "bind_wp")
in (let _137_937 = (lookup "bind_wlp")
in (let _137_936 = (lookup "if_then_else")
in (let _137_935 = (lookup "ite_wp")
in (let _137_934 = (lookup "ite_wlp")
in (let _137_933 = (lookup "wp_binop")
in (let _137_932 = (lookup "wp_as_type")
in (let _137_931 = (lookup "close_wp")
in (let _137_930 = (lookup "assert_p")
in (let _137_929 = (lookup "assume_p")
in (let _137_928 = (lookup "null_wp")
in (let _137_927 = (lookup "trivial")
in {FStar_Syntax_Syntax.qualifiers = _137_941; FStar_Syntax_Syntax.mname = _137_940; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret = _137_939; FStar_Syntax_Syntax.bind_wp = _137_938; FStar_Syntax_Syntax.bind_wlp = _137_937; FStar_Syntax_Syntax.if_then_else = _137_936; FStar_Syntax_Syntax.ite_wp = _137_935; FStar_Syntax_Syntax.ite_wlp = _137_934; FStar_Syntax_Syntax.wp_binop = _137_933; FStar_Syntax_Syntax.wp_as_type = _137_932; FStar_Syntax_Syntax.close_wp = _137_931; FStar_Syntax_Syntax.assert_p = _137_930; FStar_Syntax_Syntax.assume_p = _137_929; FStar_Syntax_Syntax.null_wp = _137_928; FStar_Syntax_Syntax.trivial = _137_927})))))))))))))))
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
(let _137_948 = (let _137_947 = (let _137_946 = (let _137_945 = (let _137_944 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat "Effect name " _137_944))
in (Prims.strcat _137_945 " not found"))
in (_137_946, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_137_947))
in (Prims.raise _137_948))
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
let lift = (let _137_949 = (desugar_term env l.FStar_Parser_AST.lift_op)
in ([], _137_949))
in (
# 1474 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect (({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift = lift}, d.FStar_Parser_AST.drange))
in (env, (se)::[]))))))
end))

# 1477 "FStar.Parser.ToSyntax.fst"
let desugar_decls : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _52_2589 d -> (match (_52_2589) with
| (env, sigelts) -> begin
(
# 1479 "FStar.Parser.ToSyntax.fst"
let _52_2593 = (desugar_decl env d)
in (match (_52_2593) with
| (env, se) -> begin
(env, (FStar_List.append sigelts se))
end))
end)) (env, []) decls))

# 1482 "FStar.Parser.ToSyntax.fst"
let open_prims_all : FStar_Parser_AST.decl Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.all_lid)) FStar_Range.dummyRange))::[]

# 1489 "FStar.Parser.ToSyntax.fst"
let desugar_modul_common : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (
# 1490 "FStar.Parser.ToSyntax.fst"
let open_ns = (fun mname d -> (
# 1491 "FStar.Parser.ToSyntax.fst"
let d = if ((FStar_List.length mname.FStar_Ident.ns) <> 0) then begin
(let _137_968 = (let _137_967 = (let _137_966 = (FStar_Ident.lid_of_ids mname.FStar_Ident.ns)
in FStar_Parser_AST.Open (_137_966))
in (FStar_Parser_AST.mk_decl _137_967 (FStar_Ident.range_of_lid mname)))
in (_137_968)::d)
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
let _52_2620 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _137_970 = (FStar_Parser_Env.prepare_module_or_interface true admitted env mname)
in (let _137_969 = (open_ns mname decls)
in (_137_970, mname, _137_969, true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _137_972 = (FStar_Parser_Env.prepare_module_or_interface false false env mname)
in (let _137_971 = (open_ns mname decls)
in (_137_972, mname, _137_971, false)))
end)
in (match (_52_2620) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(
# 1503 "FStar.Parser.ToSyntax.fst"
let _52_2623 = (desugar_decls env decls)
in (match (_52_2623) with
| (env, sigelts) -> begin
(
# 1504 "FStar.Parser.ToSyntax.fst"
let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in (env, modul, pop_when_done))
end))
end)))))

# 1512 "FStar.Parser.ToSyntax.fst"
let desugar_partial_modul : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (
# 1513 "FStar.Parser.ToSyntax.fst"
let m = if (FStar_ST.read FStar_Options.interactive_fsi) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface ((mname, decls, true))
end
| FStar_Parser_AST.Interface (mname, _52_2634, _52_2636) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (
# 1520 "FStar.Parser.ToSyntax.fst"
let _52_2644 = (desugar_modul_common curmod env m)
in (match (_52_2644) with
| (x, y, _52_2643) -> begin
(x, y)
end))))

# 1523 "FStar.Parser.ToSyntax.fst"
let desugar_modul : FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (
# 1524 "FStar.Parser.ToSyntax.fst"
let _52_2650 = (desugar_modul_common None env m)
in (match (_52_2650) with
| (env, modul, pop_when_done) -> begin
(
# 1525 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.finish_module_or_interface env modul)
in (
# 1526 "FStar.Parser.ToSyntax.fst"
let _52_2652 = if (FStar_Options.should_dump modul.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _137_983 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _137_983))
end else begin
()
end
in (let _137_984 = if pop_when_done then begin
(FStar_Parser_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end else begin
env
end
in (_137_984, modul))))
end)))

# 1530 "FStar.Parser.ToSyntax.fst"
let desugar_file : FStar_Parser_Env.env  ->  FStar_Parser_AST.file  ->  Prims.bool  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f needs_interleaving -> (
# 1531 "FStar.Parser.ToSyntax.fst"
let _52_2667 = (FStar_List.fold_left (fun _52_2659 m -> (match (_52_2659) with
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
let _52_2664 = (desugar_modul env m)
in (match (_52_2664) with
| (env, m) -> begin
(env, (m)::mods)
end)))
end)) (env, []) f)
in (match (_52_2667) with
| (env, mods) -> begin
(env, (FStar_List.rev mods))
end)))

# 1537 "FStar.Parser.ToSyntax.fst"
let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Parser_Env.env  ->  FStar_Parser_Env.env = (fun m en -> (
# 1538 "FStar.Parser.ToSyntax.fst"
let _52_2672 = (FStar_Parser_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (_52_2672) with
| (en, pop_when_done) -> begin
(
# 1539 "FStar.Parser.ToSyntax.fst"
let en = (FStar_List.fold_left FStar_Parser_Env.push_sigelt (
# 1539 "FStar.Parser.ToSyntax.fst"
let _52_2673 = en
in {FStar_Parser_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_Parser_Env.modules = _52_2673.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _52_2673.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.sigaccum = _52_2673.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _52_2673.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _52_2673.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _52_2673.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _52_2673.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _52_2673.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _52_2673.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = _52_2673.FStar_Parser_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (
# 1540 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_Env.export_interface m.FStar_Syntax_Syntax.name env)
end else begin
env
end))
end)))




