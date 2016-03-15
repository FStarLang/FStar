
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
let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _135_21 = (let _135_20 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_135_20))
in (FStar_Parser_AST.mk_term _135_21 r FStar_Parser_AST.Kind)))

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
| _51_169 -> begin
"UNKNOWN"
end))
in (
# 135 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _135_41 = (let _135_39 = (FStar_Util.char_at s i)
in (name_of_char _135_39))
in (let _135_40 = (aux (i + 1))
in (_135_41)::_135_40))
end)
in (let _135_43 = (let _135_42 = (aux 0)
in (FStar_String.concat "_" _135_42))
in (Prims.strcat "op_" _135_43)))))

# 141 "FStar.Parser.ToSyntax.fst"
let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _135_53 = (let _135_52 = (let _135_51 = (let _135_50 = (compile_op n s)
in (_135_50, r))
in (FStar_Ident.mk_ident _135_51))
in (_135_52)::[])
in (FStar_All.pipe_right _135_53 FStar_Ident.lid_of_ids)))

# 143 "FStar.Parser.ToSyntax.fst"
let op_as_fv : FStar_Parser_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.fv Prims.option = (fun env arity rng s -> (
# 144 "FStar.Parser.ToSyntax.fst"
let r = (fun l dd -> (let _135_67 = (let _135_66 = (FStar_Ident.set_lid_range l rng)
in (FStar_Syntax_Syntax.lid_as_fv _135_66 dd None))
in Some (_135_67)))
in (
# 145 "FStar.Parser.ToSyntax.fst"
let fallback = (fun _51_184 -> (match (()) with
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
| _51_212 -> begin
None
end)
end))
in (match ((let _135_70 = (compile_op_lid arity s rng)
in (FStar_Parser_Env.try_lookup_lid env _135_70))) with
| Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _51_218; FStar_Syntax_Syntax.pos = _51_216; FStar_Syntax_Syntax.vars = _51_214}) -> begin
Some (fv)
end
| _51_224 -> begin
(fallback ())
end))))

# 179 "FStar.Parser.ToSyntax.fst"
let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _135_77 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _135_77)))

# 183 "FStar.Parser.ToSyntax.fst"
let rec free_type_vars_b : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_51_233) -> begin
(env, [])
end
| FStar_Parser_AST.TVariable (x) -> begin
(
# 186 "FStar.Parser.ToSyntax.fst"
let _51_240 = (FStar_Parser_Env.push_bv env x)
in (match (_51_240) with
| (env, _51_239) -> begin
(env, (x)::[])
end))
end
| FStar_Parser_AST.Annotated (_51_242, term) -> begin
(let _135_84 = (free_type_vars env term)
in (env, _135_84))
end
| FStar_Parser_AST.TAnnotated (id, _51_248) -> begin
(
# 191 "FStar.Parser.ToSyntax.fst"
let _51_254 = (FStar_Parser_Env.push_bv env id)
in (match (_51_254) with
| (env, _51_253) -> begin
(env, [])
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _135_85 = (free_type_vars env t)
in (env, _135_85))
end))
and free_type_vars : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _135_88 = (unparen t)
in _135_88.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (_51_260) -> begin
(FStar_All.failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_Env.try_lookup_id env a)) with
| None -> begin
(a)::[]
end
| _51_266 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_51_296, ts) -> begin
(FStar_List.collect (fun _51_303 -> (match (_51_303) with
| (t, _51_302) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_51_305, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _51_312) -> begin
(let _135_91 = (free_type_vars env t1)
in (let _135_90 = (free_type_vars env t2)
in (FStar_List.append _135_91 _135_90)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(
# 221 "FStar.Parser.ToSyntax.fst"
let _51_321 = (free_type_vars_b env b)
in (match (_51_321) with
| (env, f) -> begin
(let _135_92 = (free_type_vars env t)
in (FStar_List.append f _135_92))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(
# 226 "FStar.Parser.ToSyntax.fst"
let _51_337 = (FStar_List.fold_left (fun _51_330 binder -> (match (_51_330) with
| (env, free) -> begin
(
# 227 "FStar.Parser.ToSyntax.fst"
let _51_334 = (free_type_vars_b env binder)
in (match (_51_334) with
| (env, f) -> begin
(env, (FStar_List.append f free))
end))
end)) (env, []) binders)
in (match (_51_337) with
| (env, free) -> begin
(let _135_95 = (free_type_vars env body)
in (FStar_List.append free _135_95))
end))
end
| FStar_Parser_AST.Project (t, _51_340) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) -> begin
[]
end
| (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
(FStar_Parser_AST.error "Unexpected type in free_type_vars computation" t t.FStar_Parser_AST.range)
end))

# 244 "FStar.Parser.ToSyntax.fst"
let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (
# 245 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun args t -> (match ((let _135_102 = (unparen t)
in _135_102.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _51_384 -> begin
(t, args)
end))
in (aux [] t)))

# 251 "FStar.Parser.ToSyntax.fst"
let close : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 252 "FStar.Parser.ToSyntax.fst"
let ftv = (let _135_107 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _135_107))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 255 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _135_111 = (let _135_110 = (let _135_109 = (tm_type x.FStar_Ident.idRange)
in (x, _135_109))
in FStar_Parser_AST.TAnnotated (_135_110))
in (FStar_Parser_AST.mk_binder _135_111 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 256 "FStar.Parser.ToSyntax.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))

# 259 "FStar.Parser.ToSyntax.fst"
let close_fun : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 260 "FStar.Parser.ToSyntax.fst"
let ftv = (let _135_116 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _135_116))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 263 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _135_120 = (let _135_119 = (let _135_118 = (tm_type x.FStar_Ident.idRange)
in (x, _135_118))
in FStar_Parser_AST.TAnnotated (_135_119))
in (FStar_Parser_AST.mk_binder _135_120 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 264 "FStar.Parser.ToSyntax.fst"
let t = (match ((let _135_121 = (unparen t)
in _135_121.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_51_397) -> begin
t
end
| _51_400 -> begin
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
| _51_410 -> begin
(bs, t)
end))

# 274 "FStar.Parser.ToSyntax.fst"
let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _51_414) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_51_420); FStar_Parser_AST.prange = _51_418}, _51_424) -> begin
true
end
| _51_428 -> begin
false
end))

# 279 "FStar.Parser.ToSyntax.fst"
let rec destruct_app_pattern : FStar_Parser_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 281 "FStar.Parser.ToSyntax.fst"
let _51_440 = (destruct_app_pattern env is_top_level p)
in (match (_51_440) with
| (name, args, _51_439) -> begin
(name, args, Some (t))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _51_445); FStar_Parser_AST.prange = _51_442}, args) when is_top_level -> begin
(let _135_135 = (let _135_134 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_135_134))
in (_135_135, args, None))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _51_456); FStar_Parser_AST.prange = _51_453}, args) -> begin
(FStar_Util.Inl (id), args, None)
end
| _51_464 -> begin
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
| LocalBinder (_51_467) -> begin
_51_467
end))

# 292 "FStar.Parser.ToSyntax.fst"
let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_51_470) -> begin
_51_470
end))

# 293 "FStar.Parser.ToSyntax.fst"
let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun _51_6 -> (match (_51_6) with
| LocalBinder (a, aq) -> begin
(a, aq)
end
| _51_477 -> begin
(FStar_All.failwith "Impossible")
end))

# 296 "FStar.Parser.ToSyntax.fst"
let as_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_Parser_Env.env) = (fun env imp _51_7 -> (match (_51_7) with
| (None, k) -> begin
(let _135_172 = (FStar_Syntax_Syntax.null_binder k)
in (_135_172, env))
end
| (Some (a), k) -> begin
(
# 299 "FStar.Parser.ToSyntax.fst"
let _51_490 = (FStar_Parser_Env.push_bv env a)
in (match (_51_490) with
| (env, a) -> begin
(((
# 300 "FStar.Parser.ToSyntax.fst"
let _51_491 = a
in {FStar_Syntax_Syntax.ppname = _51_491.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _51_491.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}), (trans_aqual imp)), env)
end))
end))

# 302 "FStar.Parser.ToSyntax.fst"
type env_t =
FStar_Parser_Env.env

# 303 "FStar.Parser.ToSyntax.fst"
type lenv_t =
FStar_Syntax_Syntax.bv Prims.list

# 305 "FStar.Parser.ToSyntax.fst"
let mk_lb : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.letbinding = (fun _51_496 -> (match (_51_496) with
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
| FStar_Syntax_Syntax.Pat_cons (_51_517, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out _51_525 -> (match (_51_525) with
| (p, _51_524) -> begin
(let _135_218 = (pat_vars p)
in (FStar_Util.set_union out _135_218))
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
| _51_543 -> begin
(
# 331 "FStar.Parser.ToSyntax.fst"
let _51_546 = (FStar_Parser_Env.push_bv e x)
in (match (_51_546) with
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
| _51_555 -> begin
(
# 337 "FStar.Parser.ToSyntax.fst"
let _51_558 = (FStar_Parser_Env.push_bv e a)
in (match (_51_558) with
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
let _51_580 = (aux loc env p)
in (match (_51_580) with
| (loc, env, var, p, _51_579) -> begin
(
# 346 "FStar.Parser.ToSyntax.fst"
let _51_597 = (FStar_List.fold_left (fun _51_584 p -> (match (_51_584) with
| (loc, env, ps) -> begin
(
# 347 "FStar.Parser.ToSyntax.fst"
let _51_593 = (aux loc env p)
in (match (_51_593) with
| (loc, env, _51_589, p, _51_592) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_51_597) with
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
let _51_608 = (aux loc env p)
in (match (_51_608) with
| (loc, env', binder, p, imp) -> begin
(
# 354 "FStar.Parser.ToSyntax.fst"
let binder = (match (binder) with
| LetBinder (_51_610) -> begin
(FStar_All.failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(
# 357 "FStar.Parser.ToSyntax.fst"
let t = (let _135_248 = (close_fun env t)
in (desugar_term env _135_248))
in LocalBinder (((
# 358 "FStar.Parser.ToSyntax.fst"
let _51_617 = x
in {FStar_Syntax_Syntax.ppname = _51_617.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _51_617.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), aq)))
end)
in (loc, env', binder, p, imp))
end))
end
| FStar_Parser_AST.PatWild -> begin
(
# 362 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _135_249 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in (loc, env, LocalBinder ((x, None)), _135_249, false)))
end
| FStar_Parser_AST.PatConst (c) -> begin
(
# 366 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _135_250 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in (loc, env, LocalBinder ((x, None)), _135_250, false)))
end
| (FStar_Parser_AST.PatTvar (x, imp)) | (FStar_Parser_AST.PatVar (x, imp)) -> begin
(
# 371 "FStar.Parser.ToSyntax.fst"
let aq = if imp then begin
Some (FStar_Syntax_Syntax.imp_tag)
end else begin
None
end
in (
# 372 "FStar.Parser.ToSyntax.fst"
let _51_635 = (resolvex loc env x)
in (match (_51_635) with
| (loc, env, xbv) -> begin
(let _135_251 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in (loc, env, LocalBinder ((xbv, aq)), _135_251, imp))
end)))
end
| FStar_Parser_AST.PatName (l) -> begin
(
# 376 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_datacon env) l)
in (
# 377 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _135_252 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, []))))
in (loc, env, LocalBinder ((x, None)), _135_252, false))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _51_641}, args) -> begin
(
# 381 "FStar.Parser.ToSyntax.fst"
let _51_663 = (FStar_List.fold_right (fun arg _51_652 -> (match (_51_652) with
| (loc, env, args) -> begin
(
# 382 "FStar.Parser.ToSyntax.fst"
let _51_659 = (aux loc env arg)
in (match (_51_659) with
| (loc, env, _51_656, arg, imp) -> begin
(loc, env, ((arg, imp))::args)
end))
end)) args (loc, env, []))
in (match (_51_663) with
| (loc, env, args) -> begin
(
# 384 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_datacon env) l)
in (
# 385 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _135_255 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _135_255, false))))
end))
end
| FStar_Parser_AST.PatApp (_51_667) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(
# 391 "FStar.Parser.ToSyntax.fst"
let _51_687 = (FStar_List.fold_right (fun pat _51_675 -> (match (_51_675) with
| (loc, env, pats) -> begin
(
# 392 "FStar.Parser.ToSyntax.fst"
let _51_683 = (aux loc env pat)
in (match (_51_683) with
| (loc, env, _51_679, pat, _51_682) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_51_687) with
| (loc, env, pats) -> begin
(
# 394 "FStar.Parser.ToSyntax.fst"
let pat = (let _135_268 = (let _135_267 = (let _135_263 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _135_263))
in (let _135_266 = (let _135_265 = (let _135_264 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_135_264, []))
in FStar_Syntax_Syntax.Pat_cons (_135_265))
in (FStar_All.pipe_left _135_267 _135_266)))
in (FStar_List.fold_right (fun hd tl -> (
# 395 "FStar.Parser.ToSyntax.fst"
let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (let _135_262 = (let _135_261 = (let _135_260 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_135_260, ((hd, false))::((tl, false))::[]))
in FStar_Syntax_Syntax.Pat_cons (_135_261))
in (FStar_All.pipe_left (pos_r r) _135_262)))) pats _135_268))
in (
# 398 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (loc, env, LocalBinder ((x, None)), pat, false)))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(
# 402 "FStar.Parser.ToSyntax.fst"
let _51_713 = (FStar_List.fold_left (fun _51_700 p -> (match (_51_700) with
| (loc, env, pats) -> begin
(
# 403 "FStar.Parser.ToSyntax.fst"
let _51_709 = (aux loc env p)
in (match (_51_709) with
| (loc, env, _51_705, pat, _51_708) -> begin
(loc, env, ((pat, false))::pats)
end))
end)) (loc, env, []) args)
in (match (_51_713) with
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
| _51_720 -> begin
(FStar_All.failwith "impossible")
end)
in (
# 412 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _135_271 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _135_271, false)))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(
# 419 "FStar.Parser.ToSyntax.fst"
let _51_730 = (FStar_List.hd fields)
in (match (_51_730) with
| (f, _51_729) -> begin
(
# 420 "FStar.Parser.ToSyntax.fst"
let _51_734 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_51_734) with
| (record, _51_733) -> begin
(
# 421 "FStar.Parser.ToSyntax.fst"
let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _51_737 -> (match (_51_737) with
| (f, p) -> begin
(let _135_273 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.qualify_field_to_record env record) f)
in (_135_273, p))
end))))
in (
# 423 "FStar.Parser.ToSyntax.fst"
let args = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _51_742 -> (match (_51_742) with
| (f, _51_741) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _51_746 -> (match (_51_746) with
| (g, _51_745) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_51_749, p) -> begin
p
end)
end))))
in (
# 427 "FStar.Parser.ToSyntax.fst"
let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_Env.constrname)) p.FStar_Parser_AST.prange), args))) p.FStar_Parser_AST.prange)
in (
# 428 "FStar.Parser.ToSyntax.fst"
let _51_761 = (aux loc env app)
in (match (_51_761) with
| (env, e, b, p, _51_760) -> begin
(
# 429 "FStar.Parser.ToSyntax.fst"
let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(let _135_282 = (let _135_281 = (let _135_280 = (
# 430 "FStar.Parser.ToSyntax.fst"
let _51_766 = fv
in (let _135_279 = (let _135_278 = (let _135_277 = (let _135_276 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _135_276))
in FStar_Syntax_Syntax.Record_ctor (_135_277))
in Some (_135_278))
in {FStar_Syntax_Syntax.fv_name = _51_766.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = _51_766.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _135_279}))
in (_135_280, args))
in FStar_Syntax_Syntax.Pat_cons (_135_281))
in (FStar_All.pipe_left pos _135_282))
end
| _51_769 -> begin
p
end)
in (env, e, b, p, false))
end)))))
end))
end))
end))))
in (
# 434 "FStar.Parser.ToSyntax.fst"
let _51_778 = (aux [] env p)
in (match (_51_778) with
| (_51_772, env, b, p, _51_777) -> begin
(
# 435 "FStar.Parser.ToSyntax.fst"
let _51_779 = (let _135_283 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore _135_283))
in (env, b, p))
end)))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _51_786) -> begin
(let _135_289 = (let _135_288 = (let _135_287 = (FStar_Parser_Env.qualify env x)
in (_135_287, FStar_Syntax_Syntax.tun))
in LetBinder (_135_288))
in (env, _135_289, None))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _51_793); FStar_Parser_AST.prange = _51_790}, t) -> begin
(let _135_293 = (let _135_292 = (let _135_291 = (FStar_Parser_Env.qualify env x)
in (let _135_290 = (desugar_term env t)
in (_135_291, _135_290)))
in LetBinder (_135_292))
in (env, _135_293, None))
end
| _51_801 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern at the top-level", p.FStar_Parser_AST.prange))))
end)
end else begin
(
# 446 "FStar.Parser.ToSyntax.fst"
let _51_805 = (desugar_data_pat env p)
in (match (_51_805) with
| (env, binder, p) -> begin
(
# 447 "FStar.Parser.ToSyntax.fst"
let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| _51_813 -> begin
Some (p)
end)
in (env, binder, p))
end))
end)
and desugar_binding_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun _51_817 env pat -> (
# 456 "FStar.Parser.ToSyntax.fst"
let _51_825 = (desugar_data_pat env pat)
in (match (_51_825) with
| (env, _51_823, pat) -> begin
(env, pat)
end)))
and desugar_match_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (
# 462 "FStar.Parser.ToSyntax.fst"
let env = (
# 462 "FStar.Parser.ToSyntax.fst"
let _51_830 = env
in {FStar_Parser_Env.curmodule = _51_830.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _51_830.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _51_830.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.sigaccum = _51_830.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _51_830.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _51_830.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _51_830.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _51_830.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _51_830.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _51_830.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (
# 466 "FStar.Parser.ToSyntax.fst"
let env = (
# 466 "FStar.Parser.ToSyntax.fst"
let _51_835 = env
in {FStar_Parser_Env.curmodule = _51_835.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _51_835.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _51_835.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.sigaccum = _51_835.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _51_835.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _51_835.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _51_835.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _51_835.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _51_835.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _51_835.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (
# 470 "FStar.Parser.ToSyntax.fst"
let mk = (fun e -> (FStar_Syntax_Syntax.mk e None top.FStar_Parser_AST.range))
in (
# 471 "FStar.Parser.ToSyntax.fst"
let setpos = (fun e -> (
# 471 "FStar.Parser.ToSyntax.fst"
let _51_845 = e
in {FStar_Syntax_Syntax.n = _51_845.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _51_845.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _51_845.FStar_Syntax_Syntax.vars}))
in (match ((let _135_312 = (unparen top)
in _135_312.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (_51_849) -> begin
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
| FStar_Parser_AST.Op ("*", _51_869::_51_867::[]) when (let _135_313 = (op_as_fv env 2 top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right _135_313 FStar_Option.isNone)) -> begin
(
# 489 "FStar.Parser.ToSyntax.fst"
let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", t1::t2::[]) -> begin
(
# 491 "FStar.Parser.ToSyntax.fst"
let rest = (flatten t2)
in (t1)::rest)
end
| _51_883 -> begin
(t)::[]
end))
in (
# 494 "FStar.Parser.ToSyntax.fst"
let targs = (let _135_319 = (let _135_316 = (unparen top)
in (flatten _135_316))
in (FStar_All.pipe_right _135_319 (FStar_List.map (fun t -> (let _135_318 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg _135_318))))))
in (
# 495 "FStar.Parser.ToSyntax.fst"
let tup = (let _135_320 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) _135_320))
in (mk (FStar_Syntax_Syntax.Tm_app ((tup, targs)))))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _135_321 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) a)
in (FStar_All.pipe_left setpos _135_321))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_fv env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Unexpected operator: " s), top.FStar_Parser_AST.range))))
end
| Some (fv) -> begin
(
# 505 "FStar.Parser.ToSyntax.fst"
let op = (FStar_Syntax_Syntax.fv_to_tm fv)
in (
# 506 "FStar.Parser.ToSyntax.fst"
let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _135_323 = (desugar_term env t)
in (_135_323, None)))))
in (mk (FStar_Syntax_Syntax.Tm_app ((op, args))))))
end)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _51_905; FStar_Ident.ident = _51_903; FStar_Ident.nsstr = _51_901; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _51_914; FStar_Ident.ident = _51_912; FStar_Ident.nsstr = _51_910; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _51_923; FStar_Ident.ident = _51_921; FStar_Ident.nsstr = _51_919; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _51_932; FStar_Ident.ident = _51_930; FStar_Ident.nsstr = _51_928; FStar_Ident.str = "True"}) -> begin
(let _135_324 = (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _135_324 FStar_Syntax_Syntax.Delta_constant None))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _51_941; FStar_Ident.ident = _51_939; FStar_Ident.nsstr = _51_937; FStar_Ident.str = "False"}) -> begin
(let _135_325 = (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _135_325 FStar_Syntax_Syntax.Delta_constant None))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(let _135_326 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (FStar_All.pipe_left setpos _135_326))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(
# 521 "FStar.Parser.ToSyntax.fst"
let _51_956 = (match ((FStar_Parser_Env.try_lookup_datacon env l)) with
| None -> begin
(let _135_327 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (_135_327, false))
end
| Some (head) -> begin
(let _135_328 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in (_135_328, true))
end)
in (match (_51_956) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| _51_959 -> begin
(
# 527 "FStar.Parser.ToSyntax.fst"
let args = (FStar_List.map (fun _51_962 -> (match (_51_962) with
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
let _51_990 = (FStar_List.fold_left (fun _51_973 b -> (match (_51_973) with
| (env, tparams, typs) -> begin
(
# 538 "FStar.Parser.ToSyntax.fst"
let _51_977 = (desugar_binder env b)
in (match (_51_977) with
| (xopt, t) -> begin
(
# 539 "FStar.Parser.ToSyntax.fst"
let _51_983 = (match (xopt) with
| None -> begin
(let _135_332 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (env, _135_332))
end
| Some (x) -> begin
(FStar_Parser_Env.push_bv env x)
end)
in (match (_51_983) with
| (env, x) -> begin
(let _135_336 = (let _135_335 = (let _135_334 = (let _135_333 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _135_333))
in (_135_334)::[])
in (FStar_List.append typs _135_335))
in (env, (FStar_List.append tparams ((((
# 543 "FStar.Parser.ToSyntax.fst"
let _51_984 = x
in {FStar_Syntax_Syntax.ppname = _51_984.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _51_984.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), None))::[])), _135_336))
end))
end))
end)) (env, [], []) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_51_990) with
| (env, _51_988, targs) -> begin
(
# 546 "FStar.Parser.ToSyntax.fst"
let tup = (let _135_337 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) _135_337))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app ((tup, targs)))))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(
# 550 "FStar.Parser.ToSyntax.fst"
let _51_998 = (uncurry binders t)
in (match (_51_998) with
| (bs, t) -> begin
(
# 551 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun env bs _51_8 -> (match (_51_8) with
| [] -> begin
(
# 553 "FStar.Parser.ToSyntax.fst"
let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (let _135_344 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos _135_344)))
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
let _51_1012 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_51_1012) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_binder env b)) with
| (None, _51_1019) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(
# 568 "FStar.Parser.ToSyntax.fst"
let _51_1027 = (as_binder env None b)
in (match (_51_1027) with
| ((x, _51_1024), env) -> begin
(
# 569 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env f)
in (let _135_345 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos _135_345)))
end))
end)
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(
# 574 "FStar.Parser.ToSyntax.fst"
let _51_1047 = (FStar_List.fold_left (fun _51_1035 pat -> (match (_51_1035) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (_51_1038, t) -> begin
(let _135_349 = (let _135_348 = (free_type_vars env t)
in (FStar_List.append _135_348 ftvs))
in (env, _135_349))
end
| _51_1043 -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_51_1047) with
| (_51_1045, ftv) -> begin
(
# 578 "FStar.Parser.ToSyntax.fst"
let ftv = (sort_ftv ftv)
in (
# 579 "FStar.Parser.ToSyntax.fst"
let binders = (let _135_351 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar ((a, true))) top.FStar_Parser_AST.range))))
in (FStar_List.append _135_351 binders))
in (
# 588 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun env bs sc_pat_opt _51_9 -> (match (_51_9) with
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
let body = (let _135_361 = (let _135_360 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right _135_360 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close _135_361 body))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((sc, ((pat, None, body))::[]))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (let _135_362 = (no_annot_abs (FStar_List.rev bs) body)
in (setpos _135_362))))
end
| p::rest -> begin
(
# 599 "FStar.Parser.ToSyntax.fst"
let _51_1071 = (desugar_binding_pat env p)
in (match (_51_1071) with
| (env, b, pat) -> begin
(
# 600 "FStar.Parser.ToSyntax.fst"
let _51_1122 = (match (b) with
| LetBinder (_51_1073) -> begin
(FStar_All.failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(
# 603 "FStar.Parser.ToSyntax.fst"
let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _51_1081) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _135_364 = (let _135_363 = (FStar_Syntax_Syntax.bv_to_name x)
in (_135_363, p))
in Some (_135_364))
end
| (Some (p), Some (sc, p')) -> begin
(match ((sc.FStar_Syntax_Syntax.n, p'.FStar_Syntax_Syntax.v)) with
| (FStar_Syntax_Syntax.Tm_name (_51_1095), _51_1098) -> begin
(
# 609 "FStar.Parser.ToSyntax.fst"
let tup2 = (let _135_365 = (FStar_Syntax_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _135_365 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (
# 610 "FStar.Parser.ToSyntax.fst"
let sc = (let _135_373 = (let _135_372 = (let _135_371 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (let _135_370 = (let _135_369 = (FStar_Syntax_Syntax.as_arg sc)
in (let _135_368 = (let _135_367 = (let _135_366 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _135_366))
in (_135_367)::[])
in (_135_369)::_135_368))
in (_135_371, _135_370)))
in FStar_Syntax_Syntax.Tm_app (_135_372))
in (FStar_Syntax_Syntax.mk _135_373 None top.FStar_Parser_AST.range))
in (
# 611 "FStar.Parser.ToSyntax.fst"
let p = (let _135_374 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tup2, ((p', false))::((p, false))::[]))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _135_374))
in Some ((sc, p)))))
end
| (FStar_Syntax_Syntax.Tm_app (_51_1104, args), FStar_Syntax_Syntax.Pat_cons (_51_1109, pats)) -> begin
(
# 614 "FStar.Parser.ToSyntax.fst"
let tupn = (let _135_375 = (FStar_Syntax_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _135_375 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (
# 615 "FStar.Parser.ToSyntax.fst"
let sc = (let _135_382 = (let _135_381 = (let _135_380 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (let _135_379 = (let _135_378 = (let _135_377 = (let _135_376 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _135_376))
in (_135_377)::[])
in (FStar_List.append args _135_378))
in (_135_380, _135_379)))
in FStar_Syntax_Syntax.Tm_app (_135_381))
in (mk _135_382))
in (
# 616 "FStar.Parser.ToSyntax.fst"
let p = (let _135_383 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tupn, (FStar_List.append pats (((p, false))::[]))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _135_383))
in Some ((sc, p)))))
end
| _51_1118 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((x, aq), sc_pat_opt))
end)
in (match (_51_1122) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _51_1126; FStar_Parser_AST.level = _51_1124}, phi, _51_1132) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(
# 627 "FStar.Parser.ToSyntax.fst"
let phi = (desugar_formula env phi)
in (let _135_391 = (let _135_390 = (let _135_389 = (FStar_Syntax_Syntax.fvar a FStar_Syntax_Syntax.Delta_equational None)
in (let _135_388 = (let _135_387 = (FStar_Syntax_Syntax.as_arg phi)
in (let _135_386 = (let _135_385 = (let _135_384 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _135_384))
in (_135_385)::[])
in (_135_387)::_135_386))
in (_135_389, _135_388)))
in FStar_Syntax_Syntax.Tm_app (_135_390))
in (mk _135_391)))
end
| FStar_Parser_AST.App (_51_1137) -> begin
(
# 633 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun args e -> (match ((let _135_396 = (unparen e)
in _135_396.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(
# 635 "FStar.Parser.ToSyntax.fst"
let arg = (let _135_397 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _135_397))
in (aux ((arg)::args) e))
end
| _51_1149 -> begin
(
# 638 "FStar.Parser.ToSyntax.fst"
let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app ((head, args)))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _135_400 = (let _135_399 = (let _135_398 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range), t1))::[], t2))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in (_135_398, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))
in FStar_Syntax_Syntax.Tm_meta (_135_399))
in (mk _135_400))
end
| FStar_Parser_AST.Let (is_rec, (pat, _snd)::_tl, body) -> begin
(
# 647 "FStar.Parser.ToSyntax.fst"
let ds_let_rec_or_app = (fun _51_1165 -> (match (()) with
| () -> begin
(
# 648 "FStar.Parser.ToSyntax.fst"
let bindings = ((pat, _snd))::_tl
in (
# 649 "FStar.Parser.ToSyntax.fst"
let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _51_1169 -> (match (_51_1169) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _135_404 = (destruct_app_pattern env top_level p)
in (_135_404, def))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _135_405 = (destruct_app_pattern env top_level p)
in (_135_405, def))
end
| _51_1175 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _51_1180); FStar_Parser_AST.prange = _51_1177}, t) -> begin
if top_level then begin
(let _135_408 = (let _135_407 = (let _135_406 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_135_406))
in (_135_407, [], Some (t)))
in (_135_408, def))
end else begin
((FStar_Util.Inl (id), [], Some (t)), def)
end
end
| FStar_Parser_AST.PatVar (id, _51_1189) -> begin
if top_level then begin
(let _135_411 = (let _135_410 = (let _135_409 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_135_409))
in (_135_410, [], None))
in (_135_411, def))
end else begin
((FStar_Util.Inl (id), [], None), def)
end
end
| _51_1193 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected let binding", p.FStar_Parser_AST.prange))))
end)
end)
end
end))))
in (
# 666 "FStar.Parser.ToSyntax.fst"
let _51_1222 = (FStar_List.fold_left (fun _51_1198 _51_1207 -> (match ((_51_1198, _51_1207)) with
| ((env, fnames, rec_bindings), ((f, _51_1201, _51_1203), _51_1206)) -> begin
(
# 668 "FStar.Parser.ToSyntax.fst"
let _51_1218 = (match (f) with
| FStar_Util.Inl (x) -> begin
(
# 670 "FStar.Parser.ToSyntax.fst"
let _51_1212 = (FStar_Parser_Env.push_bv env x)
in (match (_51_1212) with
| (env, xx) -> begin
(let _135_415 = (let _135_414 = (FStar_Syntax_Syntax.mk_binder xx)
in (_135_414)::rec_bindings)
in (env, FStar_Util.Inl (xx), _135_415))
end))
end
| FStar_Util.Inr (l) -> begin
(let _135_416 = (FStar_Parser_Env.push_top_level_rec_binding env l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in (_135_416, FStar_Util.Inr (l), rec_bindings))
end)
in (match (_51_1218) with
| (env, lbname, rec_bindings) -> begin
(env, (lbname)::fnames, rec_bindings)
end))
end)) (env, [], []) funs)
in (match (_51_1222) with
| (env', fnames, rec_bindings) -> begin
(
# 676 "FStar.Parser.ToSyntax.fst"
let fnames = (FStar_List.rev fnames)
in (
# 678 "FStar.Parser.ToSyntax.fst"
let desugar_one_def = (fun env lbname _51_1233 -> (match (_51_1233) with
| ((_51_1228, args, result_t), def) -> begin
(
# 679 "FStar.Parser.ToSyntax.fst"
let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _135_423 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed ((def, t))) _135_423 FStar_Parser_AST.Expr))
end)
in (
# 682 "FStar.Parser.ToSyntax.fst"
let def = (match (args) with
| [] -> begin
def
end
| _51_1240 -> begin
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
(let _135_425 = (let _135_424 = (incr_delta_qualifier body)
in (FStar_Syntax_Syntax.lid_as_fv l _135_424 None))
in FStar_Util.Inr (_135_425))
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
in (let _135_428 = (let _135_427 = (let _135_426 = (FStar_Syntax_Subst.close rec_bindings body)
in ((is_rec, lbs), _135_426))
in FStar_Syntax_Syntax.Tm_let (_135_427))
in (FStar_All.pipe_left mk _135_428))))))
end))))
end))
in (
# 696 "FStar.Parser.ToSyntax.fst"
let ds_non_rec = (fun pat t1 t2 -> (
# 697 "FStar.Parser.ToSyntax.fst"
let t1 = (desugar_term env t1)
in (
# 698 "FStar.Parser.ToSyntax.fst"
let _51_1259 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_51_1259) with
| (env, binder, pat) -> begin
(match (binder) with
| LetBinder (l, t) -> begin
(
# 701 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env t2)
in (
# 702 "FStar.Parser.ToSyntax.fst"
let fv = (let _135_435 = (incr_delta_qualifier t1)
in (FStar_Syntax_Syntax.lid_as_fv l _135_435 None))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]), body))))))
end
| LocalBinder (x, _51_1268) -> begin
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
(let _135_440 = (let _135_439 = (let _135_438 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _135_437 = (let _135_436 = (FStar_Syntax_Util.branch (pat, None, body))
in (_135_436)::[])
in (_135_438, _135_437)))
in FStar_Syntax_Syntax.Tm_match (_135_439))
in (FStar_Syntax_Syntax.mk _135_440 None body.FStar_Syntax_Syntax.pos))
end)
in (let _135_445 = (let _135_444 = (let _135_443 = (let _135_442 = (let _135_441 = (FStar_Syntax_Syntax.mk_binder x)
in (_135_441)::[])
in (FStar_Syntax_Subst.close _135_442 body))
in ((false, ((mk_lb (FStar_Util.Inl (x), x.FStar_Syntax_Syntax.sort, t1)))::[]), _135_443))
in FStar_Syntax_Syntax.Tm_let (_135_444))
in (FStar_All.pipe_left mk _135_445))))
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
in (let _135_456 = (let _135_455 = (let _135_454 = (desugar_term env t1)
in (let _135_453 = (let _135_452 = (let _135_447 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (let _135_446 = (desugar_term env t2)
in (_135_447, None, _135_446)))
in (let _135_451 = (let _135_450 = (let _135_449 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (let _135_448 = (desugar_term env t3)
in (_135_449, None, _135_448)))
in (_135_450)::[])
in (_135_452)::_135_451))
in (_135_454, _135_453)))
in FStar_Syntax_Syntax.Tm_match (_135_455))
in (mk _135_456)))
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
let desugar_branch = (fun _51_1308 -> (match (_51_1308) with
| (pat, wopt, b) -> begin
(
# 736 "FStar.Parser.ToSyntax.fst"
let _51_1311 = (desugar_match_pat env pat)
in (match (_51_1311) with
| (env, pat) -> begin
(
# 737 "FStar.Parser.ToSyntax.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _135_459 = (desugar_term env e)
in Some (_135_459))
end)
in (
# 740 "FStar.Parser.ToSyntax.fst"
let b = (desugar_term env b)
in (FStar_Syntax_Util.branch (pat, wopt, b))))
end))
end))
in (let _135_463 = (let _135_462 = (let _135_461 = (desugar_term env e)
in (let _135_460 = (FStar_List.map desugar_branch branches)
in (_135_461, _135_460)))
in FStar_Syntax_Syntax.Tm_match (_135_462))
in (FStar_All.pipe_left mk _135_463)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _135_467 = (let _135_466 = (let _135_465 = (desugar_term env e)
in (let _135_464 = (desugar_typ env t)
in (_135_465, _135_464, None)))
in FStar_Syntax_Syntax.Tm_ascribed (_135_466))
in (FStar_All.pipe_left mk _135_467))
end
| FStar_Parser_AST.Record (_51_1322, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected empty record", top.FStar_Parser_AST.range))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(
# 751 "FStar.Parser.ToSyntax.fst"
let _51_1333 = (FStar_List.hd fields)
in (match (_51_1333) with
| (f, _51_1332) -> begin
(
# 752 "FStar.Parser.ToSyntax.fst"
let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (
# 753 "FStar.Parser.ToSyntax.fst"
let _51_1339 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_51_1339) with
| (record, _51_1338) -> begin
(
# 754 "FStar.Parser.ToSyntax.fst"
let get_field = (fun xopt f -> (
# 755 "FStar.Parser.ToSyntax.fst"
let fn = f.FStar_Ident.ident
in (
# 756 "FStar.Parser.ToSyntax.fst"
let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _51_1347 -> (match (_51_1347) with
| (g, _51_1346) -> begin
(
# 757 "FStar.Parser.ToSyntax.fst"
let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_51_1351, e) -> begin
(let _135_475 = (qfn fn)
in (_135_475, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _135_478 = (let _135_477 = (let _135_476 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in (_135_476, top.FStar_Parser_AST.range))
in FStar_Syntax_Syntax.Error (_135_477))
in (Prims.raise _135_478))
end
| Some (x) -> begin
(let _135_479 = (qfn fn)
in (_135_479, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Project ((x, f))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end))))
in (
# 768 "FStar.Parser.ToSyntax.fst"
let recterm = (match (eopt) with
| None -> begin
(let _135_484 = (let _135_483 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _51_1363 -> (match (_51_1363) with
| (f, _51_1362) -> begin
(let _135_482 = (let _135_481 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _135_481))
in (_135_482, FStar_Parser_AST.Nothing))
end))))
in (record.FStar_Parser_Env.constrname, _135_483))
in FStar_Parser_AST.Construct (_135_484))
end
| Some (e) -> begin
(
# 775 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (
# 776 "FStar.Parser.ToSyntax.fst"
let xterm = (let _135_486 = (let _135_485 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_135_485))
in (FStar_Parser_AST.mk_term _135_486 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (
# 777 "FStar.Parser.ToSyntax.fst"
let record = (let _135_489 = (let _135_488 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _51_1371 -> (match (_51_1371) with
| (f, _51_1370) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _135_488))
in FStar_Parser_AST.Record (_135_489))
in FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar ((x, false))) x.FStar_Ident.idRange), e))::[], (FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level))))))
end)
in (
# 780 "FStar.Parser.ToSyntax.fst"
let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (
# 781 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _51_1387; FStar_Syntax_Syntax.pos = _51_1385; FStar_Syntax_Syntax.vars = _51_1383}, args); FStar_Syntax_Syntax.tk = _51_1381; FStar_Syntax_Syntax.pos = _51_1379; FStar_Syntax_Syntax.vars = _51_1377}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(
# 784 "FStar.Parser.ToSyntax.fst"
let e = (let _135_497 = (let _135_496 = (let _135_495 = (let _135_494 = (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos)
in (let _135_493 = (let _135_492 = (let _135_491 = (let _135_490 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _135_490))
in FStar_Syntax_Syntax.Record_ctor (_135_491))
in Some (_135_492))
in (FStar_Syntax_Syntax.fvar _135_494 FStar_Syntax_Syntax.Delta_constant _135_493)))
in (_135_495, args))
in FStar_Syntax_Syntax.Tm_app (_135_496))
in (FStar_All.pipe_left mk _135_497))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end
| _51_1401 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(
# 792 "FStar.Parser.ToSyntax.fst"
let _51_1408 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_projector_by_field_name env) f)
in (match (_51_1408) with
| (fieldname, is_rec) -> begin
(
# 793 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env e)
in (
# 794 "FStar.Parser.ToSyntax.fst"
let fn = (
# 795 "FStar.Parser.ToSyntax.fst"
let _51_1413 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_51_1413) with
| (ns, _51_1412) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (
# 797 "FStar.Parser.ToSyntax.fst"
let qual = if is_rec then begin
Some (FStar_Syntax_Syntax.Record_projector (fn))
end else begin
None
end
in (let _135_503 = (let _135_502 = (let _135_501 = (let _135_498 = (FStar_Ident.set_lid_range fieldname (FStar_Ident.range_of_lid f))
in (FStar_Syntax_Syntax.fvar _135_498 FStar_Syntax_Syntax.Delta_equational (Some (FStar_Syntax_Syntax.Record_projector (fn)))))
in (let _135_500 = (let _135_499 = (FStar_Syntax_Syntax.as_arg e)
in (_135_499)::[])
in (_135_501, _135_500)))
in FStar_Syntax_Syntax.Tm_app (_135_502))
in (FStar_All.pipe_left mk _135_503)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| _51_1423 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _51_1425 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_args : FStar_Parser_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun _51_1430 -> (match (_51_1430) with
| (a, imp) -> begin
(let _135_507 = (desugar_term env a)
in (arg_withimp_e imp _135_507))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r default_ok env t -> (
# 814 "FStar.Parser.ToSyntax.fst"
let fail = (fun msg -> (Prims.raise (FStar_Syntax_Syntax.Error ((msg, r)))))
in (
# 815 "FStar.Parser.ToSyntax.fst"
let is_requires = (fun _51_1442 -> (match (_51_1442) with
| (t, _51_1441) -> begin
(match ((let _135_515 = (unparen t)
in _135_515.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Requires (_51_1444) -> begin
true
end
| _51_1447 -> begin
false
end)
end))
in (
# 818 "FStar.Parser.ToSyntax.fst"
let is_ensures = (fun _51_1452 -> (match (_51_1452) with
| (t, _51_1451) -> begin
(match ((let _135_518 = (unparen t)
in _135_518.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ensures (_51_1454) -> begin
true
end
| _51_1457 -> begin
false
end)
end))
in (
# 821 "FStar.Parser.ToSyntax.fst"
let is_app = (fun head _51_1463 -> (match (_51_1463) with
| (t, _51_1462) -> begin
(match ((let _135_523 = (unparen t)
in _135_523.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _51_1467; FStar_Parser_AST.level = _51_1465}, _51_1472, _51_1474) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| _51_1478 -> begin
false
end)
end))
in (
# 824 "FStar.Parser.ToSyntax.fst"
let pre_process_comp_typ = (fun t -> (
# 825 "FStar.Parser.ToSyntax.fst"
let _51_1483 = (head_and_args t)
in (match (_51_1483) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(
# 828 "FStar.Parser.ToSyntax.fst"
let unit_tm = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (
# 829 "FStar.Parser.ToSyntax.fst"
let nil_pat = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr), FStar_Parser_AST.Nothing)
in (
# 830 "FStar.Parser.ToSyntax.fst"
let args = (match (args) with
| [] -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Not enough arguments to \'Lemma\'", t.FStar_Parser_AST.range))))
end
| ens::[] -> begin
(
# 833 "FStar.Parser.ToSyntax.fst"
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
# 838 "FStar.Parser.ToSyntax.fst"
let head = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_name env) lemma)
in (head, args)))))
end
| FStar_Parser_AST.Name (l) when (FStar_Parser_Env.is_effect_name env l) -> begin
(let _135_526 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_name env) l)
in (_135_526, args))
end
| FStar_Parser_AST.Name (l) when ((let _135_527 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _135_527 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(let _135_528 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in (_135_528, args))
end
| FStar_Parser_AST.Name (l) when ((let _135_529 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _135_529 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(let _135_530 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)
in (_135_530, args))
end
| FStar_Parser_AST.Name (l) when ((((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) && default_ok) -> begin
(let _135_531 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in (_135_531, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _51_1511 when default_ok -> begin
(let _135_532 = (FStar_Ident.set_lid_range env.FStar_Parser_Env.default_result_effect head.FStar_Parser_AST.range)
in (_135_532, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _51_1513 -> begin
(let _135_534 = (let _135_533 = (FStar_Parser_AST.term_to_string t)
in (FStar_Util.format1 "%s is not an effect" _135_533))
in (fail _135_534))
end)
end)))
in (
# 868 "FStar.Parser.ToSyntax.fst"
let _51_1516 = (pre_process_comp_typ t)
in (match (_51_1516) with
| (eff, args) -> begin
(
# 869 "FStar.Parser.ToSyntax.fst"
let _51_1517 = if ((FStar_List.length args) = 0) then begin
(let _135_536 = (let _135_535 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" _135_535))
in (fail _135_536))
end else begin
()
end
in (
# 871 "FStar.Parser.ToSyntax.fst"
let _51_1521 = (let _135_538 = (FStar_List.hd args)
in (let _135_537 = (FStar_List.tl args)
in (_135_538, _135_537)))
in (match (_51_1521) with
| (result_arg, rest) -> begin
(
# 872 "FStar.Parser.ToSyntax.fst"
let result_typ = (desugar_typ env (Prims.fst result_arg))
in (
# 873 "FStar.Parser.ToSyntax.fst"
let rest = (desugar_args env rest)
in (
# 874 "FStar.Parser.ToSyntax.fst"
let _51_1546 = (FStar_All.pipe_right rest (FStar_List.partition (fun _51_1527 -> (match (_51_1527) with
| (t, _51_1526) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _51_1533; FStar_Syntax_Syntax.pos = _51_1531; FStar_Syntax_Syntax.vars = _51_1529}, _51_1538::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| _51_1543 -> begin
false
end)
end))))
in (match (_51_1546) with
| (dec, rest) -> begin
(
# 880 "FStar.Parser.ToSyntax.fst"
let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _51_1550 -> (match (_51_1550) with
| (t, _51_1549) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_51_1552, (arg, _51_1555)::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| _51_1561 -> begin
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
# 888 "FStar.Parser.ToSyntax.fst"
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
# 894 "FStar.Parser.ToSyntax.fst"
let rest = if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid) then begin
(match (rest) with
| req::ens::(pat, aq)::[] -> begin
(
# 898 "FStar.Parser.ToSyntax.fst"
let pat = (match (pat.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
(
# 900 "FStar.Parser.ToSyntax.fst"
let nil = (FStar_Syntax_Syntax.mk_Tm_uinst pat ((FStar_Syntax_Syntax.U_succ (FStar_Syntax_Syntax.U_zero))::[]))
in (
# 901 "FStar.Parser.ToSyntax.fst"
let pattern = (let _135_542 = (let _135_541 = (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _135_541 FStar_Syntax_Syntax.Delta_constant None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _135_542 ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app nil (((pattern, Some (FStar_Syntax_Syntax.imp_tag)))::[]) None pat.FStar_Syntax_Syntax.pos)))
end
| _51_1575 -> begin
pat
end)
in (let _135_546 = (let _135_545 = (let _135_544 = (let _135_543 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((pat, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)))) None pat.FStar_Syntax_Syntax.pos)
in (_135_543, aq))
in (_135_544)::[])
in (ens)::_135_545)
in (req)::_135_546))
end
| _51_1578 -> begin
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
# 914 "FStar.Parser.ToSyntax.fst"
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
| _51_1590 -> begin
None
end))
in (
# 921 "FStar.Parser.ToSyntax.fst"
let mk = (fun t -> (FStar_Syntax_Syntax.mk t None f.FStar_Parser_AST.range))
in (
# 922 "FStar.Parser.ToSyntax.fst"
let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (
# 923 "FStar.Parser.ToSyntax.fst"
let setpos = (fun t -> (
# 923 "FStar.Parser.ToSyntax.fst"
let _51_1597 = t
in {FStar_Syntax_Syntax.n = _51_1597.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _51_1597.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _51_1597.FStar_Syntax_Syntax.vars}))
in (
# 924 "FStar.Parser.ToSyntax.fst"
let desugar_quant = (fun q b pats body -> (
# 925 "FStar.Parser.ToSyntax.fst"
let tk = (desugar_binder env (
# 925 "FStar.Parser.ToSyntax.fst"
let _51_1604 = b
in {FStar_Parser_AST.b = _51_1604.FStar_Parser_AST.b; FStar_Parser_AST.brange = _51_1604.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _51_1604.FStar_Parser_AST.aqual}))
in (
# 926 "FStar.Parser.ToSyntax.fst"
let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _135_581 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _135_581)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(
# 929 "FStar.Parser.ToSyntax.fst"
let _51_1618 = (FStar_Parser_Env.push_bv env a)
in (match (_51_1618) with
| (env, a) -> begin
(
# 930 "FStar.Parser.ToSyntax.fst"
let a = (
# 930 "FStar.Parser.ToSyntax.fst"
let _51_1619 = a
in {FStar_Syntax_Syntax.ppname = _51_1619.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _51_1619.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (
# 931 "FStar.Parser.ToSyntax.fst"
let pats = (desugar_pats env pats)
in (
# 932 "FStar.Parser.ToSyntax.fst"
let body = (desugar_formula env body)
in (
# 933 "FStar.Parser.ToSyntax.fst"
let body = (match (pats) with
| [] -> begin
body
end
| _51_1626 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((body, FStar_Syntax_Syntax.Meta_pattern (pats)))))
end)
in (
# 936 "FStar.Parser.ToSyntax.fst"
let body = (let _135_584 = (let _135_583 = (let _135_582 = (FStar_Syntax_Syntax.mk_binder a)
in (_135_582)::[])
in (no_annot_abs _135_583 body))
in (FStar_All.pipe_left setpos _135_584))
in (let _135_590 = (let _135_589 = (let _135_588 = (let _135_585 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Syntax_Syntax.fvar _135_585 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (let _135_587 = (let _135_586 = (FStar_Syntax_Syntax.as_arg body)
in (_135_586)::[])
in (_135_588, _135_587)))
in FStar_Syntax_Syntax.Tm_app (_135_589))
in (FStar_All.pipe_left mk _135_590)))))))
end))
end
| _51_1630 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 941 "FStar.Parser.ToSyntax.fst"
let push_quant = (fun q binders pats body -> (match (binders) with
| b::b'::_rest -> begin
(
# 943 "FStar.Parser.ToSyntax.fst"
let rest = (b')::_rest
in (
# 944 "FStar.Parser.ToSyntax.fst"
let body = (let _135_605 = (q (rest, pats, body))
in (let _135_604 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _135_605 _135_604 FStar_Parser_AST.Formula)))
in (let _135_606 = (q ((b)::[], [], body))
in (FStar_Parser_AST.mk_term _135_606 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _51_1644 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _135_607 = (unparen f)
in _135_607.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(
# 950 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env f)
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((l, f.FStar_Syntax_Syntax.pos, p)))))))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall (_1::_2::_3, pats, body) -> begin
(
# 957 "FStar.Parser.ToSyntax.fst"
let binders = (_1)::(_2)::_3
in (let _135_609 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _135_609)))
end
| FStar_Parser_AST.QExists (_1::_2::_3, pats, body) -> begin
(
# 961 "FStar.Parser.ToSyntax.fst"
let binders = (_1)::(_2)::_3
in (let _135_611 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _135_611)))
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
| _51_1702 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (
# 976 "FStar.Parser.ToSyntax.fst"
let _51_1726 = (FStar_List.fold_left (fun _51_1707 b -> (match (_51_1707) with
| (env, out) -> begin
(
# 977 "FStar.Parser.ToSyntax.fst"
let tk = (desugar_binder env (
# 977 "FStar.Parser.ToSyntax.fst"
let _51_1709 = b
in {FStar_Parser_AST.b = _51_1709.FStar_Parser_AST.b; FStar_Parser_AST.brange = _51_1709.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _51_1709.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(
# 980 "FStar.Parser.ToSyntax.fst"
let _51_1718 = (FStar_Parser_Env.push_bv env a)
in (match (_51_1718) with
| (env, a) -> begin
(
# 981 "FStar.Parser.ToSyntax.fst"
let a = (
# 981 "FStar.Parser.ToSyntax.fst"
let _51_1719 = a
in {FStar_Syntax_Syntax.ppname = _51_1719.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _51_1719.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (env, ((a, (trans_aqual b.FStar_Parser_AST.aqual)))::out))
end))
end
| _51_1723 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected binder", b.FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_51_1726) with
| (env, tpars) -> begin
(env, (FStar_List.rev tpars))
end)))
and desugar_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(let _135_618 = (desugar_typ env t)
in (Some (x), _135_618))
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _135_619 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None x.FStar_Ident.idRange)
in (Some (x), _135_619))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _135_620 = (desugar_typ env t)
in (None, _135_620))
end
| FStar_Parser_AST.Variable (x) -> begin
(Some (x), FStar_Syntax_Syntax.tun)
end))

# 993 "FStar.Parser.ToSyntax.fst"
let mk_data_discriminators : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  FStar_Ident.lid  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun quals env t tps k datas -> (
# 994 "FStar.Parser.ToSyntax.fst"
let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_Env.iface) || env.FStar_Parser_Env.admitted_iface) then begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (
# 997 "FStar.Parser.ToSyntax.fst"
let binders = (let _135_636 = (let _135_635 = (FStar_Syntax_Util.arrow_formals k)
in (Prims.fst _135_635))
in (FStar_List.append tps _135_636))
in (
# 998 "FStar.Parser.ToSyntax.fst"
let p = (FStar_Ident.range_of_lid t)
in (
# 999 "FStar.Parser.ToSyntax.fst"
let _51_1753 = (FStar_Syntax_Util.args_of_binders binders)
in (match (_51_1753) with
| (binders, args) -> begin
(
# 1000 "FStar.Parser.ToSyntax.fst"
let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _51_1757 -> (match (_51_1757) with
| (x, _51_1756) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
in (
# 1001 "FStar.Parser.ToSyntax.fst"
let binders = (let _135_642 = (let _135_641 = (let _135_640 = (let _135_639 = (let _135_638 = (FStar_Syntax_Syntax.lid_as_fv t FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _135_638))
in (FStar_Syntax_Syntax.mk_Tm_app _135_639 args None p))
in (FStar_All.pipe_left FStar_Syntax_Syntax.null_binder _135_640))
in (_135_641)::[])
in (FStar_List.append imp_binders _135_642))
in (
# 1002 "FStar.Parser.ToSyntax.fst"
let disc_type = (let _135_645 = (let _135_644 = (let _135_643 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _135_643))
in (FStar_Syntax_Syntax.mk_Total _135_644))
in (FStar_Syntax_Util.arrow binders _135_645))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (
# 1004 "FStar.Parser.ToSyntax.fst"
let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (let _135_648 = (let _135_647 = (quals ((FStar_Syntax_Syntax.Logic)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in (disc_name, [], disc_type, _135_647, (FStar_Ident.range_of_lid disc_name)))
in FStar_Syntax_Syntax.Sig_declare_typ (_135_648)))))))))
end))))))

# 1007 "FStar.Parser.ToSyntax.fst"
let mk_indexed_projectors : FStar_Syntax_Syntax.fv_qual  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun fvq refine_domain env tc lid inductive_tps imp_tps fields t -> (
# 1008 "FStar.Parser.ToSyntax.fst"
let p = (FStar_Ident.range_of_lid lid)
in (
# 1009 "FStar.Parser.ToSyntax.fst"
let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p))
in (
# 1010 "FStar.Parser.ToSyntax.fst"
let projectee = (fun ptyp -> (FStar_Syntax_Syntax.gen_bv "projectee" (Some (p)) ptyp))
in (
# 1011 "FStar.Parser.ToSyntax.fst"
let tps = (FStar_List.map2 (fun _51_1780 _51_1784 -> (match ((_51_1780, _51_1784)) with
| ((_51_1778, imp), (x, _51_1783)) -> begin
(x, imp)
end)) inductive_tps imp_tps)
in (
# 1012 "FStar.Parser.ToSyntax.fst"
let _51_1885 = (
# 1013 "FStar.Parser.ToSyntax.fst"
let _51_1788 = (FStar_Syntax_Util.head_and_args t)
in (match (_51_1788) with
| (head, args0) -> begin
(
# 1014 "FStar.Parser.ToSyntax.fst"
let args = (
# 1015 "FStar.Parser.ToSyntax.fst"
let rec arguments = (fun tps args -> (match ((tps, args)) with
| ([], _51_1794) -> begin
args
end
| (_51_1797, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Not enough arguments to type", (FStar_Ident.range_of_lid lid)))))
end
| ((_51_1802, Some (FStar_Syntax_Syntax.Implicit (_51_1804)))::tps', (_51_1811, Some (FStar_Syntax_Syntax.Implicit (_51_1813)))::args') -> begin
(arguments tps' args')
end
| ((_51_1821, Some (FStar_Syntax_Syntax.Implicit (_51_1823)))::tps', (_51_1831, _51_1833)::_51_1829) -> begin
(arguments tps' args)
end
| ((_51_1840, _51_1842)::_51_1838, (a, Some (FStar_Syntax_Syntax.Implicit (_51_1849)))::_51_1846) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected implicit annotation on argument", a.FStar_Syntax_Syntax.pos))))
end
| ((_51_1857, _51_1859)::tps', (_51_1864, _51_1866)::args') -> begin
(arguments tps' args')
end))
in (arguments inductive_tps args0))
in (
# 1024 "FStar.Parser.ToSyntax.fst"
let indices = (FStar_All.pipe_right args (FStar_List.map (fun _51_1871 -> (let _135_678 = (FStar_Syntax_Syntax.new_bv (Some (p)) FStar_Syntax_Syntax.tun)
in (FStar_All.pipe_right _135_678 FStar_Syntax_Syntax.mk_binder)))))
in (
# 1025 "FStar.Parser.ToSyntax.fst"
let arg_typ = (let _135_683 = (let _135_679 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _135_679))
in (let _135_682 = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _51_1876 -> (match (_51_1876) with
| (x, imp) -> begin
(let _135_681 = (FStar_Syntax_Syntax.bv_to_name x)
in (_135_681, imp))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app _135_683 _135_682 None p)))
in (
# 1027 "FStar.Parser.ToSyntax.fst"
let arg_binder = if (not (refine_domain)) then begin
(let _135_684 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder _135_684))
end else begin
(
# 1030 "FStar.Parser.ToSyntax.fst"
let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (
# 1031 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p)) arg_typ)
in (let _135_693 = (
# 1032 "FStar.Parser.ToSyntax.fst"
let _51_1880 = (projectee arg_typ)
in (let _135_692 = (let _135_691 = (let _135_690 = (let _135_689 = (let _135_685 = (FStar_Ident.set_lid_range disc_name p)
in (FStar_Syntax_Syntax.fvar _135_685 FStar_Syntax_Syntax.Delta_equational None))
in (let _135_688 = (let _135_687 = (let _135_686 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _135_686))
in (_135_687)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _135_689 _135_688 None p)))
in (FStar_Syntax_Util.b2t _135_690))
in (FStar_Syntax_Util.refine x _135_691))
in {FStar_Syntax_Syntax.ppname = _51_1880.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _51_1880.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _135_692}))
in (FStar_Syntax_Syntax.mk_binder _135_693))))
end
in (arg_binder, indices)))))
end))
in (match (_51_1885) with
| (arg_binder, indices) -> begin
(
# 1036 "FStar.Parser.ToSyntax.fst"
let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder))
in (
# 1037 "FStar.Parser.ToSyntax.fst"
let imp_binders = (let _135_695 = (FStar_All.pipe_right indices (FStar_List.map (fun _51_1890 -> (match (_51_1890) with
| (x, _51_1889) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
in (FStar_List.append imp_tps _135_695))
in (
# 1038 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (
# 1040 "FStar.Parser.ToSyntax.fst"
let arg = (FStar_Syntax_Util.arg_of_non_null_binder arg_binder)
in (
# 1042 "FStar.Parser.ToSyntax.fst"
let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _51_1898 -> (match (_51_1898) with
| (a, _51_1897) -> begin
(
# 1043 "FStar.Parser.ToSyntax.fst"
let _51_1902 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (_51_1902) with
| (field_name, _51_1901) -> begin
(
# 1044 "FStar.Parser.ToSyntax.fst"
let proj = (let _135_699 = (let _135_698 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.fv_to_tm _135_698))
in (FStar_Syntax_Syntax.mk_Tm_app _135_699 ((arg)::[]) None p))
in FStar_Syntax_Syntax.NT ((a, proj)))
end))
end))))
in (
# 1047 "FStar.Parser.ToSyntax.fst"
let ntps = (FStar_List.length tps)
in (
# 1048 "FStar.Parser.ToSyntax.fst"
let all_params = (FStar_List.append imp_tps fields)
in (let _135_735 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _51_1911 -> (match (_51_1911) with
| (x, _51_1910) -> begin
(
# 1051 "FStar.Parser.ToSyntax.fst"
let _51_1915 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_51_1915) with
| (field_name, _51_1914) -> begin
(
# 1052 "FStar.Parser.ToSyntax.fst"
let t = (let _135_703 = (let _135_702 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total _135_702))
in (FStar_Syntax_Util.arrow binders _135_703))
in (
# 1053 "FStar.Parser.ToSyntax.fst"
let only_decl = (((let _135_704 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _135_704)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _135_706 = (let _135_705 = (FStar_Parser_Env.current_module env)
in _135_705.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _135_706)))
in (
# 1057 "FStar.Parser.ToSyntax.fst"
let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (
# 1058 "FStar.Parser.ToSyntax.fst"
let quals = (fun q -> if only_decl then begin
(FStar_Syntax_Syntax.Assumption)::q
end else begin
q
end)
in (
# 1059 "FStar.Parser.ToSyntax.fst"
let quals = (quals ((FStar_Syntax_Syntax.Projector ((lid, x.FStar_Syntax_Syntax.ppname)))::[]))
in (
# 1060 "FStar.Parser.ToSyntax.fst"
let decl = FStar_Syntax_Syntax.Sig_declare_typ ((field_name, [], t, quals, (FStar_Ident.range_of_lid field_name)))
in if only_decl then begin
(decl)::[]
end else begin
(
# 1063 "FStar.Parser.ToSyntax.fst"
let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (
# 1064 "FStar.Parser.ToSyntax.fst"
let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _51_1927 -> (match (_51_1927) with
| (x, imp) -> begin
(
# 1065 "FStar.Parser.ToSyntax.fst"
let b = (FStar_Syntax_Syntax.is_implicit imp)
in if ((i + ntps) = j) then begin
(let _135_711 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in (_135_711, b))
end else begin
if (b && (j < ntps)) then begin
(let _135_715 = (let _135_714 = (let _135_713 = (let _135_712 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (_135_712, FStar_Syntax_Syntax.tun))
in FStar_Syntax_Syntax.Pat_dot_term (_135_713))
in (pos _135_714))
in (_135_715, b))
end else begin
(let _135_718 = (let _135_717 = (let _135_716 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_135_716))
in (pos _135_717))
in (_135_718, b))
end
end)
end))))
in (
# 1071 "FStar.Parser.ToSyntax.fst"
let pat = (let _135_723 = (let _135_721 = (let _135_720 = (let _135_719 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in (_135_719, arg_pats))
in FStar_Syntax_Syntax.Pat_cons (_135_720))
in (FStar_All.pipe_right _135_721 pos))
in (let _135_722 = (FStar_Syntax_Syntax.bv_to_name projection)
in (_135_723, None, _135_722)))
in (
# 1072 "FStar.Parser.ToSyntax.fst"
let body = (let _135_727 = (let _135_726 = (let _135_725 = (let _135_724 = (FStar_Syntax_Util.branch pat)
in (_135_724)::[])
in (arg_exp, _135_725))
in FStar_Syntax_Syntax.Tm_match (_135_726))
in (FStar_Syntax_Syntax.mk _135_727 None p))
in (
# 1073 "FStar.Parser.ToSyntax.fst"
let imp = (no_annot_abs binders body)
in (
# 1074 "FStar.Parser.ToSyntax.fst"
let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end else begin
FStar_Syntax_Syntax.Delta_equational
end
in (
# 1077 "FStar.Parser.ToSyntax.fst"
let lb = (let _135_729 = (let _135_728 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (_135_728))
in {FStar_Syntax_Syntax.lbname = _135_729; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = imp})
in (
# 1082 "FStar.Parser.ToSyntax.fst"
let impl = (let _135_734 = (let _135_733 = (let _135_732 = (let _135_731 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _135_731 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_135_732)::[])
in ((false, (lb)::[]), p, _135_733, quals))
in FStar_Syntax_Syntax.Sig_let (_135_734))
in if no_decl then begin
(impl)::[]
end else begin
(decl)::(impl)::[]
end))))))))
end))))))
end))
end))))
in (FStar_All.pipe_right _135_735 FStar_List.flatten)))))))))
end)))))))

# 1085 "FStar.Parser.ToSyntax.fst"
let mk_data_projectors : FStar_Parser_Env.env  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun env _51_1940 -> (match (_51_1940) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _51_1943, t, l, n, quals, _51_1949, _51_1951) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(
# 1088 "FStar.Parser.ToSyntax.fst"
let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _51_10 -> (match (_51_10) with
| FStar_Syntax_Syntax.RecordConstructor (_51_1956) -> begin
true
end
| _51_1959 -> begin
false
end)))) then begin
false
end else begin
(match ((FStar_Parser_Env.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > 1)
end
| _51_1963 -> begin
true
end)
end
in (
# 1094 "FStar.Parser.ToSyntax.fst"
let _51_1967 = (FStar_Syntax_Util.arrow_formals t)
in (match (_51_1967) with
| (formals, cod) -> begin
(match (formals) with
| [] -> begin
[]
end
| _51_1970 -> begin
(
# 1098 "FStar.Parser.ToSyntax.fst"
let qual = (match ((FStar_Util.find_map quals (fun _51_11 -> (match (_51_11) with
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((lid, fns)))
end
| _51_1975 -> begin
None
end)))) with
| None -> begin
FStar_Syntax_Syntax.Data_ctor
end
| Some (q) -> begin
q
end)
in (
# 1101 "FStar.Parser.ToSyntax.fst"
let _51_1982 = (FStar_Util.first_N n formals)
in (match (_51_1982) with
| (tps, rest) -> begin
(mk_indexed_projectors qual refine_domain env l lid inductive_tps tps rest cod)
end)))
end)
end)))
end
| _51_1984 -> begin
[]
end)
end))

# 1107 "FStar.Parser.ToSyntax.fst"
let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (
# 1108 "FStar.Parser.ToSyntax.fst"
let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _135_758 = (incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (_135_758))
end else begin
(incr_delta_qualifier t)
end
in (
# 1111 "FStar.Parser.ToSyntax.fst"
let lb = (let _135_763 = (let _135_759 = (FStar_Syntax_Syntax.lid_as_fv lid dd None)
in FStar_Util.Inr (_135_759))
in (let _135_762 = (let _135_760 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars _135_760))
in (let _135_761 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = _135_763; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = _135_762; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _135_761})))
in FStar_Syntax_Syntax.Sig_let (((false, (lb)::[]), rng, lids, quals)))))

# 1120 "FStar.Parser.ToSyntax.fst"
let rec desugar_tycon : FStar_Parser_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (
# 1121 "FStar.Parser.ToSyntax.fst"
let tycon_id = (fun _51_12 -> (match (_51_12) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (
# 1126 "FStar.Parser.ToSyntax.fst"
let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _135_777 = (let _135_776 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_135_776))
in (FStar_Parser_AST.mk_term _135_777 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| (FStar_Parser_AST.TAnnotated (a, _)) | (FStar_Parser_AST.TVariable (a)) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar (a)) a.FStar_Ident.idRange FStar_Parser_AST.Type)
end
| FStar_Parser_AST.NoName (t) -> begin
t
end))
in (
# 1132 "FStar.Parser.ToSyntax.fst"
let tot = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) rng FStar_Parser_AST.Expr)
in (
# 1133 "FStar.Parser.ToSyntax.fst"
let with_constructor_effect = (fun t -> (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((tot, t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level))
in (
# 1134 "FStar.Parser.ToSyntax.fst"
let apply_binders = (fun t binders -> (
# 1135 "FStar.Parser.ToSyntax.fst"
let imp_of_aqual = (fun b -> (match (b.FStar_Parser_AST.aqual) with
| Some (FStar_Parser_AST.Implicit) -> begin
FStar_Parser_AST.Hash
end
| _51_2059 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _135_790 = (let _135_789 = (let _135_788 = (binder_to_term b)
in (out, _135_788, (imp_of_aqual b)))
in FStar_Parser_AST.App (_135_789))
in (FStar_Parser_AST.mk_term _135_790 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (
# 1140 "FStar.Parser.ToSyntax.fst"
let tycon_record_as_variant = (fun _51_13 -> (match (_51_13) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(
# 1142 "FStar.Parser.ToSyntax.fst"
let constrName = (FStar_Ident.mk_ident ((Prims.strcat "Mk" id.FStar_Ident.idText), id.FStar_Ident.idRange))
in (
# 1143 "FStar.Parser.ToSyntax.fst"
let mfields = (FStar_List.map (fun _51_2072 -> (match (_51_2072) with
| (x, t) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated (((FStar_Syntax_Util.mangle_field_name x), t))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (
# 1144 "FStar.Parser.ToSyntax.fst"
let result = (let _135_796 = (let _135_795 = (let _135_794 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_135_794))
in (FStar_Parser_AST.mk_term _135_795 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _135_796 parms))
in (
# 1145 "FStar.Parser.ToSyntax.fst"
let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _135_798 = (FStar_All.pipe_right fields (FStar_List.map (fun _51_2079 -> (match (_51_2079) with
| (x, _51_2078) -> begin
(FStar_Parser_Env.qualify env x)
end))))
in (FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _135_798))))))
end
| _51_2081 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1149 "FStar.Parser.ToSyntax.fst"
let desugar_abstract_tc = (fun quals _env mutuals _51_14 -> (match (_51_14) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(
# 1151 "FStar.Parser.ToSyntax.fst"
let _51_2095 = (typars_of_binders _env binders)
in (match (_51_2095) with
| (_env', typars) -> begin
(
# 1152 "FStar.Parser.ToSyntax.fst"
let k = (match (kopt) with
| None -> begin
FStar_Syntax_Util.ktype
end
| Some (k) -> begin
(desugar_term _env' k)
end)
in (
# 1155 "FStar.Parser.ToSyntax.fst"
let tconstr = (let _135_809 = (let _135_808 = (let _135_807 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_135_807))
in (FStar_Parser_AST.mk_term _135_808 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _135_809 binders))
in (
# 1156 "FStar.Parser.ToSyntax.fst"
let qlid = (FStar_Parser_Env.qualify _env id)
in (
# 1157 "FStar.Parser.ToSyntax.fst"
let typars = (FStar_Syntax_Subst.close_binders typars)
in (
# 1158 "FStar.Parser.ToSyntax.fst"
let k = (FStar_Syntax_Subst.close typars k)
in (
# 1159 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_inductive_typ ((qlid, [], typars, k, mutuals, [], quals, rng))
in (
# 1160 "FStar.Parser.ToSyntax.fst"
let _env = (FStar_Parser_Env.push_top_level_rec_binding _env id FStar_Syntax_Syntax.Delta_constant)
in (
# 1161 "FStar.Parser.ToSyntax.fst"
let _env2 = (FStar_Parser_Env.push_top_level_rec_binding _env' id FStar_Syntax_Syntax.Delta_constant)
in (_env, _env2, se, tconstr)))))))))
end))
end
| _51_2108 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (
# 1164 "FStar.Parser.ToSyntax.fst"
let push_tparams = (fun env bs -> (
# 1165 "FStar.Parser.ToSyntax.fst"
let _51_2123 = (FStar_List.fold_left (fun _51_2114 _51_2117 -> (match ((_51_2114, _51_2117)) with
| ((env, tps), (x, imp)) -> begin
(
# 1166 "FStar.Parser.ToSyntax.fst"
let _51_2120 = (FStar_Parser_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (_51_2120) with
| (env, y) -> begin
(env, ((y, imp))::tps)
end))
end)) (env, []) bs)
in (match (_51_2123) with
| (env, bs) -> begin
(env, (FStar_List.rev bs))
end)))
in (match (tcs) with
| FStar_Parser_AST.TyconAbstract (_51_2125)::[] -> begin
(
# 1171 "FStar.Parser.ToSyntax.fst"
let tc = (FStar_List.hd tcs)
in (
# 1172 "FStar.Parser.ToSyntax.fst"
let _51_2136 = (desugar_abstract_tc quals env [] tc)
in (match (_51_2136) with
| (_51_2130, _51_2132, se, _51_2135) -> begin
(
# 1173 "FStar.Parser.ToSyntax.fst"
let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _51_2139, typars, k, [], [], quals, rng) -> begin
(
# 1175 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
quals
end else begin
(
# 1177 "FStar.Parser.ToSyntax.fst"
let _51_2148 = (let _135_817 = (FStar_Range.string_of_range rng)
in (let _135_816 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" _135_817 _135_816)))
in (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals)
end
in (
# 1180 "FStar.Parser.ToSyntax.fst"
let t = (match (typars) with
| [] -> begin
k
end
| _51_2153 -> begin
(let _135_820 = (let _135_819 = (let _135_818 = (FStar_Syntax_Syntax.mk_Total k)
in (typars, _135_818))
in FStar_Syntax_Syntax.Tm_arrow (_135_819))
in (FStar_Syntax_Syntax.mk _135_820 None rng))
end)
in FStar_Syntax_Syntax.Sig_declare_typ ((l, [], t, quals, rng))))
end
| _51_2156 -> begin
se
end)
in (
# 1185 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))
end)))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t)::[] -> begin
(
# 1190 "FStar.Parser.ToSyntax.fst"
let _51_2168 = (typars_of_binders env binders)
in (match (_51_2168) with
| (env', typars) -> begin
(
# 1191 "FStar.Parser.ToSyntax.fst"
let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _51_15 -> (match (_51_15) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| _51_2173 -> begin
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
# 1197 "FStar.Parser.ToSyntax.fst"
let t0 = t
in (
# 1198 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _51_16 -> (match (_51_16) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| _51_2181 -> begin
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
# 1203 "FStar.Parser.ToSyntax.fst"
let se = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Effect)) then begin
(
# 1205 "FStar.Parser.ToSyntax.fst"
let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (
# 1206 "FStar.Parser.ToSyntax.fst"
let typars = (FStar_Syntax_Subst.close_binders typars)
in (
# 1207 "FStar.Parser.ToSyntax.fst"
let c = (FStar_Syntax_Subst.close_comp typars c)
in (let _135_826 = (let _135_825 = (FStar_Parser_Env.qualify env id)
in (let _135_824 = (FStar_All.pipe_right quals (FStar_List.filter (fun _51_17 -> (match (_51_17) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| _51_2189 -> begin
true
end))))
in (_135_825, [], typars, c, _135_824, rng)))
in FStar_Syntax_Syntax.Sig_effect_abbrev (_135_826)))))
end else begin
(
# 1209 "FStar.Parser.ToSyntax.fst"
let t = (desugar_typ env' t)
in (
# 1210 "FStar.Parser.ToSyntax.fst"
let nm = (FStar_Parser_Env.qualify env id)
in (mk_typ_abbrev nm [] typars k t ((nm)::[]) quals rng)))
end
in (
# 1213 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[]))))))
end))
end
| FStar_Parser_AST.TyconRecord (_51_2195)::[] -> begin
(
# 1217 "FStar.Parser.ToSyntax.fst"
let trec = (FStar_List.hd tcs)
in (
# 1218 "FStar.Parser.ToSyntax.fst"
let _51_2201 = (tycon_record_as_variant trec)
in (match (_51_2201) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| _51_2205::_51_2203 -> begin
(
# 1222 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1223 "FStar.Parser.ToSyntax.fst"
let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_Env.qualify env) (tycon_id x))) tcs)
in (
# 1224 "FStar.Parser.ToSyntax.fst"
let rec collect_tcs = (fun quals et tc -> (
# 1225 "FStar.Parser.ToSyntax.fst"
let _51_2216 = et
in (match (_51_2216) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_51_2218) -> begin
(
# 1228 "FStar.Parser.ToSyntax.fst"
let trec = tc
in (
# 1229 "FStar.Parser.ToSyntax.fst"
let _51_2223 = (tycon_record_as_variant trec)
in (match (_51_2223) with
| (t, fs) -> begin
(collect_tcs ((FStar_Syntax_Syntax.RecordType (fs))::quals) (env, tcs) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(
# 1232 "FStar.Parser.ToSyntax.fst"
let _51_2235 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_51_2235) with
| (env, _51_2232, se, tconstr) -> begin
(env, (FStar_Util.Inl ((se, constructors, tconstr, quals)))::tcs)
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(
# 1235 "FStar.Parser.ToSyntax.fst"
let _51_2247 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_51_2247) with
| (env, _51_2244, se, tconstr) -> begin
(env, (FStar_Util.Inr ((se, t, quals)))::tcs)
end))
end
| _51_2249 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (
# 1238 "FStar.Parser.ToSyntax.fst"
let _51_2252 = (FStar_List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_51_2252) with
| (env, tcs) -> begin
(
# 1239 "FStar.Parser.ToSyntax.fst"
let tcs = (FStar_List.rev tcs)
in (
# 1240 "FStar.Parser.ToSyntax.fst"
let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _51_19 -> (match (_51_19) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, _51_2260, _51_2262, _51_2264, _51_2266), t, quals) -> begin
(
# 1242 "FStar.Parser.ToSyntax.fst"
let _51_2276 = (push_tparams env tpars)
in (match (_51_2276) with
| (env_tps, _51_2275) -> begin
(
# 1243 "FStar.Parser.ToSyntax.fst"
let t = (desugar_term env_tps t)
in (let _135_836 = (let _135_835 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in ([], _135_835))
in (_135_836)::[]))
end))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, _51_2284, tags, _51_2287), constrs, tconstr, quals) -> begin
(
# 1247 "FStar.Parser.ToSyntax.fst"
let tycon = (tname, tpars, k)
in (
# 1248 "FStar.Parser.ToSyntax.fst"
let _51_2298 = (push_tparams env tpars)
in (match (_51_2298) with
| (env_tps, tps) -> begin
(
# 1249 "FStar.Parser.ToSyntax.fst"
let data_tpars = (FStar_List.map (fun _51_2302 -> (match (_51_2302) with
| (x, _51_2301) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end)) tps)
in (
# 1250 "FStar.Parser.ToSyntax.fst"
let _51_2326 = (let _135_848 = (FStar_All.pipe_right constrs (FStar_List.map (fun _51_2307 -> (match (_51_2307) with
| (id, topt, of_notation) -> begin
(
# 1252 "FStar.Parser.ToSyntax.fst"
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
# 1260 "FStar.Parser.ToSyntax.fst"
let t = (let _135_840 = (FStar_Parser_Env.default_total env_tps)
in (let _135_839 = (close env_tps t)
in (desugar_term _135_840 _135_839)))
in (
# 1261 "FStar.Parser.ToSyntax.fst"
let name = (FStar_Parser_Env.qualify env id)
in (
# 1262 "FStar.Parser.ToSyntax.fst"
let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _51_18 -> (match (_51_18) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| _51_2321 -> begin
[]
end))))
in (
# 1265 "FStar.Parser.ToSyntax.fst"
let ntps = (FStar_List.length data_tpars)
in (let _135_847 = (let _135_846 = (let _135_845 = (let _135_844 = (let _135_843 = (let _135_842 = (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total _135_842))
in (FStar_Syntax_Util.arrow data_tpars _135_843))
in (name, univs, _135_844, tname, ntps, quals, mutuals, rng))
in FStar_Syntax_Syntax.Sig_datacon (_135_845))
in (tps, _135_846))
in (name, _135_847)))))))
end))))
in (FStar_All.pipe_left FStar_List.split _135_848))
in (match (_51_2326) with
| (constrNames, constrs) -> begin
(([], FStar_Syntax_Syntax.Sig_inductive_typ ((tname, univs, tpars, k, mutuals, constrNames, tags, rng))))::constrs
end)))
end)))
end
| _51_2328 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1270 "FStar.Parser.ToSyntax.fst"
let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (
# 1271 "FStar.Parser.ToSyntax.fst"
let bundle = (let _135_850 = (let _135_849 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _135_849, rng))
in FStar_Syntax_Syntax.Sig_bundle (_135_850))
in (
# 1272 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 bundle)
in (
# 1273 "FStar.Parser.ToSyntax.fst"
let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projectors env)))
in (
# 1274 "FStar.Parser.ToSyntax.fst"
let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _51_20 -> (match (_51_20) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, _51_2337, tps, k, _51_2341, constrs, quals, _51_2345) when ((FStar_List.length constrs) > 1) -> begin
(mk_data_discriminators quals env tname tps k constrs)
end
| _51_2349 -> begin
[]
end))))
in (
# 1278 "FStar.Parser.ToSyntax.fst"
let ops = (FStar_List.append discs data_ops)
in (
# 1279 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env ops)
in (env, (FStar_List.append ((bundle)::[]) ops)))))))))))
end)))))
end
| [] -> begin
(FStar_All.failwith "impossible")
end))))))))))

# 1284 "FStar.Parser.ToSyntax.fst"
let desugar_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.binder Prims.list) = (fun env binders -> (
# 1285 "FStar.Parser.ToSyntax.fst"
let _51_2373 = (FStar_List.fold_left (fun _51_2358 b -> (match (_51_2358) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| (Some (a), k) -> begin
(
# 1288 "FStar.Parser.ToSyntax.fst"
let _51_2366 = (FStar_Parser_Env.push_bv env a)
in (match (_51_2366) with
| (env, a) -> begin
(let _135_859 = (let _135_858 = (FStar_Syntax_Syntax.mk_binder (
# 1289 "FStar.Parser.ToSyntax.fst"
let _51_2367 = a
in {FStar_Syntax_Syntax.ppname = _51_2367.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _51_2367.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (_135_858)::binders)
in (env, _135_859))
end))
end
| _51_2370 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Missing name in binder", b.FStar_Parser_AST.brange))))
end)
end)) (env, []) binders)
in (match (_51_2373) with
| (env, binders) -> begin
(env, (FStar_List.rev binders))
end)))

# 1294 "FStar.Parser.ToSyntax.fst"
let rec desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(
# 1296 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_pragma (((trans_pragma p), d.FStar_Parser_AST.drange))
in (env, (se)::[]))
end
| FStar_Parser_AST.Open (lid) -> begin
(
# 1300 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_namespace env lid)
in (env, []))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(let _135_864 = (FStar_List.map trans_qual qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _135_864 tcs))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _135_866 = (let _135_865 = (desugar_term_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((isrec, lets, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Syntax_Subst.compress _135_865))
in _135_866.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let (lbs, _51_2393) -> begin
(
# 1309 "FStar.Parser.ToSyntax.fst"
let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (
# 1310 "FStar.Parser.ToSyntax.fst"
let quals = (match (quals) with
| _51_2401::_51_2399 -> begin
(FStar_List.map trans_qual quals)
end
| _51_2404 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _51_21 -> (match (_51_21) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (_51_2415); FStar_Syntax_Syntax.lbunivs = _51_2413; FStar_Syntax_Syntax.lbtyp = _51_2411; FStar_Syntax_Syntax.lbeff = _51_2409; FStar_Syntax_Syntax.lbdef = _51_2407} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _51_2425; FStar_Syntax_Syntax.lbtyp = _51_2423; FStar_Syntax_Syntax.lbeff = _51_2421; FStar_Syntax_Syntax.lbdef = _51_2419} -> begin
(FStar_Parser_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (
# 1315 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right lets (FStar_Util.for_some (fun _51_2433 -> (match (_51_2433) with
| (_51_2431, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end)))) then begin
(FStar_Syntax_Syntax.Logic)::quals
end else begin
quals
end
in (
# 1319 "FStar.Parser.ToSyntax.fst"
let lbs = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _135_871 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 1321 "FStar.Parser.ToSyntax.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 1322 "FStar.Parser.ToSyntax.fst"
let _51_2437 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((
# 1322 "FStar.Parser.ToSyntax.fst"
let _51_2439 = fv
in {FStar_Syntax_Syntax.fv_name = _51_2439.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = _51_2439.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = _51_2437.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _51_2437.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _51_2437.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _51_2437.FStar_Syntax_Syntax.lbdef})))))
in ((Prims.fst lbs), _135_871))
end else begin
lbs
end
in (
# 1324 "FStar.Parser.ToSyntax.fst"
let s = (let _135_874 = (let _135_873 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (lbs, d.FStar_Parser_AST.drange, _135_873, quals))
in FStar_Syntax_Syntax.Sig_let (_135_874))
in (
# 1325 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env s)
in (env, (s)::[])))))))
end
| _51_2446 -> begin
(FStar_All.failwith "Desugaring a let did not produce a let")
end)
end
| FStar_Parser_AST.Main (t) -> begin
(
# 1331 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env t)
in (
# 1332 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, d.FStar_Parser_AST.drange))
in (env, (se)::[])))
end
| FStar_Parser_AST.Assume (atag, id, t) -> begin
(
# 1336 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env t)
in (let _135_878 = (let _135_877 = (let _135_876 = (let _135_875 = (FStar_Parser_Env.qualify env id)
in (_135_875, f, (FStar_Syntax_Syntax.Assumption)::[], d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Sig_assume (_135_876))
in (_135_877)::[])
in (env, _135_878)))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(
# 1340 "FStar.Parser.ToSyntax.fst"
let t = (let _135_879 = (close_fun env t)
in (desugar_term env _135_879))
in (
# 1341 "FStar.Parser.ToSyntax.fst"
let quals = if (env.FStar_Parser_Env.iface && env.FStar_Parser_Env.admitted_iface) then begin
(FStar_Parser_AST.Assumption)::quals
end else begin
quals
end
in (
# 1342 "FStar.Parser.ToSyntax.fst"
let se = (let _135_882 = (let _135_881 = (FStar_Parser_Env.qualify env id)
in (let _135_880 = (FStar_List.map trans_qual quals)
in (_135_881, [], t, _135_880, d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_declare_typ (_135_882))
in (
# 1343 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(
# 1347 "FStar.Parser.ToSyntax.fst"
let t = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (
# 1348 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env id)
in (
# 1349 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_datacon ((l, [], t, FStar_Syntax_Const.exn_lid, 0, (FStar_Syntax_Syntax.ExceptionConstructor)::[], (FStar_Syntax_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (
# 1350 "FStar.Parser.ToSyntax.fst"
let se' = FStar_Syntax_Syntax.Sig_bundle (((se)::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (
# 1351 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se')
in (
# 1352 "FStar.Parser.ToSyntax.fst"
let data_ops = (mk_data_projectors env ([], se))
in (
# 1353 "FStar.Parser.ToSyntax.fst"
let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (
# 1354 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops))))))))))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(
# 1358 "FStar.Parser.ToSyntax.fst"
let t = (desugar_term env term)
in (
# 1359 "FStar.Parser.ToSyntax.fst"
let t = (let _135_886 = (let _135_883 = (FStar_Syntax_Syntax.null_binder t)
in (_135_883)::[])
in (let _135_885 = (let _135_884 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _135_884))
in (FStar_Syntax_Util.arrow _135_886 _135_885)))
in (
# 1360 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env id)
in (
# 1361 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_datacon ((l, [], t, FStar_Syntax_Const.exn_lid, 0, (FStar_Syntax_Syntax.ExceptionConstructor)::[], (FStar_Syntax_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (
# 1362 "FStar.Parser.ToSyntax.fst"
let se' = FStar_Syntax_Syntax.Sig_bundle (((se)::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (
# 1363 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se')
in (
# 1364 "FStar.Parser.ToSyntax.fst"
let data_ops = (mk_data_projectors env ([], se))
in (
# 1365 "FStar.Parser.ToSyntax.fst"
let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (
# 1366 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops)))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(
# 1370 "FStar.Parser.ToSyntax.fst"
let _51_2499 = (desugar_binders env binders)
in (match (_51_2499) with
| (env_k, binders) -> begin
(
# 1371 "FStar.Parser.ToSyntax.fst"
let k = (desugar_term env_k k)
in (
# 1372 "FStar.Parser.ToSyntax.fst"
let name = (FStar_Parser_Env.qualify env id)
in (
# 1373 "FStar.Parser.ToSyntax.fst"
let se = (mk_typ_abbrev name [] binders FStar_Syntax_Syntax.tun k ((name)::[]) [] d.FStar_Parser_AST.drange)
in (
# 1374 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))))
end))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(
# 1378 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1379 "FStar.Parser.ToSyntax.fst"
let _51_2515 = (desugar_binders env eff_binders)
in (match (_51_2515) with
| (env, binders) -> begin
(
# 1380 "FStar.Parser.ToSyntax.fst"
let _51_2526 = (
# 1381 "FStar.Parser.ToSyntax.fst"
let _51_2518 = (head_and_args defn)
in (match (_51_2518) with
| (head, args) -> begin
(
# 1382 "FStar.Parser.ToSyntax.fst"
let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_defn env) l)
end
| _51_2522 -> begin
(let _135_891 = (let _135_890 = (let _135_889 = (let _135_888 = (let _135_887 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat "Effect " _135_887))
in (Prims.strcat _135_888 " not found"))
in (_135_889, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_135_890))
in (Prims.raise _135_891))
end)
in (let _135_892 = (desugar_args env args)
in (ed, _135_892)))
end))
in (match (_51_2526) with
| (ed, args) -> begin
(
# 1386 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_Syntax_Subst.close_binders binders)
in (
# 1387 "FStar.Parser.ToSyntax.fst"
let sub = (fun _51_2532 -> (match (_51_2532) with
| (_51_2530, x) -> begin
(
# 1388 "FStar.Parser.ToSyntax.fst"
let _51_2535 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (_51_2535) with
| (edb, x) -> begin
(
# 1389 "FStar.Parser.ToSyntax.fst"
let s = (FStar_Syntax_Util.subst_of_list edb args)
in (let _135_896 = (let _135_895 = (FStar_Syntax_Subst.subst s x)
in (FStar_Syntax_Subst.close binders _135_895))
in ([], _135_896)))
end))
end))
in (
# 1391 "FStar.Parser.ToSyntax.fst"
let ed = (let _135_913 = (FStar_List.map trans_qual quals)
in (let _135_912 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _135_911 = (let _135_897 = (sub ([], ed.FStar_Syntax_Syntax.signature))
in (Prims.snd _135_897))
in (let _135_910 = (sub ed.FStar_Syntax_Syntax.ret)
in (let _135_909 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (let _135_908 = (sub ed.FStar_Syntax_Syntax.bind_wlp)
in (let _135_907 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (let _135_906 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (let _135_905 = (sub ed.FStar_Syntax_Syntax.ite_wlp)
in (let _135_904 = (sub ed.FStar_Syntax_Syntax.wp_binop)
in (let _135_903 = (sub ed.FStar_Syntax_Syntax.wp_as_type)
in (let _135_902 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (let _135_901 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (let _135_900 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (let _135_899 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (let _135_898 = (sub ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _135_913; FStar_Syntax_Syntax.mname = _135_912; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = _135_911; FStar_Syntax_Syntax.ret = _135_910; FStar_Syntax_Syntax.bind_wp = _135_909; FStar_Syntax_Syntax.bind_wlp = _135_908; FStar_Syntax_Syntax.if_then_else = _135_907; FStar_Syntax_Syntax.ite_wp = _135_906; FStar_Syntax_Syntax.ite_wlp = _135_905; FStar_Syntax_Syntax.wp_binop = _135_904; FStar_Syntax_Syntax.wp_as_type = _135_903; FStar_Syntax_Syntax.close_wp = _135_902; FStar_Syntax_Syntax.assert_p = _135_901; FStar_Syntax_Syntax.assume_p = _135_900; FStar_Syntax_Syntax.null_wp = _135_899; FStar_Syntax_Syntax.trivial = _135_898}))))))))))))))))
in (
# 1411 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (
# 1412 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 se)
in (env, (se)::[]))))))
end))
end)))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls)) -> begin
(
# 1416 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1417 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.enter_monad_scope env eff_name)
in (
# 1418 "FStar.Parser.ToSyntax.fst"
let _51_2553 = (desugar_binders env eff_binders)
in (match (_51_2553) with
| (env, binders) -> begin
(
# 1419 "FStar.Parser.ToSyntax.fst"
let eff_k = (let _135_914 = (FStar_Parser_Env.default_total env)
in (desugar_term _135_914 eff_kind))
in (
# 1420 "FStar.Parser.ToSyntax.fst"
let _51_2564 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _51_2557 decl -> (match (_51_2557) with
| (env, out) -> begin
(
# 1421 "FStar.Parser.ToSyntax.fst"
let _51_2561 = (desugar_decl env decl)
in (match (_51_2561) with
| (env, ses) -> begin
(let _135_918 = (let _135_917 = (FStar_List.hd ses)
in (_135_917)::out)
in (env, _135_918))
end))
end)) (env, [])))
in (match (_51_2564) with
| (env, decls) -> begin
(
# 1423 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_Syntax_Subst.close_binders binders)
in (
# 1424 "FStar.Parser.ToSyntax.fst"
let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (
# 1425 "FStar.Parser.ToSyntax.fst"
let lookup = (fun s -> (
# 1426 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env (FStar_Ident.mk_ident (s, d.FStar_Parser_AST.drange)))
in (let _135_922 = (let _135_921 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) _135_921))
in ([], _135_922))))
in (
# 1428 "FStar.Parser.ToSyntax.fst"
let ed = (let _135_937 = (FStar_List.map trans_qual quals)
in (let _135_936 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _135_935 = (lookup "return")
in (let _135_934 = (lookup "bind_wp")
in (let _135_933 = (lookup "bind_wlp")
in (let _135_932 = (lookup "if_then_else")
in (let _135_931 = (lookup "ite_wp")
in (let _135_930 = (lookup "ite_wlp")
in (let _135_929 = (lookup "wp_binop")
in (let _135_928 = (lookup "wp_as_type")
in (let _135_927 = (lookup "close_wp")
in (let _135_926 = (lookup "assert_p")
in (let _135_925 = (lookup "assume_p")
in (let _135_924 = (lookup "null_wp")
in (let _135_923 = (lookup "trivial")
in {FStar_Syntax_Syntax.qualifiers = _135_937; FStar_Syntax_Syntax.mname = _135_936; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret = _135_935; FStar_Syntax_Syntax.bind_wp = _135_934; FStar_Syntax_Syntax.bind_wlp = _135_933; FStar_Syntax_Syntax.if_then_else = _135_932; FStar_Syntax_Syntax.ite_wp = _135_931; FStar_Syntax_Syntax.ite_wlp = _135_930; FStar_Syntax_Syntax.wp_binop = _135_929; FStar_Syntax_Syntax.wp_as_type = _135_928; FStar_Syntax_Syntax.close_wp = _135_927; FStar_Syntax_Syntax.assert_p = _135_926; FStar_Syntax_Syntax.assume_p = _135_925; FStar_Syntax_Syntax.null_wp = _135_924; FStar_Syntax_Syntax.trivial = _135_923})))))))))))))))
in (
# 1448 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (
# 1449 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 se)
in (env, (se)::[])))))))
end)))
end))))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(
# 1453 "FStar.Parser.ToSyntax.fst"
let lookup = (fun l -> (match ((FStar_Parser_Env.try_lookup_effect_name env l)) with
| None -> begin
(let _135_944 = (let _135_943 = (let _135_942 = (let _135_941 = (let _135_940 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat "Effect name " _135_940))
in (Prims.strcat _135_941 " not found"))
in (_135_942, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_135_943))
in (Prims.raise _135_944))
end
| Some (l) -> begin
l
end))
in (
# 1456 "FStar.Parser.ToSyntax.fst"
let src = (lookup l.FStar_Parser_AST.msource)
in (
# 1457 "FStar.Parser.ToSyntax.fst"
let dst = (lookup l.FStar_Parser_AST.mdest)
in (
# 1458 "FStar.Parser.ToSyntax.fst"
let lift = (let _135_945 = (desugar_term env l.FStar_Parser_AST.lift_op)
in ([], _135_945))
in (
# 1459 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect (({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift = lift}, d.FStar_Parser_AST.drange))
in (env, (se)::[]))))))
end))

# 1462 "FStar.Parser.ToSyntax.fst"
let desugar_decls : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _51_2588 d -> (match (_51_2588) with
| (env, sigelts) -> begin
(
# 1464 "FStar.Parser.ToSyntax.fst"
let _51_2592 = (desugar_decl env d)
in (match (_51_2592) with
| (env, se) -> begin
(env, (FStar_List.append sigelts se))
end))
end)) (env, []) decls))

# 1467 "FStar.Parser.ToSyntax.fst"
let open_prims_all : FStar_Parser_AST.decl Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.all_lid)) FStar_Range.dummyRange))::[]

# 1474 "FStar.Parser.ToSyntax.fst"
let desugar_modul_common : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (
# 1475 "FStar.Parser.ToSyntax.fst"
let open_ns = (fun mname d -> (
# 1476 "FStar.Parser.ToSyntax.fst"
let d = if ((FStar_List.length mname.FStar_Ident.ns) <> 0) then begin
(let _135_964 = (let _135_963 = (let _135_962 = (FStar_Ident.lid_of_ids mname.FStar_Ident.ns)
in FStar_Parser_AST.Open (_135_962))
in (FStar_Parser_AST.mk_decl _135_963 (FStar_Ident.range_of_lid mname)))
in (_135_964)::d)
end else begin
d
end
in d))
in (
# 1480 "FStar.Parser.ToSyntax.fst"
let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod) -> begin
(FStar_Parser_Env.finish_module_or_interface env prev_mod)
end)
in (
# 1483 "FStar.Parser.ToSyntax.fst"
let _51_2619 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _135_966 = (FStar_Parser_Env.prepare_module_or_interface true admitted env mname)
in (let _135_965 = (open_ns mname decls)
in (_135_966, mname, _135_965, true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _135_968 = (FStar_Parser_Env.prepare_module_or_interface false false env mname)
in (let _135_967 = (open_ns mname decls)
in (_135_968, mname, _135_967, false)))
end)
in (match (_51_2619) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(
# 1488 "FStar.Parser.ToSyntax.fst"
let _51_2622 = (desugar_decls env decls)
in (match (_51_2622) with
| (env, sigelts) -> begin
(
# 1489 "FStar.Parser.ToSyntax.fst"
let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in (env, modul, pop_when_done))
end))
end)))))

# 1497 "FStar.Parser.ToSyntax.fst"
let desugar_partial_modul : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (
# 1498 "FStar.Parser.ToSyntax.fst"
let m = if (FStar_ST.read FStar_Options.interactive_fsi) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface ((mname, decls, true))
end
| FStar_Parser_AST.Interface (mname, _51_2633, _51_2635) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (
# 1505 "FStar.Parser.ToSyntax.fst"
let _51_2643 = (desugar_modul_common curmod env m)
in (match (_51_2643) with
| (x, y, _51_2642) -> begin
(x, y)
end))))

# 1508 "FStar.Parser.ToSyntax.fst"
let desugar_modul : FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (
# 1509 "FStar.Parser.ToSyntax.fst"
let _51_2649 = (desugar_modul_common None env m)
in (match (_51_2649) with
| (env, modul, pop_when_done) -> begin
(
# 1510 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.finish_module_or_interface env modul)
in (
# 1511 "FStar.Parser.ToSyntax.fst"
let _51_2651 = if (FStar_Options.should_dump modul.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _135_979 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _135_979))
end else begin
()
end
in (let _135_980 = if pop_when_done then begin
(FStar_Parser_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end else begin
env
end
in (_135_980, modul))))
end)))

# 1515 "FStar.Parser.ToSyntax.fst"
let desugar_file : FStar_Parser_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (
# 1516 "FStar.Parser.ToSyntax.fst"
let _51_2664 = (FStar_List.fold_left (fun _51_2657 m -> (match (_51_2657) with
| (env, mods) -> begin
(
# 1517 "FStar.Parser.ToSyntax.fst"
let _51_2661 = (desugar_modul env m)
in (match (_51_2661) with
| (env, m) -> begin
(env, (m)::mods)
end))
end)) (env, []) f)
in (match (_51_2664) with
| (env, mods) -> begin
(env, (FStar_List.rev mods))
end)))

# 1521 "FStar.Parser.ToSyntax.fst"
let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Parser_Env.env  ->  FStar_Parser_Env.env = (fun m en -> (
# 1522 "FStar.Parser.ToSyntax.fst"
let _51_2669 = (FStar_Parser_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (_51_2669) with
| (en, pop_when_done) -> begin
(
# 1523 "FStar.Parser.ToSyntax.fst"
let en = (FStar_List.fold_left FStar_Parser_Env.push_sigelt (
# 1523 "FStar.Parser.ToSyntax.fst"
let _51_2670 = en
in {FStar_Parser_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_Parser_Env.modules = _51_2670.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _51_2670.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.sigaccum = _51_2670.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _51_2670.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _51_2670.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _51_2670.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _51_2670.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _51_2670.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _51_2670.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = _51_2670.FStar_Parser_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (
# 1524 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_Env.export_interface m.FStar_Syntax_Syntax.name env)
end else begin
env
end))
end)))




