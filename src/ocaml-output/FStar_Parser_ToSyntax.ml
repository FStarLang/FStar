
open Prims
# 38 "FStar.Parser.ToSyntax.fst"
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

# 43 "FStar.Parser.ToSyntax.fst"
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

# 57 "FStar.Parser.ToSyntax.fst"
let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun _51_3 -> (match (_51_3) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions -> begin
FStar_Syntax_Syntax.ResetOptions
end))

# 61 "FStar.Parser.ToSyntax.fst"
let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _51_4 -> (match (_51_4) with
| (FStar_Parser_AST.Hash) | (FStar_Parser_AST.FsTypApp) -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| _51_50 -> begin
None
end))

# 66 "FStar.Parser.ToSyntax.fst"
let arg_withimp_e = (fun imp t -> (t, (as_imp imp)))

# 68 "FStar.Parser.ToSyntax.fst"
let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
(t, Some (FStar_Syntax_Syntax.imp_tag))
end
| _51_57 -> begin
(t, None)
end))

# 72 "FStar.Parser.ToSyntax.fst"
let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_51_61) -> begin
true
end
| _51_64 -> begin
false
end)))))

# 77 "FStar.Parser.ToSyntax.fst"
let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _51_69 -> begin
t
end))

# 81 "FStar.Parser.ToSyntax.fst"
let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _132_21 = (let _132_20 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_132_20))
in (FStar_Parser_AST.mk_term _132_21 r FStar_Parser_AST.Kind)))

# 83 "FStar.Parser.ToSyntax.fst"
let compile_op : Prims.int  ->  Prims.string  ->  Prims.string = (fun arity s -> (
# 86 "FStar.Parser.ToSyntax.fst"
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
| _51_92 -> begin
"UNKNOWN"
end))
in (
# 105 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _132_32 = (let _132_30 = (FStar_Util.char_at s i)
in (name_of_char _132_30))
in (let _132_31 = (aux (i + 1))
in (_132_32)::_132_31))
end)
in (let _132_34 = (let _132_33 = (aux 0)
in (FStar_String.concat "_" _132_33))
in (Prims.strcat "op_" _132_34)))))

# 109 "FStar.Parser.ToSyntax.fst"
let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _132_44 = (let _132_43 = (let _132_42 = (let _132_41 = (compile_op n s)
in (_132_41, r))
in (FStar_Ident.mk_ident _132_42))
in (_132_43)::[])
in (FStar_All.pipe_right _132_44 FStar_Ident.lid_of_ids)))

# 111 "FStar.Parser.ToSyntax.fst"
let op_as_lid : FStar_Parser_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Ident.lident Prims.option = (fun env arity rng s -> (
# 114 "FStar.Parser.ToSyntax.fst"
let r = (fun l -> (let _132_55 = (FStar_Ident.set_lid_range l rng)
in Some (_132_55)))
in (
# 115 "FStar.Parser.ToSyntax.fst"
let fallback = (fun _51_106 -> (match (()) with
| () -> begin
(match (s) with
| "=" -> begin
(r FStar_Syntax_Const.op_Eq)
end
| ":=" -> begin
(r FStar_Syntax_Const.op_ColonEq)
end
| "<" -> begin
(r FStar_Syntax_Const.op_LT)
end
| "<=" -> begin
(r FStar_Syntax_Const.op_LTE)
end
| ">" -> begin
(r FStar_Syntax_Const.op_GT)
end
| ">=" -> begin
(r FStar_Syntax_Const.op_GTE)
end
| "&&" -> begin
(r FStar_Syntax_Const.op_And)
end
| "||" -> begin
(r FStar_Syntax_Const.op_Or)
end
| "+" -> begin
(r FStar_Syntax_Const.op_Addition)
end
| "-" when (arity = 1) -> begin
(r FStar_Syntax_Const.op_Minus)
end
| "-" -> begin
(r FStar_Syntax_Const.op_Subtraction)
end
| "/" -> begin
(r FStar_Syntax_Const.op_Division)
end
| "%" -> begin
(r FStar_Syntax_Const.op_Modulus)
end
| "!" -> begin
(r FStar_Syntax_Const.read_lid)
end
| "@" -> begin
(r FStar_Syntax_Const.list_append_lid)
end
| "^" -> begin
(r FStar_Syntax_Const.strcat_lid)
end
| "|>" -> begin
(r FStar_Syntax_Const.pipe_right_lid)
end
| "<|" -> begin
(r FStar_Syntax_Const.pipe_left_lid)
end
| "<>" -> begin
(r FStar_Syntax_Const.op_notEq)
end
| "~" -> begin
(r FStar_Syntax_Const.not_lid)
end
| "==" -> begin
(r FStar_Syntax_Const.eq2_lid)
end
| "=!=" -> begin
(r FStar_Syntax_Const.neq2_lid)
end
| "<<" -> begin
(r FStar_Syntax_Const.precedes_lid)
end
| "/\\" -> begin
(r FStar_Syntax_Const.and_lid)
end
| "\\/" -> begin
(r FStar_Syntax_Const.or_lid)
end
| "==>" -> begin
(r FStar_Syntax_Const.imp_lid)
end
| "<==>" -> begin
(r FStar_Syntax_Const.iff_lid)
end
| _51_135 -> begin
None
end)
end))
in (match ((let _132_58 = (compile_op_lid arity s rng)
in (FStar_Parser_Env.try_lookup_lid env _132_58))) with
| Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _51_144); FStar_Syntax_Syntax.tk = _51_141; FStar_Syntax_Syntax.pos = _51_139; FStar_Syntax_Syntax.vars = _51_137}) -> begin
Some (fv.FStar_Syntax_Syntax.v)
end
| _51_150 -> begin
(fallback ())
end))))

# 148 "FStar.Parser.ToSyntax.fst"
let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _132_65 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _132_65)))

# 152 "FStar.Parser.ToSyntax.fst"
let rec free_type_vars_b : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_51_159) -> begin
(env, [])
end
| FStar_Parser_AST.TVariable (x) -> begin
(
# 157 "FStar.Parser.ToSyntax.fst"
let _51_166 = (FStar_Parser_Env.push_bv env x)
in (match (_51_166) with
| (env, _51_165) -> begin
(env, (x)::[])
end))
end
| FStar_Parser_AST.Annotated (_51_168, term) -> begin
(let _132_72 = (free_type_vars env term)
in (env, _132_72))
end
| FStar_Parser_AST.TAnnotated (id, _51_174) -> begin
(
# 162 "FStar.Parser.ToSyntax.fst"
let _51_180 = (FStar_Parser_Env.push_bv env id)
in (match (_51_180) with
| (env, _51_179) -> begin
(env, [])
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _132_73 = (free_type_vars env t)
in (env, _132_73))
end))
and free_type_vars : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _132_76 = (unparen t)
in _132_76.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (_51_186) -> begin
(FStar_All.failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_Env.try_lookup_id env a)) with
| None -> begin
(a)::[]
end
| _51_192 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_51_222, ts) -> begin
(FStar_List.collect (fun _51_229 -> (match (_51_229) with
| (t, _51_228) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_51_231, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _51_238) -> begin
(let _132_79 = (free_type_vars env t1)
in (let _132_78 = (free_type_vars env t2)
in (FStar_List.append _132_79 _132_78)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(
# 192 "FStar.Parser.ToSyntax.fst"
let _51_247 = (free_type_vars_b env b)
in (match (_51_247) with
| (env, f) -> begin
(let _132_80 = (free_type_vars env t)
in (FStar_List.append f _132_80))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(
# 197 "FStar.Parser.ToSyntax.fst"
let _51_263 = (FStar_List.fold_left (fun _51_256 binder -> (match (_51_256) with
| (env, free) -> begin
(
# 198 "FStar.Parser.ToSyntax.fst"
let _51_260 = (free_type_vars_b env binder)
in (match (_51_260) with
| (env, f) -> begin
(env, (FStar_List.append f free))
end))
end)) (env, []) binders)
in (match (_51_263) with
| (env, free) -> begin
(let _132_83 = (free_type_vars env body)
in (FStar_List.append free _132_83))
end))
end
| FStar_Parser_AST.Project (t, _51_266) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) -> begin
[]
end
| (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
(FStar_Parser_AST.error "Unexpected type in free_type_vars computation" t t.FStar_Parser_AST.range)
end))

# 213 "FStar.Parser.ToSyntax.fst"
let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (
# 216 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun args t -> (match ((let _132_90 = (unparen t)
in _132_90.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _51_310 -> begin
(t, args)
end))
in (aux [] t)))

# 220 "FStar.Parser.ToSyntax.fst"
let close : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 223 "FStar.Parser.ToSyntax.fst"
let ftv = (let _132_95 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _132_95))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 226 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _132_99 = (let _132_98 = (let _132_97 = (tm_type x.FStar_Ident.idRange)
in (x, _132_97))
in FStar_Parser_AST.TAnnotated (_132_98))
in (FStar_Parser_AST.mk_binder _132_99 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 227 "FStar.Parser.ToSyntax.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))

# 228 "FStar.Parser.ToSyntax.fst"
let close_fun : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 231 "FStar.Parser.ToSyntax.fst"
let ftv = (let _132_104 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _132_104))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 234 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _132_108 = (let _132_107 = (let _132_106 = (tm_type x.FStar_Ident.idRange)
in (x, _132_106))
in FStar_Parser_AST.TAnnotated (_132_107))
in (FStar_Parser_AST.mk_binder _132_108 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 235 "FStar.Parser.ToSyntax.fst"
let t = (match ((let _132_109 = (unparen t)
in _132_109.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_51_323) -> begin
t
end
| _51_326 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level), t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end)
in (
# 238 "FStar.Parser.ToSyntax.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result)))
end))

# 239 "FStar.Parser.ToSyntax.fst"
let rec uncurry : FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term) = (fun bs t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (binders, t) -> begin
(uncurry (FStar_List.append bs binders) t)
end
| _51_336 -> begin
(bs, t)
end))

# 243 "FStar.Parser.ToSyntax.fst"
let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _51_340) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_51_346); FStar_Parser_AST.prange = _51_344}, _51_350) -> begin
true
end
| _51_354 -> begin
false
end))

# 248 "FStar.Parser.ToSyntax.fst"
let rec destruct_app_pattern : FStar_Parser_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 252 "FStar.Parser.ToSyntax.fst"
let _51_366 = (destruct_app_pattern env is_top_level p)
in (match (_51_366) with
| (name, args, _51_365) -> begin
(name, args, Some (t))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _51_371); FStar_Parser_AST.prange = _51_368}, args) when is_top_level -> begin
(let _132_123 = (let _132_122 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_132_122))
in (_132_123, args, None))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _51_382); FStar_Parser_AST.prange = _51_379}, args) -> begin
(FStar_Util.Inl (id), args, None)
end
| _51_390 -> begin
(FStar_All.failwith "Not an app pattern")
end))

# 259 "FStar.Parser.ToSyntax.fst"
type bnd =
| LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * FStar_Syntax_Syntax.term)

# 262 "FStar.Parser.ToSyntax.fst"
let is_LocalBinder = (fun _discr_ -> (match (_discr_) with
| LocalBinder (_) -> begin
true
end
| _ -> begin
false
end))

# 263 "FStar.Parser.ToSyntax.fst"
let is_LetBinder = (fun _discr_ -> (match (_discr_) with
| LetBinder (_) -> begin
true
end
| _ -> begin
false
end))

# 262 "FStar.Parser.ToSyntax.fst"
let ___LocalBinder____0 : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun projectee -> (match (projectee) with
| LocalBinder (_51_393) -> begin
_51_393
end))

# 263 "FStar.Parser.ToSyntax.fst"
let ___LetBinder____0 : bnd  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| LetBinder (_51_396) -> begin
_51_396
end))

# 263 "FStar.Parser.ToSyntax.fst"
let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun _51_6 -> (match (_51_6) with
| LocalBinder (a, aq) -> begin
(a, aq)
end
| _51_403 -> begin
(FStar_All.failwith "Impossible")
end))

# 266 "FStar.Parser.ToSyntax.fst"
let as_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_Parser_Env.env) = (fun env imp _51_7 -> (match (_51_7) with
| (None, k) -> begin
(let _132_160 = (FStar_Syntax_Syntax.null_binder k)
in (_132_160, env))
end
| (Some (a), k) -> begin
(
# 270 "FStar.Parser.ToSyntax.fst"
let _51_416 = (FStar_Parser_Env.push_bv env a)
in (match (_51_416) with
| (env, a) -> begin
(((
# 271 "FStar.Parser.ToSyntax.fst"
let _51_417 = a
in {FStar_Syntax_Syntax.ppname = _51_417.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _51_417.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}), (trans_aqual imp)), env)
end))
end))

# 271 "FStar.Parser.ToSyntax.fst"
type env_t =
FStar_Parser_Env.env

# 273 "FStar.Parser.ToSyntax.fst"
type lenv_t =
FStar_Syntax_Syntax.bv Prims.list

# 274 "FStar.Parser.ToSyntax.fst"
let mk_lb : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.letbinding = (fun _51_422 -> (match (_51_422) with
| (n, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))

# 276 "FStar.Parser.ToSyntax.fst"
let no_annot_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t None))

# 277 "FStar.Parser.ToSyntax.fst"
let rec desugar_data_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat) = (fun env p -> (
# 280 "FStar.Parser.ToSyntax.fst"
let check_linear_pattern_variables = (fun p -> (
# 281 "FStar.Parser.ToSyntax.fst"
let rec pat_vars = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_dot_term (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_constant (_)) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (_51_443, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out _51_451 -> (match (_51_451) with
| (p, _51_450) -> begin
(let _132_206 = (pat_vars p)
in (FStar_Util.set_union out _132_206))
end)) FStar_Syntax_Syntax.no_names))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj (hd::tl) -> begin
(
# 290 "FStar.Parser.ToSyntax.fst"
let xs = (pat_vars hd)
in if (not ((FStar_Util.for_all (fun p -> (
# 291 "FStar.Parser.ToSyntax.fst"
let ys = (pat_vars p)
in ((FStar_Util.set_is_subset_of xs ys) && (FStar_Util.set_is_subset_of ys xs)))) tl))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Disjunctive pattern binds different variables in each case", p.FStar_Syntax_Syntax.p))))
end else begin
xs
end)
end))
in (pat_vars p)))
in (
# 298 "FStar.Parser.ToSyntax.fst"
let resolvex = (fun l e x -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText))))) with
| Some (y) -> begin
(l, e, y)
end
| _51_469 -> begin
(
# 302 "FStar.Parser.ToSyntax.fst"
let _51_472 = (FStar_Parser_Env.push_bv e x)
in (match (_51_472) with
| (e, x) -> begin
((x)::l, e, x)
end))
end))
in (
# 304 "FStar.Parser.ToSyntax.fst"
let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun b -> (b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText))))) with
| Some (b) -> begin
(l, e, b)
end
| _51_481 -> begin
(
# 308 "FStar.Parser.ToSyntax.fst"
let _51_484 = (FStar_Parser_Env.push_bv e a)
in (match (_51_484) with
| (e, a) -> begin
((a)::l, e, a)
end))
end))
in (
# 310 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun loc env p -> (
# 311 "FStar.Parser.ToSyntax.fst"
let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Parser_AST.prange))
in (
# 312 "FStar.Parser.ToSyntax.fst"
let pos_r = (fun r q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r))
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.PatOr (p::ps) -> begin
(
# 316 "FStar.Parser.ToSyntax.fst"
let _51_506 = (aux loc env p)
in (match (_51_506) with
| (loc, env, var, p, _51_505) -> begin
(
# 317 "FStar.Parser.ToSyntax.fst"
let _51_523 = (FStar_List.fold_left (fun _51_510 p -> (match (_51_510) with
| (loc, env, ps) -> begin
(
# 318 "FStar.Parser.ToSyntax.fst"
let _51_519 = (aux loc env p)
in (match (_51_519) with
| (loc, env, _51_515, p, _51_518) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_51_523) with
| (loc, env, ps) -> begin
(
# 320 "FStar.Parser.ToSyntax.fst"
let pat = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in (loc, env, var, pat, false))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 324 "FStar.Parser.ToSyntax.fst"
let _51_534 = (aux loc env p)
in (match (_51_534) with
| (loc, env', binder, p, imp) -> begin
(
# 325 "FStar.Parser.ToSyntax.fst"
let binder = (match (binder) with
| LetBinder (_51_536) -> begin
(FStar_All.failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(
# 328 "FStar.Parser.ToSyntax.fst"
let t = (let _132_236 = (close_fun env t)
in (desugar_term env _132_236))
in LocalBinder (((
# 329 "FStar.Parser.ToSyntax.fst"
let _51_543 = x
in {FStar_Syntax_Syntax.ppname = _51_543.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _51_543.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), aq)))
end)
in (loc, env', binder, p, imp))
end))
end
| FStar_Parser_AST.PatWild -> begin
(
# 333 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _132_237 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in (loc, env, LocalBinder ((x, None)), _132_237, false)))
end
| FStar_Parser_AST.PatConst (c) -> begin
(
# 337 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _132_238 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in (loc, env, LocalBinder ((x, None)), _132_238, false)))
end
| (FStar_Parser_AST.PatTvar (x, imp)) | (FStar_Parser_AST.PatVar (x, imp)) -> begin
(
# 342 "FStar.Parser.ToSyntax.fst"
let aq = if imp then begin
Some (FStar_Syntax_Syntax.imp_tag)
end else begin
None
end
in (
# 343 "FStar.Parser.ToSyntax.fst"
let _51_561 = (resolvex loc env x)
in (match (_51_561) with
| (loc, env, xbv) -> begin
(let _132_239 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in (loc, env, LocalBinder ((xbv, aq)), _132_239, imp))
end)))
end
| FStar_Parser_AST.PatName (l) -> begin
(
# 347 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_datacon env) l)
in (
# 348 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _132_240 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, []))))
in (loc, env, LocalBinder ((x, None)), _132_240, false))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _51_567}, args) -> begin
(
# 352 "FStar.Parser.ToSyntax.fst"
let _51_589 = (FStar_List.fold_right (fun arg _51_578 -> (match (_51_578) with
| (loc, env, args) -> begin
(
# 353 "FStar.Parser.ToSyntax.fst"
let _51_585 = (aux loc env arg)
in (match (_51_585) with
| (loc, env, _51_582, arg, imp) -> begin
(loc, env, ((arg, imp))::args)
end))
end)) args (loc, env, []))
in (match (_51_589) with
| (loc, env, args) -> begin
(
# 355 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_datacon env) l)
in (
# 356 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _132_243 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _132_243, false))))
end))
end
| FStar_Parser_AST.PatApp (_51_593) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(
# 362 "FStar.Parser.ToSyntax.fst"
let _51_613 = (FStar_List.fold_right (fun pat _51_601 -> (match (_51_601) with
| (loc, env, pats) -> begin
(
# 363 "FStar.Parser.ToSyntax.fst"
let _51_609 = (aux loc env pat)
in (match (_51_609) with
| (loc, env, _51_605, pat, _51_608) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_51_613) with
| (loc, env, pats) -> begin
(
# 365 "FStar.Parser.ToSyntax.fst"
let pat = (let _132_256 = (let _132_255 = (let _132_251 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _132_251))
in (let _132_254 = (let _132_253 = (let _132_252 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_132_252, []))
in FStar_Syntax_Syntax.Pat_cons (_132_253))
in (FStar_All.pipe_left _132_255 _132_254)))
in (FStar_List.fold_right (fun hd tl -> (
# 366 "FStar.Parser.ToSyntax.fst"
let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (let _132_250 = (let _132_249 = (let _132_248 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_132_248, ((hd, false))::((tl, false))::[]))
in FStar_Syntax_Syntax.Pat_cons (_132_249))
in (FStar_All.pipe_left (pos_r r) _132_250)))) pats _132_256))
in (
# 369 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (loc, env, LocalBinder ((x, None)), pat, false)))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(
# 373 "FStar.Parser.ToSyntax.fst"
let _51_639 = (FStar_List.fold_left (fun _51_626 p -> (match (_51_626) with
| (loc, env, pats) -> begin
(
# 374 "FStar.Parser.ToSyntax.fst"
let _51_635 = (aux loc env p)
in (match (_51_635) with
| (loc, env, _51_631, pat, _51_634) -> begin
(loc, env, ((pat, false))::pats)
end))
end)) (loc, env, []) args)
in (match (_51_639) with
| (loc, env, args) -> begin
(
# 376 "FStar.Parser.ToSyntax.fst"
let args = (FStar_List.rev args)
in (
# 377 "FStar.Parser.ToSyntax.fst"
let l = if dep then begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end else begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end
in (
# 379 "FStar.Parser.ToSyntax.fst"
let constr = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (
# 380 "FStar.Parser.ToSyntax.fst"
let l = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| _51_646 -> begin
(FStar_All.failwith "impossible")
end)
in (
# 383 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _132_259 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _132_259, false)))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(
# 390 "FStar.Parser.ToSyntax.fst"
let _51_656 = (FStar_List.hd fields)
in (match (_51_656) with
| (f, _51_655) -> begin
(
# 391 "FStar.Parser.ToSyntax.fst"
let _51_660 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_51_660) with
| (record, _51_659) -> begin
(
# 392 "FStar.Parser.ToSyntax.fst"
let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _51_663 -> (match (_51_663) with
| (f, p) -> begin
(let _132_261 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.qualify_field_to_record env record) f)
in (_132_261, p))
end))))
in (
# 394 "FStar.Parser.ToSyntax.fst"
let args = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _51_668 -> (match (_51_668) with
| (f, _51_667) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _51_672 -> (match (_51_672) with
| (g, _51_671) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_51_675, p) -> begin
p
end)
end))))
in (
# 398 "FStar.Parser.ToSyntax.fst"
let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_Env.constrname)) p.FStar_Parser_AST.prange), args))) p.FStar_Parser_AST.prange)
in (
# 399 "FStar.Parser.ToSyntax.fst"
let _51_687 = (aux loc env app)
in (match (_51_687) with
| (env, e, b, p, _51_686) -> begin
(
# 400 "FStar.Parser.ToSyntax.fst"
let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons ((fv, _51_690), args) -> begin
(let _132_270 = (let _132_269 = (let _132_268 = (let _132_267 = (let _132_266 = (let _132_265 = (let _132_264 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _132_264))
in FStar_Syntax_Syntax.Record_ctor (_132_265))
in Some (_132_266))
in (fv, _132_267))
in (_132_268, args))
in FStar_Syntax_Syntax.Pat_cons (_132_269))
in (FStar_All.pipe_left pos _132_270))
end
| _51_696 -> begin
p
end)
in (env, e, b, p, false))
end)))))
end))
end))
end))))
in (
# 405 "FStar.Parser.ToSyntax.fst"
let _51_705 = (aux [] env p)
in (match (_51_705) with
| (_51_699, env, b, p, _51_704) -> begin
(
# 406 "FStar.Parser.ToSyntax.fst"
let _51_706 = (let _132_271 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore _132_271))
in (env, b, p))
end)))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _51_713) -> begin
(let _132_277 = (let _132_276 = (let _132_275 = (FStar_Parser_Env.qualify env x)
in (_132_275, FStar_Syntax_Syntax.tun))
in LetBinder (_132_276))
in (env, _132_277, None))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _51_720); FStar_Parser_AST.prange = _51_717}, t) -> begin
(let _132_281 = (let _132_280 = (let _132_279 = (FStar_Parser_Env.qualify env x)
in (let _132_278 = (desugar_term env t)
in (_132_279, _132_278)))
in LetBinder (_132_280))
in (env, _132_281, None))
end
| _51_728 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern at the top-level", p.FStar_Parser_AST.prange))))
end)
end else begin
(
# 417 "FStar.Parser.ToSyntax.fst"
let _51_732 = (desugar_data_pat env p)
in (match (_51_732) with
| (env, binder, p) -> begin
(
# 418 "FStar.Parser.ToSyntax.fst"
let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| _51_740 -> begin
Some (p)
end)
in (env, binder, p))
end))
end)
and desugar_binding_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun _51_744 env pat -> (
# 427 "FStar.Parser.ToSyntax.fst"
let _51_752 = (desugar_data_pat env pat)
in (match (_51_752) with
| (env, _51_750, pat) -> begin
(env, pat)
end)))
and desugar_match_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (
# 433 "FStar.Parser.ToSyntax.fst"
let env = (
# 433 "FStar.Parser.ToSyntax.fst"
let _51_757 = env
in {FStar_Parser_Env.curmodule = _51_757.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _51_757.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _51_757.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.sigaccum = _51_757.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _51_757.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _51_757.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _51_757.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _51_757.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _51_757.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _51_757.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (
# 437 "FStar.Parser.ToSyntax.fst"
let env = (
# 437 "FStar.Parser.ToSyntax.fst"
let _51_762 = env
in {FStar_Parser_Env.curmodule = _51_762.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _51_762.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _51_762.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.sigaccum = _51_762.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _51_762.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _51_762.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _51_762.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _51_762.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _51_762.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _51_762.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (
# 441 "FStar.Parser.ToSyntax.fst"
let mk = (fun e -> (FStar_Syntax_Syntax.mk e None top.FStar_Parser_AST.range))
in (
# 442 "FStar.Parser.ToSyntax.fst"
let setpos = (fun e -> (
# 442 "FStar.Parser.ToSyntax.fst"
let _51_772 = e
in {FStar_Syntax_Syntax.n = _51_772.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _51_772.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _51_772.FStar_Syntax_Syntax.vars}))
in (match ((let _132_300 = (unparen top)
in _132_300.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (_51_776) -> begin
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
| FStar_Parser_AST.Op ("*", _51_796::_51_794::[]) when (let _132_301 = (op_as_lid env 2 top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right _132_301 FStar_Option.isNone)) -> begin
(
# 460 "FStar.Parser.ToSyntax.fst"
let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", t1::t2::[]) -> begin
(
# 462 "FStar.Parser.ToSyntax.fst"
let rest = (flatten t2)
in (t1)::rest)
end
| _51_810 -> begin
(t)::[]
end))
in (
# 465 "FStar.Parser.ToSyntax.fst"
let targs = (let _132_307 = (let _132_304 = (unparen top)
in (flatten _132_304))
in (FStar_All.pipe_right _132_307 (FStar_List.map (fun t -> (let _132_306 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg _132_306))))))
in (
# 466 "FStar.Parser.ToSyntax.fst"
let tup = (let _132_308 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) _132_308))
in (mk (FStar_Syntax_Syntax.Tm_app ((tup, targs)))))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _132_309 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) a)
in (FStar_All.pipe_left setpos _132_309))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_lid env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Unexpected operator: " s), top.FStar_Parser_AST.range))))
end
| Some (l) -> begin
(
# 476 "FStar.Parser.ToSyntax.fst"
let op = (FStar_Syntax_Syntax.fvar None l (FStar_Ident.range_of_lid l))
in (
# 477 "FStar.Parser.ToSyntax.fst"
let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _132_311 = (desugar_term env t)
in (_132_311, None)))))
in (mk (FStar_Syntax_Syntax.Tm_app ((op, args))))))
end)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _51_832; FStar_Ident.ident = _51_830; FStar_Ident.nsstr = _51_828; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _51_841; FStar_Ident.ident = _51_839; FStar_Ident.nsstr = _51_837; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _51_850; FStar_Ident.ident = _51_848; FStar_Ident.nsstr = _51_846; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(let _132_312 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (FStar_All.pipe_left setpos _132_312))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(
# 490 "FStar.Parser.ToSyntax.fst"
let _51_865 = (match ((FStar_Parser_Env.try_lookup_datacon env l)) with
| None -> begin
(let _132_313 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (_132_313, false))
end
| Some (head) -> begin
(let _132_314 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in (_132_314, true))
end)
in (match (_51_865) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| _51_868 -> begin
(
# 496 "FStar.Parser.ToSyntax.fst"
let args = (FStar_List.map (fun _51_871 -> (match (_51_871) with
| (t, imp) -> begin
(
# 497 "FStar.Parser.ToSyntax.fst"
let te = (desugar_term env t)
in (arg_withimp_e imp te))
end)) args)
in (
# 499 "FStar.Parser.ToSyntax.fst"
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
# 506 "FStar.Parser.ToSyntax.fst"
let _51_899 = (FStar_List.fold_left (fun _51_882 b -> (match (_51_882) with
| (env, tparams, typs) -> begin
(
# 507 "FStar.Parser.ToSyntax.fst"
let _51_886 = (desugar_binder env b)
in (match (_51_886) with
| (xopt, t) -> begin
(
# 508 "FStar.Parser.ToSyntax.fst"
let _51_892 = (match (xopt) with
| None -> begin
(let _132_318 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (env, _132_318))
end
| Some (x) -> begin
(FStar_Parser_Env.push_bv env x)
end)
in (match (_51_892) with
| (env, x) -> begin
(let _132_322 = (let _132_321 = (let _132_320 = (let _132_319 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _132_319))
in (_132_320)::[])
in (FStar_List.append typs _132_321))
in (env, (FStar_List.append tparams ((((
# 512 "FStar.Parser.ToSyntax.fst"
let _51_893 = x
in {FStar_Syntax_Syntax.ppname = _51_893.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _51_893.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), None))::[])), _132_322))
end))
end))
end)) (env, [], []) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_51_899) with
| (env, _51_897, targs) -> begin
(
# 515 "FStar.Parser.ToSyntax.fst"
let tup = (let _132_323 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) _132_323))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app ((tup, targs)))))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(
# 519 "FStar.Parser.ToSyntax.fst"
let _51_907 = (uncurry binders t)
in (match (_51_907) with
| (bs, t) -> begin
(
# 520 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun env bs _51_8 -> (match (_51_8) with
| [] -> begin
(
# 522 "FStar.Parser.ToSyntax.fst"
let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (let _132_330 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos _132_330)))
end
| hd::tl -> begin
(
# 526 "FStar.Parser.ToSyntax.fst"
let mlenv = (FStar_Parser_Env.default_ml env)
in (
# 527 "FStar.Parser.ToSyntax.fst"
let bb = (desugar_binder mlenv hd)
in (
# 528 "FStar.Parser.ToSyntax.fst"
let _51_921 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_51_921) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_binder env b)) with
| (None, _51_928) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(
# 537 "FStar.Parser.ToSyntax.fst"
let _51_936 = (as_binder env None b)
in (match (_51_936) with
| ((x, _51_933), env) -> begin
(
# 538 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env f)
in (let _132_331 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos _132_331)))
end))
end)
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(
# 543 "FStar.Parser.ToSyntax.fst"
let _51_956 = (FStar_List.fold_left (fun _51_944 pat -> (match (_51_944) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (_51_947, t) -> begin
(let _132_335 = (let _132_334 = (free_type_vars env t)
in (FStar_List.append _132_334 ftvs))
in (env, _132_335))
end
| _51_952 -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_51_956) with
| (_51_954, ftv) -> begin
(
# 547 "FStar.Parser.ToSyntax.fst"
let ftv = (sort_ftv ftv)
in (
# 548 "FStar.Parser.ToSyntax.fst"
let binders = (let _132_337 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar ((a, true))) top.FStar_Parser_AST.range))))
in (FStar_List.append _132_337 binders))
in (
# 557 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun env bs sc_pat_opt _51_9 -> (match (_51_9) with
| [] -> begin
(
# 559 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env body)
in (
# 560 "FStar.Parser.ToSyntax.fst"
let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(
# 562 "FStar.Parser.ToSyntax.fst"
let body = (let _132_347 = (let _132_346 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right _132_346 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close _132_347 body))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((sc, ((pat, None, body))::[]))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (let _132_348 = (no_annot_abs (FStar_List.rev bs) body)
in (setpos _132_348))))
end
| p::rest -> begin
(
# 568 "FStar.Parser.ToSyntax.fst"
let _51_980 = (desugar_binding_pat env p)
in (match (_51_980) with
| (env, b, pat) -> begin
(
# 569 "FStar.Parser.ToSyntax.fst"
let _51_1031 = (match (b) with
| LetBinder (_51_982) -> begin
(FStar_All.failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(
# 572 "FStar.Parser.ToSyntax.fst"
let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _51_990) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _132_350 = (let _132_349 = (FStar_Syntax_Syntax.bv_to_name x)
in (_132_349, p))
in Some (_132_350))
end
| (Some (p), Some (sc, p')) -> begin
(match ((sc.FStar_Syntax_Syntax.n, p'.FStar_Syntax_Syntax.v)) with
| (FStar_Syntax_Syntax.Tm_name (_51_1004), _51_1007) -> begin
(
# 578 "FStar.Parser.ToSyntax.fst"
let tup2 = (let _132_351 = (FStar_Syntax_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _132_351 (Some (FStar_Syntax_Syntax.Data_ctor))))
in (
# 579 "FStar.Parser.ToSyntax.fst"
let sc = (let _132_359 = (let _132_358 = (let _132_357 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (let _132_356 = (let _132_355 = (FStar_Syntax_Syntax.as_arg sc)
in (let _132_354 = (let _132_353 = (let _132_352 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _132_352))
in (_132_353)::[])
in (_132_355)::_132_354))
in (_132_357, _132_356)))
in FStar_Syntax_Syntax.Tm_app (_132_358))
in (FStar_Syntax_Syntax.mk _132_359 None top.FStar_Parser_AST.range))
in (
# 580 "FStar.Parser.ToSyntax.fst"
let p = (let _132_360 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tup2, ((p', false))::((p, false))::[]))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _132_360))
in Some ((sc, p)))))
end
| (FStar_Syntax_Syntax.Tm_app (_51_1013, args), FStar_Syntax_Syntax.Pat_cons (_51_1018, pats)) -> begin
(
# 583 "FStar.Parser.ToSyntax.fst"
let tupn = (let _132_361 = (FStar_Syntax_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _132_361 (Some (FStar_Syntax_Syntax.Data_ctor))))
in (
# 584 "FStar.Parser.ToSyntax.fst"
let sc = (let _132_368 = (let _132_367 = (let _132_366 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (let _132_365 = (let _132_364 = (let _132_363 = (let _132_362 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _132_362))
in (_132_363)::[])
in (FStar_List.append args _132_364))
in (_132_366, _132_365)))
in FStar_Syntax_Syntax.Tm_app (_132_367))
in (mk _132_368))
in (
# 585 "FStar.Parser.ToSyntax.fst"
let p = (let _132_369 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tupn, (FStar_List.append pats (((p, false))::[]))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _132_369))
in Some ((sc, p)))))
end
| _51_1027 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((x, aq), sc_pat_opt))
end)
in (match (_51_1031) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _51_1035; FStar_Parser_AST.level = _51_1033}, phi, _51_1041) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(
# 596 "FStar.Parser.ToSyntax.fst"
let phi = (desugar_formula env phi)
in (let _132_377 = (let _132_376 = (let _132_375 = (FStar_Syntax_Syntax.fvar None a (FStar_Ident.range_of_lid a))
in (let _132_374 = (let _132_373 = (FStar_Syntax_Syntax.as_arg phi)
in (let _132_372 = (let _132_371 = (let _132_370 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _132_370))
in (_132_371)::[])
in (_132_373)::_132_372))
in (_132_375, _132_374)))
in FStar_Syntax_Syntax.Tm_app (_132_376))
in (mk _132_377)))
end
| FStar_Parser_AST.App (_51_1046) -> begin
(
# 602 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun args e -> (match ((let _132_382 = (unparen e)
in _132_382.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(
# 604 "FStar.Parser.ToSyntax.fst"
let arg = (let _132_383 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _132_383))
in (aux ((arg)::args) e))
end
| _51_1058 -> begin
(
# 607 "FStar.Parser.ToSyntax.fst"
let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app ((head, args)))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _132_386 = (let _132_385 = (let _132_384 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range), t1))::[], t2))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in (_132_384, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))
in FStar_Syntax_Syntax.Tm_meta (_132_385))
in (mk _132_386))
end
| FStar_Parser_AST.Let (is_rec, (pat, _snd)::_tl, body) -> begin
(
# 616 "FStar.Parser.ToSyntax.fst"
let ds_let_rec = (fun _51_1074 -> (match (()) with
| () -> begin
(
# 617 "FStar.Parser.ToSyntax.fst"
let bindings = ((pat, _snd))::_tl
in (
# 618 "FStar.Parser.ToSyntax.fst"
let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _51_1078 -> (match (_51_1078) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _132_390 = (destruct_app_pattern env top_level p)
in (_132_390, def))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _132_391 = (destruct_app_pattern env top_level p)
in (_132_391, def))
end
| _51_1084 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _51_1089); FStar_Parser_AST.prange = _51_1086}, t) -> begin
if top_level then begin
(let _132_394 = (let _132_393 = (let _132_392 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_132_392))
in (_132_393, [], Some (t)))
in (_132_394, def))
end else begin
((FStar_Util.Inl (id), [], Some (t)), def)
end
end
| FStar_Parser_AST.PatVar (id, _51_1098) -> begin
if top_level then begin
(let _132_397 = (let _132_396 = (let _132_395 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_132_395))
in (_132_396, [], None))
in (_132_397, def))
end else begin
((FStar_Util.Inl (id), [], None), def)
end
end
| _51_1102 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected let binding", p.FStar_Parser_AST.prange))))
end)
end)
end
end))))
in (
# 635 "FStar.Parser.ToSyntax.fst"
let _51_1131 = (FStar_List.fold_left (fun _51_1107 _51_1116 -> (match ((_51_1107, _51_1116)) with
| ((env, fnames, rec_bindings), ((f, _51_1110, _51_1112), _51_1115)) -> begin
(
# 637 "FStar.Parser.ToSyntax.fst"
let _51_1127 = (match (f) with
| FStar_Util.Inl (x) -> begin
(
# 639 "FStar.Parser.ToSyntax.fst"
let _51_1121 = (FStar_Parser_Env.push_bv env x)
in (match (_51_1121) with
| (env, xx) -> begin
(let _132_401 = (let _132_400 = (FStar_Syntax_Syntax.mk_binder xx)
in (_132_400)::rec_bindings)
in (env, FStar_Util.Inl (xx), _132_401))
end))
end
| FStar_Util.Inr (l) -> begin
(let _132_402 = (FStar_Parser_Env.push_top_level_rec_binding env l.FStar_Ident.ident)
in (_132_402, FStar_Util.Inr (l), rec_bindings))
end)
in (match (_51_1127) with
| (env, lbname, rec_bindings) -> begin
(env, (lbname)::fnames, rec_bindings)
end))
end)) (env, [], []) funs)
in (match (_51_1131) with
| (env', fnames, rec_bindings) -> begin
(
# 645 "FStar.Parser.ToSyntax.fst"
let fnames = (FStar_List.rev fnames)
in (
# 647 "FStar.Parser.ToSyntax.fst"
let desugar_one_def = (fun env lbname _51_1142 -> (match (_51_1142) with
| ((_51_1137, args, result_t), def) -> begin
(
# 648 "FStar.Parser.ToSyntax.fst"
let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _132_409 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed ((def, t))) _132_409 FStar_Parser_AST.Expr))
end)
in (
# 651 "FStar.Parser.ToSyntax.fst"
let def = (match (args) with
| [] -> begin
def
end
| _51_1149 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.un_curry_abs args def) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
end)
in (
# 654 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env def)
in (
# 655 "FStar.Parser.ToSyntax.fst"
let body = if is_rec then begin
(FStar_Syntax_Subst.close rec_bindings body)
end else begin
body
end
in (mk_lb (lbname, FStar_Syntax_Syntax.tun, body))))))
end))
in (
# 657 "FStar.Parser.ToSyntax.fst"
let lbs = (FStar_List.map2 (desugar_one_def (if is_rec then begin
env'
end else begin
env
end)) fnames funs)
in (
# 658 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env' body)
in (let _132_412 = (let _132_411 = (let _132_410 = (FStar_Syntax_Subst.close rec_bindings body)
in ((is_rec, lbs), _132_410))
in FStar_Syntax_Syntax.Tm_let (_132_411))
in (FStar_All.pipe_left mk _132_412))))))
end))))
end))
in (
# 661 "FStar.Parser.ToSyntax.fst"
let ds_non_rec = (fun pat t1 t2 -> (
# 662 "FStar.Parser.ToSyntax.fst"
let t1 = (desugar_term env t1)
in (
# 663 "FStar.Parser.ToSyntax.fst"
let _51_1163 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_51_1163) with
| (env, binder, pat) -> begin
(match (binder) with
| LetBinder (l, t) -> begin
(
# 666 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env t2)
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (l); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]), body)))))
end
| LocalBinder (x, _51_1171) -> begin
(
# 670 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env t2)
in (
# 671 "FStar.Parser.ToSyntax.fst"
let body = (match (pat) with
| (None) | (Some ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (_); FStar_Syntax_Syntax.ty = _; FStar_Syntax_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _132_423 = (let _132_422 = (let _132_421 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _132_420 = (let _132_419 = (FStar_Syntax_Util.branch (pat, None, body))
in (_132_419)::[])
in (_132_421, _132_420)))
in FStar_Syntax_Syntax.Tm_match (_132_422))
in (FStar_Syntax_Syntax.mk _132_423 None body.FStar_Syntax_Syntax.pos))
end)
in (let _132_428 = (let _132_427 = (let _132_426 = (let _132_425 = (let _132_424 = (FStar_Syntax_Syntax.mk_binder x)
in (_132_424)::[])
in (FStar_Syntax_Subst.close _132_425 body))
in ((false, ((mk_lb (FStar_Util.Inl (x), x.FStar_Syntax_Syntax.sort, t1)))::[]), _132_426))
in FStar_Syntax_Syntax.Tm_let (_132_427))
in (FStar_All.pipe_left mk _132_428))))
end)
end))))
in if (is_rec || (is_app_pattern pat)) then begin
(ds_let_rec ())
end else begin
(ds_non_rec pat _snd body)
end))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(
# 685 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (let _132_439 = (let _132_438 = (let _132_437 = (desugar_term env t1)
in (let _132_436 = (let _132_435 = (let _132_430 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (let _132_429 = (desugar_term env t2)
in (_132_430, None, _132_429)))
in (let _132_434 = (let _132_433 = (let _132_432 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (let _132_431 = (desugar_term env t3)
in (_132_432, None, _132_431)))
in (_132_433)::[])
in (_132_435)::_132_434))
in (_132_437, _132_436)))
in FStar_Syntax_Syntax.Tm_match (_132_438))
in (mk _132_439)))
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(
# 691 "FStar.Parser.ToSyntax.fst"
let r = top.FStar_Parser_AST.range
in (
# 692 "FStar.Parser.ToSyntax.fst"
let handler = (FStar_Parser_AST.mk_function branches r r)
in (
# 693 "FStar.Parser.ToSyntax.fst"
let body = (FStar_Parser_AST.mk_function ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatConst (FStar_Const.Const_unit)) r), None, e))::[]) r r)
in (
# 694 "FStar.Parser.ToSyntax.fst"
let a1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (FStar_Syntax_Const.try_with_lid)) r top.FStar_Parser_AST.level), body, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (
# 695 "FStar.Parser.ToSyntax.fst"
let a2 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((a1, handler, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (desugar_term env a2))))))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(
# 699 "FStar.Parser.ToSyntax.fst"
let desugar_branch = (fun _51_1211 -> (match (_51_1211) with
| (pat, wopt, b) -> begin
(
# 700 "FStar.Parser.ToSyntax.fst"
let _51_1214 = (desugar_match_pat env pat)
in (match (_51_1214) with
| (env, pat) -> begin
(
# 701 "FStar.Parser.ToSyntax.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _132_442 = (desugar_term env e)
in Some (_132_442))
end)
in (
# 704 "FStar.Parser.ToSyntax.fst"
let b = (desugar_term env b)
in (FStar_Syntax_Util.branch (pat, wopt, b))))
end))
end))
in (let _132_446 = (let _132_445 = (let _132_444 = (desugar_term env e)
in (let _132_443 = (FStar_List.map desugar_branch branches)
in (_132_444, _132_443)))
in FStar_Syntax_Syntax.Tm_match (_132_445))
in (FStar_All.pipe_left mk _132_446)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _132_450 = (let _132_449 = (let _132_448 = (desugar_term env e)
in (let _132_447 = (desugar_typ env t)
in (_132_448, _132_447, None)))
in FStar_Syntax_Syntax.Tm_ascribed (_132_449))
in (FStar_All.pipe_left mk _132_450))
end
| FStar_Parser_AST.Record (_51_1225, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected empty record", top.FStar_Parser_AST.range))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(
# 715 "FStar.Parser.ToSyntax.fst"
let _51_1236 = (FStar_List.hd fields)
in (match (_51_1236) with
| (f, _51_1235) -> begin
(
# 716 "FStar.Parser.ToSyntax.fst"
let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (
# 717 "FStar.Parser.ToSyntax.fst"
let _51_1242 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_51_1242) with
| (record, _51_1241) -> begin
(
# 718 "FStar.Parser.ToSyntax.fst"
let get_field = (fun xopt f -> (
# 719 "FStar.Parser.ToSyntax.fst"
let fn = f.FStar_Ident.ident
in (
# 720 "FStar.Parser.ToSyntax.fst"
let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _51_1250 -> (match (_51_1250) with
| (g, _51_1249) -> begin
(
# 721 "FStar.Parser.ToSyntax.fst"
let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_51_1254, e) -> begin
(let _132_458 = (qfn fn)
in (_132_458, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _132_461 = (let _132_460 = (let _132_459 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in (_132_459, top.FStar_Parser_AST.range))
in FStar_Syntax_Syntax.Error (_132_460))
in (Prims.raise _132_461))
end
| Some (x) -> begin
(let _132_462 = (qfn fn)
in (_132_462, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Project ((x, f))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end))))
in (
# 732 "FStar.Parser.ToSyntax.fst"
let recterm = (match (eopt) with
| None -> begin
(let _132_467 = (let _132_466 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _51_1266 -> (match (_51_1266) with
| (f, _51_1265) -> begin
(let _132_465 = (let _132_464 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _132_464))
in (_132_465, FStar_Parser_AST.Nothing))
end))))
in (record.FStar_Parser_Env.constrname, _132_466))
in FStar_Parser_AST.Construct (_132_467))
end
| Some (e) -> begin
(
# 739 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (
# 740 "FStar.Parser.ToSyntax.fst"
let xterm = (let _132_469 = (let _132_468 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_132_468))
in (FStar_Parser_AST.mk_term _132_469 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (
# 741 "FStar.Parser.ToSyntax.fst"
let record = (let _132_472 = (let _132_471 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _51_1274 -> (match (_51_1274) with
| (f, _51_1273) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _132_471))
in FStar_Parser_AST.Record (_132_472))
in FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar ((x, false))) x.FStar_Ident.idRange), e))::[], (FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level))))))
end)
in (
# 744 "FStar.Parser.ToSyntax.fst"
let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (
# 745 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _51_1293); FStar_Syntax_Syntax.tk = _51_1290; FStar_Syntax_Syntax.pos = _51_1288; FStar_Syntax_Syntax.vars = _51_1286}, args); FStar_Syntax_Syntax.tk = _51_1284; FStar_Syntax_Syntax.pos = _51_1282; FStar_Syntax_Syntax.vars = _51_1280}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(
# 748 "FStar.Parser.ToSyntax.fst"
let e = (let _132_479 = (let _132_478 = (let _132_477 = (let _132_476 = (let _132_475 = (let _132_474 = (let _132_473 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _132_473))
in FStar_Syntax_Syntax.Record_ctor (_132_474))
in Some (_132_475))
in (FStar_Syntax_Syntax.fvar _132_476 fv.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos))
in (_132_477, args))
in FStar_Syntax_Syntax.Tm_app (_132_478))
in (FStar_All.pipe_left mk _132_479))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end
| _51_1307 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(
# 756 "FStar.Parser.ToSyntax.fst"
let _51_1314 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_projector_by_field_name env) f)
in (match (_51_1314) with
| (fieldname, is_rec) -> begin
(
# 757 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env e)
in (
# 758 "FStar.Parser.ToSyntax.fst"
let fn = (
# 759 "FStar.Parser.ToSyntax.fst"
let _51_1319 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_51_1319) with
| (ns, _51_1318) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (
# 761 "FStar.Parser.ToSyntax.fst"
let qual = if is_rec then begin
Some (FStar_Syntax_Syntax.Record_projector (fn))
end else begin
None
end
in (let _132_484 = (let _132_483 = (let _132_482 = (FStar_Syntax_Syntax.fvar (Some (FStar_Syntax_Syntax.Record_projector (fn))) fieldname (FStar_Ident.range_of_lid f))
in (let _132_481 = (let _132_480 = (FStar_Syntax_Syntax.as_arg e)
in (_132_480)::[])
in (_132_482, _132_481)))
in FStar_Syntax_Syntax.Tm_app (_132_483))
in (FStar_All.pipe_left mk _132_484)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| _51_1329 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _51_1331 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_args : FStar_Parser_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun _51_1336 -> (match (_51_1336) with
| (a, imp) -> begin
(let _132_488 = (desugar_term env a)
in (arg_withimp_e imp _132_488))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r default_ok env t -> (
# 778 "FStar.Parser.ToSyntax.fst"
let fail = (fun msg -> (Prims.raise (FStar_Syntax_Syntax.Error ((msg, r)))))
in (
# 779 "FStar.Parser.ToSyntax.fst"
let is_requires = (fun _51_1348 -> (match (_51_1348) with
| (t, _51_1347) -> begin
(match ((let _132_496 = (unparen t)
in _132_496.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Requires (_51_1350) -> begin
true
end
| _51_1353 -> begin
false
end)
end))
in (
# 782 "FStar.Parser.ToSyntax.fst"
let is_ensures = (fun _51_1358 -> (match (_51_1358) with
| (t, _51_1357) -> begin
(match ((let _132_499 = (unparen t)
in _132_499.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ensures (_51_1360) -> begin
true
end
| _51_1363 -> begin
false
end)
end))
in (
# 785 "FStar.Parser.ToSyntax.fst"
let is_app = (fun head _51_1369 -> (match (_51_1369) with
| (t, _51_1368) -> begin
(match ((let _132_504 = (unparen t)
in _132_504.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _51_1373; FStar_Parser_AST.level = _51_1371}, _51_1378, _51_1380) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| _51_1384 -> begin
false
end)
end))
in (
# 788 "FStar.Parser.ToSyntax.fst"
let pre_process_comp_typ = (fun t -> (
# 789 "FStar.Parser.ToSyntax.fst"
let _51_1389 = (head_and_args t)
in (match (_51_1389) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(
# 792 "FStar.Parser.ToSyntax.fst"
let unit_tm = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (
# 793 "FStar.Parser.ToSyntax.fst"
let nil_pat = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr), FStar_Parser_AST.Nothing)
in (
# 794 "FStar.Parser.ToSyntax.fst"
let args = (match (args) with
| [] -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Not enough arguments to \'Lemma\'", t.FStar_Parser_AST.range))))
end
| ens::[] -> begin
(
# 797 "FStar.Parser.ToSyntax.fst"
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
# 802 "FStar.Parser.ToSyntax.fst"
let head = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_name env) lemma)
in (head, args)))))
end
| FStar_Parser_AST.Name (l) when (FStar_Parser_Env.is_effect_name env l) -> begin
(let _132_507 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_name env) l)
in (_132_507, args))
end
| FStar_Parser_AST.Name (l) when ((let _132_508 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _132_508 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(let _132_509 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in (_132_509, args))
end
| FStar_Parser_AST.Name (l) when ((let _132_510 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _132_510 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(let _132_511 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)
in (_132_511, args))
end
| FStar_Parser_AST.Name (l) when ((((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) && default_ok) -> begin
(let _132_512 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in (_132_512, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _51_1417 when default_ok -> begin
(let _132_513 = (FStar_Ident.set_lid_range env.FStar_Parser_Env.default_result_effect head.FStar_Parser_AST.range)
in (_132_513, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _51_1419 -> begin
(let _132_515 = (let _132_514 = (FStar_Parser_AST.term_to_string t)
in (FStar_Util.format1 "%s is not an effect" _132_514))
in (fail _132_515))
end)
end)))
in (
# 832 "FStar.Parser.ToSyntax.fst"
let _51_1422 = (pre_process_comp_typ t)
in (match (_51_1422) with
| (eff, args) -> begin
(
# 833 "FStar.Parser.ToSyntax.fst"
let _51_1423 = if ((FStar_List.length args) = 0) then begin
(let _132_517 = (let _132_516 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" _132_516))
in (fail _132_517))
end else begin
()
end
in (
# 835 "FStar.Parser.ToSyntax.fst"
let _51_1427 = (let _132_519 = (FStar_List.hd args)
in (let _132_518 = (FStar_List.tl args)
in (_132_519, _132_518)))
in (match (_51_1427) with
| (result_arg, rest) -> begin
(
# 836 "FStar.Parser.ToSyntax.fst"
let result_typ = (desugar_typ env (Prims.fst result_arg))
in (
# 837 "FStar.Parser.ToSyntax.fst"
let rest = (desugar_args env rest)
in (
# 838 "FStar.Parser.ToSyntax.fst"
let _51_1455 = (FStar_All.pipe_right rest (FStar_List.partition (fun _51_1433 -> (match (_51_1433) with
| (t, _51_1432) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _51_1442); FStar_Syntax_Syntax.tk = _51_1439; FStar_Syntax_Syntax.pos = _51_1437; FStar_Syntax_Syntax.vars = _51_1435}, _51_1447::[]) -> begin
(FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.decreases_lid)
end
| _51_1452 -> begin
false
end)
end))))
in (match (_51_1455) with
| (dec, rest) -> begin
(
# 844 "FStar.Parser.ToSyntax.fst"
let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _51_1459 -> (match (_51_1459) with
| (t, _51_1458) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_51_1461, (arg, _51_1464)::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| _51_1470 -> begin
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
# 852 "FStar.Parser.ToSyntax.fst"
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
# 858 "FStar.Parser.ToSyntax.fst"
let rest = if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid) then begin
(match (rest) with
| req::ens::(pat, aq)::[] -> begin
(
# 862 "FStar.Parser.ToSyntax.fst"
let pat = (match (pat.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _51_1481) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.nil_lid) -> begin
(
# 864 "FStar.Parser.ToSyntax.fst"
let nil = (FStar_Syntax_Syntax.mk_Tm_uinst pat ((FStar_Syntax_Syntax.U_succ (FStar_Syntax_Syntax.U_zero))::[]))
in (
# 865 "FStar.Parser.ToSyntax.fst"
let pattern = (let _132_522 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _132_522 ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app nil (((pattern, Some (FStar_Syntax_Syntax.imp_tag)))::[]) None pat.FStar_Syntax_Syntax.pos)))
end
| _51_1487 -> begin
pat
end)
in (let _132_526 = (let _132_525 = (let _132_524 = (let _132_523 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((pat, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)))) None pat.FStar_Syntax_Syntax.pos)
in (_132_523, aq))
in (_132_524)::[])
in (ens)::_132_525)
in (req)::_132_526))
end
| _51_1490 -> begin
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
# 878 "FStar.Parser.ToSyntax.fst"
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
| _51_1502 -> begin
None
end))
in (
# 885 "FStar.Parser.ToSyntax.fst"
let mk = (fun t -> (FStar_Syntax_Syntax.mk t None f.FStar_Parser_AST.range))
in (
# 886 "FStar.Parser.ToSyntax.fst"
let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (
# 887 "FStar.Parser.ToSyntax.fst"
let setpos = (fun t -> (
# 887 "FStar.Parser.ToSyntax.fst"
let _51_1509 = t
in {FStar_Syntax_Syntax.n = _51_1509.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _51_1509.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _51_1509.FStar_Syntax_Syntax.vars}))
in (
# 888 "FStar.Parser.ToSyntax.fst"
let desugar_quant = (fun q b pats body -> (
# 889 "FStar.Parser.ToSyntax.fst"
let tk = (desugar_binder env (
# 889 "FStar.Parser.ToSyntax.fst"
let _51_1516 = b
in {FStar_Parser_AST.b = _51_1516.FStar_Parser_AST.b; FStar_Parser_AST.brange = _51_1516.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _51_1516.FStar_Parser_AST.aqual}))
in (
# 890 "FStar.Parser.ToSyntax.fst"
let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _132_561 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _132_561)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(
# 893 "FStar.Parser.ToSyntax.fst"
let _51_1530 = (FStar_Parser_Env.push_bv env a)
in (match (_51_1530) with
| (env, a) -> begin
(
# 894 "FStar.Parser.ToSyntax.fst"
let a = (
# 894 "FStar.Parser.ToSyntax.fst"
let _51_1531 = a
in {FStar_Syntax_Syntax.ppname = _51_1531.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _51_1531.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (
# 895 "FStar.Parser.ToSyntax.fst"
let pats = (desugar_pats env pats)
in (
# 896 "FStar.Parser.ToSyntax.fst"
let body = (desugar_formula env body)
in (
# 897 "FStar.Parser.ToSyntax.fst"
let body = (match (pats) with
| [] -> begin
body
end
| _51_1538 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((body, FStar_Syntax_Syntax.Meta_pattern (pats)))))
end)
in (
# 900 "FStar.Parser.ToSyntax.fst"
let body = (let _132_564 = (let _132_563 = (let _132_562 = (FStar_Syntax_Syntax.mk_binder a)
in (_132_562)::[])
in (no_annot_abs _132_563 body))
in (FStar_All.pipe_left setpos _132_564))
in (let _132_570 = (let _132_569 = (let _132_568 = (let _132_565 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Syntax_Syntax.fvar None _132_565 b.FStar_Parser_AST.brange))
in (let _132_567 = (let _132_566 = (FStar_Syntax_Syntax.as_arg body)
in (_132_566)::[])
in (_132_568, _132_567)))
in FStar_Syntax_Syntax.Tm_app (_132_569))
in (FStar_All.pipe_left mk _132_570)))))))
end))
end
| _51_1542 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 905 "FStar.Parser.ToSyntax.fst"
let push_quant = (fun q binders pats body -> (match (binders) with
| b::b'::_rest -> begin
(
# 907 "FStar.Parser.ToSyntax.fst"
let rest = (b')::_rest
in (
# 908 "FStar.Parser.ToSyntax.fst"
let body = (let _132_585 = (q (rest, pats, body))
in (let _132_584 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _132_585 _132_584 FStar_Parser_AST.Formula)))
in (let _132_586 = (q ((b)::[], [], body))
in (FStar_Parser_AST.mk_term _132_586 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _51_1556 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _132_587 = (unparen f)
in _132_587.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(
# 914 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env f)
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((l, f.FStar_Syntax_Syntax.pos, p)))))))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall (_1::_2::_3, pats, body) -> begin
(
# 921 "FStar.Parser.ToSyntax.fst"
let binders = (_1)::(_2)::_3
in (let _132_589 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _132_589)))
end
| FStar_Parser_AST.QExists (_1::_2::_3, pats, body) -> begin
(
# 925 "FStar.Parser.ToSyntax.fst"
let binders = (_1)::(_2)::_3
in (let _132_591 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _132_591)))
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
| _51_1614 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (
# 940 "FStar.Parser.ToSyntax.fst"
let _51_1638 = (FStar_List.fold_left (fun _51_1619 b -> (match (_51_1619) with
| (env, out) -> begin
(
# 941 "FStar.Parser.ToSyntax.fst"
let tk = (desugar_binder env (
# 941 "FStar.Parser.ToSyntax.fst"
let _51_1621 = b
in {FStar_Parser_AST.b = _51_1621.FStar_Parser_AST.b; FStar_Parser_AST.brange = _51_1621.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _51_1621.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(
# 944 "FStar.Parser.ToSyntax.fst"
let _51_1630 = (FStar_Parser_Env.push_bv env a)
in (match (_51_1630) with
| (env, a) -> begin
(
# 945 "FStar.Parser.ToSyntax.fst"
let a = (
# 945 "FStar.Parser.ToSyntax.fst"
let _51_1631 = a
in {FStar_Syntax_Syntax.ppname = _51_1631.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _51_1631.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (env, ((a, (trans_aqual b.FStar_Parser_AST.aqual)))::out))
end))
end
| _51_1635 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected binder", b.FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_51_1638) with
| (env, tpars) -> begin
(env, (FStar_List.rev tpars))
end)))
and desugar_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(let _132_598 = (desugar_typ env t)
in (Some (x), _132_598))
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _132_599 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None x.FStar_Ident.idRange)
in (Some (x), _132_599))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _132_600 = (desugar_typ env t)
in (None, _132_600))
end
| FStar_Parser_AST.Variable (x) -> begin
(Some (x), FStar_Syntax_Syntax.tun)
end))

# 955 "FStar.Parser.ToSyntax.fst"
let mk_data_discriminators : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  FStar_Ident.lid  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun quals env t tps k datas -> (
# 958 "FStar.Parser.ToSyntax.fst"
let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_Env.iface) || env.FStar_Parser_Env.admitted_iface) then begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (
# 961 "FStar.Parser.ToSyntax.fst"
let binders = (let _132_616 = (let _132_615 = (FStar_Syntax_Util.arrow_formals k)
in (Prims.fst _132_615))
in (FStar_List.append tps _132_616))
in (
# 962 "FStar.Parser.ToSyntax.fst"
let p = (FStar_Ident.range_of_lid t)
in (
# 963 "FStar.Parser.ToSyntax.fst"
let _51_1665 = (FStar_Syntax_Util.args_of_binders binders)
in (match (_51_1665) with
| (binders, args) -> begin
(
# 964 "FStar.Parser.ToSyntax.fst"
let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _51_1669 -> (match (_51_1669) with
| (x, _51_1668) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
in (
# 965 "FStar.Parser.ToSyntax.fst"
let binders = (let _132_622 = (let _132_621 = (let _132_620 = (let _132_619 = (let _132_618 = (FStar_Syntax_Syntax.lid_as_fv t None)
in (FStar_Syntax_Syntax.fv_to_tm _132_618))
in (FStar_Syntax_Syntax.mk_Tm_app _132_619 args None p))
in (FStar_All.pipe_left FStar_Syntax_Syntax.null_binder _132_620))
in (_132_621)::[])
in (FStar_List.append imp_binders _132_622))
in (
# 966 "FStar.Parser.ToSyntax.fst"
let disc_type = (let _132_625 = (let _132_624 = (let _132_623 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid None)
in (FStar_Syntax_Syntax.fv_to_tm _132_623))
in (FStar_Syntax_Syntax.mk_Total _132_624))
in (FStar_Syntax_Util.arrow binders _132_625))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (
# 968 "FStar.Parser.ToSyntax.fst"
let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (let _132_628 = (let _132_627 = (quals ((FStar_Syntax_Syntax.Logic)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in (disc_name, [], disc_type, _132_627, (FStar_Ident.range_of_lid disc_name)))
in FStar_Syntax_Syntax.Sig_declare_typ (_132_628)))))))))
end))))))

# 969 "FStar.Parser.ToSyntax.fst"
let mk_indexed_projectors : FStar_Syntax_Syntax.fv_qual  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun fvq refine_domain env tc lid inductive_tps imp_tps fields t -> (
# 972 "FStar.Parser.ToSyntax.fst"
let p = (FStar_Ident.range_of_lid lid)
in (
# 973 "FStar.Parser.ToSyntax.fst"
let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p))
in (
# 974 "FStar.Parser.ToSyntax.fst"
let projectee = (fun ptyp -> (FStar_Syntax_Syntax.gen_bv "projectee" (Some (p)) ptyp))
in (
# 975 "FStar.Parser.ToSyntax.fst"
let tps = (FStar_List.map2 (fun _51_1692 _51_1696 -> (match ((_51_1692, _51_1696)) with
| ((_51_1690, imp), (x, _51_1695)) -> begin
(x, imp)
end)) inductive_tps imp_tps)
in (
# 976 "FStar.Parser.ToSyntax.fst"
let _51_1797 = (
# 977 "FStar.Parser.ToSyntax.fst"
let _51_1700 = (FStar_Syntax_Util.head_and_args t)
in (match (_51_1700) with
| (head, args0) -> begin
(
# 978 "FStar.Parser.ToSyntax.fst"
let args = (
# 979 "FStar.Parser.ToSyntax.fst"
let rec arguments = (fun tps args -> (match ((tps, args)) with
| ([], _51_1706) -> begin
args
end
| (_51_1709, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Not enough arguments to type", (FStar_Ident.range_of_lid lid)))))
end
| ((_51_1714, Some (FStar_Syntax_Syntax.Implicit (_51_1716)))::tps', (_51_1723, Some (FStar_Syntax_Syntax.Implicit (_51_1725)))::args') -> begin
(arguments tps' args')
end
| ((_51_1733, Some (FStar_Syntax_Syntax.Implicit (_51_1735)))::tps', (_51_1743, _51_1745)::_51_1741) -> begin
(arguments tps' args)
end
| ((_51_1752, _51_1754)::_51_1750, (a, Some (FStar_Syntax_Syntax.Implicit (_51_1761)))::_51_1758) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected implicit annotation on argument", a.FStar_Syntax_Syntax.pos))))
end
| ((_51_1769, _51_1771)::tps', (_51_1776, _51_1778)::args') -> begin
(arguments tps' args')
end))
in (arguments inductive_tps args0))
in (
# 988 "FStar.Parser.ToSyntax.fst"
let indices = (FStar_All.pipe_right args (FStar_List.map (fun _51_1783 -> (let _132_658 = (FStar_Syntax_Syntax.new_bv (Some (p)) FStar_Syntax_Syntax.tun)
in (FStar_All.pipe_right _132_658 FStar_Syntax_Syntax.mk_binder)))))
in (
# 989 "FStar.Parser.ToSyntax.fst"
let arg_typ = (let _132_663 = (let _132_659 = (FStar_Syntax_Syntax.lid_as_fv tc None)
in (FStar_Syntax_Syntax.fv_to_tm _132_659))
in (let _132_662 = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _51_1788 -> (match (_51_1788) with
| (x, imp) -> begin
(let _132_661 = (FStar_Syntax_Syntax.bv_to_name x)
in (_132_661, imp))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app _132_663 _132_662 None p)))
in (
# 991 "FStar.Parser.ToSyntax.fst"
let arg_binder = if (not (refine_domain)) then begin
(let _132_664 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder _132_664))
end else begin
(
# 994 "FStar.Parser.ToSyntax.fst"
let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (
# 995 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p)) arg_typ)
in (let _132_672 = (
# 996 "FStar.Parser.ToSyntax.fst"
let _51_1792 = (projectee arg_typ)
in (let _132_671 = (let _132_670 = (let _132_669 = (let _132_668 = (FStar_Syntax_Syntax.fvar None disc_name p)
in (let _132_667 = (let _132_666 = (let _132_665 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _132_665))
in (_132_666)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _132_668 _132_667 None p)))
in (FStar_Syntax_Util.b2t _132_669))
in (FStar_Syntax_Util.refine x _132_670))
in {FStar_Syntax_Syntax.ppname = _51_1792.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _51_1792.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _132_671}))
in (FStar_Syntax_Syntax.mk_binder _132_672))))
end
in (arg_binder, indices)))))
end))
in (match (_51_1797) with
| (arg_binder, indices) -> begin
(
# 1000 "FStar.Parser.ToSyntax.fst"
let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder))
in (
# 1001 "FStar.Parser.ToSyntax.fst"
let imp_binders = (let _132_674 = (FStar_All.pipe_right indices (FStar_List.map (fun _51_1802 -> (match (_51_1802) with
| (x, _51_1801) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
in (FStar_List.append imp_tps _132_674))
in (
# 1002 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (
# 1004 "FStar.Parser.ToSyntax.fst"
let arg = (FStar_Syntax_Util.arg_of_non_null_binder arg_binder)
in (
# 1006 "FStar.Parser.ToSyntax.fst"
let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _51_1810 -> (match (_51_1810) with
| (a, _51_1809) -> begin
(
# 1007 "FStar.Parser.ToSyntax.fst"
let _51_1814 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (_51_1814) with
| (field_name, _51_1813) -> begin
(
# 1008 "FStar.Parser.ToSyntax.fst"
let proj = (let _132_678 = (let _132_677 = (FStar_Syntax_Syntax.lid_as_fv field_name None)
in (FStar_Syntax_Syntax.fv_to_tm _132_677))
in (FStar_Syntax_Syntax.mk_Tm_app _132_678 ((arg)::[]) None p))
in FStar_Syntax_Syntax.NT ((a, proj)))
end))
end))))
in (
# 1011 "FStar.Parser.ToSyntax.fst"
let ntps = (FStar_List.length tps)
in (
# 1012 "FStar.Parser.ToSyntax.fst"
let all_params = (FStar_List.append imp_tps fields)
in (let _132_710 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _51_1823 -> (match (_51_1823) with
| (x, _51_1822) -> begin
(
# 1015 "FStar.Parser.ToSyntax.fst"
let _51_1827 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_51_1827) with
| (field_name, _51_1826) -> begin
(
# 1016 "FStar.Parser.ToSyntax.fst"
let t = (let _132_682 = (let _132_681 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total _132_681))
in (FStar_Syntax_Util.arrow binders _132_682))
in (
# 1017 "FStar.Parser.ToSyntax.fst"
let only_decl = (((let _132_683 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _132_683)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _132_685 = (let _132_684 = (FStar_Parser_Env.current_module env)
in _132_684.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _132_685)))
in (
# 1021 "FStar.Parser.ToSyntax.fst"
let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (
# 1022 "FStar.Parser.ToSyntax.fst"
let quals = (fun q -> if only_decl then begin
(FStar_Syntax_Syntax.Assumption)::q
end else begin
q
end)
in (
# 1023 "FStar.Parser.ToSyntax.fst"
let quals = (quals ((FStar_Syntax_Syntax.Projector ((lid, x.FStar_Syntax_Syntax.ppname)))::[]))
in (
# 1024 "FStar.Parser.ToSyntax.fst"
let decl = FStar_Syntax_Syntax.Sig_declare_typ ((field_name, [], t, quals, (FStar_Ident.range_of_lid field_name)))
in if only_decl then begin
(decl)::[]
end else begin
(
# 1027 "FStar.Parser.ToSyntax.fst"
let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (
# 1028 "FStar.Parser.ToSyntax.fst"
let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _51_1839 -> (match (_51_1839) with
| (x, imp) -> begin
(
# 1029 "FStar.Parser.ToSyntax.fst"
let b = (FStar_Syntax_Syntax.is_implicit imp)
in if ((i + ntps) = j) then begin
(let _132_690 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in (_132_690, b))
end else begin
if (b && (j < ntps)) then begin
(let _132_694 = (let _132_693 = (let _132_692 = (let _132_691 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (_132_691, FStar_Syntax_Syntax.tun))
in FStar_Syntax_Syntax.Pat_dot_term (_132_692))
in (pos _132_693))
in (_132_694, b))
end else begin
(let _132_697 = (let _132_696 = (let _132_695 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_132_695))
in (pos _132_696))
in (_132_697, b))
end
end)
end))))
in (
# 1035 "FStar.Parser.ToSyntax.fst"
let pat = (let _132_702 = (let _132_700 = (let _132_699 = (let _132_698 = (FStar_Syntax_Syntax.lid_as_fv lid (Some (fvq)))
in (_132_698, arg_pats))
in FStar_Syntax_Syntax.Pat_cons (_132_699))
in (FStar_All.pipe_right _132_700 pos))
in (let _132_701 = (FStar_Syntax_Syntax.bv_to_name projection)
in (_132_702, None, _132_701)))
in (
# 1036 "FStar.Parser.ToSyntax.fst"
let body = (let _132_706 = (let _132_705 = (let _132_704 = (let _132_703 = (FStar_Syntax_Util.branch pat)
in (_132_703)::[])
in (arg_exp, _132_704))
in FStar_Syntax_Syntax.Tm_match (_132_705))
in (FStar_Syntax_Syntax.mk _132_706 None p))
in (
# 1037 "FStar.Parser.ToSyntax.fst"
let imp = (no_annot_abs binders body)
in (
# 1038 "FStar.Parser.ToSyntax.fst"
let lb = {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (field_name); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = imp}
in (
# 1043 "FStar.Parser.ToSyntax.fst"
let impl = (let _132_709 = (let _132_708 = (let _132_707 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (_132_707)::[])
in ((false, (lb)::[]), p, _132_708, quals))
in FStar_Syntax_Syntax.Sig_let (_132_709))
in if no_decl then begin
(impl)::[]
end else begin
(decl)::(impl)::[]
end)))))))
end))))))
end))
end))))
in (FStar_All.pipe_right _132_710 FStar_List.flatten)))))))))
end)))))))

# 1044 "FStar.Parser.ToSyntax.fst"
let mk_data_projectors : FStar_Parser_Env.env  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun env _51_1850 -> (match (_51_1850) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _51_1853, t, l, n, quals, _51_1859, _51_1861) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(
# 1049 "FStar.Parser.ToSyntax.fst"
let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _51_10 -> (match (_51_10) with
| FStar_Syntax_Syntax.RecordConstructor (_51_1866) -> begin
true
end
| _51_1869 -> begin
false
end)))) then begin
false
end else begin
(match ((FStar_Parser_Env.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > 1)
end
| _51_1873 -> begin
true
end)
end
in (
# 1055 "FStar.Parser.ToSyntax.fst"
let _51_1877 = (FStar_Syntax_Util.arrow_formals t)
in (match (_51_1877) with
| (formals, cod) -> begin
(match (formals) with
| [] -> begin
[]
end
| _51_1880 -> begin
(
# 1059 "FStar.Parser.ToSyntax.fst"
let qual = (match ((FStar_Util.find_map quals (fun _51_11 -> (match (_51_11) with
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((lid, fns)))
end
| _51_1885 -> begin
None
end)))) with
| None -> begin
FStar_Syntax_Syntax.Data_ctor
end
| Some (q) -> begin
q
end)
in (
# 1062 "FStar.Parser.ToSyntax.fst"
let _51_1892 = (FStar_Util.first_N n formals)
in (match (_51_1892) with
| (tps, rest) -> begin
(mk_indexed_projectors qual refine_domain env l lid inductive_tps tps rest cod)
end)))
end)
end)))
end
| _51_1894 -> begin
[]
end)
end))

# 1066 "FStar.Parser.ToSyntax.fst"
let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (
# 1069 "FStar.Parser.ToSyntax.fst"
let lb = (let _132_735 = (let _132_733 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars _132_733))
in (let _132_734 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (lid); FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = _132_735; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _132_734}))
in FStar_Syntax_Syntax.Sig_let (((false, (lb)::[]), rng, lids, quals))))

# 1076 "FStar.Parser.ToSyntax.fst"
let rec desugar_tycon : FStar_Parser_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (
# 1079 "FStar.Parser.ToSyntax.fst"
let tycon_id = (fun _51_12 -> (match (_51_12) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (
# 1084 "FStar.Parser.ToSyntax.fst"
let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _132_749 = (let _132_748 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_132_748))
in (FStar_Parser_AST.mk_term _132_749 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| (FStar_Parser_AST.TAnnotated (a, _)) | (FStar_Parser_AST.TVariable (a)) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar (a)) a.FStar_Ident.idRange FStar_Parser_AST.Type)
end
| FStar_Parser_AST.NoName (t) -> begin
t
end))
in (
# 1090 "FStar.Parser.ToSyntax.fst"
let tot = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) rng FStar_Parser_AST.Expr)
in (
# 1091 "FStar.Parser.ToSyntax.fst"
let with_constructor_effect = (fun t -> (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((tot, t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level))
in (
# 1092 "FStar.Parser.ToSyntax.fst"
let apply_binders = (fun t binders -> (
# 1093 "FStar.Parser.ToSyntax.fst"
let imp_of_aqual = (fun b -> (match (b.FStar_Parser_AST.aqual) with
| Some (FStar_Parser_AST.Implicit) -> begin
FStar_Parser_AST.Hash
end
| _51_1968 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _132_762 = (let _132_761 = (let _132_760 = (binder_to_term b)
in (out, _132_760, (imp_of_aqual b)))
in FStar_Parser_AST.App (_132_761))
in (FStar_Parser_AST.mk_term _132_762 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (
# 1098 "FStar.Parser.ToSyntax.fst"
let tycon_record_as_variant = (fun _51_13 -> (match (_51_13) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(
# 1100 "FStar.Parser.ToSyntax.fst"
let constrName = (FStar_Ident.mk_ident ((Prims.strcat "Mk" id.FStar_Ident.idText), id.FStar_Ident.idRange))
in (
# 1101 "FStar.Parser.ToSyntax.fst"
let mfields = (FStar_List.map (fun _51_1981 -> (match (_51_1981) with
| (x, t) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated (((FStar_Syntax_Util.mangle_field_name x), t))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (
# 1102 "FStar.Parser.ToSyntax.fst"
let result = (let _132_768 = (let _132_767 = (let _132_766 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_132_766))
in (FStar_Parser_AST.mk_term _132_767 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _132_768 parms))
in (
# 1103 "FStar.Parser.ToSyntax.fst"
let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _132_770 = (FStar_All.pipe_right fields (FStar_List.map (fun _51_1988 -> (match (_51_1988) with
| (x, _51_1987) -> begin
(FStar_Parser_Env.qualify env x)
end))))
in (FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _132_770))))))
end
| _51_1990 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1107 "FStar.Parser.ToSyntax.fst"
let desugar_abstract_tc = (fun quals _env mutuals _51_14 -> (match (_51_14) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(
# 1109 "FStar.Parser.ToSyntax.fst"
let _51_2004 = (typars_of_binders _env binders)
in (match (_51_2004) with
| (_env', typars) -> begin
(
# 1110 "FStar.Parser.ToSyntax.fst"
let k = (match (kopt) with
| None -> begin
FStar_Syntax_Util.ktype
end
| Some (k) -> begin
(desugar_term _env' k)
end)
in (
# 1113 "FStar.Parser.ToSyntax.fst"
let tconstr = (let _132_781 = (let _132_780 = (let _132_779 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_132_779))
in (FStar_Parser_AST.mk_term _132_780 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _132_781 binders))
in (
# 1114 "FStar.Parser.ToSyntax.fst"
let qlid = (FStar_Parser_Env.qualify _env id)
in (
# 1115 "FStar.Parser.ToSyntax.fst"
let typars = (FStar_Syntax_Subst.close_binders typars)
in (
# 1116 "FStar.Parser.ToSyntax.fst"
let k = (FStar_Syntax_Subst.close typars k)
in (
# 1117 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_inductive_typ ((qlid, [], typars, k, mutuals, [], quals, rng))
in (
# 1118 "FStar.Parser.ToSyntax.fst"
let _env = (FStar_Parser_Env.push_top_level_rec_binding _env id)
in (
# 1119 "FStar.Parser.ToSyntax.fst"
let _env2 = (FStar_Parser_Env.push_top_level_rec_binding _env' id)
in (_env, _env2, se, tconstr)))))))))
end))
end
| _51_2017 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (
# 1122 "FStar.Parser.ToSyntax.fst"
let push_tparams = (fun env bs -> (
# 1123 "FStar.Parser.ToSyntax.fst"
let _51_2032 = (FStar_List.fold_left (fun _51_2023 _51_2026 -> (match ((_51_2023, _51_2026)) with
| ((env, tps), (x, imp)) -> begin
(
# 1124 "FStar.Parser.ToSyntax.fst"
let _51_2029 = (FStar_Parser_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (_51_2029) with
| (env, y) -> begin
(env, ((y, imp))::tps)
end))
end)) (env, []) bs)
in (match (_51_2032) with
| (env, bs) -> begin
(env, (FStar_List.rev bs))
end)))
in (match (tcs) with
| FStar_Parser_AST.TyconAbstract (_51_2034)::[] -> begin
(
# 1129 "FStar.Parser.ToSyntax.fst"
let tc = (FStar_List.hd tcs)
in (
# 1130 "FStar.Parser.ToSyntax.fst"
let _51_2045 = (desugar_abstract_tc quals env [] tc)
in (match (_51_2045) with
| (_51_2039, _51_2041, se, _51_2044) -> begin
(
# 1131 "FStar.Parser.ToSyntax.fst"
let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _51_2048, typars, k, [], [], quals, rng) -> begin
(
# 1133 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
quals
end else begin
(
# 1135 "FStar.Parser.ToSyntax.fst"
let _51_2057 = (let _132_789 = (FStar_Range.string_of_range rng)
in (let _132_788 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" _132_789 _132_788)))
in (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals)
end
in (
# 1138 "FStar.Parser.ToSyntax.fst"
let t = (match (typars) with
| [] -> begin
k
end
| _51_2062 -> begin
(let _132_792 = (let _132_791 = (let _132_790 = (FStar_Syntax_Syntax.mk_Total k)
in (typars, _132_790))
in FStar_Syntax_Syntax.Tm_arrow (_132_791))
in (FStar_Syntax_Syntax.mk _132_792 None rng))
end)
in FStar_Syntax_Syntax.Sig_declare_typ ((l, [], t, quals, rng))))
end
| _51_2065 -> begin
se
end)
in (
# 1143 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))
end)))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t)::[] -> begin
(
# 1148 "FStar.Parser.ToSyntax.fst"
let _51_2077 = (typars_of_binders env binders)
in (match (_51_2077) with
| (env', typars) -> begin
(
# 1149 "FStar.Parser.ToSyntax.fst"
let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _51_15 -> (match (_51_15) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| _51_2082 -> begin
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
# 1155 "FStar.Parser.ToSyntax.fst"
let t0 = t
in (
# 1156 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _51_16 -> (match (_51_16) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| _51_2090 -> begin
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
# 1161 "FStar.Parser.ToSyntax.fst"
let se = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Effect)) then begin
(
# 1163 "FStar.Parser.ToSyntax.fst"
let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (
# 1164 "FStar.Parser.ToSyntax.fst"
let typars = (FStar_Syntax_Subst.close_binders typars)
in (
# 1165 "FStar.Parser.ToSyntax.fst"
let c = (FStar_Syntax_Subst.close_comp typars c)
in (let _132_798 = (let _132_797 = (FStar_Parser_Env.qualify env id)
in (let _132_796 = (FStar_All.pipe_right quals (FStar_List.filter (fun _51_17 -> (match (_51_17) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| _51_2098 -> begin
true
end))))
in (_132_797, [], typars, c, _132_796, rng)))
in FStar_Syntax_Syntax.Sig_effect_abbrev (_132_798)))))
end else begin
(
# 1167 "FStar.Parser.ToSyntax.fst"
let t = (desugar_typ env' t)
in (
# 1168 "FStar.Parser.ToSyntax.fst"
let nm = (FStar_Parser_Env.qualify env id)
in (mk_typ_abbrev nm [] typars k t ((nm)::[]) quals rng)))
end
in (
# 1171 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[]))))))
end))
end
| FStar_Parser_AST.TyconRecord (_51_2104)::[] -> begin
(
# 1175 "FStar.Parser.ToSyntax.fst"
let trec = (FStar_List.hd tcs)
in (
# 1176 "FStar.Parser.ToSyntax.fst"
let _51_2110 = (tycon_record_as_variant trec)
in (match (_51_2110) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| _51_2114::_51_2112 -> begin
(
# 1180 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1181 "FStar.Parser.ToSyntax.fst"
let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_Env.qualify env) (tycon_id x))) tcs)
in (
# 1182 "FStar.Parser.ToSyntax.fst"
let rec collect_tcs = (fun quals et tc -> (
# 1183 "FStar.Parser.ToSyntax.fst"
let _51_2125 = et
in (match (_51_2125) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_51_2127) -> begin
(
# 1186 "FStar.Parser.ToSyntax.fst"
let trec = tc
in (
# 1187 "FStar.Parser.ToSyntax.fst"
let _51_2132 = (tycon_record_as_variant trec)
in (match (_51_2132) with
| (t, fs) -> begin
(collect_tcs ((FStar_Syntax_Syntax.RecordType (fs))::quals) (env, tcs) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(
# 1190 "FStar.Parser.ToSyntax.fst"
let _51_2144 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_51_2144) with
| (env, _51_2141, se, tconstr) -> begin
(env, (FStar_Util.Inl ((se, constructors, tconstr, quals)))::tcs)
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(
# 1193 "FStar.Parser.ToSyntax.fst"
let _51_2156 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_51_2156) with
| (env, _51_2153, se, tconstr) -> begin
(env, (FStar_Util.Inr ((se, t, quals)))::tcs)
end))
end
| _51_2158 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (
# 1196 "FStar.Parser.ToSyntax.fst"
let _51_2161 = (FStar_List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_51_2161) with
| (env, tcs) -> begin
(
# 1197 "FStar.Parser.ToSyntax.fst"
let tcs = (FStar_List.rev tcs)
in (
# 1198 "FStar.Parser.ToSyntax.fst"
let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _51_19 -> (match (_51_19) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, _51_2169, _51_2171, _51_2173, _51_2175), t, quals) -> begin
(
# 1200 "FStar.Parser.ToSyntax.fst"
let _51_2185 = (push_tparams env tpars)
in (match (_51_2185) with
| (env_tps, _51_2184) -> begin
(
# 1201 "FStar.Parser.ToSyntax.fst"
let t = (desugar_term env_tps t)
in (let _132_808 = (let _132_807 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in ([], _132_807))
in (_132_808)::[]))
end))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, _51_2193, tags, _51_2196), constrs, tconstr, quals) -> begin
(
# 1205 "FStar.Parser.ToSyntax.fst"
let tycon = (tname, tpars, k)
in (
# 1206 "FStar.Parser.ToSyntax.fst"
let _51_2207 = (push_tparams env tpars)
in (match (_51_2207) with
| (env_tps, tps) -> begin
(
# 1207 "FStar.Parser.ToSyntax.fst"
let data_tpars = (FStar_List.map (fun _51_2211 -> (match (_51_2211) with
| (x, _51_2210) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end)) tps)
in (
# 1208 "FStar.Parser.ToSyntax.fst"
let _51_2235 = (let _132_820 = (FStar_All.pipe_right constrs (FStar_List.map (fun _51_2216 -> (match (_51_2216) with
| (id, topt, of_notation) -> begin
(
# 1210 "FStar.Parser.ToSyntax.fst"
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
# 1218 "FStar.Parser.ToSyntax.fst"
let t = (let _132_812 = (FStar_Parser_Env.default_total env_tps)
in (let _132_811 = (close env_tps t)
in (desugar_term _132_812 _132_811)))
in (
# 1219 "FStar.Parser.ToSyntax.fst"
let name = (FStar_Parser_Env.qualify env id)
in (
# 1220 "FStar.Parser.ToSyntax.fst"
let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _51_18 -> (match (_51_18) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| _51_2230 -> begin
[]
end))))
in (
# 1223 "FStar.Parser.ToSyntax.fst"
let ntps = (FStar_List.length data_tpars)
in (let _132_819 = (let _132_818 = (let _132_817 = (let _132_816 = (let _132_815 = (let _132_814 = (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total _132_814))
in (FStar_Syntax_Util.arrow data_tpars _132_815))
in (name, univs, _132_816, tname, ntps, quals, mutuals, rng))
in FStar_Syntax_Syntax.Sig_datacon (_132_817))
in (tps, _132_818))
in (name, _132_819)))))))
end))))
in (FStar_All.pipe_left FStar_List.split _132_820))
in (match (_51_2235) with
| (constrNames, constrs) -> begin
(([], FStar_Syntax_Syntax.Sig_inductive_typ ((tname, univs, tpars, k, mutuals, constrNames, tags, rng))))::constrs
end)))
end)))
end
| _51_2237 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1228 "FStar.Parser.ToSyntax.fst"
let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (
# 1229 "FStar.Parser.ToSyntax.fst"
let bundle = (let _132_822 = (let _132_821 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _132_821, rng))
in FStar_Syntax_Syntax.Sig_bundle (_132_822))
in (
# 1230 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 bundle)
in (
# 1231 "FStar.Parser.ToSyntax.fst"
let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projectors env)))
in (
# 1232 "FStar.Parser.ToSyntax.fst"
let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _51_20 -> (match (_51_20) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, _51_2246, tps, k, _51_2250, constrs, quals, _51_2254) when ((FStar_List.length constrs) > 1) -> begin
(mk_data_discriminators quals env tname tps k constrs)
end
| _51_2258 -> begin
[]
end))))
in (
# 1236 "FStar.Parser.ToSyntax.fst"
let ops = (FStar_List.append discs data_ops)
in (
# 1237 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env ops)
in (env, (FStar_List.append ((bundle)::[]) ops)))))))))))
end)))))
end
| [] -> begin
(FStar_All.failwith "impossible")
end))))))))))

# 1240 "FStar.Parser.ToSyntax.fst"
let desugar_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.binder Prims.list) = (fun env binders -> (
# 1243 "FStar.Parser.ToSyntax.fst"
let _51_2282 = (FStar_List.fold_left (fun _51_2267 b -> (match (_51_2267) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| (Some (a), k) -> begin
(
# 1246 "FStar.Parser.ToSyntax.fst"
let _51_2275 = (FStar_Parser_Env.push_bv env a)
in (match (_51_2275) with
| (env, a) -> begin
(let _132_831 = (let _132_830 = (FStar_Syntax_Syntax.mk_binder (
# 1247 "FStar.Parser.ToSyntax.fst"
let _51_2276 = a
in {FStar_Syntax_Syntax.ppname = _51_2276.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _51_2276.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (_132_830)::binders)
in (env, _132_831))
end))
end
| _51_2279 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Missing name in binder", b.FStar_Parser_AST.brange))))
end)
end)) (env, []) binders)
in (match (_51_2282) with
| (env, binders) -> begin
(env, (FStar_List.rev binders))
end)))

# 1250 "FStar.Parser.ToSyntax.fst"
let rec desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(
# 1254 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_pragma (((trans_pragma p), d.FStar_Parser_AST.drange))
in (env, (se)::[]))
end
| FStar_Parser_AST.Open (lid) -> begin
(
# 1258 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_namespace env lid)
in (env, []))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(let _132_836 = (FStar_List.map trans_qual qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _132_836 tcs))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _132_838 = (let _132_837 = (desugar_term_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((isrec, lets, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Syntax_Subst.compress _132_837))
in _132_838.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let (lbs, _51_2302) -> begin
(
# 1267 "FStar.Parser.ToSyntax.fst"
let lids = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (
# 1268 "FStar.Parser.ToSyntax.fst"
let quals = (match (quals) with
| _51_2310::_51_2308 -> begin
(FStar_List.map trans_qual quals)
end
| _51_2313 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _51_21 -> (match (_51_21) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (_51_2324); FStar_Syntax_Syntax.lbunivs = _51_2322; FStar_Syntax_Syntax.lbtyp = _51_2320; FStar_Syntax_Syntax.lbeff = _51_2318; FStar_Syntax_Syntax.lbdef = _51_2316} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (l); FStar_Syntax_Syntax.lbunivs = _51_2334; FStar_Syntax_Syntax.lbtyp = _51_2332; FStar_Syntax_Syntax.lbeff = _51_2330; FStar_Syntax_Syntax.lbdef = _51_2328} -> begin
(FStar_Parser_Env.lookup_letbinding_quals env l)
end))))
end)
in (
# 1273 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right lets (FStar_Util.for_some (fun _51_2342 -> (match (_51_2342) with
| (_51_2340, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end)))) then begin
(FStar_Syntax_Syntax.Logic)::quals
end else begin
quals
end
in (
# 1277 "FStar.Parser.ToSyntax.fst"
let s = FStar_Syntax_Syntax.Sig_let ((lbs, d.FStar_Parser_AST.drange, lids, quals))
in (
# 1278 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env s)
in (env, (s)::[]))))))
end
| _51_2347 -> begin
(FStar_All.failwith "Desugaring a let did not produce a let")
end)
end
| FStar_Parser_AST.Main (t) -> begin
(
# 1284 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env t)
in (
# 1285 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, d.FStar_Parser_AST.drange))
in (env, (se)::[])))
end
| FStar_Parser_AST.Assume (atag, id, t) -> begin
(
# 1289 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env t)
in (let _132_845 = (let _132_844 = (let _132_843 = (let _132_842 = (FStar_Parser_Env.qualify env id)
in (_132_842, f, (FStar_Syntax_Syntax.Assumption)::[], d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Sig_assume (_132_843))
in (_132_844)::[])
in (env, _132_845)))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(
# 1293 "FStar.Parser.ToSyntax.fst"
let t = (let _132_846 = (close_fun env t)
in (desugar_term env _132_846))
in (
# 1294 "FStar.Parser.ToSyntax.fst"
let quals = if (env.FStar_Parser_Env.iface && env.FStar_Parser_Env.admitted_iface) then begin
(FStar_Parser_AST.Assumption)::quals
end else begin
quals
end
in (
# 1295 "FStar.Parser.ToSyntax.fst"
let se = (let _132_849 = (let _132_848 = (FStar_Parser_Env.qualify env id)
in (let _132_847 = (FStar_List.map trans_qual quals)
in (_132_848, [], t, _132_847, d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_declare_typ (_132_849))
in (
# 1296 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(
# 1300 "FStar.Parser.ToSyntax.fst"
let t = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (
# 1301 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env id)
in (
# 1302 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_datacon ((l, [], t, FStar_Syntax_Const.exn_lid, 0, (FStar_Syntax_Syntax.ExceptionConstructor)::[], (FStar_Syntax_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (
# 1303 "FStar.Parser.ToSyntax.fst"
let se' = FStar_Syntax_Syntax.Sig_bundle (((se)::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (
# 1304 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se')
in (
# 1305 "FStar.Parser.ToSyntax.fst"
let data_ops = (mk_data_projectors env ([], se))
in (
# 1306 "FStar.Parser.ToSyntax.fst"
let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (
# 1307 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops))))))))))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(
# 1311 "FStar.Parser.ToSyntax.fst"
let t = (desugar_term env term)
in (
# 1312 "FStar.Parser.ToSyntax.fst"
let t = (let _132_853 = (let _132_850 = (FStar_Syntax_Syntax.null_binder t)
in (_132_850)::[])
in (let _132_852 = (let _132_851 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _132_851))
in (FStar_Syntax_Util.arrow _132_853 _132_852)))
in (
# 1313 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env id)
in (
# 1314 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_datacon ((l, [], t, FStar_Syntax_Const.exn_lid, 0, (FStar_Syntax_Syntax.ExceptionConstructor)::[], (FStar_Syntax_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (
# 1315 "FStar.Parser.ToSyntax.fst"
let se' = FStar_Syntax_Syntax.Sig_bundle (((se)::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (
# 1316 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se')
in (
# 1317 "FStar.Parser.ToSyntax.fst"
let data_ops = (mk_data_projectors env ([], se))
in (
# 1318 "FStar.Parser.ToSyntax.fst"
let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (
# 1319 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops)))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(
# 1323 "FStar.Parser.ToSyntax.fst"
let _51_2400 = (desugar_binders env binders)
in (match (_51_2400) with
| (env_k, binders) -> begin
(
# 1324 "FStar.Parser.ToSyntax.fst"
let k = (desugar_term env_k k)
in (
# 1325 "FStar.Parser.ToSyntax.fst"
let name = (FStar_Parser_Env.qualify env id)
in (
# 1326 "FStar.Parser.ToSyntax.fst"
let se = (mk_typ_abbrev name [] binders FStar_Syntax_Syntax.tun k ((name)::[]) [] d.FStar_Parser_AST.drange)
in (
# 1327 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))))
end))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(
# 1331 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1332 "FStar.Parser.ToSyntax.fst"
let _51_2416 = (desugar_binders env eff_binders)
in (match (_51_2416) with
| (env, binders) -> begin
(
# 1333 "FStar.Parser.ToSyntax.fst"
let _51_2427 = (
# 1334 "FStar.Parser.ToSyntax.fst"
let _51_2419 = (head_and_args defn)
in (match (_51_2419) with
| (head, args) -> begin
(
# 1335 "FStar.Parser.ToSyntax.fst"
let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_defn env) l)
end
| _51_2423 -> begin
(let _132_858 = (let _132_857 = (let _132_856 = (let _132_855 = (let _132_854 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat "Effect " _132_854))
in (Prims.strcat _132_855 " not found"))
in (_132_856, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_132_857))
in (Prims.raise _132_858))
end)
in (let _132_859 = (desugar_args env args)
in (ed, _132_859)))
end))
in (match (_51_2427) with
| (ed, args) -> begin
(
# 1339 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_Syntax_Subst.close_binders binders)
in (
# 1340 "FStar.Parser.ToSyntax.fst"
let sub = (fun _51_2433 -> (match (_51_2433) with
| (_51_2431, x) -> begin
(
# 1341 "FStar.Parser.ToSyntax.fst"
let _51_2436 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (_51_2436) with
| (edb, x) -> begin
(
# 1342 "FStar.Parser.ToSyntax.fst"
let s = (FStar_Syntax_Util.subst_of_list edb args)
in (let _132_863 = (let _132_862 = (FStar_Syntax_Subst.subst s x)
in (FStar_Syntax_Subst.close binders _132_862))
in ([], _132_863)))
end))
end))
in (
# 1344 "FStar.Parser.ToSyntax.fst"
let ed = (let _132_880 = (FStar_List.map trans_qual quals)
in (let _132_879 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _132_878 = (let _132_864 = (sub ([], ed.FStar_Syntax_Syntax.signature))
in (Prims.snd _132_864))
in (let _132_877 = (sub ed.FStar_Syntax_Syntax.ret)
in (let _132_876 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (let _132_875 = (sub ed.FStar_Syntax_Syntax.bind_wlp)
in (let _132_874 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (let _132_873 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (let _132_872 = (sub ed.FStar_Syntax_Syntax.ite_wlp)
in (let _132_871 = (sub ed.FStar_Syntax_Syntax.wp_binop)
in (let _132_870 = (sub ed.FStar_Syntax_Syntax.wp_as_type)
in (let _132_869 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (let _132_868 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (let _132_867 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (let _132_866 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (let _132_865 = (sub ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _132_880; FStar_Syntax_Syntax.mname = _132_879; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = _132_878; FStar_Syntax_Syntax.ret = _132_877; FStar_Syntax_Syntax.bind_wp = _132_876; FStar_Syntax_Syntax.bind_wlp = _132_875; FStar_Syntax_Syntax.if_then_else = _132_874; FStar_Syntax_Syntax.ite_wp = _132_873; FStar_Syntax_Syntax.ite_wlp = _132_872; FStar_Syntax_Syntax.wp_binop = _132_871; FStar_Syntax_Syntax.wp_as_type = _132_870; FStar_Syntax_Syntax.close_wp = _132_869; FStar_Syntax_Syntax.assert_p = _132_868; FStar_Syntax_Syntax.assume_p = _132_867; FStar_Syntax_Syntax.null_wp = _132_866; FStar_Syntax_Syntax.trivial = _132_865}))))))))))))))))
in (
# 1364 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (
# 1365 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 se)
in (env, (se)::[]))))))
end))
end)))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls)) -> begin
(
# 1369 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1370 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.enter_monad_scope env eff_name)
in (
# 1371 "FStar.Parser.ToSyntax.fst"
let _51_2454 = (desugar_binders env eff_binders)
in (match (_51_2454) with
| (env, binders) -> begin
(
# 1372 "FStar.Parser.ToSyntax.fst"
let eff_k = (let _132_881 = (FStar_Parser_Env.default_total env)
in (desugar_term _132_881 eff_kind))
in (
# 1373 "FStar.Parser.ToSyntax.fst"
let _51_2465 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _51_2458 decl -> (match (_51_2458) with
| (env, out) -> begin
(
# 1374 "FStar.Parser.ToSyntax.fst"
let _51_2462 = (desugar_decl env decl)
in (match (_51_2462) with
| (env, ses) -> begin
(let _132_885 = (let _132_884 = (FStar_List.hd ses)
in (_132_884)::out)
in (env, _132_885))
end))
end)) (env, [])))
in (match (_51_2465) with
| (env, decls) -> begin
(
# 1376 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_Syntax_Subst.close_binders binders)
in (
# 1377 "FStar.Parser.ToSyntax.fst"
let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (
# 1378 "FStar.Parser.ToSyntax.fst"
let lookup = (fun s -> (
# 1379 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env (FStar_Ident.mk_ident (s, d.FStar_Parser_AST.drange)))
in (let _132_889 = (let _132_888 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) _132_888))
in ([], _132_889))))
in (
# 1381 "FStar.Parser.ToSyntax.fst"
let ed = (let _132_904 = (FStar_List.map trans_qual quals)
in (let _132_903 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _132_902 = (lookup "return")
in (let _132_901 = (lookup "bind_wp")
in (let _132_900 = (lookup "bind_wlp")
in (let _132_899 = (lookup "if_then_else")
in (let _132_898 = (lookup "ite_wp")
in (let _132_897 = (lookup "ite_wlp")
in (let _132_896 = (lookup "wp_binop")
in (let _132_895 = (lookup "wp_as_type")
in (let _132_894 = (lookup "close_wp")
in (let _132_893 = (lookup "assert_p")
in (let _132_892 = (lookup "assume_p")
in (let _132_891 = (lookup "null_wp")
in (let _132_890 = (lookup "trivial")
in {FStar_Syntax_Syntax.qualifiers = _132_904; FStar_Syntax_Syntax.mname = _132_903; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret = _132_902; FStar_Syntax_Syntax.bind_wp = _132_901; FStar_Syntax_Syntax.bind_wlp = _132_900; FStar_Syntax_Syntax.if_then_else = _132_899; FStar_Syntax_Syntax.ite_wp = _132_898; FStar_Syntax_Syntax.ite_wlp = _132_897; FStar_Syntax_Syntax.wp_binop = _132_896; FStar_Syntax_Syntax.wp_as_type = _132_895; FStar_Syntax_Syntax.close_wp = _132_894; FStar_Syntax_Syntax.assert_p = _132_893; FStar_Syntax_Syntax.assume_p = _132_892; FStar_Syntax_Syntax.null_wp = _132_891; FStar_Syntax_Syntax.trivial = _132_890})))))))))))))))
in (
# 1401 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (
# 1402 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 se)
in (env, (se)::[])))))))
end)))
end))))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(
# 1406 "FStar.Parser.ToSyntax.fst"
let lookup = (fun l -> (match ((FStar_Parser_Env.try_lookup_effect_name env l)) with
| None -> begin
(let _132_911 = (let _132_910 = (let _132_909 = (let _132_908 = (let _132_907 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat "Effect name " _132_907))
in (Prims.strcat _132_908 " not found"))
in (_132_909, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_132_910))
in (Prims.raise _132_911))
end
| Some (l) -> begin
l
end))
in (
# 1409 "FStar.Parser.ToSyntax.fst"
let src = (lookup l.FStar_Parser_AST.msource)
in (
# 1410 "FStar.Parser.ToSyntax.fst"
let dst = (lookup l.FStar_Parser_AST.mdest)
in (
# 1411 "FStar.Parser.ToSyntax.fst"
let lift = (let _132_912 = (desugar_term env l.FStar_Parser_AST.lift_op)
in ([], _132_912))
in (
# 1412 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect (({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift = lift}, d.FStar_Parser_AST.drange))
in (env, (se)::[]))))))
end))

# 1413 "FStar.Parser.ToSyntax.fst"
let desugar_decls : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _51_2489 d -> (match (_51_2489) with
| (env, sigelts) -> begin
(
# 1417 "FStar.Parser.ToSyntax.fst"
let _51_2493 = (desugar_decl env d)
in (match (_51_2493) with
| (env, se) -> begin
(env, (FStar_List.append sigelts se))
end))
end)) (env, []) decls))

# 1418 "FStar.Parser.ToSyntax.fst"
let open_prims_all : FStar_Parser_AST.decl Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.all_lid)) FStar_Range.dummyRange))::[]

# 1422 "FStar.Parser.ToSyntax.fst"
let desugar_modul_common : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (
# 1428 "FStar.Parser.ToSyntax.fst"
let open_ns = (fun mname d -> (
# 1429 "FStar.Parser.ToSyntax.fst"
let d = if ((FStar_List.length mname.FStar_Ident.ns) <> 0) then begin
(let _132_931 = (let _132_930 = (let _132_929 = (FStar_Ident.lid_of_ids mname.FStar_Ident.ns)
in FStar_Parser_AST.Open (_132_929))
in (FStar_Parser_AST.mk_decl _132_930 (FStar_Ident.range_of_lid mname)))
in (_132_931)::d)
end else begin
d
end
in d))
in (
# 1433 "FStar.Parser.ToSyntax.fst"
let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod) -> begin
(FStar_Parser_Env.finish_module_or_interface env prev_mod)
end)
in (
# 1436 "FStar.Parser.ToSyntax.fst"
let _51_2520 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _132_933 = (FStar_Parser_Env.prepare_module_or_interface true admitted env mname)
in (let _132_932 = (open_ns mname decls)
in (_132_933, mname, _132_932, true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _132_935 = (FStar_Parser_Env.prepare_module_or_interface false false env mname)
in (let _132_934 = (open_ns mname decls)
in (_132_935, mname, _132_934, false)))
end)
in (match (_51_2520) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(
# 1441 "FStar.Parser.ToSyntax.fst"
let _51_2523 = (desugar_decls env decls)
in (match (_51_2523) with
| (env, sigelts) -> begin
(
# 1442 "FStar.Parser.ToSyntax.fst"
let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in (env, modul, pop_when_done))
end))
end)))))

# 1448 "FStar.Parser.ToSyntax.fst"
let desugar_partial_modul : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (
# 1451 "FStar.Parser.ToSyntax.fst"
let m = if (FStar_ST.read FStar_Options.interactive_fsi) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface ((mname, decls, true))
end
| FStar_Parser_AST.Interface (mname, _51_2534, _51_2536) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (
# 1458 "FStar.Parser.ToSyntax.fst"
let _51_2544 = (desugar_modul_common curmod env m)
in (match (_51_2544) with
| (x, y, _51_2543) -> begin
(x, y)
end))))

# 1459 "FStar.Parser.ToSyntax.fst"
let desugar_modul : FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (
# 1462 "FStar.Parser.ToSyntax.fst"
let _51_2550 = (desugar_modul_common None env m)
in (match (_51_2550) with
| (env, modul, pop_when_done) -> begin
(
# 1463 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.finish_module_or_interface env modul)
in (
# 1464 "FStar.Parser.ToSyntax.fst"
let _51_2552 = if (FStar_Options.should_dump modul.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _132_946 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _132_946))
end else begin
()
end
in (let _132_947 = if pop_when_done then begin
(FStar_Parser_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end else begin
env
end
in (_132_947, modul))))
end)))

# 1466 "FStar.Parser.ToSyntax.fst"
let desugar_file : FStar_Parser_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (
# 1469 "FStar.Parser.ToSyntax.fst"
let _51_2565 = (FStar_List.fold_left (fun _51_2558 m -> (match (_51_2558) with
| (env, mods) -> begin
(
# 1470 "FStar.Parser.ToSyntax.fst"
let _51_2562 = (desugar_modul env m)
in (match (_51_2562) with
| (env, m) -> begin
(env, (m)::mods)
end))
end)) (env, []) f)
in (match (_51_2565) with
| (env, mods) -> begin
(env, (FStar_List.rev mods))
end)))

# 1472 "FStar.Parser.ToSyntax.fst"
let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Parser_Env.env  ->  FStar_Parser_Env.env = (fun m en -> (
# 1475 "FStar.Parser.ToSyntax.fst"
let _51_2570 = (FStar_Parser_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (_51_2570) with
| (en, pop_when_done) -> begin
(
# 1476 "FStar.Parser.ToSyntax.fst"
let en = (FStar_List.fold_left FStar_Parser_Env.push_sigelt (
# 1476 "FStar.Parser.ToSyntax.fst"
let _51_2571 = en
in {FStar_Parser_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_Parser_Env.modules = _51_2571.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _51_2571.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.sigaccum = _51_2571.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _51_2571.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _51_2571.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _51_2571.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _51_2571.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _51_2571.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _51_2571.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = _51_2571.FStar_Parser_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (
# 1477 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_Env.export_interface m.FStar_Syntax_Syntax.name env)
end else begin
env
end))
end)))




