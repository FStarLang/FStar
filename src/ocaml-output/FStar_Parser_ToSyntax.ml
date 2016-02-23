
open Prims
# 40 "FStar.Parser.ToSyntax.fst"
let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _52_1 -> (match (_52_1) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Syntax_Syntax.Equality)
end
| _52_29 -> begin
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
(FStar_All.failwith "Impossible")
end))

# 59 "FStar.Parser.ToSyntax.fst"
let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun _52_3 -> (match (_52_3) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions -> begin
FStar_Syntax_Syntax.ResetOptions
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
let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _131_21 = (let _131_20 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_131_20))
in (FStar_Parser_AST.mk_term _131_21 r FStar_Parser_AST.Kind)))

# 85 "FStar.Parser.ToSyntax.fst"
let compile_op : Prims.int  ->  Prims.string  ->  Prims.string = (fun arity s -> (
# 86 "FStar.Parser.ToSyntax.fst"
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
| _52_93 -> begin
"UNKNOWN"
end))
in (
# 105 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _131_32 = (let _131_30 = (FStar_Util.char_at s i)
in (name_of_char _131_30))
in (let _131_31 = (aux (i + 1))
in (_131_32)::_131_31))
end)
in (let _131_34 = (let _131_33 = (aux 0)
in (FStar_String.concat "_" _131_33))
in (Prims.strcat "op_" _131_34)))))

# 111 "FStar.Parser.ToSyntax.fst"
let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _131_44 = (let _131_43 = (let _131_42 = (let _131_41 = (compile_op n s)
in (_131_41, r))
in (FStar_Ident.mk_ident _131_42))
in (_131_43)::[])
in (FStar_All.pipe_right _131_44 FStar_Ident.lid_of_ids)))

# 113 "FStar.Parser.ToSyntax.fst"
let op_as_lid : FStar_Parser_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Ident.lident Prims.option = (fun env arity rng s -> (
# 114 "FStar.Parser.ToSyntax.fst"
let r = (fun l -> (let _131_55 = (FStar_Ident.set_lid_range l rng)
in Some (_131_55)))
in (
# 115 "FStar.Parser.ToSyntax.fst"
let fallback = (fun _52_107 -> (match (()) with
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
| "*" -> begin
(r FStar_Syntax_Const.op_Multiply)
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
| _52_137 -> begin
None
end)
end))
in (match ((let _131_58 = (compile_op_lid arity s rng)
in (FStar_Parser_Env.try_lookup_lid env _131_58))) with
| Some ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _52_146); FStar_Syntax_Syntax.tk = _52_143; FStar_Syntax_Syntax.pos = _52_141; FStar_Syntax_Syntax.vars = _52_139}) -> begin
Some (fv.FStar_Syntax_Syntax.v)
end
| _52_152 -> begin
(fallback ())
end))))

# 151 "FStar.Parser.ToSyntax.fst"
let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _131_65 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _131_65)))

# 155 "FStar.Parser.ToSyntax.fst"
let rec free_type_vars_b : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_52_161) -> begin
(env, [])
end
| FStar_Parser_AST.TVariable (x) -> begin
(
# 158 "FStar.Parser.ToSyntax.fst"
let _52_168 = (FStar_Parser_Env.push_bv env x)
in (match (_52_168) with
| (env, _52_167) -> begin
(env, (x)::[])
end))
end
| FStar_Parser_AST.Annotated (_52_170, term) -> begin
(let _131_72 = (free_type_vars env term)
in (env, _131_72))
end
| FStar_Parser_AST.TAnnotated (id, _52_176) -> begin
(
# 163 "FStar.Parser.ToSyntax.fst"
let _52_182 = (FStar_Parser_Env.push_bv env id)
in (match (_52_182) with
| (env, _52_181) -> begin
(env, [])
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _131_73 = (free_type_vars env t)
in (env, _131_73))
end))
and free_type_vars : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _131_76 = (unparen t)
in _131_76.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (_52_188) -> begin
(FStar_All.failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_Env.try_lookup_id env a)) with
| None -> begin
(a)::[]
end
| _52_194 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_52_224, ts) -> begin
(FStar_List.collect (fun _52_231 -> (match (_52_231) with
| (t, _52_230) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_52_233, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _52_240) -> begin
(let _131_79 = (free_type_vars env t1)
in (let _131_78 = (free_type_vars env t2)
in (FStar_List.append _131_79 _131_78)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(
# 193 "FStar.Parser.ToSyntax.fst"
let _52_249 = (free_type_vars_b env b)
in (match (_52_249) with
| (env, f) -> begin
(let _131_80 = (free_type_vars env t)
in (FStar_List.append f _131_80))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(
# 198 "FStar.Parser.ToSyntax.fst"
let _52_265 = (FStar_List.fold_left (fun _52_258 binder -> (match (_52_258) with
| (env, free) -> begin
(
# 199 "FStar.Parser.ToSyntax.fst"
let _52_262 = (free_type_vars_b env binder)
in (match (_52_262) with
| (env, f) -> begin
(env, (FStar_List.append f free))
end))
end)) (env, []) binders)
in (match (_52_265) with
| (env, free) -> begin
(let _131_83 = (free_type_vars env body)
in (FStar_List.append free _131_83))
end))
end
| FStar_Parser_AST.Project (t, _52_268) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) -> begin
[]
end
| (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
(FStar_Parser_AST.error "Unexpected type in free_type_vars computation" t t.FStar_Parser_AST.range)
end))

# 216 "FStar.Parser.ToSyntax.fst"
let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (
# 217 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun args t -> (match ((let _131_90 = (unparen t)
in _131_90.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _52_312 -> begin
(t, args)
end))
in (aux [] t)))

# 223 "FStar.Parser.ToSyntax.fst"
let close : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 224 "FStar.Parser.ToSyntax.fst"
let ftv = (let _131_95 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _131_95))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 227 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _131_99 = (let _131_98 = (let _131_97 = (tm_type x.FStar_Ident.idRange)
in (x, _131_97))
in FStar_Parser_AST.TAnnotated (_131_98))
in (FStar_Parser_AST.mk_binder _131_99 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 228 "FStar.Parser.ToSyntax.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))

# 231 "FStar.Parser.ToSyntax.fst"
let close_fun : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 232 "FStar.Parser.ToSyntax.fst"
let ftv = (let _131_104 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _131_104))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 235 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _131_108 = (let _131_107 = (let _131_106 = (tm_type x.FStar_Ident.idRange)
in (x, _131_106))
in FStar_Parser_AST.TAnnotated (_131_107))
in (FStar_Parser_AST.mk_binder _131_108 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 236 "FStar.Parser.ToSyntax.fst"
let t = (match ((let _131_109 = (unparen t)
in _131_109.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_52_325) -> begin
t
end
| _52_328 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level), t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end)
in (
# 239 "FStar.Parser.ToSyntax.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result)))
end))

# 242 "FStar.Parser.ToSyntax.fst"
let rec uncurry : FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term) = (fun bs t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (binders, t) -> begin
(uncurry (FStar_List.append bs binders) t)
end
| _52_338 -> begin
(bs, t)
end))

# 246 "FStar.Parser.ToSyntax.fst"
let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _52_342) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_52_348); FStar_Parser_AST.prange = _52_346}, _52_352) -> begin
true
end
| _52_356 -> begin
false
end))

# 251 "FStar.Parser.ToSyntax.fst"
let rec destruct_app_pattern : FStar_Parser_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 253 "FStar.Parser.ToSyntax.fst"
let _52_368 = (destruct_app_pattern env is_top_level p)
in (match (_52_368) with
| (name, args, _52_367) -> begin
(name, args, Some (t))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _52_373); FStar_Parser_AST.prange = _52_370}, args) when is_top_level -> begin
(let _131_123 = (let _131_122 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_131_122))
in (_131_123, args, None))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _52_384); FStar_Parser_AST.prange = _52_381}, args) -> begin
(FStar_Util.Inl (id), args, None)
end
| _52_392 -> begin
(FStar_All.failwith "Not an app pattern")
end))

# 262 "FStar.Parser.ToSyntax.fst"
type bnd =
| LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * FStar_Syntax_Syntax.term)

# 263 "FStar.Parser.ToSyntax.fst"
let is_LocalBinder = (fun _discr_ -> (match (_discr_) with
| LocalBinder (_) -> begin
true
end
| _ -> begin
false
end))

# 264 "FStar.Parser.ToSyntax.fst"
let is_LetBinder = (fun _discr_ -> (match (_discr_) with
| LetBinder (_) -> begin
true
end
| _ -> begin
false
end))

# 263 "FStar.Parser.ToSyntax.fst"
let ___LocalBinder____0 : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun projectee -> (match (projectee) with
| LocalBinder (_52_395) -> begin
_52_395
end))

# 264 "FStar.Parser.ToSyntax.fst"
let ___LetBinder____0 : bnd  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| LetBinder (_52_398) -> begin
_52_398
end))

# 265 "FStar.Parser.ToSyntax.fst"
let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun _52_6 -> (match (_52_6) with
| LocalBinder (a, aq) -> begin
(a, aq)
end
| _52_405 -> begin
(FStar_All.failwith "Impossible")
end))

# 268 "FStar.Parser.ToSyntax.fst"
let as_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_Parser_Env.env) = (fun env imp _52_7 -> (match (_52_7) with
| (None, k) -> begin
(let _131_160 = (FStar_Syntax_Syntax.null_binder k)
in (_131_160, env))
end
| (Some (a), k) -> begin
(
# 271 "FStar.Parser.ToSyntax.fst"
let _52_418 = (FStar_Parser_Env.push_bv env a)
in (match (_52_418) with
| (env, a) -> begin
(((
# 272 "FStar.Parser.ToSyntax.fst"
let _52_419 = a
in {FStar_Syntax_Syntax.ppname = _52_419.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_419.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}), (trans_aqual imp)), env)
end))
end))

# 274 "FStar.Parser.ToSyntax.fst"
type env_t =
FStar_Parser_Env.env

# 275 "FStar.Parser.ToSyntax.fst"
type lenv_t =
FStar_Syntax_Syntax.bv Prims.list

# 277 "FStar.Parser.ToSyntax.fst"
let mk_lb : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.letbinding = (fun _52_424 -> (match (_52_424) with
| (n, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))

# 278 "FStar.Parser.ToSyntax.fst"
let no_annot_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t None))

# 280 "FStar.Parser.ToSyntax.fst"
let rec desugar_data_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat) = (fun env p -> (
# 281 "FStar.Parser.ToSyntax.fst"
let check_linear_pattern_variables = (fun p -> (
# 282 "FStar.Parser.ToSyntax.fst"
let rec pat_vars = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_dot_term (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_constant (_)) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (_52_445, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out _52_453 -> (match (_52_453) with
| (p, _52_452) -> begin
(let _131_206 = (pat_vars p)
in (FStar_Util.set_union out _131_206))
end)) FStar_Syntax_Syntax.no_names))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj (hd::tl) -> begin
(
# 291 "FStar.Parser.ToSyntax.fst"
let xs = (pat_vars hd)
in if (not ((FStar_Util.for_all (fun p -> (
# 292 "FStar.Parser.ToSyntax.fst"
let ys = (pat_vars p)
in ((FStar_Util.set_is_subset_of xs ys) && (FStar_Util.set_is_subset_of ys xs)))) tl))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Disjunctive pattern binds different variables in each case", p.FStar_Syntax_Syntax.p))))
end else begin
xs
end)
end))
in (pat_vars p)))
in (
# 299 "FStar.Parser.ToSyntax.fst"
let resolvex = (fun l e x -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText))))) with
| Some (y) -> begin
(l, e, y)
end
| _52_471 -> begin
(
# 303 "FStar.Parser.ToSyntax.fst"
let _52_474 = (FStar_Parser_Env.push_bv e x)
in (match (_52_474) with
| (e, x) -> begin
((x)::l, e, x)
end))
end))
in (
# 305 "FStar.Parser.ToSyntax.fst"
let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun b -> (b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText))))) with
| Some (b) -> begin
(l, e, b)
end
| _52_483 -> begin
(
# 309 "FStar.Parser.ToSyntax.fst"
let _52_486 = (FStar_Parser_Env.push_bv e a)
in (match (_52_486) with
| (e, a) -> begin
((a)::l, e, a)
end))
end))
in (
# 311 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun loc env p -> (
# 312 "FStar.Parser.ToSyntax.fst"
let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Parser_AST.prange))
in (
# 313 "FStar.Parser.ToSyntax.fst"
let pos_r = (fun r q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r))
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.PatOr (p::ps) -> begin
(
# 317 "FStar.Parser.ToSyntax.fst"
let _52_508 = (aux loc env p)
in (match (_52_508) with
| (loc, env, var, p, _52_507) -> begin
(
# 318 "FStar.Parser.ToSyntax.fst"
let _52_525 = (FStar_List.fold_left (fun _52_512 p -> (match (_52_512) with
| (loc, env, ps) -> begin
(
# 319 "FStar.Parser.ToSyntax.fst"
let _52_521 = (aux loc env p)
in (match (_52_521) with
| (loc, env, _52_517, p, _52_520) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_52_525) with
| (loc, env, ps) -> begin
(
# 321 "FStar.Parser.ToSyntax.fst"
let pat = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in (loc, env, var, pat, false))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 325 "FStar.Parser.ToSyntax.fst"
let _52_536 = (aux loc env p)
in (match (_52_536) with
| (loc, env', binder, p, imp) -> begin
(
# 326 "FStar.Parser.ToSyntax.fst"
let binder = (match (binder) with
| LetBinder (_52_538) -> begin
(FStar_All.failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(
# 329 "FStar.Parser.ToSyntax.fst"
let t = (let _131_236 = (close_fun env t)
in (desugar_term env _131_236))
in LocalBinder (((
# 330 "FStar.Parser.ToSyntax.fst"
let _52_545 = x
in {FStar_Syntax_Syntax.ppname = _52_545.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_545.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), aq)))
end)
in (loc, env', binder, p, imp))
end))
end
| FStar_Parser_AST.PatWild -> begin
(
# 334 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _131_237 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in (loc, env, LocalBinder ((x, None)), _131_237, false)))
end
| FStar_Parser_AST.PatConst (c) -> begin
(
# 338 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _131_238 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in (loc, env, LocalBinder ((x, None)), _131_238, false)))
end
| (FStar_Parser_AST.PatTvar (x, imp)) | (FStar_Parser_AST.PatVar (x, imp)) -> begin
(
# 343 "FStar.Parser.ToSyntax.fst"
let aq = if imp then begin
Some (FStar_Syntax_Syntax.imp_tag)
end else begin
None
end
in (
# 344 "FStar.Parser.ToSyntax.fst"
let _52_563 = (resolvex loc env x)
in (match (_52_563) with
| (loc, env, xbv) -> begin
(let _131_239 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in (loc, env, LocalBinder ((xbv, aq)), _131_239, imp))
end)))
end
| FStar_Parser_AST.PatName (l) -> begin
(
# 348 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_datacon env) l)
in (
# 349 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _131_240 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, []))))
in (loc, env, LocalBinder ((x, None)), _131_240, false))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _52_569}, args) -> begin
(
# 353 "FStar.Parser.ToSyntax.fst"
let _52_591 = (FStar_List.fold_right (fun arg _52_580 -> (match (_52_580) with
| (loc, env, args) -> begin
(
# 354 "FStar.Parser.ToSyntax.fst"
let _52_587 = (aux loc env arg)
in (match (_52_587) with
| (loc, env, _52_584, arg, imp) -> begin
(loc, env, ((arg, imp))::args)
end))
end)) args (loc, env, []))
in (match (_52_591) with
| (loc, env, args) -> begin
(
# 356 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_datacon env) l)
in (
# 357 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _131_243 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _131_243, false))))
end))
end
| FStar_Parser_AST.PatApp (_52_595) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(
# 363 "FStar.Parser.ToSyntax.fst"
let _52_615 = (FStar_List.fold_right (fun pat _52_603 -> (match (_52_603) with
| (loc, env, pats) -> begin
(
# 364 "FStar.Parser.ToSyntax.fst"
let _52_611 = (aux loc env pat)
in (match (_52_611) with
| (loc, env, _52_607, pat, _52_610) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_52_615) with
| (loc, env, pats) -> begin
(
# 366 "FStar.Parser.ToSyntax.fst"
let pat = (let _131_256 = (let _131_255 = (let _131_251 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _131_251))
in (let _131_254 = (let _131_253 = (let _131_252 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_131_252, []))
in FStar_Syntax_Syntax.Pat_cons (_131_253))
in (FStar_All.pipe_left _131_255 _131_254)))
in (FStar_List.fold_right (fun hd tl -> (
# 367 "FStar.Parser.ToSyntax.fst"
let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (let _131_250 = (let _131_249 = (let _131_248 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_131_248, ((hd, false))::((tl, false))::[]))
in FStar_Syntax_Syntax.Pat_cons (_131_249))
in (FStar_All.pipe_left (pos_r r) _131_250)))) pats _131_256))
in (
# 370 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (loc, env, LocalBinder ((x, None)), pat, false)))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(
# 374 "FStar.Parser.ToSyntax.fst"
let _52_641 = (FStar_List.fold_left (fun _52_628 p -> (match (_52_628) with
| (loc, env, pats) -> begin
(
# 375 "FStar.Parser.ToSyntax.fst"
let _52_637 = (aux loc env p)
in (match (_52_637) with
| (loc, env, _52_633, pat, _52_636) -> begin
(loc, env, ((pat, false))::pats)
end))
end)) (loc, env, []) args)
in (match (_52_641) with
| (loc, env, args) -> begin
(
# 377 "FStar.Parser.ToSyntax.fst"
let args = (FStar_List.rev args)
in (
# 378 "FStar.Parser.ToSyntax.fst"
let l = if dep then begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end else begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end
in (
# 380 "FStar.Parser.ToSyntax.fst"
let constr = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (
# 381 "FStar.Parser.ToSyntax.fst"
let l = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| _52_648 -> begin
(FStar_All.failwith "impossible")
end)
in (
# 384 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _131_259 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _131_259, false)))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(
# 391 "FStar.Parser.ToSyntax.fst"
let _52_658 = (FStar_List.hd fields)
in (match (_52_658) with
| (f, _52_657) -> begin
(
# 392 "FStar.Parser.ToSyntax.fst"
let _52_662 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_52_662) with
| (record, _52_661) -> begin
(
# 393 "FStar.Parser.ToSyntax.fst"
let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _52_665 -> (match (_52_665) with
| (f, p) -> begin
(let _131_261 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.qualify_field_to_record env record) f)
in (_131_261, p))
end))))
in (
# 395 "FStar.Parser.ToSyntax.fst"
let args = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _52_670 -> (match (_52_670) with
| (f, _52_669) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _52_674 -> (match (_52_674) with
| (g, _52_673) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_52_677, p) -> begin
p
end)
end))))
in (
# 399 "FStar.Parser.ToSyntax.fst"
let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_Env.constrname)) p.FStar_Parser_AST.prange), args))) p.FStar_Parser_AST.prange)
in (
# 400 "FStar.Parser.ToSyntax.fst"
let _52_689 = (aux loc env app)
in (match (_52_689) with
| (env, e, b, p, _52_688) -> begin
(
# 401 "FStar.Parser.ToSyntax.fst"
let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons ((fv, _52_692), args) -> begin
(let _131_270 = (let _131_269 = (let _131_268 = (let _131_267 = (let _131_266 = (let _131_265 = (let _131_264 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _131_264))
in FStar_Syntax_Syntax.Record_ctor (_131_265))
in Some (_131_266))
in (fv, _131_267))
in (_131_268, args))
in FStar_Syntax_Syntax.Pat_cons (_131_269))
in (FStar_All.pipe_left pos _131_270))
end
| _52_698 -> begin
p
end)
in (env, e, b, p, false))
end)))))
end))
end))
end))))
in (
# 406 "FStar.Parser.ToSyntax.fst"
let _52_707 = (aux [] env p)
in (match (_52_707) with
| (_52_701, env, b, p, _52_706) -> begin
(
# 407 "FStar.Parser.ToSyntax.fst"
let _52_708 = (let _131_271 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore _131_271))
in (env, b, p))
end)))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _52_715) -> begin
(let _131_277 = (let _131_276 = (let _131_275 = (FStar_Parser_Env.qualify env x)
in (_131_275, FStar_Syntax_Syntax.tun))
in LetBinder (_131_276))
in (env, _131_277, None))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _52_722); FStar_Parser_AST.prange = _52_719}, t) -> begin
(let _131_281 = (let _131_280 = (let _131_279 = (FStar_Parser_Env.qualify env x)
in (let _131_278 = (desugar_term env t)
in (_131_279, _131_278)))
in LetBinder (_131_280))
in (env, _131_281, None))
end
| _52_730 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern at the top-level", p.FStar_Parser_AST.prange))))
end)
end else begin
(
# 418 "FStar.Parser.ToSyntax.fst"
let _52_734 = (desugar_data_pat env p)
in (match (_52_734) with
| (env, binder, p) -> begin
(
# 419 "FStar.Parser.ToSyntax.fst"
let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| _52_742 -> begin
Some (p)
end)
in (env, binder, p))
end))
end)
and desugar_binding_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun _52_746 env pat -> (
# 428 "FStar.Parser.ToSyntax.fst"
let _52_754 = (desugar_data_pat env pat)
in (match (_52_754) with
| (env, _52_752, pat) -> begin
(env, pat)
end)))
and desugar_match_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (
# 434 "FStar.Parser.ToSyntax.fst"
let env = (
# 434 "FStar.Parser.ToSyntax.fst"
let _52_759 = env
in {FStar_Parser_Env.curmodule = _52_759.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _52_759.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _52_759.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.sigaccum = _52_759.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _52_759.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _52_759.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _52_759.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _52_759.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _52_759.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _52_759.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (
# 438 "FStar.Parser.ToSyntax.fst"
let env = (
# 438 "FStar.Parser.ToSyntax.fst"
let _52_764 = env
in {FStar_Parser_Env.curmodule = _52_764.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _52_764.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _52_764.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.sigaccum = _52_764.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _52_764.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _52_764.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _52_764.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _52_764.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _52_764.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _52_764.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (
# 442 "FStar.Parser.ToSyntax.fst"
let mk = (fun e -> (FStar_Syntax_Syntax.mk e None top.FStar_Parser_AST.range))
in (
# 443 "FStar.Parser.ToSyntax.fst"
let setpos = (fun e -> (
# 443 "FStar.Parser.ToSyntax.fst"
let _52_774 = e
in {FStar_Syntax_Syntax.n = _52_774.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _52_774.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _52_774.FStar_Syntax_Syntax.vars}))
in (match ((let _131_300 = (unparen top)
in _131_300.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (_52_778) -> begin
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
| FStar_Parser_AST.Op ("*", _52_798::_52_796::[]) when env.FStar_Parser_Env.expect_typ -> begin
(
# 461 "FStar.Parser.ToSyntax.fst"
let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", t1::t2::[]) -> begin
(
# 463 "FStar.Parser.ToSyntax.fst"
let rest = (flatten t2)
in (t1)::rest)
end
| _52_812 -> begin
(t)::[]
end))
in (
# 466 "FStar.Parser.ToSyntax.fst"
let targs = (let _131_306 = (let _131_303 = (unparen top)
in (flatten _131_303))
in (FStar_All.pipe_right _131_306 (FStar_List.map (fun t -> (let _131_305 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg _131_305))))))
in (
# 467 "FStar.Parser.ToSyntax.fst"
let tup = (let _131_307 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) _131_307))
in (mk (FStar_Syntax_Syntax.Tm_app ((tup, targs)))))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _131_308 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) a)
in (FStar_All.pipe_left setpos _131_308))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_lid env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Unexpected operator: " s), top.FStar_Parser_AST.range))))
end
| Some (l) -> begin
(
# 477 "FStar.Parser.ToSyntax.fst"
let op = (FStar_Syntax_Syntax.fvar None l (FStar_Ident.range_of_lid l))
in (
# 478 "FStar.Parser.ToSyntax.fst"
let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _131_310 = (desugar_term env t)
in (_131_310, None)))))
in (mk (FStar_Syntax_Syntax.Tm_app ((op, args))))))
end)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _52_834; FStar_Ident.ident = _52_832; FStar_Ident.nsstr = _52_830; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _52_843; FStar_Ident.ident = _52_841; FStar_Ident.nsstr = _52_839; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _52_852; FStar_Ident.ident = _52_850; FStar_Ident.nsstr = _52_848; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(let _131_311 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (FStar_All.pipe_left setpos _131_311))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(
# 491 "FStar.Parser.ToSyntax.fst"
let _52_867 = (match ((FStar_Parser_Env.try_lookup_datacon env l)) with
| None -> begin
(let _131_312 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (_131_312, false))
end
| Some (head) -> begin
(let _131_313 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in (_131_313, true))
end)
in (match (_52_867) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| _52_870 -> begin
(
# 497 "FStar.Parser.ToSyntax.fst"
let args = (FStar_List.map (fun _52_873 -> (match (_52_873) with
| (t, imp) -> begin
(
# 498 "FStar.Parser.ToSyntax.fst"
let te = (desugar_term env t)
in (arg_withimp_e imp te))
end)) args)
in (
# 500 "FStar.Parser.ToSyntax.fst"
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
# 507 "FStar.Parser.ToSyntax.fst"
let _52_901 = (FStar_List.fold_left (fun _52_884 b -> (match (_52_884) with
| (env, tparams, typs) -> begin
(
# 508 "FStar.Parser.ToSyntax.fst"
let _52_888 = (desugar_binder env b)
in (match (_52_888) with
| (xopt, t) -> begin
(
# 509 "FStar.Parser.ToSyntax.fst"
let _52_894 = (match (xopt) with
| None -> begin
(let _131_317 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (env, _131_317))
end
| Some (x) -> begin
(FStar_Parser_Env.push_bv env x)
end)
in (match (_52_894) with
| (env, x) -> begin
(let _131_321 = (let _131_320 = (let _131_319 = (let _131_318 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _131_318))
in (_131_319)::[])
in (FStar_List.append typs _131_320))
in (env, (FStar_List.append tparams ((((
# 513 "FStar.Parser.ToSyntax.fst"
let _52_895 = x
in {FStar_Syntax_Syntax.ppname = _52_895.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_895.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), None))::[])), _131_321))
end))
end))
end)) (env, [], []) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_52_901) with
| (env, _52_899, targs) -> begin
(
# 516 "FStar.Parser.ToSyntax.fst"
let tup = (let _131_322 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) _131_322))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app ((tup, targs)))))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(
# 520 "FStar.Parser.ToSyntax.fst"
let _52_909 = (uncurry binders t)
in (match (_52_909) with
| (bs, t) -> begin
(
# 521 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun env bs _52_8 -> (match (_52_8) with
| [] -> begin
(
# 523 "FStar.Parser.ToSyntax.fst"
let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (let _131_329 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos _131_329)))
end
| hd::tl -> begin
(
# 527 "FStar.Parser.ToSyntax.fst"
let mlenv = (FStar_Parser_Env.default_ml env)
in (
# 528 "FStar.Parser.ToSyntax.fst"
let bb = (desugar_binder mlenv hd)
in (
# 529 "FStar.Parser.ToSyntax.fst"
let _52_923 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_52_923) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_binder env b)) with
| (None, _52_930) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(
# 538 "FStar.Parser.ToSyntax.fst"
let _52_938 = (as_binder env None b)
in (match (_52_938) with
| ((x, _52_935), env) -> begin
(
# 539 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env f)
in (let _131_330 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos _131_330)))
end))
end)
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(
# 544 "FStar.Parser.ToSyntax.fst"
let _52_958 = (FStar_List.fold_left (fun _52_946 pat -> (match (_52_946) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (_52_949, t) -> begin
(let _131_334 = (let _131_333 = (free_type_vars env t)
in (FStar_List.append _131_333 ftvs))
in (env, _131_334))
end
| _52_954 -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_52_958) with
| (_52_956, ftv) -> begin
(
# 548 "FStar.Parser.ToSyntax.fst"
let ftv = (sort_ftv ftv)
in (
# 549 "FStar.Parser.ToSyntax.fst"
let binders = (let _131_336 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar ((a, true))) top.FStar_Parser_AST.range))))
in (FStar_List.append _131_336 binders))
in (
# 558 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun env bs sc_pat_opt _52_9 -> (match (_52_9) with
| [] -> begin
(
# 560 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env body)
in (
# 561 "FStar.Parser.ToSyntax.fst"
let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(
# 563 "FStar.Parser.ToSyntax.fst"
let body = (let _131_346 = (let _131_345 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right _131_345 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close _131_346 body))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((sc, ((pat, None, body))::[]))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (let _131_347 = (no_annot_abs (FStar_List.rev bs) body)
in (setpos _131_347))))
end
| p::rest -> begin
(
# 569 "FStar.Parser.ToSyntax.fst"
let _52_982 = (desugar_binding_pat env p)
in (match (_52_982) with
| (env, b, pat) -> begin
(
# 570 "FStar.Parser.ToSyntax.fst"
let _52_1033 = (match (b) with
| LetBinder (_52_984) -> begin
(FStar_All.failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(
# 573 "FStar.Parser.ToSyntax.fst"
let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _52_992) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _131_349 = (let _131_348 = (FStar_Syntax_Syntax.bv_to_name x)
in (_131_348, p))
in Some (_131_349))
end
| (Some (p), Some (sc, p')) -> begin
(match ((sc.FStar_Syntax_Syntax.n, p'.FStar_Syntax_Syntax.v)) with
| (FStar_Syntax_Syntax.Tm_name (_52_1006), _52_1009) -> begin
(
# 579 "FStar.Parser.ToSyntax.fst"
let tup2 = (let _131_350 = (FStar_Syntax_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _131_350 (Some (FStar_Syntax_Syntax.Data_ctor))))
in (
# 580 "FStar.Parser.ToSyntax.fst"
let sc = (let _131_358 = (let _131_357 = (let _131_356 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (let _131_355 = (let _131_354 = (FStar_Syntax_Syntax.as_arg sc)
in (let _131_353 = (let _131_352 = (let _131_351 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _131_351))
in (_131_352)::[])
in (_131_354)::_131_353))
in (_131_356, _131_355)))
in FStar_Syntax_Syntax.Tm_app (_131_357))
in (FStar_Syntax_Syntax.mk _131_358 None top.FStar_Parser_AST.range))
in (
# 581 "FStar.Parser.ToSyntax.fst"
let p = (let _131_359 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tup2, ((p', false))::((p, false))::[]))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _131_359))
in Some ((sc, p)))))
end
| (FStar_Syntax_Syntax.Tm_app (_52_1015, args), FStar_Syntax_Syntax.Pat_cons (_52_1020, pats)) -> begin
(
# 584 "FStar.Parser.ToSyntax.fst"
let tupn = (let _131_360 = (FStar_Syntax_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _131_360 (Some (FStar_Syntax_Syntax.Data_ctor))))
in (
# 585 "FStar.Parser.ToSyntax.fst"
let sc = (let _131_367 = (let _131_366 = (let _131_365 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (let _131_364 = (let _131_363 = (let _131_362 = (let _131_361 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _131_361))
in (_131_362)::[])
in (FStar_List.append args _131_363))
in (_131_365, _131_364)))
in FStar_Syntax_Syntax.Tm_app (_131_366))
in (mk _131_367))
in (
# 586 "FStar.Parser.ToSyntax.fst"
let p = (let _131_368 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tupn, (FStar_List.append pats (((p, false))::[]))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _131_368))
in Some ((sc, p)))))
end
| _52_1029 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((x, aq), sc_pat_opt))
end)
in (match (_52_1033) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _52_1037; FStar_Parser_AST.level = _52_1035}, phi, _52_1043) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(
# 597 "FStar.Parser.ToSyntax.fst"
let phi = (desugar_formula env phi)
in (let _131_376 = (let _131_375 = (let _131_374 = (FStar_Syntax_Syntax.fvar None a (FStar_Ident.range_of_lid a))
in (let _131_373 = (let _131_372 = (FStar_Syntax_Syntax.as_arg phi)
in (let _131_371 = (let _131_370 = (let _131_369 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _131_369))
in (_131_370)::[])
in (_131_372)::_131_371))
in (_131_374, _131_373)))
in FStar_Syntax_Syntax.Tm_app (_131_375))
in (mk _131_376)))
end
| FStar_Parser_AST.App (_52_1048) -> begin
(
# 603 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun args e -> (match ((let _131_381 = (unparen e)
in _131_381.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(
# 605 "FStar.Parser.ToSyntax.fst"
let arg = (let _131_382 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _131_382))
in (aux ((arg)::args) e))
end
| _52_1060 -> begin
(
# 608 "FStar.Parser.ToSyntax.fst"
let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app ((head, args)))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _131_385 = (let _131_384 = (let _131_383 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range), t1))::[], t2))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in (_131_383, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))
in FStar_Syntax_Syntax.Tm_meta (_131_384))
in (mk _131_385))
end
| FStar_Parser_AST.Let (is_rec, (pat, _snd)::_tl, body) -> begin
(
# 617 "FStar.Parser.ToSyntax.fst"
let ds_let_rec = (fun _52_1076 -> (match (()) with
| () -> begin
(
# 618 "FStar.Parser.ToSyntax.fst"
let bindings = ((pat, _snd))::_tl
in (
# 619 "FStar.Parser.ToSyntax.fst"
let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _52_1080 -> (match (_52_1080) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _131_389 = (destruct_app_pattern env top_level p)
in (_131_389, def))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _131_390 = (destruct_app_pattern env top_level p)
in (_131_390, def))
end
| _52_1086 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _52_1091); FStar_Parser_AST.prange = _52_1088}, t) -> begin
if top_level then begin
(let _131_393 = (let _131_392 = (let _131_391 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_131_391))
in (_131_392, [], Some (t)))
in (_131_393, def))
end else begin
((FStar_Util.Inl (id), [], Some (t)), def)
end
end
| FStar_Parser_AST.PatVar (id, _52_1100) -> begin
if top_level then begin
(let _131_396 = (let _131_395 = (let _131_394 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_131_394))
in (_131_395, [], None))
in (_131_396, def))
end else begin
((FStar_Util.Inl (id), [], None), def)
end
end
| _52_1104 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected let binding", p.FStar_Parser_AST.prange))))
end)
end)
end
end))))
in (
# 636 "FStar.Parser.ToSyntax.fst"
let _52_1133 = (FStar_List.fold_left (fun _52_1109 _52_1118 -> (match ((_52_1109, _52_1118)) with
| ((env, fnames, rec_bindings), ((f, _52_1112, _52_1114), _52_1117)) -> begin
(
# 638 "FStar.Parser.ToSyntax.fst"
let _52_1129 = (match (f) with
| FStar_Util.Inl (x) -> begin
(
# 640 "FStar.Parser.ToSyntax.fst"
let _52_1123 = (FStar_Parser_Env.push_bv env x)
in (match (_52_1123) with
| (env, xx) -> begin
(let _131_400 = (let _131_399 = (FStar_Syntax_Syntax.mk_binder xx)
in (_131_399)::rec_bindings)
in (env, FStar_Util.Inl (xx), _131_400))
end))
end
| FStar_Util.Inr (l) -> begin
(let _131_401 = (FStar_Parser_Env.push_top_level_rec_binding env l.FStar_Ident.ident)
in (_131_401, FStar_Util.Inr (l), rec_bindings))
end)
in (match (_52_1129) with
| (env, lbname, rec_bindings) -> begin
(env, (lbname)::fnames, rec_bindings)
end))
end)) (env, [], []) funs)
in (match (_52_1133) with
| (env', fnames, rec_bindings) -> begin
(
# 646 "FStar.Parser.ToSyntax.fst"
let fnames = (FStar_List.rev fnames)
in (
# 648 "FStar.Parser.ToSyntax.fst"
let desugar_one_def = (fun env lbname _52_1144 -> (match (_52_1144) with
| ((_52_1139, args, result_t), def) -> begin
(
# 649 "FStar.Parser.ToSyntax.fst"
let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _131_408 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed ((def, t))) _131_408 FStar_Parser_AST.Expr))
end)
in (
# 652 "FStar.Parser.ToSyntax.fst"
let def = (match (args) with
| [] -> begin
def
end
| _52_1151 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.un_curry_abs args def) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
end)
in (
# 655 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env def)
in (
# 656 "FStar.Parser.ToSyntax.fst"
let body = if is_rec then begin
(FStar_Syntax_Subst.close rec_bindings body)
end else begin
body
end
in (mk_lb (lbname, FStar_Syntax_Syntax.tun, body))))))
end))
in (
# 658 "FStar.Parser.ToSyntax.fst"
let lbs = (FStar_List.map2 (desugar_one_def (if is_rec then begin
env'
end else begin
env
end)) fnames funs)
in (
# 659 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env' body)
in (let _131_411 = (let _131_410 = (let _131_409 = (FStar_Syntax_Subst.close rec_bindings body)
in ((is_rec, lbs), _131_409))
in FStar_Syntax_Syntax.Tm_let (_131_410))
in (FStar_All.pipe_left mk _131_411))))))
end))))
end))
in (
# 662 "FStar.Parser.ToSyntax.fst"
let ds_non_rec = (fun pat t1 t2 -> (
# 663 "FStar.Parser.ToSyntax.fst"
let t1 = (desugar_term env t1)
in (
# 664 "FStar.Parser.ToSyntax.fst"
let _52_1165 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_52_1165) with
| (env, binder, pat) -> begin
(match (binder) with
| LetBinder (l, t) -> begin
(
# 667 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env t2)
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (l); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]), body)))))
end
| LocalBinder (x, _52_1173) -> begin
(
# 671 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env t2)
in (
# 672 "FStar.Parser.ToSyntax.fst"
let body = (match (pat) with
| (None) | (Some ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (_); FStar_Syntax_Syntax.ty = _; FStar_Syntax_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _131_422 = (let _131_421 = (let _131_420 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _131_419 = (let _131_418 = (FStar_Syntax_Util.branch (pat, None, body))
in (_131_418)::[])
in (_131_420, _131_419)))
in FStar_Syntax_Syntax.Tm_match (_131_421))
in (FStar_Syntax_Syntax.mk _131_422 None body.FStar_Syntax_Syntax.pos))
end)
in (let _131_427 = (let _131_426 = (let _131_425 = (let _131_424 = (let _131_423 = (FStar_Syntax_Syntax.mk_binder x)
in (_131_423)::[])
in (FStar_Syntax_Subst.close _131_424 body))
in ((false, ((mk_lb (FStar_Util.Inl (x), x.FStar_Syntax_Syntax.sort, t1)))::[]), _131_425))
in FStar_Syntax_Syntax.Tm_let (_131_426))
in (FStar_All.pipe_left mk _131_427))))
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
# 686 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (let _131_438 = (let _131_437 = (let _131_436 = (desugar_term env t1)
in (let _131_435 = (let _131_434 = (let _131_429 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (let _131_428 = (desugar_term env t2)
in (_131_429, None, _131_428)))
in (let _131_433 = (let _131_432 = (let _131_431 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (let _131_430 = (desugar_term env t3)
in (_131_431, None, _131_430)))
in (_131_432)::[])
in (_131_434)::_131_433))
in (_131_436, _131_435)))
in FStar_Syntax_Syntax.Tm_match (_131_437))
in (mk _131_438)))
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(
# 692 "FStar.Parser.ToSyntax.fst"
let r = top.FStar_Parser_AST.range
in (
# 693 "FStar.Parser.ToSyntax.fst"
let handler = (FStar_Parser_AST.mk_function branches r r)
in (
# 694 "FStar.Parser.ToSyntax.fst"
let body = (FStar_Parser_AST.mk_function ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatConst (FStar_Const.Const_unit)) r), None, e))::[]) r r)
in (
# 695 "FStar.Parser.ToSyntax.fst"
let a1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (FStar_Syntax_Const.try_with_lid)) r top.FStar_Parser_AST.level), body, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (
# 696 "FStar.Parser.ToSyntax.fst"
let a2 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((a1, handler, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (desugar_term env a2))))))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(
# 700 "FStar.Parser.ToSyntax.fst"
let desugar_branch = (fun _52_1213 -> (match (_52_1213) with
| (pat, wopt, b) -> begin
(
# 701 "FStar.Parser.ToSyntax.fst"
let _52_1216 = (desugar_match_pat env pat)
in (match (_52_1216) with
| (env, pat) -> begin
(
# 702 "FStar.Parser.ToSyntax.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _131_441 = (desugar_term env e)
in Some (_131_441))
end)
in (
# 705 "FStar.Parser.ToSyntax.fst"
let b = (desugar_term env b)
in (FStar_Syntax_Util.branch (pat, wopt, b))))
end))
end))
in (let _131_445 = (let _131_444 = (let _131_443 = (desugar_term env e)
in (let _131_442 = (FStar_List.map desugar_branch branches)
in (_131_443, _131_442)))
in FStar_Syntax_Syntax.Tm_match (_131_444))
in (FStar_All.pipe_left mk _131_445)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _131_449 = (let _131_448 = (let _131_447 = (desugar_term env e)
in (let _131_446 = (desugar_typ env t)
in (_131_447, _131_446, None)))
in FStar_Syntax_Syntax.Tm_ascribed (_131_448))
in (FStar_All.pipe_left mk _131_449))
end
| FStar_Parser_AST.Record (_52_1227, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected empty record", top.FStar_Parser_AST.range))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(
# 716 "FStar.Parser.ToSyntax.fst"
let _52_1238 = (FStar_List.hd fields)
in (match (_52_1238) with
| (f, _52_1237) -> begin
(
# 717 "FStar.Parser.ToSyntax.fst"
let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (
# 718 "FStar.Parser.ToSyntax.fst"
let _52_1244 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_52_1244) with
| (record, _52_1243) -> begin
(
# 719 "FStar.Parser.ToSyntax.fst"
let get_field = (fun xopt f -> (
# 720 "FStar.Parser.ToSyntax.fst"
let fn = f.FStar_Ident.ident
in (
# 721 "FStar.Parser.ToSyntax.fst"
let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _52_1252 -> (match (_52_1252) with
| (g, _52_1251) -> begin
(
# 722 "FStar.Parser.ToSyntax.fst"
let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_52_1256, e) -> begin
(let _131_457 = (qfn fn)
in (_131_457, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _131_460 = (let _131_459 = (let _131_458 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in (_131_458, top.FStar_Parser_AST.range))
in FStar_Syntax_Syntax.Error (_131_459))
in (Prims.raise _131_460))
end
| Some (x) -> begin
(let _131_461 = (qfn fn)
in (_131_461, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Project ((x, f))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end))))
in (
# 733 "FStar.Parser.ToSyntax.fst"
let recterm = (match (eopt) with
| None -> begin
(let _131_466 = (let _131_465 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _52_1268 -> (match (_52_1268) with
| (f, _52_1267) -> begin
(let _131_464 = (let _131_463 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _131_463))
in (_131_464, FStar_Parser_AST.Nothing))
end))))
in (record.FStar_Parser_Env.constrname, _131_465))
in FStar_Parser_AST.Construct (_131_466))
end
| Some (e) -> begin
(
# 740 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (
# 741 "FStar.Parser.ToSyntax.fst"
let xterm = (let _131_468 = (let _131_467 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_131_467))
in (FStar_Parser_AST.mk_term _131_468 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (
# 742 "FStar.Parser.ToSyntax.fst"
let record = (let _131_471 = (let _131_470 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _52_1276 -> (match (_52_1276) with
| (f, _52_1275) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _131_470))
in FStar_Parser_AST.Record (_131_471))
in FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar ((x, false))) x.FStar_Ident.idRange), e))::[], (FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level))))))
end)
in (
# 745 "FStar.Parser.ToSyntax.fst"
let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (
# 746 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _52_1295); FStar_Syntax_Syntax.tk = _52_1292; FStar_Syntax_Syntax.pos = _52_1290; FStar_Syntax_Syntax.vars = _52_1288}, args); FStar_Syntax_Syntax.tk = _52_1286; FStar_Syntax_Syntax.pos = _52_1284; FStar_Syntax_Syntax.vars = _52_1282}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(
# 749 "FStar.Parser.ToSyntax.fst"
let e = (let _131_478 = (let _131_477 = (let _131_476 = (let _131_475 = (let _131_474 = (let _131_473 = (let _131_472 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _131_472))
in FStar_Syntax_Syntax.Record_ctor (_131_473))
in Some (_131_474))
in (FStar_Syntax_Syntax.fvar _131_475 fv.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos))
in (_131_476, args))
in FStar_Syntax_Syntax.Tm_app (_131_477))
in (FStar_All.pipe_left mk _131_478))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end
| _52_1309 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(
# 757 "FStar.Parser.ToSyntax.fst"
let _52_1316 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_projector_by_field_name env) f)
in (match (_52_1316) with
| (fieldname, is_rec) -> begin
(
# 758 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env e)
in (
# 759 "FStar.Parser.ToSyntax.fst"
let fn = (
# 760 "FStar.Parser.ToSyntax.fst"
let _52_1321 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_52_1321) with
| (ns, _52_1320) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (
# 762 "FStar.Parser.ToSyntax.fst"
let qual = if is_rec then begin
Some (FStar_Syntax_Syntax.Record_projector (fn))
end else begin
None
end
in (let _131_483 = (let _131_482 = (let _131_481 = (FStar_Syntax_Syntax.fvar (Some (FStar_Syntax_Syntax.Record_projector (fn))) fieldname (FStar_Ident.range_of_lid f))
in (let _131_480 = (let _131_479 = (FStar_Syntax_Syntax.as_arg e)
in (_131_479)::[])
in (_131_481, _131_480)))
in FStar_Syntax_Syntax.Tm_app (_131_482))
in (FStar_All.pipe_left mk _131_483)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| _52_1331 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _52_1333 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_args : FStar_Parser_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun _52_1338 -> (match (_52_1338) with
| (a, imp) -> begin
(let _131_487 = (desugar_term env a)
in (arg_withimp_e imp _131_487))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r default_ok env t -> (
# 779 "FStar.Parser.ToSyntax.fst"
let fail = (fun msg -> (Prims.raise (FStar_Syntax_Syntax.Error ((msg, r)))))
in (
# 780 "FStar.Parser.ToSyntax.fst"
let is_requires = (fun _52_1350 -> (match (_52_1350) with
| (t, _52_1349) -> begin
(match ((let _131_495 = (unparen t)
in _131_495.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Requires (_52_1352) -> begin
true
end
| _52_1355 -> begin
false
end)
end))
in (
# 783 "FStar.Parser.ToSyntax.fst"
let is_ensures = (fun _52_1360 -> (match (_52_1360) with
| (t, _52_1359) -> begin
(match ((let _131_498 = (unparen t)
in _131_498.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ensures (_52_1362) -> begin
true
end
| _52_1365 -> begin
false
end)
end))
in (
# 786 "FStar.Parser.ToSyntax.fst"
let is_app = (fun head _52_1371 -> (match (_52_1371) with
| (t, _52_1370) -> begin
(match ((let _131_503 = (unparen t)
in _131_503.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _52_1375; FStar_Parser_AST.level = _52_1373}, _52_1380, _52_1382) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| _52_1386 -> begin
false
end)
end))
in (
# 789 "FStar.Parser.ToSyntax.fst"
let pre_process_comp_typ = (fun t -> (
# 790 "FStar.Parser.ToSyntax.fst"
let _52_1391 = (head_and_args t)
in (match (_52_1391) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(
# 793 "FStar.Parser.ToSyntax.fst"
let unit_tm = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (
# 794 "FStar.Parser.ToSyntax.fst"
let nil_pat = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr), FStar_Parser_AST.Nothing)
in (
# 795 "FStar.Parser.ToSyntax.fst"
let args = (match (args) with
| [] -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Not enough arguments to \'Lemma\'", t.FStar_Parser_AST.range))))
end
| ens::[] -> begin
(
# 798 "FStar.Parser.ToSyntax.fst"
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
# 803 "FStar.Parser.ToSyntax.fst"
let head = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_name env) lemma)
in (head, args)))))
end
| FStar_Parser_AST.Name (l) when (FStar_Parser_Env.is_effect_name env l) -> begin
(let _131_506 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_name env) l)
in (_131_506, args))
end
| FStar_Parser_AST.Name (l) when ((let _131_507 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _131_507 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(let _131_508 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in (_131_508, args))
end
| FStar_Parser_AST.Name (l) when ((let _131_509 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _131_509 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(let _131_510 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)
in (_131_510, args))
end
| FStar_Parser_AST.Name (l) when ((((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) && default_ok) -> begin
(let _131_511 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in (_131_511, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _52_1419 when default_ok -> begin
(let _131_512 = (FStar_Ident.set_lid_range env.FStar_Parser_Env.default_result_effect head.FStar_Parser_AST.range)
in (_131_512, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _52_1421 -> begin
(let _131_514 = (let _131_513 = (FStar_Parser_AST.term_to_string t)
in (FStar_Util.format1 "%s is not an effect" _131_513))
in (fail _131_514))
end)
end)))
in (
# 833 "FStar.Parser.ToSyntax.fst"
let _52_1424 = (pre_process_comp_typ t)
in (match (_52_1424) with
| (eff, args) -> begin
(
# 834 "FStar.Parser.ToSyntax.fst"
let _52_1425 = if ((FStar_List.length args) = 0) then begin
(let _131_516 = (let _131_515 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" _131_515))
in (fail _131_516))
end else begin
()
end
in (
# 836 "FStar.Parser.ToSyntax.fst"
let _52_1429 = (let _131_518 = (FStar_List.hd args)
in (let _131_517 = (FStar_List.tl args)
in (_131_518, _131_517)))
in (match (_52_1429) with
| (result_arg, rest) -> begin
(
# 837 "FStar.Parser.ToSyntax.fst"
let result_typ = (desugar_typ env (Prims.fst result_arg))
in (
# 838 "FStar.Parser.ToSyntax.fst"
let rest = (desugar_args env rest)
in (
# 839 "FStar.Parser.ToSyntax.fst"
let _52_1457 = (FStar_All.pipe_right rest (FStar_List.partition (fun _52_1435 -> (match (_52_1435) with
| (t, _52_1434) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv, _52_1444); FStar_Syntax_Syntax.tk = _52_1441; FStar_Syntax_Syntax.pos = _52_1439; FStar_Syntax_Syntax.vars = _52_1437}, _52_1449::[]) -> begin
(FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.decreases_lid)
end
| _52_1454 -> begin
false
end)
end))))
in (match (_52_1457) with
| (dec, rest) -> begin
(
# 845 "FStar.Parser.ToSyntax.fst"
let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _52_1461 -> (match (_52_1461) with
| (t, _52_1460) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_52_1463, (arg, _52_1466)::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| _52_1472 -> begin
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
# 853 "FStar.Parser.ToSyntax.fst"
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
# 859 "FStar.Parser.ToSyntax.fst"
let rest = if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid) then begin
(match (rest) with
| req::ens::(pat, aq)::[] -> begin
(
# 863 "FStar.Parser.ToSyntax.fst"
let pat = (match (pat.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _52_1483) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.nil_lid) -> begin
(
# 865 "FStar.Parser.ToSyntax.fst"
let nil = (FStar_Syntax_Syntax.mk_Tm_uinst pat ((FStar_Syntax_Syntax.U_succ (FStar_Syntax_Syntax.U_zero))::[]))
in (
# 866 "FStar.Parser.ToSyntax.fst"
let pattern = (let _131_521 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Tm_uinst _131_521 ((FStar_Syntax_Syntax.U_zero)::(FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app nil (((pattern, Some (FStar_Syntax_Syntax.imp_tag)))::[]) None pat.FStar_Syntax_Syntax.pos)))
end
| _52_1489 -> begin
pat
end)
in (let _131_525 = (let _131_524 = (let _131_523 = (let _131_522 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((pat, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)))) None pat.FStar_Syntax_Syntax.pos)
in (_131_522, aq))
in (_131_523)::[])
in (ens)::_131_524)
in (req)::_131_525))
end
| _52_1492 -> begin
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
# 879 "FStar.Parser.ToSyntax.fst"
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
| _52_1504 -> begin
None
end))
in (
# 886 "FStar.Parser.ToSyntax.fst"
let mk = (fun t -> (FStar_Syntax_Syntax.mk t None f.FStar_Parser_AST.range))
in (
# 887 "FStar.Parser.ToSyntax.fst"
let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (
# 888 "FStar.Parser.ToSyntax.fst"
let setpos = (fun t -> (
# 888 "FStar.Parser.ToSyntax.fst"
let _52_1511 = t
in {FStar_Syntax_Syntax.n = _52_1511.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _52_1511.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _52_1511.FStar_Syntax_Syntax.vars}))
in (
# 889 "FStar.Parser.ToSyntax.fst"
let desugar_quant = (fun q b pats body -> (
# 890 "FStar.Parser.ToSyntax.fst"
let tk = (desugar_binder env (
# 890 "FStar.Parser.ToSyntax.fst"
let _52_1518 = b
in {FStar_Parser_AST.b = _52_1518.FStar_Parser_AST.b; FStar_Parser_AST.brange = _52_1518.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _52_1518.FStar_Parser_AST.aqual}))
in (
# 891 "FStar.Parser.ToSyntax.fst"
let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _131_560 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _131_560)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(
# 894 "FStar.Parser.ToSyntax.fst"
let _52_1532 = (FStar_Parser_Env.push_bv env a)
in (match (_52_1532) with
| (env, a) -> begin
(
# 895 "FStar.Parser.ToSyntax.fst"
let a = (
# 895 "FStar.Parser.ToSyntax.fst"
let _52_1533 = a
in {FStar_Syntax_Syntax.ppname = _52_1533.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_1533.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (
# 896 "FStar.Parser.ToSyntax.fst"
let pats = (desugar_pats env pats)
in (
# 897 "FStar.Parser.ToSyntax.fst"
let body = (desugar_formula env body)
in (
# 898 "FStar.Parser.ToSyntax.fst"
let body = (match (pats) with
| [] -> begin
body
end
| _52_1540 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((body, FStar_Syntax_Syntax.Meta_pattern (pats)))))
end)
in (
# 901 "FStar.Parser.ToSyntax.fst"
let body = (let _131_563 = (let _131_562 = (let _131_561 = (FStar_Syntax_Syntax.mk_binder a)
in (_131_561)::[])
in (no_annot_abs _131_562 body))
in (FStar_All.pipe_left setpos _131_563))
in (let _131_569 = (let _131_568 = (let _131_567 = (let _131_564 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Syntax_Syntax.fvar None _131_564 b.FStar_Parser_AST.brange))
in (let _131_566 = (let _131_565 = (FStar_Syntax_Syntax.as_arg body)
in (_131_565)::[])
in (_131_567, _131_566)))
in FStar_Syntax_Syntax.Tm_app (_131_568))
in (FStar_All.pipe_left mk _131_569)))))))
end))
end
| _52_1544 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 906 "FStar.Parser.ToSyntax.fst"
let push_quant = (fun q binders pats body -> (match (binders) with
| b::b'::_rest -> begin
(
# 908 "FStar.Parser.ToSyntax.fst"
let rest = (b')::_rest
in (
# 909 "FStar.Parser.ToSyntax.fst"
let body = (let _131_584 = (q (rest, pats, body))
in (let _131_583 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _131_584 _131_583 FStar_Parser_AST.Formula)))
in (let _131_585 = (q ((b)::[], [], body))
in (FStar_Parser_AST.mk_term _131_585 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _52_1558 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _131_586 = (unparen f)
in _131_586.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(
# 915 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env f)
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((l, f.FStar_Syntax_Syntax.pos, p)))))))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall (_1::_2::_3, pats, body) -> begin
(
# 922 "FStar.Parser.ToSyntax.fst"
let binders = (_1)::(_2)::_3
in (let _131_588 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _131_588)))
end
| FStar_Parser_AST.QExists (_1::_2::_3, pats, body) -> begin
(
# 926 "FStar.Parser.ToSyntax.fst"
let binders = (_1)::(_2)::_3
in (let _131_590 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _131_590)))
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
| _52_1616 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (
# 941 "FStar.Parser.ToSyntax.fst"
let _52_1640 = (FStar_List.fold_left (fun _52_1621 b -> (match (_52_1621) with
| (env, out) -> begin
(
# 942 "FStar.Parser.ToSyntax.fst"
let tk = (desugar_binder env (
# 942 "FStar.Parser.ToSyntax.fst"
let _52_1623 = b
in {FStar_Parser_AST.b = _52_1623.FStar_Parser_AST.b; FStar_Parser_AST.brange = _52_1623.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _52_1623.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(
# 945 "FStar.Parser.ToSyntax.fst"
let _52_1632 = (FStar_Parser_Env.push_bv env a)
in (match (_52_1632) with
| (env, a) -> begin
(
# 946 "FStar.Parser.ToSyntax.fst"
let a = (
# 946 "FStar.Parser.ToSyntax.fst"
let _52_1633 = a
in {FStar_Syntax_Syntax.ppname = _52_1633.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_1633.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (env, ((a, (trans_aqual b.FStar_Parser_AST.aqual)))::out))
end))
end
| _52_1637 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected binder", b.FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_52_1640) with
| (env, tpars) -> begin
(env, (FStar_List.rev tpars))
end)))
and desugar_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(let _131_597 = (desugar_typ env t)
in (Some (x), _131_597))
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _131_598 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None x.FStar_Ident.idRange)
in (Some (x), _131_598))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _131_599 = (desugar_typ env t)
in (None, _131_599))
end
| FStar_Parser_AST.Variable (x) -> begin
(Some (x), FStar_Syntax_Syntax.tun)
end))

# 958 "FStar.Parser.ToSyntax.fst"
let mk_data_discriminators : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  FStar_Ident.lid  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun quals env t tps k datas -> (
# 959 "FStar.Parser.ToSyntax.fst"
let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_Env.iface) || env.FStar_Parser_Env.admitted_iface) then begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (
# 962 "FStar.Parser.ToSyntax.fst"
let binders = (let _131_615 = (let _131_614 = (FStar_Syntax_Util.arrow_formals k)
in (Prims.fst _131_614))
in (FStar_List.append tps _131_615))
in (
# 963 "FStar.Parser.ToSyntax.fst"
let p = (FStar_Ident.range_of_lid t)
in (
# 964 "FStar.Parser.ToSyntax.fst"
let _52_1667 = (FStar_Syntax_Util.args_of_binders binders)
in (match (_52_1667) with
| (binders, args) -> begin
(
# 965 "FStar.Parser.ToSyntax.fst"
let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _52_1671 -> (match (_52_1671) with
| (x, _52_1670) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
in (
# 966 "FStar.Parser.ToSyntax.fst"
let binders = (let _131_621 = (let _131_620 = (let _131_619 = (let _131_618 = (let _131_617 = (FStar_Syntax_Syntax.lid_as_fv t None)
in (FStar_Syntax_Syntax.fv_to_tm _131_617))
in (FStar_Syntax_Syntax.mk_Tm_app _131_618 args None p))
in (FStar_All.pipe_left FStar_Syntax_Syntax.null_binder _131_619))
in (_131_620)::[])
in (FStar_List.append imp_binders _131_621))
in (
# 967 "FStar.Parser.ToSyntax.fst"
let disc_type = (let _131_624 = (let _131_623 = (let _131_622 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid None)
in (FStar_Syntax_Syntax.fv_to_tm _131_622))
in (FStar_Syntax_Syntax.mk_Total _131_623))
in (FStar_Syntax_Util.arrow binders _131_624))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (
# 969 "FStar.Parser.ToSyntax.fst"
let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (let _131_627 = (let _131_626 = (quals ((FStar_Syntax_Syntax.Logic)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in (disc_name, [], disc_type, _131_626, (FStar_Ident.range_of_lid disc_name)))
in FStar_Syntax_Syntax.Sig_declare_typ (_131_627)))))))))
end))))))

# 972 "FStar.Parser.ToSyntax.fst"
let mk_indexed_projectors : FStar_Syntax_Syntax.fv_qual  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun fvq refine_domain env tc lid inductive_tps imp_tps fields t -> (
# 973 "FStar.Parser.ToSyntax.fst"
let p = (FStar_Ident.range_of_lid lid)
in (
# 974 "FStar.Parser.ToSyntax.fst"
let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p))
in (
# 975 "FStar.Parser.ToSyntax.fst"
let projectee = (fun ptyp -> (FStar_Syntax_Syntax.gen_bv "projectee" (Some (p)) ptyp))
in (
# 976 "FStar.Parser.ToSyntax.fst"
let tps = (FStar_List.map2 (fun _52_1694 _52_1698 -> (match ((_52_1694, _52_1698)) with
| ((_52_1692, imp), (x, _52_1697)) -> begin
(x, imp)
end)) inductive_tps imp_tps)
in (
# 977 "FStar.Parser.ToSyntax.fst"
let _52_1799 = (
# 978 "FStar.Parser.ToSyntax.fst"
let _52_1702 = (FStar_Syntax_Util.head_and_args t)
in (match (_52_1702) with
| (head, args0) -> begin
(
# 979 "FStar.Parser.ToSyntax.fst"
let args = (
# 980 "FStar.Parser.ToSyntax.fst"
let rec arguments = (fun tps args -> (match ((tps, args)) with
| ([], _52_1708) -> begin
args
end
| (_52_1711, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Not enough arguments to type", (FStar_Ident.range_of_lid lid)))))
end
| ((_52_1716, Some (FStar_Syntax_Syntax.Implicit (_52_1718)))::tps', (_52_1725, Some (FStar_Syntax_Syntax.Implicit (_52_1727)))::args') -> begin
(arguments tps' args')
end
| ((_52_1735, Some (FStar_Syntax_Syntax.Implicit (_52_1737)))::tps', (_52_1745, _52_1747)::_52_1743) -> begin
(arguments tps' args)
end
| ((_52_1754, _52_1756)::_52_1752, (a, Some (FStar_Syntax_Syntax.Implicit (_52_1763)))::_52_1760) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected implicit annotation on argument", a.FStar_Syntax_Syntax.pos))))
end
| ((_52_1771, _52_1773)::tps', (_52_1778, _52_1780)::args') -> begin
(arguments tps' args')
end))
in (arguments inductive_tps args0))
in (
# 989 "FStar.Parser.ToSyntax.fst"
let indices = (FStar_All.pipe_right args (FStar_List.map (fun _52_1785 -> (let _131_657 = (FStar_Syntax_Syntax.new_bv (Some (p)) FStar_Syntax_Syntax.tun)
in (FStar_All.pipe_right _131_657 FStar_Syntax_Syntax.mk_binder)))))
in (
# 990 "FStar.Parser.ToSyntax.fst"
let arg_typ = (let _131_662 = (let _131_658 = (FStar_Syntax_Syntax.lid_as_fv tc None)
in (FStar_Syntax_Syntax.fv_to_tm _131_658))
in (let _131_661 = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _52_1790 -> (match (_52_1790) with
| (x, imp) -> begin
(let _131_660 = (FStar_Syntax_Syntax.bv_to_name x)
in (_131_660, imp))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app _131_662 _131_661 None p)))
in (
# 992 "FStar.Parser.ToSyntax.fst"
let arg_binder = if (not (refine_domain)) then begin
(let _131_663 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder _131_663))
end else begin
(
# 995 "FStar.Parser.ToSyntax.fst"
let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (
# 996 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p)) arg_typ)
in (let _131_671 = (
# 997 "FStar.Parser.ToSyntax.fst"
let _52_1794 = (projectee arg_typ)
in (let _131_670 = (let _131_669 = (let _131_668 = (let _131_667 = (FStar_Syntax_Syntax.fvar None disc_name p)
in (let _131_666 = (let _131_665 = (let _131_664 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _131_664))
in (_131_665)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _131_667 _131_666 None p)))
in (FStar_Syntax_Util.b2t _131_668))
in (FStar_Syntax_Util.refine x _131_669))
in {FStar_Syntax_Syntax.ppname = _52_1794.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_1794.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _131_670}))
in (FStar_Syntax_Syntax.mk_binder _131_671))))
end
in (arg_binder, indices)))))
end))
in (match (_52_1799) with
| (arg_binder, indices) -> begin
(
# 1001 "FStar.Parser.ToSyntax.fst"
let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder))
in (
# 1002 "FStar.Parser.ToSyntax.fst"
let imp_binders = (let _131_673 = (FStar_All.pipe_right indices (FStar_List.map (fun _52_1804 -> (match (_52_1804) with
| (x, _52_1803) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
in (FStar_List.append imp_tps _131_673))
in (
# 1003 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (
# 1005 "FStar.Parser.ToSyntax.fst"
let arg = (FStar_Syntax_Util.arg_of_non_null_binder arg_binder)
in (
# 1007 "FStar.Parser.ToSyntax.fst"
let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _52_1812 -> (match (_52_1812) with
| (a, _52_1811) -> begin
(
# 1008 "FStar.Parser.ToSyntax.fst"
let _52_1816 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (_52_1816) with
| (field_name, _52_1815) -> begin
(
# 1009 "FStar.Parser.ToSyntax.fst"
let proj = (let _131_677 = (let _131_676 = (FStar_Syntax_Syntax.lid_as_fv field_name None)
in (FStar_Syntax_Syntax.fv_to_tm _131_676))
in (FStar_Syntax_Syntax.mk_Tm_app _131_677 ((arg)::[]) None p))
in FStar_Syntax_Syntax.NT ((a, proj)))
end))
end))))
in (
# 1012 "FStar.Parser.ToSyntax.fst"
let ntps = (FStar_List.length tps)
in (
# 1013 "FStar.Parser.ToSyntax.fst"
let all_params = (FStar_List.append imp_tps fields)
in (let _131_709 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _52_1825 -> (match (_52_1825) with
| (x, _52_1824) -> begin
(
# 1016 "FStar.Parser.ToSyntax.fst"
let _52_1829 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_52_1829) with
| (field_name, _52_1828) -> begin
(
# 1017 "FStar.Parser.ToSyntax.fst"
let t = (let _131_681 = (let _131_680 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total _131_680))
in (FStar_Syntax_Util.arrow binders _131_681))
in (
# 1018 "FStar.Parser.ToSyntax.fst"
let only_decl = (((let _131_682 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _131_682)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _131_684 = (let _131_683 = (FStar_Parser_Env.current_module env)
in _131_683.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _131_684)))
in (
# 1022 "FStar.Parser.ToSyntax.fst"
let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (
# 1023 "FStar.Parser.ToSyntax.fst"
let quals = (fun q -> if only_decl then begin
(FStar_Syntax_Syntax.Assumption)::q
end else begin
q
end)
in (
# 1024 "FStar.Parser.ToSyntax.fst"
let quals = (quals ((FStar_Syntax_Syntax.Projector ((lid, x.FStar_Syntax_Syntax.ppname)))::[]))
in (
# 1025 "FStar.Parser.ToSyntax.fst"
let decl = FStar_Syntax_Syntax.Sig_declare_typ ((field_name, [], t, quals, (FStar_Ident.range_of_lid field_name)))
in if only_decl then begin
(decl)::[]
end else begin
(
# 1028 "FStar.Parser.ToSyntax.fst"
let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (
# 1029 "FStar.Parser.ToSyntax.fst"
let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _52_1841 -> (match (_52_1841) with
| (x, imp) -> begin
(
# 1030 "FStar.Parser.ToSyntax.fst"
let b = (FStar_Syntax_Syntax.is_implicit imp)
in if ((i + ntps) = j) then begin
(let _131_689 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in (_131_689, b))
end else begin
if (b && (j < ntps)) then begin
(let _131_693 = (let _131_692 = (let _131_691 = (let _131_690 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (_131_690, FStar_Syntax_Syntax.tun))
in FStar_Syntax_Syntax.Pat_dot_term (_131_691))
in (pos _131_692))
in (_131_693, b))
end else begin
(let _131_696 = (let _131_695 = (let _131_694 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_131_694))
in (pos _131_695))
in (_131_696, b))
end
end)
end))))
in (
# 1036 "FStar.Parser.ToSyntax.fst"
let pat = (let _131_701 = (let _131_699 = (let _131_698 = (let _131_697 = (FStar_Syntax_Syntax.lid_as_fv lid (Some (fvq)))
in (_131_697, arg_pats))
in FStar_Syntax_Syntax.Pat_cons (_131_698))
in (FStar_All.pipe_right _131_699 pos))
in (let _131_700 = (FStar_Syntax_Syntax.bv_to_name projection)
in (_131_701, None, _131_700)))
in (
# 1037 "FStar.Parser.ToSyntax.fst"
let body = (let _131_705 = (let _131_704 = (let _131_703 = (let _131_702 = (FStar_Syntax_Util.branch pat)
in (_131_702)::[])
in (arg_exp, _131_703))
in FStar_Syntax_Syntax.Tm_match (_131_704))
in (FStar_Syntax_Syntax.mk _131_705 None p))
in (
# 1038 "FStar.Parser.ToSyntax.fst"
let imp = (no_annot_abs binders body)
in (
# 1039 "FStar.Parser.ToSyntax.fst"
let lb = {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (field_name); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = imp}
in (
# 1044 "FStar.Parser.ToSyntax.fst"
let impl = (let _131_708 = (let _131_707 = (let _131_706 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (_131_706)::[])
in ((false, (lb)::[]), p, _131_707, quals))
in FStar_Syntax_Syntax.Sig_let (_131_708))
in if no_decl then begin
(impl)::[]
end else begin
(decl)::(impl)::[]
end)))))))
end))))))
end))
end))))
in (FStar_All.pipe_right _131_709 FStar_List.flatten)))))))))
end)))))))

# 1047 "FStar.Parser.ToSyntax.fst"
let mk_data_projectors : FStar_Parser_Env.env  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun env _52_1852 -> (match (_52_1852) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _52_1855, t, l, n, quals, _52_1861, _52_1863) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(
# 1050 "FStar.Parser.ToSyntax.fst"
let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _52_10 -> (match (_52_10) with
| FStar_Syntax_Syntax.RecordConstructor (_52_1868) -> begin
true
end
| _52_1871 -> begin
false
end)))) then begin
false
end else begin
(match ((FStar_Parser_Env.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > 1)
end
| _52_1875 -> begin
true
end)
end
in (
# 1056 "FStar.Parser.ToSyntax.fst"
let _52_1879 = (FStar_Syntax_Util.arrow_formals t)
in (match (_52_1879) with
| (formals, cod) -> begin
(match (formals) with
| [] -> begin
[]
end
| _52_1882 -> begin
(
# 1060 "FStar.Parser.ToSyntax.fst"
let qual = (match ((FStar_Util.find_map quals (fun _52_11 -> (match (_52_11) with
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((lid, fns)))
end
| _52_1887 -> begin
None
end)))) with
| None -> begin
FStar_Syntax_Syntax.Data_ctor
end
| Some (q) -> begin
q
end)
in (
# 1063 "FStar.Parser.ToSyntax.fst"
let _52_1894 = (FStar_Util.first_N n formals)
in (match (_52_1894) with
| (tps, rest) -> begin
(mk_indexed_projectors qual refine_domain env l lid inductive_tps tps rest cod)
end)))
end)
end)))
end
| _52_1896 -> begin
[]
end)
end))

# 1069 "FStar.Parser.ToSyntax.fst"
let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (
# 1070 "FStar.Parser.ToSyntax.fst"
let lb = (let _131_734 = (let _131_732 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars _131_732))
in (let _131_733 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (lid); FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = _131_734; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _131_733}))
in FStar_Syntax_Syntax.Sig_let (((false, (lb)::[]), rng, lids, quals))))

# 1079 "FStar.Parser.ToSyntax.fst"
let rec desugar_tycon : FStar_Parser_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (
# 1080 "FStar.Parser.ToSyntax.fst"
let tycon_id = (fun _52_12 -> (match (_52_12) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (
# 1085 "FStar.Parser.ToSyntax.fst"
let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _131_748 = (let _131_747 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_131_747))
in (FStar_Parser_AST.mk_term _131_748 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| (FStar_Parser_AST.TAnnotated (a, _)) | (FStar_Parser_AST.TVariable (a)) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar (a)) a.FStar_Ident.idRange FStar_Parser_AST.Type)
end
| FStar_Parser_AST.NoName (t) -> begin
t
end))
in (
# 1091 "FStar.Parser.ToSyntax.fst"
let tot = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) rng FStar_Parser_AST.Expr)
in (
# 1092 "FStar.Parser.ToSyntax.fst"
let with_constructor_effect = (fun t -> (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((tot, t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level))
in (
# 1093 "FStar.Parser.ToSyntax.fst"
let apply_binders = (fun t binders -> (
# 1094 "FStar.Parser.ToSyntax.fst"
let imp_of_aqual = (fun b -> (match (b.FStar_Parser_AST.aqual) with
| Some (FStar_Parser_AST.Implicit) -> begin
FStar_Parser_AST.Hash
end
| _52_1970 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _131_761 = (let _131_760 = (let _131_759 = (binder_to_term b)
in (out, _131_759, (imp_of_aqual b)))
in FStar_Parser_AST.App (_131_760))
in (FStar_Parser_AST.mk_term _131_761 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (
# 1099 "FStar.Parser.ToSyntax.fst"
let tycon_record_as_variant = (fun _52_13 -> (match (_52_13) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(
# 1101 "FStar.Parser.ToSyntax.fst"
let constrName = (FStar_Ident.mk_ident ((Prims.strcat "Mk" id.FStar_Ident.idText), id.FStar_Ident.idRange))
in (
# 1102 "FStar.Parser.ToSyntax.fst"
let mfields = (FStar_List.map (fun _52_1983 -> (match (_52_1983) with
| (x, t) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated (((FStar_Syntax_Util.mangle_field_name x), t))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (
# 1103 "FStar.Parser.ToSyntax.fst"
let result = (let _131_767 = (let _131_766 = (let _131_765 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_131_765))
in (FStar_Parser_AST.mk_term _131_766 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _131_767 parms))
in (
# 1104 "FStar.Parser.ToSyntax.fst"
let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _131_769 = (FStar_All.pipe_right fields (FStar_List.map (fun _52_1990 -> (match (_52_1990) with
| (x, _52_1989) -> begin
(FStar_Parser_Env.qualify env x)
end))))
in (FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _131_769))))))
end
| _52_1992 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1108 "FStar.Parser.ToSyntax.fst"
let desugar_abstract_tc = (fun quals _env mutuals _52_14 -> (match (_52_14) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(
# 1110 "FStar.Parser.ToSyntax.fst"
let _52_2006 = (typars_of_binders _env binders)
in (match (_52_2006) with
| (_env', typars) -> begin
(
# 1111 "FStar.Parser.ToSyntax.fst"
let k = (match (kopt) with
| None -> begin
FStar_Syntax_Util.ktype
end
| Some (k) -> begin
(desugar_term _env' k)
end)
in (
# 1114 "FStar.Parser.ToSyntax.fst"
let tconstr = (let _131_780 = (let _131_779 = (let _131_778 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_131_778))
in (FStar_Parser_AST.mk_term _131_779 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _131_780 binders))
in (
# 1115 "FStar.Parser.ToSyntax.fst"
let qlid = (FStar_Parser_Env.qualify _env id)
in (
# 1116 "FStar.Parser.ToSyntax.fst"
let typars = (FStar_Syntax_Subst.close_binders typars)
in (
# 1117 "FStar.Parser.ToSyntax.fst"
let k = (FStar_Syntax_Subst.close typars k)
in (
# 1118 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_inductive_typ ((qlid, [], typars, k, mutuals, [], quals, rng))
in (
# 1119 "FStar.Parser.ToSyntax.fst"
let _env = (FStar_Parser_Env.push_top_level_rec_binding _env id)
in (
# 1120 "FStar.Parser.ToSyntax.fst"
let _env2 = (FStar_Parser_Env.push_top_level_rec_binding _env' id)
in (_env, _env2, se, tconstr)))))))))
end))
end
| _52_2019 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (
# 1123 "FStar.Parser.ToSyntax.fst"
let push_tparams = (fun env bs -> (
# 1124 "FStar.Parser.ToSyntax.fst"
let _52_2034 = (FStar_List.fold_left (fun _52_2025 _52_2028 -> (match ((_52_2025, _52_2028)) with
| ((env, tps), (x, imp)) -> begin
(
# 1125 "FStar.Parser.ToSyntax.fst"
let _52_2031 = (FStar_Parser_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (_52_2031) with
| (env, y) -> begin
(env, ((y, imp))::tps)
end))
end)) (env, []) bs)
in (match (_52_2034) with
| (env, bs) -> begin
(env, (FStar_List.rev bs))
end)))
in (match (tcs) with
| FStar_Parser_AST.TyconAbstract (_52_2036)::[] -> begin
(
# 1130 "FStar.Parser.ToSyntax.fst"
let tc = (FStar_List.hd tcs)
in (
# 1131 "FStar.Parser.ToSyntax.fst"
let _52_2047 = (desugar_abstract_tc quals env [] tc)
in (match (_52_2047) with
| (_52_2041, _52_2043, se, _52_2046) -> begin
(
# 1132 "FStar.Parser.ToSyntax.fst"
let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _52_2050, typars, k, [], [], quals, rng) -> begin
(
# 1134 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
quals
end else begin
(
# 1136 "FStar.Parser.ToSyntax.fst"
let _52_2059 = (let _131_788 = (FStar_Range.string_of_range rng)
in (let _131_787 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" _131_788 _131_787)))
in (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals)
end
in (
# 1139 "FStar.Parser.ToSyntax.fst"
let t = (match (typars) with
| [] -> begin
k
end
| _52_2064 -> begin
(let _131_791 = (let _131_790 = (let _131_789 = (FStar_Syntax_Syntax.mk_Total k)
in (typars, _131_789))
in FStar_Syntax_Syntax.Tm_arrow (_131_790))
in (FStar_Syntax_Syntax.mk _131_791 None rng))
end)
in FStar_Syntax_Syntax.Sig_declare_typ ((l, [], t, quals, rng))))
end
| _52_2067 -> begin
se
end)
in (
# 1144 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))
end)))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t)::[] -> begin
(
# 1149 "FStar.Parser.ToSyntax.fst"
let _52_2079 = (typars_of_binders env binders)
in (match (_52_2079) with
| (env', typars) -> begin
(
# 1150 "FStar.Parser.ToSyntax.fst"
let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _52_15 -> (match (_52_15) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| _52_2084 -> begin
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
# 1156 "FStar.Parser.ToSyntax.fst"
let t0 = t
in (
# 1157 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _52_16 -> (match (_52_16) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| _52_2092 -> begin
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
# 1162 "FStar.Parser.ToSyntax.fst"
let se = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Effect)) then begin
(
# 1164 "FStar.Parser.ToSyntax.fst"
let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (
# 1165 "FStar.Parser.ToSyntax.fst"
let typars = (FStar_Syntax_Subst.close_binders typars)
in (
# 1166 "FStar.Parser.ToSyntax.fst"
let c = (FStar_Syntax_Subst.close_comp typars c)
in (let _131_797 = (let _131_796 = (FStar_Parser_Env.qualify env id)
in (let _131_795 = (FStar_All.pipe_right quals (FStar_List.filter (fun _52_17 -> (match (_52_17) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| _52_2100 -> begin
true
end))))
in (_131_796, [], typars, c, _131_795, rng)))
in FStar_Syntax_Syntax.Sig_effect_abbrev (_131_797)))))
end else begin
(
# 1168 "FStar.Parser.ToSyntax.fst"
let t = (desugar_typ env' t)
in (
# 1169 "FStar.Parser.ToSyntax.fst"
let nm = (FStar_Parser_Env.qualify env id)
in (mk_typ_abbrev nm [] typars k t ((nm)::[]) quals rng)))
end
in (
# 1172 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[]))))))
end))
end
| FStar_Parser_AST.TyconRecord (_52_2106)::[] -> begin
(
# 1176 "FStar.Parser.ToSyntax.fst"
let trec = (FStar_List.hd tcs)
in (
# 1177 "FStar.Parser.ToSyntax.fst"
let _52_2112 = (tycon_record_as_variant trec)
in (match (_52_2112) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| _52_2116::_52_2114 -> begin
(
# 1181 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1182 "FStar.Parser.ToSyntax.fst"
let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_Env.qualify env) (tycon_id x))) tcs)
in (
# 1183 "FStar.Parser.ToSyntax.fst"
let rec collect_tcs = (fun quals et tc -> (
# 1184 "FStar.Parser.ToSyntax.fst"
let _52_2127 = et
in (match (_52_2127) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_52_2129) -> begin
(
# 1187 "FStar.Parser.ToSyntax.fst"
let trec = tc
in (
# 1188 "FStar.Parser.ToSyntax.fst"
let _52_2134 = (tycon_record_as_variant trec)
in (match (_52_2134) with
| (t, fs) -> begin
(collect_tcs ((FStar_Syntax_Syntax.RecordType (fs))::quals) (env, tcs) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(
# 1191 "FStar.Parser.ToSyntax.fst"
let _52_2146 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_52_2146) with
| (env, _52_2143, se, tconstr) -> begin
(env, (FStar_Util.Inl ((se, constructors, tconstr, quals)))::tcs)
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(
# 1194 "FStar.Parser.ToSyntax.fst"
let _52_2158 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_52_2158) with
| (env, _52_2155, se, tconstr) -> begin
(env, (FStar_Util.Inr ((se, t, quals)))::tcs)
end))
end
| _52_2160 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (
# 1197 "FStar.Parser.ToSyntax.fst"
let _52_2163 = (FStar_List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_52_2163) with
| (env, tcs) -> begin
(
# 1198 "FStar.Parser.ToSyntax.fst"
let tcs = (FStar_List.rev tcs)
in (
# 1199 "FStar.Parser.ToSyntax.fst"
let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _52_19 -> (match (_52_19) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, _52_2171, _52_2173, _52_2175, _52_2177), t, quals) -> begin
(
# 1201 "FStar.Parser.ToSyntax.fst"
let _52_2187 = (push_tparams env tpars)
in (match (_52_2187) with
| (env_tps, _52_2186) -> begin
(
# 1202 "FStar.Parser.ToSyntax.fst"
let t = (desugar_term env_tps t)
in (let _131_807 = (let _131_806 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in ([], _131_806))
in (_131_807)::[]))
end))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, _52_2195, tags, _52_2198), constrs, tconstr, quals) -> begin
(
# 1206 "FStar.Parser.ToSyntax.fst"
let tycon = (tname, tpars, k)
in (
# 1207 "FStar.Parser.ToSyntax.fst"
let _52_2209 = (push_tparams env tpars)
in (match (_52_2209) with
| (env_tps, tps) -> begin
(
# 1208 "FStar.Parser.ToSyntax.fst"
let data_tpars = (FStar_List.map (fun _52_2213 -> (match (_52_2213) with
| (x, _52_2212) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end)) tps)
in (
# 1209 "FStar.Parser.ToSyntax.fst"
let _52_2237 = (let _131_819 = (FStar_All.pipe_right constrs (FStar_List.map (fun _52_2218 -> (match (_52_2218) with
| (id, topt, of_notation) -> begin
(
# 1211 "FStar.Parser.ToSyntax.fst"
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
# 1219 "FStar.Parser.ToSyntax.fst"
let t = (let _131_811 = (FStar_Parser_Env.default_total env_tps)
in (let _131_810 = (close env_tps t)
in (desugar_term _131_811 _131_810)))
in (
# 1220 "FStar.Parser.ToSyntax.fst"
let name = (FStar_Parser_Env.qualify env id)
in (
# 1221 "FStar.Parser.ToSyntax.fst"
let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _52_18 -> (match (_52_18) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| _52_2232 -> begin
[]
end))))
in (
# 1224 "FStar.Parser.ToSyntax.fst"
let ntps = (FStar_List.length data_tpars)
in (let _131_818 = (let _131_817 = (let _131_816 = (let _131_815 = (let _131_814 = (let _131_813 = (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total _131_813))
in (FStar_Syntax_Util.arrow data_tpars _131_814))
in (name, univs, _131_815, tname, ntps, quals, mutuals, rng))
in FStar_Syntax_Syntax.Sig_datacon (_131_816))
in (tps, _131_817))
in (name, _131_818)))))))
end))))
in (FStar_All.pipe_left FStar_List.split _131_819))
in (match (_52_2237) with
| (constrNames, constrs) -> begin
(([], FStar_Syntax_Syntax.Sig_inductive_typ ((tname, univs, tpars, k, mutuals, constrNames, tags, rng))))::constrs
end)))
end)))
end
| _52_2239 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1229 "FStar.Parser.ToSyntax.fst"
let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (
# 1230 "FStar.Parser.ToSyntax.fst"
let bundle = (let _131_821 = (let _131_820 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _131_820, rng))
in FStar_Syntax_Syntax.Sig_bundle (_131_821))
in (
# 1231 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 bundle)
in (
# 1232 "FStar.Parser.ToSyntax.fst"
let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projectors env)))
in (
# 1233 "FStar.Parser.ToSyntax.fst"
let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _52_20 -> (match (_52_20) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, _52_2248, tps, k, _52_2252, constrs, quals, _52_2256) when ((FStar_List.length constrs) > 1) -> begin
(mk_data_discriminators quals env tname tps k constrs)
end
| _52_2260 -> begin
[]
end))))
in (
# 1237 "FStar.Parser.ToSyntax.fst"
let ops = (FStar_List.append discs data_ops)
in (
# 1238 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env ops)
in (env, (FStar_List.append ((bundle)::[]) ops)))))))))))
end)))))
end
| [] -> begin
(FStar_All.failwith "impossible")
end))))))))))

# 1243 "FStar.Parser.ToSyntax.fst"
let desugar_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.binder Prims.list) = (fun env binders -> (
# 1244 "FStar.Parser.ToSyntax.fst"
let _52_2284 = (FStar_List.fold_left (fun _52_2269 b -> (match (_52_2269) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| (Some (a), k) -> begin
(
# 1247 "FStar.Parser.ToSyntax.fst"
let _52_2277 = (FStar_Parser_Env.push_bv env a)
in (match (_52_2277) with
| (env, a) -> begin
(let _131_830 = (let _131_829 = (FStar_Syntax_Syntax.mk_binder (
# 1248 "FStar.Parser.ToSyntax.fst"
let _52_2278 = a
in {FStar_Syntax_Syntax.ppname = _52_2278.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _52_2278.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (_131_829)::binders)
in (env, _131_830))
end))
end
| _52_2281 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Missing name in binder", b.FStar_Parser_AST.brange))))
end)
end)) (env, []) binders)
in (match (_52_2284) with
| (env, binders) -> begin
(env, (FStar_List.rev binders))
end)))

# 1253 "FStar.Parser.ToSyntax.fst"
let rec desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(
# 1255 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_pragma (((trans_pragma p), d.FStar_Parser_AST.drange))
in (env, (se)::[]))
end
| FStar_Parser_AST.Open (lid) -> begin
(
# 1259 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_namespace env lid)
in (env, []))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(let _131_835 = (FStar_List.map trans_qual qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _131_835 tcs))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _131_837 = (let _131_836 = (desugar_term_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((isrec, lets, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Syntax_Subst.compress _131_836))
in _131_837.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let (lbs, _52_2304) -> begin
(
# 1268 "FStar.Parser.ToSyntax.fst"
let lids = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (
# 1269 "FStar.Parser.ToSyntax.fst"
let quals = (match (quals) with
| _52_2312::_52_2310 -> begin
(FStar_List.map trans_qual quals)
end
| _52_2315 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _52_21 -> (match (_52_21) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (_52_2326); FStar_Syntax_Syntax.lbunivs = _52_2324; FStar_Syntax_Syntax.lbtyp = _52_2322; FStar_Syntax_Syntax.lbeff = _52_2320; FStar_Syntax_Syntax.lbdef = _52_2318} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (l); FStar_Syntax_Syntax.lbunivs = _52_2336; FStar_Syntax_Syntax.lbtyp = _52_2334; FStar_Syntax_Syntax.lbeff = _52_2332; FStar_Syntax_Syntax.lbdef = _52_2330} -> begin
(FStar_Parser_Env.lookup_letbinding_quals env l)
end))))
end)
in (
# 1274 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right lets (FStar_Util.for_some (fun _52_2344 -> (match (_52_2344) with
| (_52_2342, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end)))) then begin
(FStar_Syntax_Syntax.Logic)::quals
end else begin
quals
end
in (
# 1278 "FStar.Parser.ToSyntax.fst"
let s = FStar_Syntax_Syntax.Sig_let ((lbs, d.FStar_Parser_AST.drange, lids, quals))
in (
# 1279 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env s)
in (env, (s)::[]))))))
end
| _52_2349 -> begin
(FStar_All.failwith "Desugaring a let did not produce a let")
end)
end
| FStar_Parser_AST.Main (t) -> begin
(
# 1285 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env t)
in (
# 1286 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, d.FStar_Parser_AST.drange))
in (env, (se)::[])))
end
| FStar_Parser_AST.Assume (atag, id, t) -> begin
(
# 1290 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env t)
in (let _131_844 = (let _131_843 = (let _131_842 = (let _131_841 = (FStar_Parser_Env.qualify env id)
in (_131_841, f, (FStar_Syntax_Syntax.Assumption)::[], d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Sig_assume (_131_842))
in (_131_843)::[])
in (env, _131_844)))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(
# 1294 "FStar.Parser.ToSyntax.fst"
let t = (let _131_845 = (close_fun env t)
in (desugar_term env _131_845))
in (
# 1295 "FStar.Parser.ToSyntax.fst"
let quals = if (env.FStar_Parser_Env.iface && env.FStar_Parser_Env.admitted_iface) then begin
(FStar_Parser_AST.Assumption)::quals
end else begin
quals
end
in (
# 1296 "FStar.Parser.ToSyntax.fst"
let se = (let _131_848 = (let _131_847 = (FStar_Parser_Env.qualify env id)
in (let _131_846 = (FStar_List.map trans_qual quals)
in (_131_847, [], t, _131_846, d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_declare_typ (_131_848))
in (
# 1297 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(
# 1301 "FStar.Parser.ToSyntax.fst"
let t = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (
# 1302 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env id)
in (
# 1303 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_datacon ((l, [], t, FStar_Syntax_Const.exn_lid, 0, (FStar_Syntax_Syntax.ExceptionConstructor)::[], (FStar_Syntax_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (
# 1304 "FStar.Parser.ToSyntax.fst"
let se' = FStar_Syntax_Syntax.Sig_bundle (((se)::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (
# 1305 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se')
in (
# 1306 "FStar.Parser.ToSyntax.fst"
let data_ops = (mk_data_projectors env ([], se))
in (
# 1307 "FStar.Parser.ToSyntax.fst"
let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (
# 1308 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops))))))))))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(
# 1312 "FStar.Parser.ToSyntax.fst"
let t = (desugar_term env term)
in (
# 1313 "FStar.Parser.ToSyntax.fst"
let t = (let _131_852 = (let _131_849 = (FStar_Syntax_Syntax.null_binder t)
in (_131_849)::[])
in (let _131_851 = (let _131_850 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _131_850))
in (FStar_Syntax_Util.arrow _131_852 _131_851)))
in (
# 1314 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env id)
in (
# 1315 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_datacon ((l, [], t, FStar_Syntax_Const.exn_lid, 0, (FStar_Syntax_Syntax.ExceptionConstructor)::[], (FStar_Syntax_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (
# 1316 "FStar.Parser.ToSyntax.fst"
let se' = FStar_Syntax_Syntax.Sig_bundle (((se)::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (
# 1317 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se')
in (
# 1318 "FStar.Parser.ToSyntax.fst"
let data_ops = (mk_data_projectors env ([], se))
in (
# 1319 "FStar.Parser.ToSyntax.fst"
let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (
# 1320 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops)))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(
# 1324 "FStar.Parser.ToSyntax.fst"
let _52_2402 = (desugar_binders env binders)
in (match (_52_2402) with
| (env_k, binders) -> begin
(
# 1325 "FStar.Parser.ToSyntax.fst"
let k = (desugar_term env_k k)
in (
# 1326 "FStar.Parser.ToSyntax.fst"
let name = (FStar_Parser_Env.qualify env id)
in (
# 1327 "FStar.Parser.ToSyntax.fst"
let se = (mk_typ_abbrev name [] binders FStar_Syntax_Syntax.tun k ((name)::[]) [] d.FStar_Parser_AST.drange)
in (
# 1328 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))))
end))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(
# 1332 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1333 "FStar.Parser.ToSyntax.fst"
let _52_2418 = (desugar_binders env eff_binders)
in (match (_52_2418) with
| (env, binders) -> begin
(
# 1334 "FStar.Parser.ToSyntax.fst"
let _52_2429 = (
# 1335 "FStar.Parser.ToSyntax.fst"
let _52_2421 = (head_and_args defn)
in (match (_52_2421) with
| (head, args) -> begin
(
# 1336 "FStar.Parser.ToSyntax.fst"
let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_defn env) l)
end
| _52_2425 -> begin
(let _131_857 = (let _131_856 = (let _131_855 = (let _131_854 = (let _131_853 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat "Effect " _131_853))
in (Prims.strcat _131_854 " not found"))
in (_131_855, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_131_856))
in (Prims.raise _131_857))
end)
in (let _131_858 = (desugar_args env args)
in (ed, _131_858)))
end))
in (match (_52_2429) with
| (ed, args) -> begin
(
# 1340 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_Syntax_Subst.close_binders binders)
in (
# 1341 "FStar.Parser.ToSyntax.fst"
let subst = (FStar_Syntax_Util.subst_of_list ed.FStar_Syntax_Syntax.binders args)
in (
# 1342 "FStar.Parser.ToSyntax.fst"
let sub = (fun x -> (let _131_862 = (let _131_861 = (FStar_Syntax_Subst.subst subst (Prims.snd x))
in (FStar_Syntax_Subst.close binders _131_861))
in ([], _131_862)))
in (
# 1343 "FStar.Parser.ToSyntax.fst"
let ed = (let _131_879 = (FStar_List.map trans_qual quals)
in (let _131_878 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _131_877 = (let _131_863 = (sub ([], ed.FStar_Syntax_Syntax.signature))
in (Prims.snd _131_863))
in (let _131_876 = (sub ed.FStar_Syntax_Syntax.ret)
in (let _131_875 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (let _131_874 = (sub ed.FStar_Syntax_Syntax.bind_wlp)
in (let _131_873 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (let _131_872 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (let _131_871 = (sub ed.FStar_Syntax_Syntax.ite_wlp)
in (let _131_870 = (sub ed.FStar_Syntax_Syntax.wp_binop)
in (let _131_869 = (sub ed.FStar_Syntax_Syntax.wp_as_type)
in (let _131_868 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (let _131_867 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (let _131_866 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (let _131_865 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (let _131_864 = (sub ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _131_879; FStar_Syntax_Syntax.mname = _131_878; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = _131_877; FStar_Syntax_Syntax.ret = _131_876; FStar_Syntax_Syntax.bind_wp = _131_875; FStar_Syntax_Syntax.bind_wlp = _131_874; FStar_Syntax_Syntax.if_then_else = _131_873; FStar_Syntax_Syntax.ite_wp = _131_872; FStar_Syntax_Syntax.ite_wlp = _131_871; FStar_Syntax_Syntax.wp_binop = _131_870; FStar_Syntax_Syntax.wp_as_type = _131_869; FStar_Syntax_Syntax.close_wp = _131_868; FStar_Syntax_Syntax.assert_p = _131_867; FStar_Syntax_Syntax.assume_p = _131_866; FStar_Syntax_Syntax.null_wp = _131_865; FStar_Syntax_Syntax.trivial = _131_864}))))))))))))))))
in (
# 1363 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (
# 1364 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 se)
in (env, (se)::[])))))))
end))
end)))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls)) -> begin
(
# 1368 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1369 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.enter_monad_scope env eff_name)
in (
# 1370 "FStar.Parser.ToSyntax.fst"
let _52_2450 = (desugar_binders env eff_binders)
in (match (_52_2450) with
| (env, binders) -> begin
(
# 1371 "FStar.Parser.ToSyntax.fst"
let eff_k = (let _131_880 = (FStar_Parser_Env.default_total env)
in (desugar_term _131_880 eff_kind))
in (
# 1372 "FStar.Parser.ToSyntax.fst"
let _52_2461 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _52_2454 decl -> (match (_52_2454) with
| (env, out) -> begin
(
# 1373 "FStar.Parser.ToSyntax.fst"
let _52_2458 = (desugar_decl env decl)
in (match (_52_2458) with
| (env, ses) -> begin
(let _131_884 = (let _131_883 = (FStar_List.hd ses)
in (_131_883)::out)
in (env, _131_884))
end))
end)) (env, [])))
in (match (_52_2461) with
| (env, decls) -> begin
(
# 1375 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_Syntax_Subst.close_binders binders)
in (
# 1376 "FStar.Parser.ToSyntax.fst"
let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (
# 1377 "FStar.Parser.ToSyntax.fst"
let lookup = (fun s -> (
# 1378 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env (FStar_Ident.mk_ident (s, d.FStar_Parser_AST.drange)))
in (let _131_888 = (let _131_887 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) _131_887))
in ([], _131_888))))
in (
# 1380 "FStar.Parser.ToSyntax.fst"
let ed = (let _131_903 = (FStar_List.map trans_qual quals)
in (let _131_902 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _131_901 = (lookup "return")
in (let _131_900 = (lookup "bind_wp")
in (let _131_899 = (lookup "bind_wlp")
in (let _131_898 = (lookup "if_then_else")
in (let _131_897 = (lookup "ite_wp")
in (let _131_896 = (lookup "ite_wlp")
in (let _131_895 = (lookup "wp_binop")
in (let _131_894 = (lookup "wp_as_type")
in (let _131_893 = (lookup "close_wp")
in (let _131_892 = (lookup "assert_p")
in (let _131_891 = (lookup "assume_p")
in (let _131_890 = (lookup "null_wp")
in (let _131_889 = (lookup "trivial")
in {FStar_Syntax_Syntax.qualifiers = _131_903; FStar_Syntax_Syntax.mname = _131_902; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret = _131_901; FStar_Syntax_Syntax.bind_wp = _131_900; FStar_Syntax_Syntax.bind_wlp = _131_899; FStar_Syntax_Syntax.if_then_else = _131_898; FStar_Syntax_Syntax.ite_wp = _131_897; FStar_Syntax_Syntax.ite_wlp = _131_896; FStar_Syntax_Syntax.wp_binop = _131_895; FStar_Syntax_Syntax.wp_as_type = _131_894; FStar_Syntax_Syntax.close_wp = _131_893; FStar_Syntax_Syntax.assert_p = _131_892; FStar_Syntax_Syntax.assume_p = _131_891; FStar_Syntax_Syntax.null_wp = _131_890; FStar_Syntax_Syntax.trivial = _131_889})))))))))))))))
in (
# 1400 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (
# 1401 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 se)
in (env, (se)::[])))))))
end)))
end))))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(
# 1405 "FStar.Parser.ToSyntax.fst"
let lookup = (fun l -> (match ((FStar_Parser_Env.try_lookup_effect_name env l)) with
| None -> begin
(let _131_910 = (let _131_909 = (let _131_908 = (let _131_907 = (let _131_906 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat "Effect name " _131_906))
in (Prims.strcat _131_907 " not found"))
in (_131_908, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_131_909))
in (Prims.raise _131_910))
end
| Some (l) -> begin
l
end))
in (
# 1408 "FStar.Parser.ToSyntax.fst"
let src = (lookup l.FStar_Parser_AST.msource)
in (
# 1409 "FStar.Parser.ToSyntax.fst"
let dst = (lookup l.FStar_Parser_AST.mdest)
in (
# 1410 "FStar.Parser.ToSyntax.fst"
let lift = (let _131_911 = (desugar_term env l.FStar_Parser_AST.lift_op)
in ([], _131_911))
in (
# 1411 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect (({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift = lift}, d.FStar_Parser_AST.drange))
in (env, (se)::[]))))))
end))

# 1414 "FStar.Parser.ToSyntax.fst"
let desugar_decls : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _52_2485 d -> (match (_52_2485) with
| (env, sigelts) -> begin
(
# 1416 "FStar.Parser.ToSyntax.fst"
let _52_2489 = (desugar_decl env d)
in (match (_52_2489) with
| (env, se) -> begin
(env, (FStar_List.append sigelts se))
end))
end)) (env, []) decls))

# 1419 "FStar.Parser.ToSyntax.fst"
let open_prims_all : FStar_Parser_AST.decl Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.all_lid)) FStar_Range.dummyRange))::[]

# 1426 "FStar.Parser.ToSyntax.fst"
let desugar_modul_common = (fun curmod env m -> (
# 1427 "FStar.Parser.ToSyntax.fst"
let open_ns = (fun mname d -> (
# 1428 "FStar.Parser.ToSyntax.fst"
let d = if ((FStar_List.length mname.FStar_Ident.ns) <> 0) then begin
(let _131_927 = (let _131_926 = (let _131_925 = (FStar_Ident.lid_of_ids mname.FStar_Ident.ns)
in FStar_Parser_AST.Open (_131_925))
in (FStar_Parser_AST.mk_decl _131_926 (FStar_Ident.range_of_lid mname)))
in (_131_927)::d)
end else begin
d
end
in d))
in (
# 1432 "FStar.Parser.ToSyntax.fst"
let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod, _52_2500) -> begin
(FStar_Parser_Env.finish_module_or_interface env prev_mod)
end)
in (
# 1435 "FStar.Parser.ToSyntax.fst"
let _52_2519 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _131_929 = (FStar_Parser_Env.prepare_module_or_interface true admitted env mname)
in (let _131_928 = (open_ns mname decls)
in (_131_929, mname, _131_928, true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _131_931 = (FStar_Parser_Env.prepare_module_or_interface false false env mname)
in (let _131_930 = (open_ns mname decls)
in (_131_931, mname, _131_930, false)))
end)
in (match (_52_2519) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(
# 1440 "FStar.Parser.ToSyntax.fst"
let _52_2522 = (desugar_decls env decls)
in (match (_52_2522) with
| (env, sigelts) -> begin
(
# 1441 "FStar.Parser.ToSyntax.fst"
let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in (env, modul, pop_when_done))
end))
end)))))

# 1449 "FStar.Parser.ToSyntax.fst"
let desugar_partial_modul = (fun curmod env m -> (
# 1450 "FStar.Parser.ToSyntax.fst"
let m = if (FStar_ST.read FStar_Options.interactive_fsi) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface ((mname, decls, true))
end
| FStar_Parser_AST.Interface (mname, _52_2533, _52_2535) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (
# 1457 "FStar.Parser.ToSyntax.fst"
let _52_2543 = (desugar_modul_common curmod env m)
in (match (_52_2543) with
| (x, y, _52_2542) -> begin
(x, y)
end))))

# 1460 "FStar.Parser.ToSyntax.fst"
let desugar_modul : FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (
# 1461 "FStar.Parser.ToSyntax.fst"
let _52_2549 = (desugar_modul_common None env m)
in (match (_52_2549) with
| (env, modul, pop_when_done) -> begin
(
# 1462 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.finish_module_or_interface env modul)
in (
# 1463 "FStar.Parser.ToSyntax.fst"
let _52_2551 = if (FStar_Options.should_dump modul.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _131_939 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _131_939))
end else begin
()
end
in (let _131_940 = if pop_when_done then begin
(FStar_Parser_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end else begin
env
end
in (_131_940, modul))))
end)))

# 1467 "FStar.Parser.ToSyntax.fst"
let desugar_file : FStar_Parser_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (
# 1468 "FStar.Parser.ToSyntax.fst"
let _52_2564 = (FStar_List.fold_left (fun _52_2557 m -> (match (_52_2557) with
| (env, mods) -> begin
(
# 1469 "FStar.Parser.ToSyntax.fst"
let _52_2561 = (desugar_modul env m)
in (match (_52_2561) with
| (env, m) -> begin
(env, (m)::mods)
end))
end)) (env, []) f)
in (match (_52_2564) with
| (env, mods) -> begin
(env, (FStar_List.rev mods))
end)))

# 1473 "FStar.Parser.ToSyntax.fst"
let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Parser_Env.env  ->  FStar_Parser_Env.env = (fun m en -> (
# 1474 "FStar.Parser.ToSyntax.fst"
let _52_2569 = (FStar_Parser_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (_52_2569) with
| (en, pop_when_done) -> begin
(
# 1475 "FStar.Parser.ToSyntax.fst"
let en = (FStar_List.fold_left FStar_Parser_Env.push_sigelt (
# 1475 "FStar.Parser.ToSyntax.fst"
let _52_2570 = en
in {FStar_Parser_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_Parser_Env.modules = _52_2570.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _52_2570.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.sigaccum = _52_2570.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _52_2570.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _52_2570.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _52_2570.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _52_2570.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _52_2570.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _52_2570.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = _52_2570.FStar_Parser_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (
# 1476 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_Env.export_interface m.FStar_Syntax_Syntax.name env)
end else begin
env
end))
end)))




