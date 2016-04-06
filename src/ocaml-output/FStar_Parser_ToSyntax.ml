
open Prims
# 40 "FStar.Parser.ToSyntax.fst"
let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _56_1 -> (match (_56_1) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Syntax_Syntax.Equality)
end
| _56_28 -> begin
None
end))

# 45 "FStar.Parser.ToSyntax.fst"
let trans_qual : FStar_Range.range  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun r _56_2 -> (match (_56_2) with
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
FStar_Syntax_Syntax.Unfoldable
end
| FStar_Parser_AST.DefaultEffect -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("The \'default\' qualifier on effects is no longer supported", r))))
end))

# 59 "FStar.Parser.ToSyntax.fst"
let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun _56_3 -> (match (_56_3) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end))

# 63 "FStar.Parser.ToSyntax.fst"
let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _56_4 -> (match (_56_4) with
| FStar_Parser_AST.Hash -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| _56_51 -> begin
None
end))

# 66 "FStar.Parser.ToSyntax.fst"
let arg_withimp_e = (fun imp t -> (t, (as_imp imp)))

# 68 "FStar.Parser.ToSyntax.fst"
let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
(t, Some (FStar_Syntax_Syntax.imp_tag))
end
| _56_58 -> begin
(t, None)
end))

# 73 "FStar.Parser.ToSyntax.fst"
let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_56_62) -> begin
true
end
| _56_65 -> begin
false
end)))))

# 78 "FStar.Parser.ToSyntax.fst"
let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _56_70 -> begin
t
end))

# 82 "FStar.Parser.ToSyntax.fst"
let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _145_23 = (let _145_22 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_145_22))
in (FStar_Parser_AST.mk_term _145_23 r FStar_Parser_AST.Kind)))

# 84 "FStar.Parser.ToSyntax.fst"
let rec delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (
# 85 "FStar.Parser.ToSyntax.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_56_75) -> begin
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
let name_of_char = (fun _56_5 -> (match (_56_5) with
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
| _56_170 -> begin
"UNKNOWN"
end))
in (
# 134 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _145_43 = (let _145_41 = (FStar_Util.char_at s i)
in (name_of_char _145_41))
in (let _145_42 = (aux (i + 1))
in (_145_43)::_145_42))
end)
in (let _145_45 = (let _145_44 = (aux 0)
in (FStar_String.concat "_" _145_44))
in (Prims.strcat "op_" _145_45)))))

# 140 "FStar.Parser.ToSyntax.fst"
let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _145_55 = (let _145_54 = (let _145_53 = (let _145_52 = (compile_op n s)
in (_145_52, r))
in (FStar_Ident.mk_ident _145_53))
in (_145_54)::[])
in (FStar_All.pipe_right _145_55 FStar_Ident.lid_of_ids)))

# 142 "FStar.Parser.ToSyntax.fst"
let op_as_term : FStar_Parser_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.term Prims.option = (fun env arity rng s -> (
# 143 "FStar.Parser.ToSyntax.fst"
let r = (fun l dd -> (let _145_70 = (let _145_69 = (let _145_68 = (FStar_Ident.set_lid_range l rng)
in (FStar_Syntax_Syntax.lid_as_fv _145_68 dd None))
in (FStar_All.pipe_right _145_69 FStar_Syntax_Syntax.fv_to_tm))
in Some (_145_70)))
in (
# 144 "FStar.Parser.ToSyntax.fst"
let fallback = (fun _56_185 -> (match (()) with
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
| _56_213 -> begin
None
end)
end))
in (match ((let _145_73 = (compile_op_lid arity s rng)
in (FStar_Parser_Env.try_lookup_lid env _145_73))) with
| Some (t) -> begin
Some (t)
end
| _56_217 -> begin
(fallback ())
end))))

# 178 "FStar.Parser.ToSyntax.fst"
let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _145_80 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _145_80)))

# 182 "FStar.Parser.ToSyntax.fst"
let rec free_type_vars_b : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_56_226) -> begin
(env, [])
end
| FStar_Parser_AST.TVariable (x) -> begin
(
# 185 "FStar.Parser.ToSyntax.fst"
let _56_233 = (FStar_Parser_Env.push_bv env x)
in (match (_56_233) with
| (env, _56_232) -> begin
(env, (x)::[])
end))
end
| FStar_Parser_AST.Annotated (_56_235, term) -> begin
(let _145_87 = (free_type_vars env term)
in (env, _145_87))
end
| FStar_Parser_AST.TAnnotated (id, _56_241) -> begin
(
# 190 "FStar.Parser.ToSyntax.fst"
let _56_247 = (FStar_Parser_Env.push_bv env id)
in (match (_56_247) with
| (env, _56_246) -> begin
(env, [])
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _145_88 = (free_type_vars env t)
in (env, _145_88))
end))
and free_type_vars : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _145_91 = (unparen t)
in _145_91.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (_56_253) -> begin
(FStar_All.failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_Env.try_lookup_id env a)) with
| None -> begin
(a)::[]
end
| _56_259 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_56_289, ts) -> begin
(FStar_List.collect (fun _56_296 -> (match (_56_296) with
| (t, _56_295) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_56_298, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _56_305) -> begin
(let _145_94 = (free_type_vars env t1)
in (let _145_93 = (free_type_vars env t2)
in (FStar_List.append _145_94 _145_93)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(
# 220 "FStar.Parser.ToSyntax.fst"
let _56_314 = (free_type_vars_b env b)
in (match (_56_314) with
| (env, f) -> begin
(let _145_95 = (free_type_vars env t)
in (FStar_List.append f _145_95))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(
# 225 "FStar.Parser.ToSyntax.fst"
let _56_330 = (FStar_List.fold_left (fun _56_323 binder -> (match (_56_323) with
| (env, free) -> begin
(
# 226 "FStar.Parser.ToSyntax.fst"
let _56_327 = (free_type_vars_b env binder)
in (match (_56_327) with
| (env, f) -> begin
(env, (FStar_List.append f free))
end))
end)) (env, []) binders)
in (match (_56_330) with
| (env, free) -> begin
(let _145_98 = (free_type_vars env body)
in (FStar_List.append free _145_98))
end))
end
| FStar_Parser_AST.Project (t, _56_333) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
[]
end))

# 243 "FStar.Parser.ToSyntax.fst"
let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (
# 244 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun args t -> (match ((let _145_105 = (unparen t)
in _145_105.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _56_377 -> begin
(t, args)
end))
in (aux [] t)))

# 250 "FStar.Parser.ToSyntax.fst"
let close : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 251 "FStar.Parser.ToSyntax.fst"
let ftv = (let _145_110 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _145_110))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 254 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _145_114 = (let _145_113 = (let _145_112 = (tm_type x.FStar_Ident.idRange)
in (x, _145_112))
in FStar_Parser_AST.TAnnotated (_145_113))
in (FStar_Parser_AST.mk_binder _145_114 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 255 "FStar.Parser.ToSyntax.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))

# 258 "FStar.Parser.ToSyntax.fst"
let close_fun : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 259 "FStar.Parser.ToSyntax.fst"
let ftv = (let _145_119 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _145_119))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 262 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _145_123 = (let _145_122 = (let _145_121 = (tm_type x.FStar_Ident.idRange)
in (x, _145_121))
in FStar_Parser_AST.TAnnotated (_145_122))
in (FStar_Parser_AST.mk_binder _145_123 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 263 "FStar.Parser.ToSyntax.fst"
let t = (match ((let _145_124 = (unparen t)
in _145_124.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_56_390) -> begin
t
end
| _56_393 -> begin
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
| _56_403 -> begin
(bs, t)
end))

# 273 "FStar.Parser.ToSyntax.fst"
let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _56_407) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_56_413); FStar_Parser_AST.prange = _56_411}, _56_417) -> begin
true
end
| _56_421 -> begin
false
end))

# 278 "FStar.Parser.ToSyntax.fst"
let rec destruct_app_pattern : FStar_Parser_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 280 "FStar.Parser.ToSyntax.fst"
let _56_433 = (destruct_app_pattern env is_top_level p)
in (match (_56_433) with
| (name, args, _56_432) -> begin
(name, args, Some (t))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _56_438); FStar_Parser_AST.prange = _56_435}, args) when is_top_level -> begin
(let _145_138 = (let _145_137 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_145_137))
in (_145_138, args, None))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _56_449); FStar_Parser_AST.prange = _56_446}, args) -> begin
(FStar_Util.Inl (id), args, None)
end
| _56_457 -> begin
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
| LocalBinder (_56_460) -> begin
_56_460
end))

# 291 "FStar.Parser.ToSyntax.fst"
let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_56_463) -> begin
_56_463
end))

# 292 "FStar.Parser.ToSyntax.fst"
let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun _56_6 -> (match (_56_6) with
| LocalBinder (a, aq) -> begin
(a, aq)
end
| _56_470 -> begin
(FStar_All.failwith "Impossible")
end))

# 295 "FStar.Parser.ToSyntax.fst"
let as_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_Parser_Env.env) = (fun env imp _56_7 -> (match (_56_7) with
| (None, k) -> begin
(let _145_175 = (FStar_Syntax_Syntax.null_binder k)
in (_145_175, env))
end
| (Some (a), k) -> begin
(
# 298 "FStar.Parser.ToSyntax.fst"
let _56_483 = (FStar_Parser_Env.push_bv env a)
in (match (_56_483) with
| (env, a) -> begin
(((
# 299 "FStar.Parser.ToSyntax.fst"
let _56_484 = a
in {FStar_Syntax_Syntax.ppname = _56_484.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_484.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}), (trans_aqual imp)), env)
end))
end))

# 301 "FStar.Parser.ToSyntax.fst"
type env_t =
FStar_Parser_Env.env

# 302 "FStar.Parser.ToSyntax.fst"
type lenv_t =
FStar_Syntax_Syntax.bv Prims.list

# 304 "FStar.Parser.ToSyntax.fst"
let mk_lb : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.letbinding = (fun _56_489 -> (match (_56_489) with
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
| FStar_Syntax_Syntax.Pat_cons (_56_510, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out _56_518 -> (match (_56_518) with
| (p, _56_517) -> begin
(let _145_221 = (pat_vars p)
in (FStar_Util.set_union out _145_221))
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
| _56_536 -> begin
(
# 330 "FStar.Parser.ToSyntax.fst"
let _56_539 = (FStar_Parser_Env.push_bv e x)
in (match (_56_539) with
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
| _56_548 -> begin
(
# 336 "FStar.Parser.ToSyntax.fst"
let _56_551 = (FStar_Parser_Env.push_bv e a)
in (match (_56_551) with
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
let _56_573 = (aux loc env p)
in (match (_56_573) with
| (loc, env, var, p, _56_572) -> begin
(
# 345 "FStar.Parser.ToSyntax.fst"
let _56_590 = (FStar_List.fold_left (fun _56_577 p -> (match (_56_577) with
| (loc, env, ps) -> begin
(
# 346 "FStar.Parser.ToSyntax.fst"
let _56_586 = (aux loc env p)
in (match (_56_586) with
| (loc, env, _56_582, p, _56_585) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_56_590) with
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
let _56_601 = (aux loc env p)
in (match (_56_601) with
| (loc, env', binder, p, imp) -> begin
(
# 353 "FStar.Parser.ToSyntax.fst"
let binder = (match (binder) with
| LetBinder (_56_603) -> begin
(FStar_All.failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(
# 356 "FStar.Parser.ToSyntax.fst"
let t = (let _145_251 = (close_fun env t)
in (desugar_term env _145_251))
in LocalBinder (((
# 357 "FStar.Parser.ToSyntax.fst"
let _56_610 = x
in {FStar_Syntax_Syntax.ppname = _56_610.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_610.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), aq)))
end)
in (loc, env', binder, p, imp))
end))
end
| FStar_Parser_AST.PatWild -> begin
(
# 361 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _145_252 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in (loc, env, LocalBinder ((x, None)), _145_252, false)))
end
| FStar_Parser_AST.PatConst (c) -> begin
(
# 365 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _145_253 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in (loc, env, LocalBinder ((x, None)), _145_253, false)))
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
let _56_629 = (resolvex loc env x)
in (match (_56_629) with
| (loc, env, xbv) -> begin
(let _145_254 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in (loc, env, LocalBinder ((xbv, aq)), _145_254, imp))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(
# 376 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_datacon env) l)
in (
# 377 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _145_255 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, []))))
in (loc, env, LocalBinder ((x, None)), _145_255, false))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _56_635}, args) -> begin
(
# 381 "FStar.Parser.ToSyntax.fst"
let _56_657 = (FStar_List.fold_right (fun arg _56_646 -> (match (_56_646) with
| (loc, env, args) -> begin
(
# 382 "FStar.Parser.ToSyntax.fst"
let _56_653 = (aux loc env arg)
in (match (_56_653) with
| (loc, env, _56_650, arg, imp) -> begin
(loc, env, ((arg, imp))::args)
end))
end)) args (loc, env, []))
in (match (_56_657) with
| (loc, env, args) -> begin
(
# 384 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_datacon env) l)
in (
# 385 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _145_258 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _145_258, false))))
end))
end
| FStar_Parser_AST.PatApp (_56_661) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(
# 391 "FStar.Parser.ToSyntax.fst"
let _56_681 = (FStar_List.fold_right (fun pat _56_669 -> (match (_56_669) with
| (loc, env, pats) -> begin
(
# 392 "FStar.Parser.ToSyntax.fst"
let _56_677 = (aux loc env pat)
in (match (_56_677) with
| (loc, env, _56_673, pat, _56_676) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_56_681) with
| (loc, env, pats) -> begin
(
# 394 "FStar.Parser.ToSyntax.fst"
let pat = (let _145_271 = (let _145_270 = (let _145_266 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _145_266))
in (let _145_269 = (let _145_268 = (let _145_267 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_145_267, []))
in FStar_Syntax_Syntax.Pat_cons (_145_268))
in (FStar_All.pipe_left _145_270 _145_269)))
in (FStar_List.fold_right (fun hd tl -> (
# 395 "FStar.Parser.ToSyntax.fst"
let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (let _145_265 = (let _145_264 = (let _145_263 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_145_263, ((hd, false))::((tl, false))::[]))
in FStar_Syntax_Syntax.Pat_cons (_145_264))
in (FStar_All.pipe_left (pos_r r) _145_265)))) pats _145_271))
in (
# 398 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (loc, env, LocalBinder ((x, None)), pat, false)))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(
# 402 "FStar.Parser.ToSyntax.fst"
let _56_707 = (FStar_List.fold_left (fun _56_694 p -> (match (_56_694) with
| (loc, env, pats) -> begin
(
# 403 "FStar.Parser.ToSyntax.fst"
let _56_703 = (aux loc env p)
in (match (_56_703) with
| (loc, env, _56_699, pat, _56_702) -> begin
(loc, env, ((pat, false))::pats)
end))
end)) (loc, env, []) args)
in (match (_56_707) with
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
| _56_714 -> begin
(FStar_All.failwith "impossible")
end)
in (
# 412 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _145_274 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _145_274, false)))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(
# 419 "FStar.Parser.ToSyntax.fst"
let _56_724 = (FStar_List.hd fields)
in (match (_56_724) with
| (f, _56_723) -> begin
(
# 420 "FStar.Parser.ToSyntax.fst"
let _56_728 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_56_728) with
| (record, _56_727) -> begin
(
# 421 "FStar.Parser.ToSyntax.fst"
let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _56_731 -> (match (_56_731) with
| (f, p) -> begin
(let _145_276 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.qualify_field_to_record env record) f)
in (_145_276, p))
end))))
in (
# 423 "FStar.Parser.ToSyntax.fst"
let args = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _56_736 -> (match (_56_736) with
| (f, _56_735) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _56_740 -> (match (_56_740) with
| (g, _56_739) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_56_743, p) -> begin
p
end)
end))))
in (
# 427 "FStar.Parser.ToSyntax.fst"
let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_Env.constrname)) p.FStar_Parser_AST.prange), args))) p.FStar_Parser_AST.prange)
in (
# 428 "FStar.Parser.ToSyntax.fst"
let _56_755 = (aux loc env app)
in (match (_56_755) with
| (env, e, b, p, _56_754) -> begin
(
# 429 "FStar.Parser.ToSyntax.fst"
let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(let _145_285 = (let _145_284 = (let _145_283 = (
# 430 "FStar.Parser.ToSyntax.fst"
let _56_760 = fv
in (let _145_282 = (let _145_281 = (let _145_280 = (let _145_279 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _145_279))
in FStar_Syntax_Syntax.Record_ctor (_145_280))
in Some (_145_281))
in {FStar_Syntax_Syntax.fv_name = _56_760.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = _56_760.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _145_282}))
in (_145_283, args))
in FStar_Syntax_Syntax.Pat_cons (_145_284))
in (FStar_All.pipe_left pos _145_285))
end
| _56_763 -> begin
p
end)
in (env, e, b, p, false))
end)))))
end))
end))
end))))
in (
# 434 "FStar.Parser.ToSyntax.fst"
let _56_772 = (aux [] env p)
in (match (_56_772) with
| (_56_766, env, b, p, _56_771) -> begin
(
# 435 "FStar.Parser.ToSyntax.fst"
let _56_773 = (let _145_286 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore _145_286))
in (env, b, p))
end)))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _56_780) -> begin
(let _145_292 = (let _145_291 = (let _145_290 = (FStar_Parser_Env.qualify env x)
in (_145_290, FStar_Syntax_Syntax.tun))
in LetBinder (_145_291))
in (env, _145_292, None))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _56_787); FStar_Parser_AST.prange = _56_784}, t) -> begin
(let _145_296 = (let _145_295 = (let _145_294 = (FStar_Parser_Env.qualify env x)
in (let _145_293 = (desugar_term env t)
in (_145_294, _145_293)))
in LetBinder (_145_295))
in (env, _145_296, None))
end
| _56_795 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern at the top-level", p.FStar_Parser_AST.prange))))
end)
end else begin
(
# 446 "FStar.Parser.ToSyntax.fst"
let _56_799 = (desugar_data_pat env p)
in (match (_56_799) with
| (env, binder, p) -> begin
(
# 447 "FStar.Parser.ToSyntax.fst"
let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| _56_807 -> begin
Some (p)
end)
in (env, binder, p))
end))
end)
and desugar_binding_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun _56_811 env pat -> (
# 456 "FStar.Parser.ToSyntax.fst"
let _56_819 = (desugar_data_pat env pat)
in (match (_56_819) with
| (env, _56_817, pat) -> begin
(env, pat)
end)))
and desugar_match_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (
# 462 "FStar.Parser.ToSyntax.fst"
let env = (
# 462 "FStar.Parser.ToSyntax.fst"
let _56_824 = env
in {FStar_Parser_Env.curmodule = _56_824.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _56_824.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _56_824.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _56_824.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _56_824.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _56_824.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _56_824.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _56_824.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _56_824.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _56_824.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _56_824.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (
# 466 "FStar.Parser.ToSyntax.fst"
let env = (
# 466 "FStar.Parser.ToSyntax.fst"
let _56_829 = env
in {FStar_Parser_Env.curmodule = _56_829.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _56_829.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _56_829.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _56_829.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _56_829.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _56_829.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _56_829.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _56_829.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _56_829.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _56_829.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _56_829.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (
# 470 "FStar.Parser.ToSyntax.fst"
let mk = (fun e -> (FStar_Syntax_Syntax.mk e None top.FStar_Parser_AST.range))
in (
# 471 "FStar.Parser.ToSyntax.fst"
let setpos = (fun e -> (
# 471 "FStar.Parser.ToSyntax.fst"
let _56_839 = e
in {FStar_Syntax_Syntax.n = _56_839.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _56_839.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _56_839.FStar_Syntax_Syntax.vars}))
in (match ((let _145_315 = (unparen top)
in _145_315.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (_56_843) -> begin
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
| FStar_Parser_AST.Op ("*", _56_863::_56_861::[]) when (let _145_316 = (op_as_term env 2 top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right _145_316 FStar_Option.isNone)) -> begin
(
# 489 "FStar.Parser.ToSyntax.fst"
let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", t1::t2::[]) -> begin
(
# 491 "FStar.Parser.ToSyntax.fst"
let rest = (flatten t2)
in (t1)::rest)
end
| _56_877 -> begin
(t)::[]
end))
in (
# 494 "FStar.Parser.ToSyntax.fst"
let targs = (let _145_322 = (let _145_319 = (unparen top)
in (flatten _145_319))
in (FStar_All.pipe_right _145_322 (FStar_List.map (fun t -> (let _145_321 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg _145_321))))))
in (
# 495 "FStar.Parser.ToSyntax.fst"
let tup = (let _145_323 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) _145_323))
in (mk (FStar_Syntax_Syntax.Tm_app ((tup, targs)))))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _145_324 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) a)
in (FStar_All.pipe_left setpos _145_324))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Unexpected operator: " s), top.FStar_Parser_AST.range))))
end
| Some (op) -> begin
(
# 505 "FStar.Parser.ToSyntax.fst"
let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _145_326 = (desugar_term env t)
in (_145_326, None)))))
in (mk (FStar_Syntax_Syntax.Tm_app ((op, args)))))
end)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _56_898; FStar_Ident.ident = _56_896; FStar_Ident.nsstr = _56_894; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _56_907; FStar_Ident.ident = _56_905; FStar_Ident.nsstr = _56_903; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _56_916; FStar_Ident.ident = _56_914; FStar_Ident.nsstr = _56_912; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _56_925; FStar_Ident.ident = _56_923; FStar_Ident.nsstr = _56_921; FStar_Ident.str = "True"}) -> begin
(let _145_327 = (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _145_327 FStar_Syntax_Syntax.Delta_constant None))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _56_934; FStar_Ident.ident = _56_932; FStar_Ident.nsstr = _56_930; FStar_Ident.str = "False"}) -> begin
(let _145_328 = (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _145_328 FStar_Syntax_Syntax.Delta_constant None))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(let _145_329 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (FStar_All.pipe_left setpos _145_329))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(
# 520 "FStar.Parser.ToSyntax.fst"
let _56_949 = (match ((FStar_Parser_Env.try_lookup_datacon env l)) with
| None -> begin
(let _145_330 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (_145_330, false))
end
| Some (head) -> begin
(let _145_331 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in (_145_331, true))
end)
in (match (_56_949) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| _56_952 -> begin
(
# 526 "FStar.Parser.ToSyntax.fst"
let args = (FStar_List.map (fun _56_955 -> (match (_56_955) with
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
let _56_983 = (FStar_List.fold_left (fun _56_966 b -> (match (_56_966) with
| (env, tparams, typs) -> begin
(
# 537 "FStar.Parser.ToSyntax.fst"
let _56_970 = (desugar_binder env b)
in (match (_56_970) with
| (xopt, t) -> begin
(
# 538 "FStar.Parser.ToSyntax.fst"
let _56_976 = (match (xopt) with
| None -> begin
(let _145_335 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (env, _145_335))
end
| Some (x) -> begin
(FStar_Parser_Env.push_bv env x)
end)
in (match (_56_976) with
| (env, x) -> begin
(let _145_339 = (let _145_338 = (let _145_337 = (let _145_336 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _145_336))
in (_145_337)::[])
in (FStar_List.append typs _145_338))
in (env, (FStar_List.append tparams ((((
# 542 "FStar.Parser.ToSyntax.fst"
let _56_977 = x
in {FStar_Syntax_Syntax.ppname = _56_977.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_977.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), None))::[])), _145_339))
end))
end))
end)) (env, [], []) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_56_983) with
| (env, _56_981, targs) -> begin
(
# 545 "FStar.Parser.ToSyntax.fst"
let tup = (let _145_340 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) _145_340))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app ((tup, targs)))))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(
# 549 "FStar.Parser.ToSyntax.fst"
let _56_991 = (uncurry binders t)
in (match (_56_991) with
| (bs, t) -> begin
(
# 550 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun env bs _56_8 -> (match (_56_8) with
| [] -> begin
(
# 552 "FStar.Parser.ToSyntax.fst"
let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (let _145_347 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos _145_347)))
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
let _56_1005 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_56_1005) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_binder env b)) with
| (None, _56_1012) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(
# 567 "FStar.Parser.ToSyntax.fst"
let _56_1020 = (as_binder env None b)
in (match (_56_1020) with
| ((x, _56_1017), env) -> begin
(
# 568 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env f)
in (let _145_348 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos _145_348)))
end))
end)
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(
# 573 "FStar.Parser.ToSyntax.fst"
let _56_1040 = (FStar_List.fold_left (fun _56_1028 pat -> (match (_56_1028) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (_56_1031, t) -> begin
(let _145_352 = (let _145_351 = (free_type_vars env t)
in (FStar_List.append _145_351 ftvs))
in (env, _145_352))
end
| _56_1036 -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_56_1040) with
| (_56_1038, ftv) -> begin
(
# 577 "FStar.Parser.ToSyntax.fst"
let ftv = (sort_ftv ftv)
in (
# 578 "FStar.Parser.ToSyntax.fst"
let binders = (let _145_354 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar ((a, Some (FStar_Parser_AST.Implicit)))) top.FStar_Parser_AST.range))))
in (FStar_List.append _145_354 binders))
in (
# 587 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun env bs sc_pat_opt _56_9 -> (match (_56_9) with
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
let body = (let _145_364 = (let _145_363 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right _145_363 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close _145_364 body))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((sc, ((pat, None, body))::[]))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (let _145_365 = (no_annot_abs (FStar_List.rev bs) body)
in (setpos _145_365))))
end
| p::rest -> begin
(
# 598 "FStar.Parser.ToSyntax.fst"
let _56_1064 = (desugar_binding_pat env p)
in (match (_56_1064) with
| (env, b, pat) -> begin
(
# 599 "FStar.Parser.ToSyntax.fst"
let _56_1115 = (match (b) with
| LetBinder (_56_1066) -> begin
(FStar_All.failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(
# 602 "FStar.Parser.ToSyntax.fst"
let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _56_1074) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _145_367 = (let _145_366 = (FStar_Syntax_Syntax.bv_to_name x)
in (_145_366, p))
in Some (_145_367))
end
| (Some (p), Some (sc, p')) -> begin
(match ((sc.FStar_Syntax_Syntax.n, p'.FStar_Syntax_Syntax.v)) with
| (FStar_Syntax_Syntax.Tm_name (_56_1088), _56_1091) -> begin
(
# 608 "FStar.Parser.ToSyntax.fst"
let tup2 = (let _145_368 = (FStar_Syntax_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _145_368 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (
# 609 "FStar.Parser.ToSyntax.fst"
let sc = (let _145_376 = (let _145_375 = (let _145_374 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (let _145_373 = (let _145_372 = (FStar_Syntax_Syntax.as_arg sc)
in (let _145_371 = (let _145_370 = (let _145_369 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _145_369))
in (_145_370)::[])
in (_145_372)::_145_371))
in (_145_374, _145_373)))
in FStar_Syntax_Syntax.Tm_app (_145_375))
in (FStar_Syntax_Syntax.mk _145_376 None top.FStar_Parser_AST.range))
in (
# 610 "FStar.Parser.ToSyntax.fst"
let p = (let _145_377 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tup2, ((p', false))::((p, false))::[]))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _145_377))
in Some ((sc, p)))))
end
| (FStar_Syntax_Syntax.Tm_app (_56_1097, args), FStar_Syntax_Syntax.Pat_cons (_56_1102, pats)) -> begin
(
# 613 "FStar.Parser.ToSyntax.fst"
let tupn = (let _145_378 = (FStar_Syntax_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _145_378 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (
# 614 "FStar.Parser.ToSyntax.fst"
let sc = (let _145_385 = (let _145_384 = (let _145_383 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (let _145_382 = (let _145_381 = (let _145_380 = (let _145_379 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _145_379))
in (_145_380)::[])
in (FStar_List.append args _145_381))
in (_145_383, _145_382)))
in FStar_Syntax_Syntax.Tm_app (_145_384))
in (mk _145_385))
in (
# 615 "FStar.Parser.ToSyntax.fst"
let p = (let _145_386 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tupn, (FStar_List.append pats (((p, false))::[]))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _145_386))
in Some ((sc, p)))))
end
| _56_1111 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((x, aq), sc_pat_opt))
end)
in (match (_56_1115) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _56_1119; FStar_Parser_AST.level = _56_1117}, phi, _56_1125) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(
# 626 "FStar.Parser.ToSyntax.fst"
let phi = (desugar_formula env phi)
in (let _145_394 = (let _145_393 = (let _145_392 = (FStar_Syntax_Syntax.fvar a FStar_Syntax_Syntax.Delta_equational None)
in (let _145_391 = (let _145_390 = (FStar_Syntax_Syntax.as_arg phi)
in (let _145_389 = (let _145_388 = (let _145_387 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _145_387))
in (_145_388)::[])
in (_145_390)::_145_389))
in (_145_392, _145_391)))
in FStar_Syntax_Syntax.Tm_app (_145_393))
in (mk _145_394)))
end
| FStar_Parser_AST.App (_56_1130) -> begin
(
# 632 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun args e -> (match ((let _145_399 = (unparen e)
in _145_399.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(
# 634 "FStar.Parser.ToSyntax.fst"
let arg = (let _145_400 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _145_400))
in (aux ((arg)::args) e))
end
| _56_1142 -> begin
(
# 637 "FStar.Parser.ToSyntax.fst"
let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app ((head, args)))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _145_403 = (let _145_402 = (let _145_401 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range), t1))::[], t2))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in (_145_401, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))
in FStar_Syntax_Syntax.Tm_meta (_145_402))
in (mk _145_403))
end
| FStar_Parser_AST.Let (is_rec, (pat, _snd)::_tl, body) -> begin
(
# 646 "FStar.Parser.ToSyntax.fst"
let ds_let_rec_or_app = (fun _56_1158 -> (match (()) with
| () -> begin
(
# 647 "FStar.Parser.ToSyntax.fst"
let bindings = ((pat, _snd))::_tl
in (
# 648 "FStar.Parser.ToSyntax.fst"
let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _56_1162 -> (match (_56_1162) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _145_407 = (destruct_app_pattern env top_level p)
in (_145_407, def))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _145_408 = (destruct_app_pattern env top_level p)
in (_145_408, def))
end
| _56_1168 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _56_1173); FStar_Parser_AST.prange = _56_1170}, t) -> begin
if top_level then begin
(let _145_411 = (let _145_410 = (let _145_409 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_145_409))
in (_145_410, [], Some (t)))
in (_145_411, def))
end else begin
((FStar_Util.Inl (id), [], Some (t)), def)
end
end
| FStar_Parser_AST.PatVar (id, _56_1182) -> begin
if top_level then begin
(let _145_414 = (let _145_413 = (let _145_412 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_145_412))
in (_145_413, [], None))
in (_145_414, def))
end else begin
((FStar_Util.Inl (id), [], None), def)
end
end
| _56_1186 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected let binding", p.FStar_Parser_AST.prange))))
end)
end)
end
end))))
in (
# 665 "FStar.Parser.ToSyntax.fst"
let _56_1215 = (FStar_List.fold_left (fun _56_1191 _56_1200 -> (match ((_56_1191, _56_1200)) with
| ((env, fnames, rec_bindings), ((f, _56_1194, _56_1196), _56_1199)) -> begin
(
# 667 "FStar.Parser.ToSyntax.fst"
let _56_1211 = (match (f) with
| FStar_Util.Inl (x) -> begin
(
# 669 "FStar.Parser.ToSyntax.fst"
let _56_1205 = (FStar_Parser_Env.push_bv env x)
in (match (_56_1205) with
| (env, xx) -> begin
(let _145_418 = (let _145_417 = (FStar_Syntax_Syntax.mk_binder xx)
in (_145_417)::rec_bindings)
in (env, FStar_Util.Inl (xx), _145_418))
end))
end
| FStar_Util.Inr (l) -> begin
(let _145_419 = (FStar_Parser_Env.push_top_level_rec_binding env l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in (_145_419, FStar_Util.Inr (l), rec_bindings))
end)
in (match (_56_1211) with
| (env, lbname, rec_bindings) -> begin
(env, (lbname)::fnames, rec_bindings)
end))
end)) (env, [], []) funs)
in (match (_56_1215) with
| (env', fnames, rec_bindings) -> begin
(
# 675 "FStar.Parser.ToSyntax.fst"
let fnames = (FStar_List.rev fnames)
in (
# 677 "FStar.Parser.ToSyntax.fst"
let desugar_one_def = (fun env lbname _56_1226 -> (match (_56_1226) with
| ((_56_1221, args, result_t), def) -> begin
(
# 678 "FStar.Parser.ToSyntax.fst"
let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _145_426 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed ((def, t))) _145_426 FStar_Parser_AST.Expr))
end)
in (
# 681 "FStar.Parser.ToSyntax.fst"
let def = (match (args) with
| [] -> begin
def
end
| _56_1233 -> begin
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
(let _145_428 = (let _145_427 = (incr_delta_qualifier body)
in (FStar_Syntax_Syntax.lid_as_fv l _145_427 None))
in FStar_Util.Inr (_145_428))
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
in (let _145_431 = (let _145_430 = (let _145_429 = (FStar_Syntax_Subst.close rec_bindings body)
in ((is_rec, lbs), _145_429))
in FStar_Syntax_Syntax.Tm_let (_145_430))
in (FStar_All.pipe_left mk _145_431))))))
end))))
end))
in (
# 695 "FStar.Parser.ToSyntax.fst"
let ds_non_rec = (fun pat t1 t2 -> (
# 696 "FStar.Parser.ToSyntax.fst"
let t1 = (desugar_term env t1)
in (
# 697 "FStar.Parser.ToSyntax.fst"
let _56_1252 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_56_1252) with
| (env, binder, pat) -> begin
(match (binder) with
| LetBinder (l, t) -> begin
(
# 700 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env t2)
in (
# 701 "FStar.Parser.ToSyntax.fst"
let fv = (let _145_438 = (incr_delta_qualifier t1)
in (FStar_Syntax_Syntax.lid_as_fv l _145_438 None))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]), body))))))
end
| LocalBinder (x, _56_1261) -> begin
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
(let _145_443 = (let _145_442 = (let _145_441 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _145_440 = (let _145_439 = (FStar_Syntax_Util.branch (pat, None, body))
in (_145_439)::[])
in (_145_441, _145_440)))
in FStar_Syntax_Syntax.Tm_match (_145_442))
in (FStar_Syntax_Syntax.mk _145_443 None body.FStar_Syntax_Syntax.pos))
end)
in (let _145_448 = (let _145_447 = (let _145_446 = (let _145_445 = (let _145_444 = (FStar_Syntax_Syntax.mk_binder x)
in (_145_444)::[])
in (FStar_Syntax_Subst.close _145_445 body))
in ((false, ((mk_lb (FStar_Util.Inl (x), x.FStar_Syntax_Syntax.sort, t1)))::[]), _145_446))
in FStar_Syntax_Syntax.Tm_let (_145_447))
in (FStar_All.pipe_left mk _145_448))))
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
in (let _145_459 = (let _145_458 = (let _145_457 = (desugar_term env t1)
in (let _145_456 = (let _145_455 = (let _145_450 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (let _145_449 = (desugar_term env t2)
in (_145_450, None, _145_449)))
in (let _145_454 = (let _145_453 = (let _145_452 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (let _145_451 = (desugar_term env t3)
in (_145_452, None, _145_451)))
in (_145_453)::[])
in (_145_455)::_145_454))
in (_145_457, _145_456)))
in FStar_Syntax_Syntax.Tm_match (_145_458))
in (mk _145_459)))
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
let desugar_branch = (fun _56_1301 -> (match (_56_1301) with
| (pat, wopt, b) -> begin
(
# 735 "FStar.Parser.ToSyntax.fst"
let _56_1304 = (desugar_match_pat env pat)
in (match (_56_1304) with
| (env, pat) -> begin
(
# 736 "FStar.Parser.ToSyntax.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _145_462 = (desugar_term env e)
in Some (_145_462))
end)
in (
# 739 "FStar.Parser.ToSyntax.fst"
let b = (desugar_term env b)
in (FStar_Syntax_Util.branch (pat, wopt, b))))
end))
end))
in (let _145_466 = (let _145_465 = (let _145_464 = (desugar_term env e)
in (let _145_463 = (FStar_List.map desugar_branch branches)
in (_145_464, _145_463)))
in FStar_Syntax_Syntax.Tm_match (_145_465))
in (FStar_All.pipe_left mk _145_466)))
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
in (let _145_469 = (let _145_468 = (let _145_467 = (desugar_term env e)
in (_145_467, annot, None))
in FStar_Syntax_Syntax.Tm_ascribed (_145_468))
in (FStar_All.pipe_left mk _145_469)))))
end
| FStar_Parser_AST.Record (_56_1318, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected empty record", top.FStar_Parser_AST.range))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(
# 755 "FStar.Parser.ToSyntax.fst"
let _56_1329 = (FStar_List.hd fields)
in (match (_56_1329) with
| (f, _56_1328) -> begin
(
# 756 "FStar.Parser.ToSyntax.fst"
let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (
# 757 "FStar.Parser.ToSyntax.fst"
let _56_1335 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_56_1335) with
| (record, _56_1334) -> begin
(
# 758 "FStar.Parser.ToSyntax.fst"
let get_field = (fun xopt f -> (
# 759 "FStar.Parser.ToSyntax.fst"
let fn = f.FStar_Ident.ident
in (
# 760 "FStar.Parser.ToSyntax.fst"
let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _56_1343 -> (match (_56_1343) with
| (g, _56_1342) -> begin
(
# 761 "FStar.Parser.ToSyntax.fst"
let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_56_1347, e) -> begin
(let _145_477 = (qfn fn)
in (_145_477, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _145_480 = (let _145_479 = (let _145_478 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in (_145_478, top.FStar_Parser_AST.range))
in FStar_Syntax_Syntax.Error (_145_479))
in (Prims.raise _145_480))
end
| Some (x) -> begin
(let _145_481 = (qfn fn)
in (_145_481, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Project ((x, f))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end))))
in (
# 772 "FStar.Parser.ToSyntax.fst"
let recterm = (match (eopt) with
| None -> begin
(let _145_486 = (let _145_485 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _56_1359 -> (match (_56_1359) with
| (f, _56_1358) -> begin
(let _145_484 = (let _145_483 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _145_483))
in (_145_484, FStar_Parser_AST.Nothing))
end))))
in (record.FStar_Parser_Env.constrname, _145_485))
in FStar_Parser_AST.Construct (_145_486))
end
| Some (e) -> begin
(
# 779 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (
# 780 "FStar.Parser.ToSyntax.fst"
let xterm = (let _145_488 = (let _145_487 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_145_487))
in (FStar_Parser_AST.mk_term _145_488 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (
# 781 "FStar.Parser.ToSyntax.fst"
let record = (let _145_491 = (let _145_490 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _56_1367 -> (match (_56_1367) with
| (f, _56_1366) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _145_490))
in FStar_Parser_AST.Record (_145_491))
in FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar ((x, None))) x.FStar_Ident.idRange), e))::[], (FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level))))))
end)
in (
# 784 "FStar.Parser.ToSyntax.fst"
let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (
# 785 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _56_1383; FStar_Syntax_Syntax.pos = _56_1381; FStar_Syntax_Syntax.vars = _56_1379}, args); FStar_Syntax_Syntax.tk = _56_1377; FStar_Syntax_Syntax.pos = _56_1375; FStar_Syntax_Syntax.vars = _56_1373}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(
# 788 "FStar.Parser.ToSyntax.fst"
let e = (let _145_499 = (let _145_498 = (let _145_497 = (let _145_496 = (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos)
in (let _145_495 = (let _145_494 = (let _145_493 = (let _145_492 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _145_492))
in FStar_Syntax_Syntax.Record_ctor (_145_493))
in Some (_145_494))
in (FStar_Syntax_Syntax.fvar _145_496 FStar_Syntax_Syntax.Delta_constant _145_495)))
in (_145_497, args))
in FStar_Syntax_Syntax.Tm_app (_145_498))
in (FStar_All.pipe_left mk _145_499))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end
| _56_1397 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(
# 796 "FStar.Parser.ToSyntax.fst"
let _56_1404 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_projector_by_field_name env) f)
in (match (_56_1404) with
| (fieldname, is_rec) -> begin
(
# 797 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env e)
in (
# 798 "FStar.Parser.ToSyntax.fst"
let fn = (
# 799 "FStar.Parser.ToSyntax.fst"
let _56_1409 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_56_1409) with
| (ns, _56_1408) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (
# 801 "FStar.Parser.ToSyntax.fst"
let qual = if is_rec then begin
Some (FStar_Syntax_Syntax.Record_projector (fn))
end else begin
None
end
in (let _145_505 = (let _145_504 = (let _145_503 = (let _145_500 = (FStar_Ident.set_lid_range fieldname (FStar_Ident.range_of_lid f))
in (FStar_Syntax_Syntax.fvar _145_500 FStar_Syntax_Syntax.Delta_equational qual))
in (let _145_502 = (let _145_501 = (FStar_Syntax_Syntax.as_arg e)
in (_145_501)::[])
in (_145_503, _145_502)))
in FStar_Syntax_Syntax.Tm_app (_145_504))
in (FStar_All.pipe_left mk _145_505)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| _56_1419 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _56_1421 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_args : FStar_Parser_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun _56_1426 -> (match (_56_1426) with
| (a, imp) -> begin
(let _145_509 = (desugar_term env a)
in (arg_withimp_e imp _145_509))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r default_ok env t -> (
# 818 "FStar.Parser.ToSyntax.fst"
let fail = (fun msg -> (Prims.raise (FStar_Syntax_Syntax.Error ((msg, r)))))
in (
# 819 "FStar.Parser.ToSyntax.fst"
let is_requires = (fun _56_1438 -> (match (_56_1438) with
| (t, _56_1437) -> begin
(match ((let _145_517 = (unparen t)
in _145_517.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Requires (_56_1440) -> begin
true
end
| _56_1443 -> begin
false
end)
end))
in (
# 822 "FStar.Parser.ToSyntax.fst"
let is_ensures = (fun _56_1448 -> (match (_56_1448) with
| (t, _56_1447) -> begin
(match ((let _145_520 = (unparen t)
in _145_520.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ensures (_56_1450) -> begin
true
end
| _56_1453 -> begin
false
end)
end))
in (
# 825 "FStar.Parser.ToSyntax.fst"
let is_app = (fun head _56_1459 -> (match (_56_1459) with
| (t, _56_1458) -> begin
(match ((let _145_525 = (unparen t)
in _145_525.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _56_1463; FStar_Parser_AST.level = _56_1461}, _56_1468, _56_1470) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| _56_1474 -> begin
false
end)
end))
in (
# 828 "FStar.Parser.ToSyntax.fst"
let pre_process_comp_typ = (fun t -> (
# 829 "FStar.Parser.ToSyntax.fst"
let _56_1479 = (head_and_args t)
in (match (_56_1479) with
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
(let _145_528 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_name env) l)
in (_145_528, args))
end
| FStar_Parser_AST.Name (l) when ((let _145_529 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _145_529 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(let _145_530 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in (_145_530, args))
end
| FStar_Parser_AST.Name (l) when ((let _145_531 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _145_531 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(let _145_532 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)
in (_145_532, args))
end
| FStar_Parser_AST.Name (l) when ((((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) && default_ok) -> begin
(let _145_533 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in (_145_533, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _56_1507 when default_ok -> begin
(let _145_534 = (FStar_Ident.set_lid_range env.FStar_Parser_Env.default_result_effect head.FStar_Parser_AST.range)
in (_145_534, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _56_1509 -> begin
(let _145_536 = (let _145_535 = (FStar_Parser_AST.term_to_string t)
in (FStar_Util.format1 "%s is not an effect" _145_535))
in (fail _145_536))
end)
end)))
in (
# 872 "FStar.Parser.ToSyntax.fst"
let _56_1512 = (pre_process_comp_typ t)
in (match (_56_1512) with
| (eff, args) -> begin
(
# 873 "FStar.Parser.ToSyntax.fst"
let _56_1513 = if ((FStar_List.length args) = 0) then begin
(let _145_538 = (let _145_537 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" _145_537))
in (fail _145_538))
end else begin
()
end
in (
# 875 "FStar.Parser.ToSyntax.fst"
let _56_1517 = (let _145_540 = (FStar_List.hd args)
in (let _145_539 = (FStar_List.tl args)
in (_145_540, _145_539)))
in (match (_56_1517) with
| (result_arg, rest) -> begin
(
# 876 "FStar.Parser.ToSyntax.fst"
let result_typ = (desugar_typ env (Prims.fst result_arg))
in (
# 877 "FStar.Parser.ToSyntax.fst"
let rest = (desugar_args env rest)
in (
# 878 "FStar.Parser.ToSyntax.fst"
let _56_1542 = (FStar_All.pipe_right rest (FStar_List.partition (fun _56_1523 -> (match (_56_1523) with
| (t, _56_1522) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _56_1529; FStar_Syntax_Syntax.pos = _56_1527; FStar_Syntax_Syntax.vars = _56_1525}, _56_1534::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| _56_1539 -> begin
false
end)
end))))
in (match (_56_1542) with
| (dec, rest) -> begin
(
# 884 "FStar.Parser.ToSyntax.fst"
let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _56_1546 -> (match (_56_1546) with
| (t, _56_1545) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_56_1548, (arg, _56_1551)::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| _56_1557 -> begin
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
let pattern = (let _145_544 = (let _145_543 = (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _145_543 FStar_Syntax_Syntax.Delta_constant None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _145_544 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app nil (((pattern, Some (FStar_Syntax_Syntax.imp_tag)))::[]) None pat.FStar_Syntax_Syntax.pos)))
end
| _56_1572 -> begin
pat
end)
in (let _145_548 = (let _145_547 = (let _145_546 = (let _145_545 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((pat, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)))) None pat.FStar_Syntax_Syntax.pos)
in (_145_545, aq))
in (_145_546)::[])
in (ens)::_145_547)
in (req)::_145_548))
end
| _56_1575 -> begin
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
| _56_1587 -> begin
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
let _56_1594 = t
in {FStar_Syntax_Syntax.n = _56_1594.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _56_1594.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _56_1594.FStar_Syntax_Syntax.vars}))
in (
# 932 "FStar.Parser.ToSyntax.fst"
let desugar_quant = (fun q b pats body -> (
# 933 "FStar.Parser.ToSyntax.fst"
let tk = (desugar_binder env (
# 933 "FStar.Parser.ToSyntax.fst"
let _56_1601 = b
in {FStar_Parser_AST.b = _56_1601.FStar_Parser_AST.b; FStar_Parser_AST.brange = _56_1601.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _56_1601.FStar_Parser_AST.aqual}))
in (
# 934 "FStar.Parser.ToSyntax.fst"
let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _145_583 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _145_583)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(
# 937 "FStar.Parser.ToSyntax.fst"
let _56_1615 = (FStar_Parser_Env.push_bv env a)
in (match (_56_1615) with
| (env, a) -> begin
(
# 938 "FStar.Parser.ToSyntax.fst"
let a = (
# 938 "FStar.Parser.ToSyntax.fst"
let _56_1616 = a
in {FStar_Syntax_Syntax.ppname = _56_1616.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1616.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
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
| _56_1623 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((body, FStar_Syntax_Syntax.Meta_pattern (pats)))))
end)
in (
# 944 "FStar.Parser.ToSyntax.fst"
let body = (let _145_586 = (let _145_585 = (let _145_584 = (FStar_Syntax_Syntax.mk_binder a)
in (_145_584)::[])
in (no_annot_abs _145_585 body))
in (FStar_All.pipe_left setpos _145_586))
in (let _145_592 = (let _145_591 = (let _145_590 = (let _145_587 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Syntax_Syntax.fvar _145_587 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (let _145_589 = (let _145_588 = (FStar_Syntax_Syntax.as_arg body)
in (_145_588)::[])
in (_145_590, _145_589)))
in FStar_Syntax_Syntax.Tm_app (_145_591))
in (FStar_All.pipe_left mk _145_592)))))))
end))
end
| _56_1627 -> begin
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
let body = (let _145_607 = (q (rest, pats, body))
in (let _145_606 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _145_607 _145_606 FStar_Parser_AST.Formula)))
in (let _145_608 = (q ((b)::[], [], body))
in (FStar_Parser_AST.mk_term _145_608 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _56_1641 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _145_609 = (unparen f)
in _145_609.FStar_Parser_AST.tm)) with
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
in (let _145_611 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _145_611)))
end
| FStar_Parser_AST.QExists (_1::_2::_3, pats, body) -> begin
(
# 969 "FStar.Parser.ToSyntax.fst"
let binders = (_1)::(_2)::_3
in (let _145_613 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _145_613)))
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
| _56_1699 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (
# 984 "FStar.Parser.ToSyntax.fst"
let _56_1723 = (FStar_List.fold_left (fun _56_1704 b -> (match (_56_1704) with
| (env, out) -> begin
(
# 985 "FStar.Parser.ToSyntax.fst"
let tk = (desugar_binder env (
# 985 "FStar.Parser.ToSyntax.fst"
let _56_1706 = b
in {FStar_Parser_AST.b = _56_1706.FStar_Parser_AST.b; FStar_Parser_AST.brange = _56_1706.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _56_1706.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(
# 988 "FStar.Parser.ToSyntax.fst"
let _56_1715 = (FStar_Parser_Env.push_bv env a)
in (match (_56_1715) with
| (env, a) -> begin
(
# 989 "FStar.Parser.ToSyntax.fst"
let a = (
# 989 "FStar.Parser.ToSyntax.fst"
let _56_1716 = a
in {FStar_Syntax_Syntax.ppname = _56_1716.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1716.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (env, ((a, (trans_aqual b.FStar_Parser_AST.aqual)))::out))
end))
end
| _56_1720 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected binder", b.FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_56_1723) with
| (env, tpars) -> begin
(env, (FStar_List.rev tpars))
end)))
and desugar_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(let _145_620 = (desugar_typ env t)
in (Some (x), _145_620))
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _145_621 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None x.FStar_Ident.idRange)
in (Some (x), _145_621))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _145_622 = (desugar_typ env t)
in (None, _145_622))
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
let binders = (let _145_638 = (let _145_637 = (FStar_Syntax_Util.arrow_formals k)
in (Prims.fst _145_637))
in (FStar_List.append tps _145_638))
in (
# 1006 "FStar.Parser.ToSyntax.fst"
let p = (FStar_Ident.range_of_lid t)
in (
# 1007 "FStar.Parser.ToSyntax.fst"
let _56_1750 = (FStar_Syntax_Util.args_of_binders binders)
in (match (_56_1750) with
| (binders, args) -> begin
(
# 1008 "FStar.Parser.ToSyntax.fst"
let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _56_1754 -> (match (_56_1754) with
| (x, _56_1753) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
in (
# 1009 "FStar.Parser.ToSyntax.fst"
let binders = (let _145_644 = (let _145_643 = (let _145_642 = (let _145_641 = (let _145_640 = (FStar_Syntax_Syntax.lid_as_fv t FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _145_640))
in (FStar_Syntax_Syntax.mk_Tm_app _145_641 args None p))
in (FStar_All.pipe_left FStar_Syntax_Syntax.null_binder _145_642))
in (_145_643)::[])
in (FStar_List.append imp_binders _145_644))
in (
# 1010 "FStar.Parser.ToSyntax.fst"
let disc_type = (let _145_647 = (let _145_646 = (let _145_645 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _145_645))
in (FStar_Syntax_Syntax.mk_Total _145_646))
in (FStar_Syntax_Util.arrow binders _145_647))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (
# 1012 "FStar.Parser.ToSyntax.fst"
let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (let _145_650 = (let _145_649 = (quals ((FStar_Syntax_Syntax.Logic)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in (disc_name, [], disc_type, _145_649, (FStar_Ident.range_of_lid disc_name)))
in FStar_Syntax_Syntax.Sig_declare_typ (_145_650)))))))))
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
let tps = (FStar_List.map2 (fun _56_1778 _56_1782 -> (match ((_56_1778, _56_1782)) with
| ((_56_1776, imp), (x, _56_1781)) -> begin
(x, imp)
end)) inductive_tps imp_tps)
in (
# 1020 "FStar.Parser.ToSyntax.fst"
let _56_1883 = (
# 1021 "FStar.Parser.ToSyntax.fst"
let _56_1786 = (FStar_Syntax_Util.head_and_args t)
in (match (_56_1786) with
| (head, args0) -> begin
(
# 1022 "FStar.Parser.ToSyntax.fst"
let args = (
# 1023 "FStar.Parser.ToSyntax.fst"
let rec arguments = (fun tps args -> (match ((tps, args)) with
| ([], _56_1792) -> begin
args
end
| (_56_1795, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Not enough arguments to type", (FStar_Ident.range_of_lid lid)))))
end
| ((_56_1800, Some (FStar_Syntax_Syntax.Implicit (_56_1802)))::tps', (_56_1809, Some (FStar_Syntax_Syntax.Implicit (_56_1811)))::args') -> begin
(arguments tps' args')
end
| ((_56_1819, Some (FStar_Syntax_Syntax.Implicit (_56_1821)))::tps', (_56_1829, _56_1831)::_56_1827) -> begin
(arguments tps' args)
end
| ((_56_1838, _56_1840)::_56_1836, (a, Some (FStar_Syntax_Syntax.Implicit (_56_1847)))::_56_1844) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected implicit annotation on argument", a.FStar_Syntax_Syntax.pos))))
end
| ((_56_1855, _56_1857)::tps', (_56_1862, _56_1864)::args') -> begin
(arguments tps' args')
end))
in (arguments inductive_tps args0))
in (
# 1032 "FStar.Parser.ToSyntax.fst"
let indices = (FStar_All.pipe_right args (FStar_List.map (fun _56_1869 -> (let _145_682 = (FStar_Syntax_Syntax.new_bv (Some (p)) FStar_Syntax_Syntax.tun)
in (FStar_All.pipe_right _145_682 FStar_Syntax_Syntax.mk_binder)))))
in (
# 1033 "FStar.Parser.ToSyntax.fst"
let arg_typ = (let _145_687 = (let _145_683 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _145_683))
in (let _145_686 = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _56_1874 -> (match (_56_1874) with
| (x, imp) -> begin
(let _145_685 = (FStar_Syntax_Syntax.bv_to_name x)
in (_145_685, imp))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app _145_687 _145_686 None p)))
in (
# 1035 "FStar.Parser.ToSyntax.fst"
let arg_binder = if (not (refine_domain)) then begin
(let _145_688 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder _145_688))
end else begin
(
# 1038 "FStar.Parser.ToSyntax.fst"
let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (
# 1039 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p)) arg_typ)
in (let _145_697 = (
# 1040 "FStar.Parser.ToSyntax.fst"
let _56_1878 = (projectee arg_typ)
in (let _145_696 = (let _145_695 = (let _145_694 = (let _145_693 = (let _145_689 = (FStar_Ident.set_lid_range disc_name p)
in (FStar_Syntax_Syntax.fvar _145_689 FStar_Syntax_Syntax.Delta_equational None))
in (let _145_692 = (let _145_691 = (let _145_690 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _145_690))
in (_145_691)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _145_693 _145_692 None p)))
in (FStar_Syntax_Util.b2t _145_694))
in (FStar_Syntax_Util.refine x _145_695))
in {FStar_Syntax_Syntax.ppname = _56_1878.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1878.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_696}))
in (FStar_Syntax_Syntax.mk_binder _145_697))))
end
in (arg_binder, indices)))))
end))
in (match (_56_1883) with
| (arg_binder, indices) -> begin
(
# 1044 "FStar.Parser.ToSyntax.fst"
let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder))
in (
# 1045 "FStar.Parser.ToSyntax.fst"
let imp_binders = (let _145_699 = (FStar_All.pipe_right indices (FStar_List.map (fun _56_1888 -> (match (_56_1888) with
| (x, _56_1887) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
in (FStar_List.append imp_tps _145_699))
in (
# 1046 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (
# 1048 "FStar.Parser.ToSyntax.fst"
let arg = (FStar_Syntax_Util.arg_of_non_null_binder arg_binder)
in (
# 1050 "FStar.Parser.ToSyntax.fst"
let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _56_1896 -> (match (_56_1896) with
| (a, _56_1895) -> begin
(
# 1051 "FStar.Parser.ToSyntax.fst"
let _56_1900 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (_56_1900) with
| (field_name, _56_1899) -> begin
(
# 1052 "FStar.Parser.ToSyntax.fst"
let proj = (let _145_703 = (let _145_702 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.fv_to_tm _145_702))
in (FStar_Syntax_Syntax.mk_Tm_app _145_703 ((arg)::[]) None p))
in FStar_Syntax_Syntax.NT ((a, proj)))
end))
end))))
in (
# 1055 "FStar.Parser.ToSyntax.fst"
let ntps = (FStar_List.length tps)
in (
# 1056 "FStar.Parser.ToSyntax.fst"
let all_params = (FStar_List.append imp_tps fields)
in (let _145_739 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _56_1909 -> (match (_56_1909) with
| (x, _56_1908) -> begin
(
# 1059 "FStar.Parser.ToSyntax.fst"
let _56_1913 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_56_1913) with
| (field_name, _56_1912) -> begin
(
# 1060 "FStar.Parser.ToSyntax.fst"
let t = (let _145_707 = (let _145_706 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total _145_706))
in (FStar_Syntax_Util.arrow binders _145_707))
in (
# 1061 "FStar.Parser.ToSyntax.fst"
let only_decl = (((let _145_708 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _145_708)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _145_710 = (let _145_709 = (FStar_Parser_Env.current_module env)
in _145_709.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _145_710)))
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
let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _56_1925 -> (match (_56_1925) with
| (x, imp) -> begin
(
# 1073 "FStar.Parser.ToSyntax.fst"
let b = (FStar_Syntax_Syntax.is_implicit imp)
in if ((i + ntps) = j) then begin
(let _145_715 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in (_145_715, b))
end else begin
if (b && (j < ntps)) then begin
(let _145_719 = (let _145_718 = (let _145_717 = (let _145_716 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (_145_716, FStar_Syntax_Syntax.tun))
in FStar_Syntax_Syntax.Pat_dot_term (_145_717))
in (pos _145_718))
in (_145_719, b))
end else begin
(let _145_722 = (let _145_721 = (let _145_720 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_145_720))
in (pos _145_721))
in (_145_722, b))
end
end)
end))))
in (
# 1079 "FStar.Parser.ToSyntax.fst"
let pat = (let _145_727 = (let _145_725 = (let _145_724 = (let _145_723 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in (_145_723, arg_pats))
in FStar_Syntax_Syntax.Pat_cons (_145_724))
in (FStar_All.pipe_right _145_725 pos))
in (let _145_726 = (FStar_Syntax_Syntax.bv_to_name projection)
in (_145_727, None, _145_726)))
in (
# 1080 "FStar.Parser.ToSyntax.fst"
let body = (let _145_731 = (let _145_730 = (let _145_729 = (let _145_728 = (FStar_Syntax_Util.branch pat)
in (_145_728)::[])
in (arg_exp, _145_729))
in FStar_Syntax_Syntax.Tm_match (_145_730))
in (FStar_Syntax_Syntax.mk _145_731 None p))
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
let lb = (let _145_733 = (let _145_732 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (_145_732))
in {FStar_Syntax_Syntax.lbname = _145_733; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = imp})
in (
# 1090 "FStar.Parser.ToSyntax.fst"
let impl = (let _145_738 = (let _145_737 = (let _145_736 = (let _145_735 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _145_735 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_145_736)::[])
in ((false, (lb)::[]), p, _145_737, quals))
in FStar_Syntax_Syntax.Sig_let (_145_738))
in if no_decl then begin
(impl)::[]
end else begin
(decl)::(impl)::[]
end))))))))
end))))))
end))
end))))
in (FStar_All.pipe_right _145_739 FStar_List.flatten)))))))))
end)))))))

# 1093 "FStar.Parser.ToSyntax.fst"
let mk_data_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env _56_1939 -> (match (_56_1939) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _56_1942, t, l, n, quals, _56_1948, _56_1950) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(
# 1096 "FStar.Parser.ToSyntax.fst"
let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _56_10 -> (match (_56_10) with
| FStar_Syntax_Syntax.RecordConstructor (_56_1955) -> begin
true
end
| _56_1958 -> begin
false
end)))) then begin
false
end else begin
(match ((FStar_Parser_Env.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > 1)
end
| _56_1962 -> begin
true
end)
end
in (
# 1102 "FStar.Parser.ToSyntax.fst"
let _56_1966 = (FStar_Syntax_Util.arrow_formals t)
in (match (_56_1966) with
| (formals, cod) -> begin
(match (formals) with
| [] -> begin
[]
end
| _56_1969 -> begin
(
# 1106 "FStar.Parser.ToSyntax.fst"
let fv_qual = (match ((FStar_Util.find_map quals (fun _56_11 -> (match (_56_11) with
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((lid, fns)))
end
| _56_1974 -> begin
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
let _56_1982 = (FStar_Util.first_N n formals)
in (match (_56_1982) with
| (tps, rest) -> begin
(mk_indexed_projectors iquals fv_qual refine_domain env l lid inductive_tps tps rest cod)
end))))
end)
end)))
end
| _56_1984 -> begin
[]
end)
end))

# 1118 "FStar.Parser.ToSyntax.fst"
let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (
# 1119 "FStar.Parser.ToSyntax.fst"
let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _145_764 = (incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (_145_764))
end else begin
(incr_delta_qualifier t)
end
in (
# 1122 "FStar.Parser.ToSyntax.fst"
let lb = (let _145_769 = (let _145_765 = (FStar_Syntax_Syntax.lid_as_fv lid dd None)
in FStar_Util.Inr (_145_765))
in (let _145_768 = (let _145_766 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars _145_766))
in (let _145_767 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = _145_769; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = _145_768; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _145_767})))
in FStar_Syntax_Syntax.Sig_let (((false, (lb)::[]), rng, lids, quals)))))

# 1131 "FStar.Parser.ToSyntax.fst"
let rec desugar_tycon : FStar_Parser_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (
# 1132 "FStar.Parser.ToSyntax.fst"
let tycon_id = (fun _56_12 -> (match (_56_12) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (
# 1137 "FStar.Parser.ToSyntax.fst"
let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _145_783 = (let _145_782 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_145_782))
in (FStar_Parser_AST.mk_term _145_783 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
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
| _56_2059 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _145_796 = (let _145_795 = (let _145_794 = (binder_to_term b)
in (out, _145_794, (imp_of_aqual b)))
in FStar_Parser_AST.App (_145_795))
in (FStar_Parser_AST.mk_term _145_796 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (
# 1151 "FStar.Parser.ToSyntax.fst"
let tycon_record_as_variant = (fun _56_13 -> (match (_56_13) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(
# 1153 "FStar.Parser.ToSyntax.fst"
let constrName = (FStar_Ident.mk_ident ((Prims.strcat "Mk" id.FStar_Ident.idText), id.FStar_Ident.idRange))
in (
# 1154 "FStar.Parser.ToSyntax.fst"
let mfields = (FStar_List.map (fun _56_2072 -> (match (_56_2072) with
| (x, t) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated (((FStar_Syntax_Util.mangle_field_name x), t))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (
# 1155 "FStar.Parser.ToSyntax.fst"
let result = (let _145_802 = (let _145_801 = (let _145_800 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_145_800))
in (FStar_Parser_AST.mk_term _145_801 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _145_802 parms))
in (
# 1156 "FStar.Parser.ToSyntax.fst"
let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _145_804 = (FStar_All.pipe_right fields (FStar_List.map (fun _56_2079 -> (match (_56_2079) with
| (x, _56_2078) -> begin
(FStar_Parser_Env.qualify env x)
end))))
in (FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _145_804))))))
end
| _56_2081 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1160 "FStar.Parser.ToSyntax.fst"
let desugar_abstract_tc = (fun quals _env mutuals _56_14 -> (match (_56_14) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(
# 1162 "FStar.Parser.ToSyntax.fst"
let _56_2095 = (typars_of_binders _env binders)
in (match (_56_2095) with
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
let tconstr = (let _145_815 = (let _145_814 = (let _145_813 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_145_813))
in (FStar_Parser_AST.mk_term _145_814 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _145_815 binders))
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
| _56_2108 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (
# 1175 "FStar.Parser.ToSyntax.fst"
let push_tparams = (fun env bs -> (
# 1176 "FStar.Parser.ToSyntax.fst"
let _56_2123 = (FStar_List.fold_left (fun _56_2114 _56_2117 -> (match ((_56_2114, _56_2117)) with
| ((env, tps), (x, imp)) -> begin
(
# 1177 "FStar.Parser.ToSyntax.fst"
let _56_2120 = (FStar_Parser_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (_56_2120) with
| (env, y) -> begin
(env, ((y, imp))::tps)
end))
end)) (env, []) bs)
in (match (_56_2123) with
| (env, bs) -> begin
(env, (FStar_List.rev bs))
end)))
in (match (tcs) with
| FStar_Parser_AST.TyconAbstract (_56_2125)::[] -> begin
(
# 1182 "FStar.Parser.ToSyntax.fst"
let tc = (FStar_List.hd tcs)
in (
# 1183 "FStar.Parser.ToSyntax.fst"
let _56_2136 = (desugar_abstract_tc quals env [] tc)
in (match (_56_2136) with
| (_56_2130, _56_2132, se, _56_2135) -> begin
(
# 1184 "FStar.Parser.ToSyntax.fst"
let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _56_2139, typars, k, [], [], quals, rng) -> begin
(
# 1186 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
quals
end else begin
(
# 1188 "FStar.Parser.ToSyntax.fst"
let _56_2148 = (let _145_823 = (FStar_Range.string_of_range rng)
in (let _145_822 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" _145_823 _145_822)))
in (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals)
end
in (
# 1191 "FStar.Parser.ToSyntax.fst"
let t = (match (typars) with
| [] -> begin
k
end
| _56_2153 -> begin
(let _145_826 = (let _145_825 = (let _145_824 = (FStar_Syntax_Syntax.mk_Total k)
in (typars, _145_824))
in FStar_Syntax_Syntax.Tm_arrow (_145_825))
in (FStar_Syntax_Syntax.mk _145_826 None rng))
end)
in FStar_Syntax_Syntax.Sig_declare_typ ((l, [], t, quals, rng))))
end
| _56_2156 -> begin
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
let _56_2168 = (typars_of_binders env binders)
in (match (_56_2168) with
| (env', typars) -> begin
(
# 1202 "FStar.Parser.ToSyntax.fst"
let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _56_15 -> (match (_56_15) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| _56_2173 -> begin
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
let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _56_16 -> (match (_56_16) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| _56_2181 -> begin
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
in (let _145_832 = (let _145_831 = (FStar_Parser_Env.qualify env id)
in (let _145_830 = (FStar_All.pipe_right quals (FStar_List.filter (fun _56_17 -> (match (_56_17) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| _56_2189 -> begin
true
end))))
in (_145_831, [], typars, c, _145_830, rng)))
in FStar_Syntax_Syntax.Sig_effect_abbrev (_145_832)))))
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
| FStar_Parser_AST.TyconRecord (_56_2195)::[] -> begin
(
# 1228 "FStar.Parser.ToSyntax.fst"
let trec = (FStar_List.hd tcs)
in (
# 1229 "FStar.Parser.ToSyntax.fst"
let _56_2201 = (tycon_record_as_variant trec)
in (match (_56_2201) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| _56_2205::_56_2203 -> begin
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
let _56_2216 = et
in (match (_56_2216) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_56_2218) -> begin
(
# 1239 "FStar.Parser.ToSyntax.fst"
let trec = tc
in (
# 1240 "FStar.Parser.ToSyntax.fst"
let _56_2223 = (tycon_record_as_variant trec)
in (match (_56_2223) with
| (t, fs) -> begin
(collect_tcs ((FStar_Syntax_Syntax.RecordType (fs))::quals) (env, tcs) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(
# 1243 "FStar.Parser.ToSyntax.fst"
let _56_2235 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_56_2235) with
| (env, _56_2232, se, tconstr) -> begin
(env, (FStar_Util.Inl ((se, constructors, tconstr, quals)))::tcs)
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(
# 1246 "FStar.Parser.ToSyntax.fst"
let _56_2247 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_56_2247) with
| (env, _56_2244, se, tconstr) -> begin
(env, (FStar_Util.Inr ((se, t, quals)))::tcs)
end))
end
| _56_2249 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (
# 1249 "FStar.Parser.ToSyntax.fst"
let _56_2252 = (FStar_List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_56_2252) with
| (env, tcs) -> begin
(
# 1250 "FStar.Parser.ToSyntax.fst"
let tcs = (FStar_List.rev tcs)
in (
# 1251 "FStar.Parser.ToSyntax.fst"
let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _56_19 -> (match (_56_19) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, _56_2260, _56_2262, _56_2264, _56_2266), t, quals) -> begin
(
# 1253 "FStar.Parser.ToSyntax.fst"
let _56_2276 = (push_tparams env tpars)
in (match (_56_2276) with
| (env_tps, _56_2275) -> begin
(
# 1254 "FStar.Parser.ToSyntax.fst"
let t = (desugar_term env_tps t)
in (let _145_842 = (let _145_841 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in ([], _145_841))
in (_145_842)::[]))
end))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, _56_2284, tags, _56_2287), constrs, tconstr, quals) -> begin
(
# 1258 "FStar.Parser.ToSyntax.fst"
let tycon = (tname, tpars, k)
in (
# 1259 "FStar.Parser.ToSyntax.fst"
let _56_2298 = (push_tparams env tpars)
in (match (_56_2298) with
| (env_tps, tps) -> begin
(
# 1260 "FStar.Parser.ToSyntax.fst"
let data_tpars = (FStar_List.map (fun _56_2302 -> (match (_56_2302) with
| (x, _56_2301) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end)) tps)
in (
# 1261 "FStar.Parser.ToSyntax.fst"
let _56_2326 = (let _145_854 = (FStar_All.pipe_right constrs (FStar_List.map (fun _56_2307 -> (match (_56_2307) with
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
let t = (let _145_846 = (FStar_Parser_Env.default_total env_tps)
in (let _145_845 = (close env_tps t)
in (desugar_term _145_846 _145_845)))
in (
# 1272 "FStar.Parser.ToSyntax.fst"
let name = (FStar_Parser_Env.qualify env id)
in (
# 1273 "FStar.Parser.ToSyntax.fst"
let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _56_18 -> (match (_56_18) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| _56_2321 -> begin
[]
end))))
in (
# 1276 "FStar.Parser.ToSyntax.fst"
let ntps = (FStar_List.length data_tpars)
in (let _145_853 = (let _145_852 = (let _145_851 = (let _145_850 = (let _145_849 = (let _145_848 = (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total _145_848))
in (FStar_Syntax_Util.arrow data_tpars _145_849))
in (name, univs, _145_850, tname, ntps, quals, mutuals, rng))
in FStar_Syntax_Syntax.Sig_datacon (_145_851))
in (tps, _145_852))
in (name, _145_853)))))))
end))))
in (FStar_All.pipe_left FStar_List.split _145_854))
in (match (_56_2326) with
| (constrNames, constrs) -> begin
(([], FStar_Syntax_Syntax.Sig_inductive_typ ((tname, univs, tpars, k, mutuals, constrNames, tags, rng))))::constrs
end)))
end)))
end
| _56_2328 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1281 "FStar.Parser.ToSyntax.fst"
let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (
# 1282 "FStar.Parser.ToSyntax.fst"
let bundle = (let _145_856 = (let _145_855 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _145_855, rng))
in FStar_Syntax_Syntax.Sig_bundle (_145_856))
in (
# 1283 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 bundle)
in (
# 1284 "FStar.Parser.ToSyntax.fst"
let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projectors quals env)))
in (
# 1285 "FStar.Parser.ToSyntax.fst"
let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _56_20 -> (match (_56_20) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, _56_2337, tps, k, _56_2341, constrs, quals, _56_2345) when ((FStar_List.length constrs) > 1) -> begin
(
# 1287 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract quals) then begin
(FStar_Syntax_Syntax.Private)::quals
end else begin
quals
end
in (mk_data_discriminators quals env tname tps k constrs))
end
| _56_2350 -> begin
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
let _56_2374 = (FStar_List.fold_left (fun _56_2359 b -> (match (_56_2359) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| (Some (a), k) -> begin
(
# 1302 "FStar.Parser.ToSyntax.fst"
let _56_2367 = (FStar_Parser_Env.push_bv env a)
in (match (_56_2367) with
| (env, a) -> begin
(let _145_865 = (let _145_864 = (FStar_Syntax_Syntax.mk_binder (
# 1303 "FStar.Parser.ToSyntax.fst"
let _56_2368 = a
in {FStar_Syntax_Syntax.ppname = _56_2368.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_2368.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (_145_864)::binders)
in (env, _145_865))
end))
end
| _56_2371 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Missing name in binder", b.FStar_Parser_AST.brange))))
end)
end)) (env, []) binders)
in (match (_56_2374) with
| (env, binders) -> begin
(env, (FStar_List.rev binders))
end)))

# 1308 "FStar.Parser.ToSyntax.fst"
let rec desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (
# 1309 "FStar.Parser.ToSyntax.fst"
let trans_qual = (trans_qual d.FStar_Parser_AST.drange)
in (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(
# 1312 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_pragma (((trans_pragma p), d.FStar_Parser_AST.drange))
in (env, (se)::[]))
end
| FStar_Parser_AST.TopLevelModule (_56_2382) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Multiple modules in a file are no longer supported", d.FStar_Parser_AST.drange))))
end
| FStar_Parser_AST.Open (lid) -> begin
(
# 1319 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_namespace env lid)
in (env, []))
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(let _145_871 = (FStar_Parser_Env.push_module_abbrev env x l)
in (_145_871, []))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(let _145_872 = (FStar_List.map trans_qual qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _145_872 tcs))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _145_874 = (let _145_873 = (desugar_term_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((isrec, lets, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Syntax_Subst.compress _145_873))
in _145_874.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let (lbs, _56_2402) -> begin
(
# 1331 "FStar.Parser.ToSyntax.fst"
let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (
# 1332 "FStar.Parser.ToSyntax.fst"
let quals = (match (quals) with
| _56_2410::_56_2408 -> begin
(FStar_List.map trans_qual quals)
end
| _56_2413 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _56_21 -> (match (_56_21) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (_56_2424); FStar_Syntax_Syntax.lbunivs = _56_2422; FStar_Syntax_Syntax.lbtyp = _56_2420; FStar_Syntax_Syntax.lbeff = _56_2418; FStar_Syntax_Syntax.lbdef = _56_2416} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _56_2434; FStar_Syntax_Syntax.lbtyp = _56_2432; FStar_Syntax_Syntax.lbeff = _56_2430; FStar_Syntax_Syntax.lbdef = _56_2428} -> begin
(FStar_Parser_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (
# 1337 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right lets (FStar_Util.for_some (fun _56_2442 -> (match (_56_2442) with
| (_56_2440, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end)))) then begin
(FStar_Syntax_Syntax.Logic)::quals
end else begin
quals
end
in (
# 1341 "FStar.Parser.ToSyntax.fst"
let lbs = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _145_879 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 1343 "FStar.Parser.ToSyntax.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 1344 "FStar.Parser.ToSyntax.fst"
let _56_2446 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((
# 1344 "FStar.Parser.ToSyntax.fst"
let _56_2448 = fv
in {FStar_Syntax_Syntax.fv_name = _56_2448.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = _56_2448.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = _56_2446.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _56_2446.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _56_2446.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _56_2446.FStar_Syntax_Syntax.lbdef})))))
in ((Prims.fst lbs), _145_879))
end else begin
lbs
end
in (
# 1346 "FStar.Parser.ToSyntax.fst"
let s = (let _145_882 = (let _145_881 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (lbs, d.FStar_Parser_AST.drange, _145_881, quals))
in FStar_Syntax_Syntax.Sig_let (_145_882))
in (
# 1347 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env s)
in (env, (s)::[])))))))
end
| _56_2455 -> begin
(FStar_All.failwith "Desugaring a let did not produce a let")
end)
end
| FStar_Parser_AST.Main (t) -> begin
(
# 1353 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env t)
in (
# 1354 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, d.FStar_Parser_AST.drange))
in (env, (se)::[])))
end
| FStar_Parser_AST.Assume (atag, id, t) -> begin
(
# 1358 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env t)
in (let _145_886 = (let _145_885 = (let _145_884 = (let _145_883 = (FStar_Parser_Env.qualify env id)
in (_145_883, f, (FStar_Syntax_Syntax.Assumption)::[], d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Sig_assume (_145_884))
in (_145_885)::[])
in (env, _145_886)))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(
# 1362 "FStar.Parser.ToSyntax.fst"
let t = (let _145_887 = (close_fun env t)
in (desugar_term env _145_887))
in (
# 1363 "FStar.Parser.ToSyntax.fst"
let quals = if (env.FStar_Parser_Env.iface && env.FStar_Parser_Env.admitted_iface) then begin
(FStar_Parser_AST.Assumption)::quals
end else begin
quals
end
in (
# 1364 "FStar.Parser.ToSyntax.fst"
let se = (let _145_890 = (let _145_889 = (FStar_Parser_Env.qualify env id)
in (let _145_888 = (FStar_List.map trans_qual quals)
in (_145_889, [], t, _145_888, d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_declare_typ (_145_890))
in (
# 1365 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(
# 1369 "FStar.Parser.ToSyntax.fst"
let t = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (
# 1370 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env id)
in (
# 1371 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_datacon ((l, [], t, FStar_Syntax_Const.exn_lid, 0, (FStar_Syntax_Syntax.ExceptionConstructor)::[], (FStar_Syntax_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (
# 1372 "FStar.Parser.ToSyntax.fst"
let se' = FStar_Syntax_Syntax.Sig_bundle (((se)::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (
# 1373 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se')
in (
# 1374 "FStar.Parser.ToSyntax.fst"
let data_ops = (mk_data_projectors [] env ([], se))
in (
# 1375 "FStar.Parser.ToSyntax.fst"
let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (
# 1376 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops))))))))))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(
# 1380 "FStar.Parser.ToSyntax.fst"
let t = (desugar_term env term)
in (
# 1381 "FStar.Parser.ToSyntax.fst"
let t = (let _145_894 = (let _145_891 = (FStar_Syntax_Syntax.null_binder t)
in (_145_891)::[])
in (let _145_893 = (let _145_892 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _145_892))
in (FStar_Syntax_Util.arrow _145_894 _145_893)))
in (
# 1382 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env id)
in (
# 1383 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_datacon ((l, [], t, FStar_Syntax_Const.exn_lid, 0, (FStar_Syntax_Syntax.ExceptionConstructor)::[], (FStar_Syntax_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (
# 1384 "FStar.Parser.ToSyntax.fst"
let se' = FStar_Syntax_Syntax.Sig_bundle (((se)::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (
# 1385 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se')
in (
# 1386 "FStar.Parser.ToSyntax.fst"
let data_ops = (mk_data_projectors [] env ([], se))
in (
# 1387 "FStar.Parser.ToSyntax.fst"
let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (
# 1388 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops)))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(
# 1392 "FStar.Parser.ToSyntax.fst"
let _56_2508 = (desugar_binders env binders)
in (match (_56_2508) with
| (env_k, binders) -> begin
(
# 1393 "FStar.Parser.ToSyntax.fst"
let k = (desugar_term env_k k)
in (
# 1394 "FStar.Parser.ToSyntax.fst"
let name = (FStar_Parser_Env.qualify env id)
in (
# 1395 "FStar.Parser.ToSyntax.fst"
let se = (mk_typ_abbrev name [] binders FStar_Syntax_Syntax.tun k ((name)::[]) [] d.FStar_Parser_AST.drange)
in (
# 1396 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))))
end))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(
# 1400 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1401 "FStar.Parser.ToSyntax.fst"
let _56_2524 = (desugar_binders env eff_binders)
in (match (_56_2524) with
| (env, binders) -> begin
(
# 1402 "FStar.Parser.ToSyntax.fst"
let _56_2535 = (
# 1403 "FStar.Parser.ToSyntax.fst"
let _56_2527 = (head_and_args defn)
in (match (_56_2527) with
| (head, args) -> begin
(
# 1404 "FStar.Parser.ToSyntax.fst"
let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_defn env) l)
end
| _56_2531 -> begin
(let _145_899 = (let _145_898 = (let _145_897 = (let _145_896 = (let _145_895 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat "Effect " _145_895))
in (Prims.strcat _145_896 " not found"))
in (_145_897, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_145_898))
in (Prims.raise _145_899))
end)
in (let _145_900 = (desugar_args env args)
in (ed, _145_900)))
end))
in (match (_56_2535) with
| (ed, args) -> begin
(
# 1408 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_Syntax_Subst.close_binders binders)
in (
# 1409 "FStar.Parser.ToSyntax.fst"
let sub = (fun _56_2541 -> (match (_56_2541) with
| (_56_2539, x) -> begin
(
# 1410 "FStar.Parser.ToSyntax.fst"
let _56_2544 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (_56_2544) with
| (edb, x) -> begin
(
# 1411 "FStar.Parser.ToSyntax.fst"
let s = (FStar_Syntax_Util.subst_of_list edb args)
in (let _145_904 = (let _145_903 = (FStar_Syntax_Subst.subst s x)
in (FStar_Syntax_Subst.close binders _145_903))
in ([], _145_904)))
end))
end))
in (
# 1413 "FStar.Parser.ToSyntax.fst"
let ed = (let _145_921 = (FStar_List.map trans_qual quals)
in (let _145_920 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _145_919 = (let _145_905 = (sub ([], ed.FStar_Syntax_Syntax.signature))
in (Prims.snd _145_905))
in (let _145_918 = (sub ed.FStar_Syntax_Syntax.ret)
in (let _145_917 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (let _145_916 = (sub ed.FStar_Syntax_Syntax.bind_wlp)
in (let _145_915 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (let _145_914 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (let _145_913 = (sub ed.FStar_Syntax_Syntax.ite_wlp)
in (let _145_912 = (sub ed.FStar_Syntax_Syntax.wp_binop)
in (let _145_911 = (sub ed.FStar_Syntax_Syntax.wp_as_type)
in (let _145_910 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (let _145_909 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (let _145_908 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (let _145_907 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (let _145_906 = (sub ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _145_921; FStar_Syntax_Syntax.mname = _145_920; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = _145_919; FStar_Syntax_Syntax.ret = _145_918; FStar_Syntax_Syntax.bind_wp = _145_917; FStar_Syntax_Syntax.bind_wlp = _145_916; FStar_Syntax_Syntax.if_then_else = _145_915; FStar_Syntax_Syntax.ite_wp = _145_914; FStar_Syntax_Syntax.ite_wlp = _145_913; FStar_Syntax_Syntax.wp_binop = _145_912; FStar_Syntax_Syntax.wp_as_type = _145_911; FStar_Syntax_Syntax.close_wp = _145_910; FStar_Syntax_Syntax.assert_p = _145_909; FStar_Syntax_Syntax.assume_p = _145_908; FStar_Syntax_Syntax.null_wp = _145_907; FStar_Syntax_Syntax.trivial = _145_906}))))))))))))))))
in (
# 1433 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (
# 1434 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 se)
in (env, (se)::[]))))))
end))
end)))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls)) -> begin
(
# 1438 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1439 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.enter_monad_scope env eff_name)
in (
# 1440 "FStar.Parser.ToSyntax.fst"
let _56_2562 = (desugar_binders env eff_binders)
in (match (_56_2562) with
| (env, binders) -> begin
(
# 1441 "FStar.Parser.ToSyntax.fst"
let eff_k = (let _145_922 = (FStar_Parser_Env.default_total env)
in (desugar_term _145_922 eff_kind))
in (
# 1442 "FStar.Parser.ToSyntax.fst"
let _56_2573 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _56_2566 decl -> (match (_56_2566) with
| (env, out) -> begin
(
# 1443 "FStar.Parser.ToSyntax.fst"
let _56_2570 = (desugar_decl env decl)
in (match (_56_2570) with
| (env, ses) -> begin
(let _145_926 = (let _145_925 = (FStar_List.hd ses)
in (_145_925)::out)
in (env, _145_926))
end))
end)) (env, [])))
in (match (_56_2573) with
| (env, decls) -> begin
(
# 1445 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_Syntax_Subst.close_binders binders)
in (
# 1446 "FStar.Parser.ToSyntax.fst"
let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (
# 1447 "FStar.Parser.ToSyntax.fst"
let lookup = (fun s -> (
# 1448 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env (FStar_Ident.mk_ident (s, d.FStar_Parser_AST.drange)))
in (let _145_930 = (let _145_929 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) _145_929))
in ([], _145_930))))
in (
# 1450 "FStar.Parser.ToSyntax.fst"
let ed = (let _145_945 = (FStar_List.map trans_qual quals)
in (let _145_944 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _145_943 = (lookup "return")
in (let _145_942 = (lookup "bind_wp")
in (let _145_941 = (lookup "bind_wlp")
in (let _145_940 = (lookup "if_then_else")
in (let _145_939 = (lookup "ite_wp")
in (let _145_938 = (lookup "ite_wlp")
in (let _145_937 = (lookup "wp_binop")
in (let _145_936 = (lookup "wp_as_type")
in (let _145_935 = (lookup "close_wp")
in (let _145_934 = (lookup "assert_p")
in (let _145_933 = (lookup "assume_p")
in (let _145_932 = (lookup "null_wp")
in (let _145_931 = (lookup "trivial")
in {FStar_Syntax_Syntax.qualifiers = _145_945; FStar_Syntax_Syntax.mname = _145_944; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret = _145_943; FStar_Syntax_Syntax.bind_wp = _145_942; FStar_Syntax_Syntax.bind_wlp = _145_941; FStar_Syntax_Syntax.if_then_else = _145_940; FStar_Syntax_Syntax.ite_wp = _145_939; FStar_Syntax_Syntax.ite_wlp = _145_938; FStar_Syntax_Syntax.wp_binop = _145_937; FStar_Syntax_Syntax.wp_as_type = _145_936; FStar_Syntax_Syntax.close_wp = _145_935; FStar_Syntax_Syntax.assert_p = _145_934; FStar_Syntax_Syntax.assume_p = _145_933; FStar_Syntax_Syntax.null_wp = _145_932; FStar_Syntax_Syntax.trivial = _145_931})))))))))))))))
in (
# 1470 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (
# 1471 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 se)
in (env, (se)::[])))))))
end)))
end))))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(
# 1475 "FStar.Parser.ToSyntax.fst"
let lookup = (fun l -> (match ((FStar_Parser_Env.try_lookup_effect_name env l)) with
| None -> begin
(let _145_952 = (let _145_951 = (let _145_950 = (let _145_949 = (let _145_948 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat "Effect name " _145_948))
in (Prims.strcat _145_949 " not found"))
in (_145_950, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_145_951))
in (Prims.raise _145_952))
end
| Some (l) -> begin
l
end))
in (
# 1478 "FStar.Parser.ToSyntax.fst"
let src = (lookup l.FStar_Parser_AST.msource)
in (
# 1479 "FStar.Parser.ToSyntax.fst"
let dst = (lookup l.FStar_Parser_AST.mdest)
in (
# 1480 "FStar.Parser.ToSyntax.fst"
let lift = (let _145_953 = (desugar_term env l.FStar_Parser_AST.lift_op)
in ([], _145_953))
in (
# 1481 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect (({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift = lift}, d.FStar_Parser_AST.drange))
in (env, (se)::[]))))))
end)))

# 1484 "FStar.Parser.ToSyntax.fst"
let desugar_decls : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _56_2597 d -> (match (_56_2597) with
| (env, sigelts) -> begin
(
# 1486 "FStar.Parser.ToSyntax.fst"
let _56_2601 = (desugar_decl env d)
in (match (_56_2601) with
| (env, se) -> begin
(env, (FStar_List.append sigelts se))
end))
end)) (env, []) decls))

# 1489 "FStar.Parser.ToSyntax.fst"
let open_prims_all : FStar_Parser_AST.decl Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.all_lid)) FStar_Range.dummyRange))::[]

# 1496 "FStar.Parser.ToSyntax.fst"
let desugar_modul_common : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (
# 1497 "FStar.Parser.ToSyntax.fst"
let open_ns = (fun mname d -> (
# 1498 "FStar.Parser.ToSyntax.fst"
let d = if ((FStar_List.length mname.FStar_Ident.ns) <> 0) then begin
(let _145_972 = (let _145_971 = (let _145_970 = (FStar_Ident.lid_of_ids mname.FStar_Ident.ns)
in FStar_Parser_AST.Open (_145_970))
in (FStar_Parser_AST.mk_decl _145_971 (FStar_Ident.range_of_lid mname)))
in (_145_972)::d)
end else begin
d
end
in d))
in (
# 1502 "FStar.Parser.ToSyntax.fst"
let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod) -> begin
(FStar_Parser_Env.finish_module_or_interface env prev_mod)
end)
in (
# 1505 "FStar.Parser.ToSyntax.fst"
let _56_2628 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _145_974 = (FStar_Parser_Env.prepare_module_or_interface true admitted env mname)
in (let _145_973 = (open_ns mname decls)
in (_145_974, mname, _145_973, true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _145_976 = (FStar_Parser_Env.prepare_module_or_interface false false env mname)
in (let _145_975 = (open_ns mname decls)
in (_145_976, mname, _145_975, false)))
end)
in (match (_56_2628) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(
# 1510 "FStar.Parser.ToSyntax.fst"
let _56_2631 = (desugar_decls env decls)
in (match (_56_2631) with
| (env, sigelts) -> begin
(
# 1511 "FStar.Parser.ToSyntax.fst"
let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in (env, modul, pop_when_done))
end))
end)))))

# 1519 "FStar.Parser.ToSyntax.fst"
let desugar_partial_modul : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (
# 1520 "FStar.Parser.ToSyntax.fst"
let m = if (FStar_ST.read FStar_Options.interactive_fsi) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface ((mname, decls, true))
end
| FStar_Parser_AST.Interface (mname, _56_2642, _56_2644) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (
# 1527 "FStar.Parser.ToSyntax.fst"
let _56_2652 = (desugar_modul_common curmod env m)
in (match (_56_2652) with
| (x, y, _56_2651) -> begin
(x, y)
end))))

# 1530 "FStar.Parser.ToSyntax.fst"
let desugar_modul : FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (
# 1531 "FStar.Parser.ToSyntax.fst"
let _56_2658 = (desugar_modul_common None env m)
in (match (_56_2658) with
| (env, modul, pop_when_done) -> begin
(
# 1532 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.finish_module_or_interface env modul)
in (
# 1533 "FStar.Parser.ToSyntax.fst"
let _56_2660 = if (FStar_Options.should_dump modul.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _145_987 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _145_987))
end else begin
()
end
in (let _145_988 = if pop_when_done then begin
(FStar_Parser_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end else begin
env
end
in (_145_988, modul))))
end)))

# 1537 "FStar.Parser.ToSyntax.fst"
let desugar_file : FStar_Parser_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (
# 1538 "FStar.Parser.ToSyntax.fst"
let _56_2673 = (FStar_List.fold_left (fun _56_2666 m -> (match (_56_2666) with
| (env, mods) -> begin
(
# 1539 "FStar.Parser.ToSyntax.fst"
let _56_2670 = (desugar_modul env m)
in (match (_56_2670) with
| (env, m) -> begin
(env, (m)::mods)
end))
end)) (env, []) f)
in (match (_56_2673) with
| (env, mods) -> begin
(env, (FStar_List.rev mods))
end)))

# 1543 "FStar.Parser.ToSyntax.fst"
let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Parser_Env.env  ->  FStar_Parser_Env.env = (fun m en -> (
# 1544 "FStar.Parser.ToSyntax.fst"
let _56_2678 = (FStar_Parser_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (_56_2678) with
| (en, pop_when_done) -> begin
(
# 1545 "FStar.Parser.ToSyntax.fst"
let en = (FStar_List.fold_left FStar_Parser_Env.push_sigelt (
# 1545 "FStar.Parser.ToSyntax.fst"
let _56_2679 = en
in {FStar_Parser_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_Parser_Env.modules = _56_2679.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _56_2679.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _56_2679.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _56_2679.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _56_2679.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _56_2679.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _56_2679.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _56_2679.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _56_2679.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _56_2679.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = _56_2679.FStar_Parser_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (
# 1546 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_Env.export_interface m.FStar_Syntax_Syntax.name env)
end else begin
env
end))
end)))




