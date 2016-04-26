
open Prims
# 40 "FStar.Parser.ToSyntax.fst"
let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _63_1 -> (match (_63_1) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Syntax_Syntax.Equality)
end
| _63_28 -> begin
None
end))

# 45 "FStar.Parser.ToSyntax.fst"
let trans_qual : FStar_Range.range  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun r _63_2 -> (match (_63_2) with
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
let _63_42 = (FStar_TypeChecker_Errors.warn r "The \'opaque\' qualifier is deprecated; use \'unfoldable\', which is also the default")
in FStar_Syntax_Syntax.Unfoldable)
end
| FStar_Parser_AST.DefaultEffect -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("The \'default\' qualifier on effects is no longer supported", r))))
end))

# 59 "FStar.Parser.ToSyntax.fst"
let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun _63_3 -> (match (_63_3) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end))

# 63 "FStar.Parser.ToSyntax.fst"
let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _63_4 -> (match (_63_4) with
| FStar_Parser_AST.Hash -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| _63_53 -> begin
None
end))

# 66 "FStar.Parser.ToSyntax.fst"
let arg_withimp_e = (fun imp t -> (t, (as_imp imp)))

# 68 "FStar.Parser.ToSyntax.fst"
let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
(t, Some (FStar_Syntax_Syntax.imp_tag))
end
| _63_60 -> begin
(t, None)
end))

# 73 "FStar.Parser.ToSyntax.fst"
let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_63_64) -> begin
true
end
| _63_67 -> begin
false
end)))))

# 78 "FStar.Parser.ToSyntax.fst"
let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _63_72 -> begin
t
end))

# 82 "FStar.Parser.ToSyntax.fst"
let tm_type_z : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _152_23 = (let _152_22 = (FStar_Ident.lid_of_path (("Type0")::[]) r)
in FStar_Parser_AST.Name (_152_22))
in (FStar_Parser_AST.mk_term _152_23 r FStar_Parser_AST.Kind)))

# 83 "FStar.Parser.ToSyntax.fst"
let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _152_27 = (let _152_26 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_152_26))
in (FStar_Parser_AST.mk_term _152_27 r FStar_Parser_AST.Kind)))

# 85 "FStar.Parser.ToSyntax.fst"
let rec delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (
# 86 "FStar.Parser.ToSyntax.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_63_78) -> begin
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
let name_of_char = (fun _63_5 -> (match (_63_5) with
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
| _63_173 -> begin
"UNKNOWN"
end))
in (
# 135 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _152_47 = (let _152_45 = (FStar_Util.char_at s i)
in (name_of_char _152_45))
in (let _152_46 = (aux (i + 1))
in (_152_47)::_152_46))
end)
in (let _152_49 = (let _152_48 = (aux 0)
in (FStar_String.concat "_" _152_48))
in (Prims.strcat "op_" _152_49)))))

# 141 "FStar.Parser.ToSyntax.fst"
let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _152_59 = (let _152_58 = (let _152_57 = (let _152_56 = (compile_op n s)
in (_152_56, r))
in (FStar_Ident.mk_ident _152_57))
in (_152_58)::[])
in (FStar_All.pipe_right _152_59 FStar_Ident.lid_of_ids)))

# 143 "FStar.Parser.ToSyntax.fst"
let op_as_term : FStar_Parser_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.term Prims.option = (fun env arity rng s -> (
# 144 "FStar.Parser.ToSyntax.fst"
let r = (fun l dd -> (let _152_74 = (let _152_73 = (let _152_72 = (FStar_Ident.set_lid_range l rng)
in (FStar_Syntax_Syntax.lid_as_fv _152_72 dd None))
in (FStar_All.pipe_right _152_73 FStar_Syntax_Syntax.fv_to_tm))
in Some (_152_74)))
in (
# 145 "FStar.Parser.ToSyntax.fst"
let fallback = (fun _63_188 -> (match (()) with
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
| _63_216 -> begin
None
end)
end))
in (match ((let _152_77 = (compile_op_lid arity s rng)
in (FStar_Parser_Env.try_lookup_lid env _152_77))) with
| Some (t) -> begin
Some (t)
end
| _63_220 -> begin
(fallback ())
end))))

# 179 "FStar.Parser.ToSyntax.fst"
let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _152_84 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _152_84)))

# 183 "FStar.Parser.ToSyntax.fst"
let rec free_type_vars_b : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_63_229) -> begin
(env, [])
end
| FStar_Parser_AST.TVariable (x) -> begin
(
# 186 "FStar.Parser.ToSyntax.fst"
let _63_236 = (FStar_Parser_Env.push_bv env x)
in (match (_63_236) with
| (env, _63_235) -> begin
(env, (x)::[])
end))
end
| FStar_Parser_AST.Annotated (_63_238, term) -> begin
(let _152_91 = (free_type_vars env term)
in (env, _152_91))
end
| FStar_Parser_AST.TAnnotated (id, _63_244) -> begin
(
# 191 "FStar.Parser.ToSyntax.fst"
let _63_250 = (FStar_Parser_Env.push_bv env id)
in (match (_63_250) with
| (env, _63_249) -> begin
(env, [])
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _152_92 = (free_type_vars env t)
in (env, _152_92))
end))
and free_type_vars : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _152_95 = (unparen t)
in _152_95.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (_63_256) -> begin
(FStar_All.failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_Env.try_lookup_id env a)) with
| None -> begin
(a)::[]
end
| _63_262 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_63_292, ts) -> begin
(FStar_List.collect (fun _63_299 -> (match (_63_299) with
| (t, _63_298) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_63_301, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _63_308) -> begin
(let _152_98 = (free_type_vars env t1)
in (let _152_97 = (free_type_vars env t2)
in (FStar_List.append _152_98 _152_97)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(
# 221 "FStar.Parser.ToSyntax.fst"
let _63_317 = (free_type_vars_b env b)
in (match (_63_317) with
| (env, f) -> begin
(let _152_99 = (free_type_vars env t)
in (FStar_List.append f _152_99))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(
# 226 "FStar.Parser.ToSyntax.fst"
let _63_333 = (FStar_List.fold_left (fun _63_326 binder -> (match (_63_326) with
| (env, free) -> begin
(
# 227 "FStar.Parser.ToSyntax.fst"
let _63_330 = (free_type_vars_b env binder)
in (match (_63_330) with
| (env, f) -> begin
(env, (FStar_List.append f free))
end))
end)) (env, []) binders)
in (match (_63_333) with
| (env, free) -> begin
(let _152_102 = (free_type_vars env body)
in (FStar_List.append free _152_102))
end))
end
| FStar_Parser_AST.Project (t, _63_336) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
[]
end))

# 244 "FStar.Parser.ToSyntax.fst"
let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (
# 245 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun args t -> (match ((let _152_109 = (unparen t)
in _152_109.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _63_380 -> begin
(t, args)
end))
in (aux [] t)))

# 251 "FStar.Parser.ToSyntax.fst"
let close : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 252 "FStar.Parser.ToSyntax.fst"
let ftv = (let _152_114 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _152_114))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 255 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _152_118 = (let _152_117 = (let _152_116 = (tm_type x.FStar_Ident.idRange)
in (x, _152_116))
in FStar_Parser_AST.TAnnotated (_152_117))
in (FStar_Parser_AST.mk_binder _152_118 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 256 "FStar.Parser.ToSyntax.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))

# 259 "FStar.Parser.ToSyntax.fst"
let close_fun : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 260 "FStar.Parser.ToSyntax.fst"
let ftv = (let _152_123 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _152_123))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 263 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _152_127 = (let _152_126 = (let _152_125 = (tm_type x.FStar_Ident.idRange)
in (x, _152_125))
in FStar_Parser_AST.TAnnotated (_152_126))
in (FStar_Parser_AST.mk_binder _152_127 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 264 "FStar.Parser.ToSyntax.fst"
let t = (match ((let _152_128 = (unparen t)
in _152_128.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_63_393) -> begin
t
end
| _63_396 -> begin
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
| _63_406 -> begin
(bs, t)
end))

# 274 "FStar.Parser.ToSyntax.fst"
let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _63_410) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_63_416); FStar_Parser_AST.prange = _63_414}, _63_420) -> begin
true
end
| _63_424 -> begin
false
end))

# 279 "FStar.Parser.ToSyntax.fst"
let rec destruct_app_pattern : FStar_Parser_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 281 "FStar.Parser.ToSyntax.fst"
let _63_436 = (destruct_app_pattern env is_top_level p)
in (match (_63_436) with
| (name, args, _63_435) -> begin
(name, args, Some (t))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _63_441); FStar_Parser_AST.prange = _63_438}, args) when is_top_level -> begin
(let _152_142 = (let _152_141 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_152_141))
in (_152_142, args, None))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _63_452); FStar_Parser_AST.prange = _63_449}, args) -> begin
(FStar_Util.Inl (id), args, None)
end
| _63_460 -> begin
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
| LocalBinder (_63_463) -> begin
_63_463
end))

# 292 "FStar.Parser.ToSyntax.fst"
let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_63_466) -> begin
_63_466
end))

# 293 "FStar.Parser.ToSyntax.fst"
let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun _63_6 -> (match (_63_6) with
| LocalBinder (a, aq) -> begin
(a, aq)
end
| _63_473 -> begin
(FStar_All.failwith "Impossible")
end))

# 296 "FStar.Parser.ToSyntax.fst"
let as_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_Parser_Env.env) = (fun env imp _63_7 -> (match (_63_7) with
| (None, k) -> begin
(let _152_179 = (FStar_Syntax_Syntax.null_binder k)
in (_152_179, env))
end
| (Some (a), k) -> begin
(
# 299 "FStar.Parser.ToSyntax.fst"
let _63_486 = (FStar_Parser_Env.push_bv env a)
in (match (_63_486) with
| (env, a) -> begin
(((
# 300 "FStar.Parser.ToSyntax.fst"
let _63_487 = a
in {FStar_Syntax_Syntax.ppname = _63_487.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_487.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}), (trans_aqual imp)), env)
end))
end))

# 302 "FStar.Parser.ToSyntax.fst"
type env_t =
FStar_Parser_Env.env

# 303 "FStar.Parser.ToSyntax.fst"
type lenv_t =
FStar_Syntax_Syntax.bv Prims.list

# 305 "FStar.Parser.ToSyntax.fst"
let mk_lb : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.letbinding = (fun _63_492 -> (match (_63_492) with
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
| FStar_Syntax_Syntax.Pat_cons (_63_513, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out _63_521 -> (match (_63_521) with
| (p, _63_520) -> begin
(let _152_225 = (pat_vars p)
in (FStar_Util.set_union out _152_225))
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
| _63_539 -> begin
(
# 331 "FStar.Parser.ToSyntax.fst"
let _63_542 = (FStar_Parser_Env.push_bv e x)
in (match (_63_542) with
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
| _63_551 -> begin
(
# 337 "FStar.Parser.ToSyntax.fst"
let _63_554 = (FStar_Parser_Env.push_bv e a)
in (match (_63_554) with
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
let _63_576 = (aux loc env p)
in (match (_63_576) with
| (loc, env, var, p, _63_575) -> begin
(
# 346 "FStar.Parser.ToSyntax.fst"
let _63_593 = (FStar_List.fold_left (fun _63_580 p -> (match (_63_580) with
| (loc, env, ps) -> begin
(
# 347 "FStar.Parser.ToSyntax.fst"
let _63_589 = (aux loc env p)
in (match (_63_589) with
| (loc, env, _63_585, p, _63_588) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_63_593) with
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
let _63_604 = (aux loc env p)
in (match (_63_604) with
| (loc, env', binder, p, imp) -> begin
(
# 354 "FStar.Parser.ToSyntax.fst"
let binder = (match (binder) with
| LetBinder (_63_606) -> begin
(FStar_All.failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(
# 357 "FStar.Parser.ToSyntax.fst"
let t = (let _152_255 = (close_fun env t)
in (desugar_term env _152_255))
in LocalBinder (((
# 358 "FStar.Parser.ToSyntax.fst"
let _63_613 = x
in {FStar_Syntax_Syntax.ppname = _63_613.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_613.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), aq)))
end)
in (loc, env', binder, p, imp))
end))
end
| FStar_Parser_AST.PatWild -> begin
(
# 362 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _152_256 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in (loc, env, LocalBinder ((x, None)), _152_256, false)))
end
| FStar_Parser_AST.PatConst (c) -> begin
(
# 366 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _152_257 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in (loc, env, LocalBinder ((x, None)), _152_257, false)))
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
let _63_632 = (resolvex loc env x)
in (match (_63_632) with
| (loc, env, xbv) -> begin
(let _152_258 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in (loc, env, LocalBinder ((xbv, aq)), _152_258, imp))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(
# 377 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_datacon env) l)
in (
# 378 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _152_259 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, []))))
in (loc, env, LocalBinder ((x, None)), _152_259, false))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _63_638}, args) -> begin
(
# 382 "FStar.Parser.ToSyntax.fst"
let _63_660 = (FStar_List.fold_right (fun arg _63_649 -> (match (_63_649) with
| (loc, env, args) -> begin
(
# 383 "FStar.Parser.ToSyntax.fst"
let _63_656 = (aux loc env arg)
in (match (_63_656) with
| (loc, env, _63_653, arg, imp) -> begin
(loc, env, ((arg, imp))::args)
end))
end)) args (loc, env, []))
in (match (_63_660) with
| (loc, env, args) -> begin
(
# 385 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_datacon env) l)
in (
# 386 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _152_262 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _152_262, false))))
end))
end
| FStar_Parser_AST.PatApp (_63_664) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(
# 392 "FStar.Parser.ToSyntax.fst"
let _63_684 = (FStar_List.fold_right (fun pat _63_672 -> (match (_63_672) with
| (loc, env, pats) -> begin
(
# 393 "FStar.Parser.ToSyntax.fst"
let _63_680 = (aux loc env pat)
in (match (_63_680) with
| (loc, env, _63_676, pat, _63_679) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_63_684) with
| (loc, env, pats) -> begin
(
# 395 "FStar.Parser.ToSyntax.fst"
let pat = (let _152_275 = (let _152_274 = (let _152_270 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _152_270))
in (let _152_273 = (let _152_272 = (let _152_271 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_152_271, []))
in FStar_Syntax_Syntax.Pat_cons (_152_272))
in (FStar_All.pipe_left _152_274 _152_273)))
in (FStar_List.fold_right (fun hd tl -> (
# 396 "FStar.Parser.ToSyntax.fst"
let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (let _152_269 = (let _152_268 = (let _152_267 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_152_267, ((hd, false))::((tl, false))::[]))
in FStar_Syntax_Syntax.Pat_cons (_152_268))
in (FStar_All.pipe_left (pos_r r) _152_269)))) pats _152_275))
in (
# 399 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (loc, env, LocalBinder ((x, None)), pat, false)))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(
# 403 "FStar.Parser.ToSyntax.fst"
let _63_710 = (FStar_List.fold_left (fun _63_697 p -> (match (_63_697) with
| (loc, env, pats) -> begin
(
# 404 "FStar.Parser.ToSyntax.fst"
let _63_706 = (aux loc env p)
in (match (_63_706) with
| (loc, env, _63_702, pat, _63_705) -> begin
(loc, env, ((pat, false))::pats)
end))
end)) (loc, env, []) args)
in (match (_63_710) with
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
| _63_717 -> begin
(FStar_All.failwith "impossible")
end)
in (
# 413 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _152_278 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _152_278, false)))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(
# 420 "FStar.Parser.ToSyntax.fst"
let _63_727 = (FStar_List.hd fields)
in (match (_63_727) with
| (f, _63_726) -> begin
(
# 421 "FStar.Parser.ToSyntax.fst"
let _63_731 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_63_731) with
| (record, _63_730) -> begin
(
# 422 "FStar.Parser.ToSyntax.fst"
let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _63_734 -> (match (_63_734) with
| (f, p) -> begin
(let _152_280 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.qualify_field_to_record env record) f)
in (_152_280, p))
end))))
in (
# 424 "FStar.Parser.ToSyntax.fst"
let args = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _63_739 -> (match (_63_739) with
| (f, _63_738) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _63_743 -> (match (_63_743) with
| (g, _63_742) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_63_746, p) -> begin
p
end)
end))))
in (
# 428 "FStar.Parser.ToSyntax.fst"
let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_Env.constrname)) p.FStar_Parser_AST.prange), args))) p.FStar_Parser_AST.prange)
in (
# 429 "FStar.Parser.ToSyntax.fst"
let _63_758 = (aux loc env app)
in (match (_63_758) with
| (env, e, b, p, _63_757) -> begin
(
# 430 "FStar.Parser.ToSyntax.fst"
let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(let _152_289 = (let _152_288 = (let _152_287 = (
# 431 "FStar.Parser.ToSyntax.fst"
let _63_763 = fv
in (let _152_286 = (let _152_285 = (let _152_284 = (let _152_283 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _152_283))
in FStar_Syntax_Syntax.Record_ctor (_152_284))
in Some (_152_285))
in {FStar_Syntax_Syntax.fv_name = _63_763.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = _63_763.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _152_286}))
in (_152_287, args))
in FStar_Syntax_Syntax.Pat_cons (_152_288))
in (FStar_All.pipe_left pos _152_289))
end
| _63_766 -> begin
p
end)
in (env, e, b, p, false))
end)))))
end))
end))
end))))
in (
# 435 "FStar.Parser.ToSyntax.fst"
let _63_775 = (aux [] env p)
in (match (_63_775) with
| (_63_769, env, b, p, _63_774) -> begin
(
# 436 "FStar.Parser.ToSyntax.fst"
let _63_776 = (let _152_290 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore _152_290))
in (env, b, p))
end)))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _63_783) -> begin
(let _152_296 = (let _152_295 = (let _152_294 = (FStar_Parser_Env.qualify env x)
in (_152_294, FStar_Syntax_Syntax.tun))
in LetBinder (_152_295))
in (env, _152_296, None))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _63_790); FStar_Parser_AST.prange = _63_787}, t) -> begin
(let _152_300 = (let _152_299 = (let _152_298 = (FStar_Parser_Env.qualify env x)
in (let _152_297 = (desugar_term env t)
in (_152_298, _152_297)))
in LetBinder (_152_299))
in (env, _152_300, None))
end
| _63_798 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern at the top-level", p.FStar_Parser_AST.prange))))
end)
end else begin
(
# 447 "FStar.Parser.ToSyntax.fst"
let _63_802 = (desugar_data_pat env p)
in (match (_63_802) with
| (env, binder, p) -> begin
(
# 448 "FStar.Parser.ToSyntax.fst"
let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| _63_810 -> begin
Some (p)
end)
in (env, binder, p))
end))
end)
and desugar_binding_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun _63_814 env pat -> (
# 457 "FStar.Parser.ToSyntax.fst"
let _63_822 = (desugar_data_pat env pat)
in (match (_63_822) with
| (env, _63_820, pat) -> begin
(env, pat)
end)))
and desugar_match_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (
# 463 "FStar.Parser.ToSyntax.fst"
let env = (
# 463 "FStar.Parser.ToSyntax.fst"
let _63_827 = env
in {FStar_Parser_Env.curmodule = _63_827.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _63_827.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _63_827.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _63_827.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _63_827.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _63_827.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _63_827.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _63_827.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _63_827.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _63_827.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _63_827.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (
# 467 "FStar.Parser.ToSyntax.fst"
let env = (
# 467 "FStar.Parser.ToSyntax.fst"
let _63_832 = env
in {FStar_Parser_Env.curmodule = _63_832.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _63_832.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _63_832.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _63_832.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _63_832.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _63_832.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _63_832.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _63_832.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _63_832.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _63_832.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _63_832.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (
# 471 "FStar.Parser.ToSyntax.fst"
let mk = (fun e -> (FStar_Syntax_Syntax.mk e None top.FStar_Parser_AST.range))
in (
# 472 "FStar.Parser.ToSyntax.fst"
let setpos = (fun e -> (
# 472 "FStar.Parser.ToSyntax.fst"
let _63_842 = e
in {FStar_Syntax_Syntax.n = _63_842.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _63_842.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _63_842.FStar_Syntax_Syntax.vars}))
in (match ((let _152_319 = (unparen top)
in _152_319.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (_63_846) -> begin
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
| FStar_Parser_AST.Op ("*", _63_866::_63_864::[]) when (let _152_320 = (op_as_term env 2 top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right _152_320 FStar_Option.isNone)) -> begin
(
# 490 "FStar.Parser.ToSyntax.fst"
let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", t1::t2::[]) -> begin
(
# 492 "FStar.Parser.ToSyntax.fst"
let rest = (flatten t2)
in (t1)::rest)
end
| _63_880 -> begin
(t)::[]
end))
in (
# 495 "FStar.Parser.ToSyntax.fst"
let targs = (let _152_326 = (let _152_323 = (unparen top)
in (flatten _152_323))
in (FStar_All.pipe_right _152_326 (FStar_List.map (fun t -> (let _152_325 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg _152_325))))))
in (
# 496 "FStar.Parser.ToSyntax.fst"
let tup = (let _152_327 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) _152_327))
in (mk (FStar_Syntax_Syntax.Tm_app ((tup, targs)))))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _152_328 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) a)
in (FStar_All.pipe_left setpos _152_328))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Unexpected operator: " s), top.FStar_Parser_AST.range))))
end
| Some (op) -> begin
(
# 506 "FStar.Parser.ToSyntax.fst"
let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _152_330 = (desugar_term env t)
in (_152_330, None)))))
in (mk (FStar_Syntax_Syntax.Tm_app ((op, args)))))
end)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _63_901; FStar_Ident.ident = _63_899; FStar_Ident.nsstr = _63_897; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _63_910; FStar_Ident.ident = _63_908; FStar_Ident.nsstr = _63_906; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _63_919; FStar_Ident.ident = _63_917; FStar_Ident.nsstr = _63_915; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _63_928; FStar_Ident.ident = _63_926; FStar_Ident.nsstr = _63_924; FStar_Ident.str = "True"}) -> begin
(let _152_331 = (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _152_331 FStar_Syntax_Syntax.Delta_constant None))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _63_937; FStar_Ident.ident = _63_935; FStar_Ident.nsstr = _63_933; FStar_Ident.str = "False"}) -> begin
(let _152_332 = (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _152_332 FStar_Syntax_Syntax.Delta_constant None))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(let _152_333 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (FStar_All.pipe_left setpos _152_333))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(
# 521 "FStar.Parser.ToSyntax.fst"
let _63_952 = (match ((FStar_Parser_Env.try_lookup_datacon env l)) with
| None -> begin
(let _152_334 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (_152_334, false))
end
| Some (head) -> begin
(let _152_335 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in (_152_335, true))
end)
in (match (_63_952) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| _63_955 -> begin
(
# 527 "FStar.Parser.ToSyntax.fst"
let args = (FStar_List.map (fun _63_958 -> (match (_63_958) with
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
let _63_986 = (FStar_List.fold_left (fun _63_969 b -> (match (_63_969) with
| (env, tparams, typs) -> begin
(
# 538 "FStar.Parser.ToSyntax.fst"
let _63_973 = (desugar_binder env b)
in (match (_63_973) with
| (xopt, t) -> begin
(
# 539 "FStar.Parser.ToSyntax.fst"
let _63_979 = (match (xopt) with
| None -> begin
(let _152_339 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (env, _152_339))
end
| Some (x) -> begin
(FStar_Parser_Env.push_bv env x)
end)
in (match (_63_979) with
| (env, x) -> begin
(let _152_343 = (let _152_342 = (let _152_341 = (let _152_340 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _152_340))
in (_152_341)::[])
in (FStar_List.append typs _152_342))
in (env, (FStar_List.append tparams ((((
# 543 "FStar.Parser.ToSyntax.fst"
let _63_980 = x
in {FStar_Syntax_Syntax.ppname = _63_980.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_980.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), None))::[])), _152_343))
end))
end))
end)) (env, [], []) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_63_986) with
| (env, _63_984, targs) -> begin
(
# 546 "FStar.Parser.ToSyntax.fst"
let tup = (let _152_344 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) _152_344))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app ((tup, targs)))))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(
# 550 "FStar.Parser.ToSyntax.fst"
let _63_994 = (uncurry binders t)
in (match (_63_994) with
| (bs, t) -> begin
(
# 551 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun env bs _63_8 -> (match (_63_8) with
| [] -> begin
(
# 553 "FStar.Parser.ToSyntax.fst"
let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (let _152_351 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos _152_351)))
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
let _63_1008 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_63_1008) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_binder env b)) with
| (None, _63_1015) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(
# 568 "FStar.Parser.ToSyntax.fst"
let _63_1023 = (as_binder env None b)
in (match (_63_1023) with
| ((x, _63_1020), env) -> begin
(
# 569 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env f)
in (let _152_352 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos _152_352)))
end))
end)
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(
# 574 "FStar.Parser.ToSyntax.fst"
let _63_1043 = (FStar_List.fold_left (fun _63_1031 pat -> (match (_63_1031) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (_63_1034, t) -> begin
(let _152_356 = (let _152_355 = (free_type_vars env t)
in (FStar_List.append _152_355 ftvs))
in (env, _152_356))
end
| _63_1039 -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_63_1043) with
| (_63_1041, ftv) -> begin
(
# 578 "FStar.Parser.ToSyntax.fst"
let ftv = (sort_ftv ftv)
in (
# 579 "FStar.Parser.ToSyntax.fst"
let binders = (let _152_358 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar ((a, Some (FStar_Parser_AST.Implicit)))) top.FStar_Parser_AST.range))))
in (FStar_List.append _152_358 binders))
in (
# 588 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun env bs sc_pat_opt _63_9 -> (match (_63_9) with
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
let body = (let _152_368 = (let _152_367 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right _152_367 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close _152_368 body))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((sc, ((pat, None, body))::[]))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (let _152_369 = (no_annot_abs (FStar_List.rev bs) body)
in (setpos _152_369))))
end
| p::rest -> begin
(
# 599 "FStar.Parser.ToSyntax.fst"
let _63_1067 = (desugar_binding_pat env p)
in (match (_63_1067) with
| (env, b, pat) -> begin
(
# 600 "FStar.Parser.ToSyntax.fst"
let _63_1118 = (match (b) with
| LetBinder (_63_1069) -> begin
(FStar_All.failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(
# 603 "FStar.Parser.ToSyntax.fst"
let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _63_1077) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _152_371 = (let _152_370 = (FStar_Syntax_Syntax.bv_to_name x)
in (_152_370, p))
in Some (_152_371))
end
| (Some (p), Some (sc, p')) -> begin
(match ((sc.FStar_Syntax_Syntax.n, p'.FStar_Syntax_Syntax.v)) with
| (FStar_Syntax_Syntax.Tm_name (_63_1091), _63_1094) -> begin
(
# 609 "FStar.Parser.ToSyntax.fst"
let tup2 = (let _152_372 = (FStar_Syntax_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _152_372 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (
# 610 "FStar.Parser.ToSyntax.fst"
let sc = (let _152_380 = (let _152_379 = (let _152_378 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (let _152_377 = (let _152_376 = (FStar_Syntax_Syntax.as_arg sc)
in (let _152_375 = (let _152_374 = (let _152_373 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _152_373))
in (_152_374)::[])
in (_152_376)::_152_375))
in (_152_378, _152_377)))
in FStar_Syntax_Syntax.Tm_app (_152_379))
in (FStar_Syntax_Syntax.mk _152_380 None top.FStar_Parser_AST.range))
in (
# 611 "FStar.Parser.ToSyntax.fst"
let p = (let _152_381 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tup2, ((p', false))::((p, false))::[]))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _152_381))
in Some ((sc, p)))))
end
| (FStar_Syntax_Syntax.Tm_app (_63_1100, args), FStar_Syntax_Syntax.Pat_cons (_63_1105, pats)) -> begin
(
# 614 "FStar.Parser.ToSyntax.fst"
let tupn = (let _152_382 = (FStar_Syntax_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _152_382 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (
# 615 "FStar.Parser.ToSyntax.fst"
let sc = (let _152_389 = (let _152_388 = (let _152_387 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (let _152_386 = (let _152_385 = (let _152_384 = (let _152_383 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _152_383))
in (_152_384)::[])
in (FStar_List.append args _152_385))
in (_152_387, _152_386)))
in FStar_Syntax_Syntax.Tm_app (_152_388))
in (mk _152_389))
in (
# 616 "FStar.Parser.ToSyntax.fst"
let p = (let _152_390 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tupn, (FStar_List.append pats (((p, false))::[]))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _152_390))
in Some ((sc, p)))))
end
| _63_1114 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((x, aq), sc_pat_opt))
end)
in (match (_63_1118) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _63_1122; FStar_Parser_AST.level = _63_1120}, phi, _63_1128) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(
# 627 "FStar.Parser.ToSyntax.fst"
let phi = (desugar_formula env phi)
in (let _152_398 = (let _152_397 = (let _152_396 = (FStar_Syntax_Syntax.fvar a FStar_Syntax_Syntax.Delta_equational None)
in (let _152_395 = (let _152_394 = (FStar_Syntax_Syntax.as_arg phi)
in (let _152_393 = (let _152_392 = (let _152_391 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _152_391))
in (_152_392)::[])
in (_152_394)::_152_393))
in (_152_396, _152_395)))
in FStar_Syntax_Syntax.Tm_app (_152_397))
in (mk _152_398)))
end
| FStar_Parser_AST.App (_63_1133) -> begin
(
# 633 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun args e -> (match ((let _152_403 = (unparen e)
in _152_403.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(
# 635 "FStar.Parser.ToSyntax.fst"
let arg = (let _152_404 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _152_404))
in (aux ((arg)::args) e))
end
| _63_1145 -> begin
(
# 638 "FStar.Parser.ToSyntax.fst"
let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app ((head, args)))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _152_407 = (let _152_406 = (let _152_405 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range), t1))::[], t2))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in (_152_405, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))
in FStar_Syntax_Syntax.Tm_meta (_152_406))
in (mk _152_407))
end
| FStar_Parser_AST.Let (is_rec, (pat, _snd)::_tl, body) -> begin
(
# 647 "FStar.Parser.ToSyntax.fst"
let ds_let_rec_or_app = (fun _63_1161 -> (match (()) with
| () -> begin
(
# 648 "FStar.Parser.ToSyntax.fst"
let bindings = ((pat, _snd))::_tl
in (
# 649 "FStar.Parser.ToSyntax.fst"
let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _63_1165 -> (match (_63_1165) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _152_411 = (destruct_app_pattern env top_level p)
in (_152_411, def))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _152_412 = (destruct_app_pattern env top_level p)
in (_152_412, def))
end
| _63_1171 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _63_1176); FStar_Parser_AST.prange = _63_1173}, t) -> begin
if top_level then begin
(let _152_415 = (let _152_414 = (let _152_413 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_152_413))
in (_152_414, [], Some (t)))
in (_152_415, def))
end else begin
((FStar_Util.Inl (id), [], Some (t)), def)
end
end
| FStar_Parser_AST.PatVar (id, _63_1185) -> begin
if top_level then begin
(let _152_418 = (let _152_417 = (let _152_416 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_152_416))
in (_152_417, [], None))
in (_152_418, def))
end else begin
((FStar_Util.Inl (id), [], None), def)
end
end
| _63_1189 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected let binding", p.FStar_Parser_AST.prange))))
end)
end)
end
end))))
in (
# 666 "FStar.Parser.ToSyntax.fst"
let _63_1218 = (FStar_List.fold_left (fun _63_1194 _63_1203 -> (match ((_63_1194, _63_1203)) with
| ((env, fnames, rec_bindings), ((f, _63_1197, _63_1199), _63_1202)) -> begin
(
# 668 "FStar.Parser.ToSyntax.fst"
let _63_1214 = (match (f) with
| FStar_Util.Inl (x) -> begin
(
# 670 "FStar.Parser.ToSyntax.fst"
let _63_1208 = (FStar_Parser_Env.push_bv env x)
in (match (_63_1208) with
| (env, xx) -> begin
(let _152_422 = (let _152_421 = (FStar_Syntax_Syntax.mk_binder xx)
in (_152_421)::rec_bindings)
in (env, FStar_Util.Inl (xx), _152_422))
end))
end
| FStar_Util.Inr (l) -> begin
(let _152_423 = (FStar_Parser_Env.push_top_level_rec_binding env l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in (_152_423, FStar_Util.Inr (l), rec_bindings))
end)
in (match (_63_1214) with
| (env, lbname, rec_bindings) -> begin
(env, (lbname)::fnames, rec_bindings)
end))
end)) (env, [], []) funs)
in (match (_63_1218) with
| (env', fnames, rec_bindings) -> begin
(
# 676 "FStar.Parser.ToSyntax.fst"
let fnames = (FStar_List.rev fnames)
in (
# 678 "FStar.Parser.ToSyntax.fst"
let desugar_one_def = (fun env lbname _63_1229 -> (match (_63_1229) with
| ((_63_1224, args, result_t), def) -> begin
(
# 679 "FStar.Parser.ToSyntax.fst"
let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _152_430 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed ((def, t))) _152_430 FStar_Parser_AST.Expr))
end)
in (
# 682 "FStar.Parser.ToSyntax.fst"
let def = (match (args) with
| [] -> begin
def
end
| _63_1236 -> begin
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
(let _152_432 = (let _152_431 = (incr_delta_qualifier body)
in (FStar_Syntax_Syntax.lid_as_fv l _152_431 None))
in FStar_Util.Inr (_152_432))
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
in (let _152_435 = (let _152_434 = (let _152_433 = (FStar_Syntax_Subst.close rec_bindings body)
in ((is_rec, lbs), _152_433))
in FStar_Syntax_Syntax.Tm_let (_152_434))
in (FStar_All.pipe_left mk _152_435))))))
end))))
end))
in (
# 696 "FStar.Parser.ToSyntax.fst"
let ds_non_rec = (fun pat t1 t2 -> (
# 697 "FStar.Parser.ToSyntax.fst"
let t1 = (desugar_term env t1)
in (
# 698 "FStar.Parser.ToSyntax.fst"
let _63_1255 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_63_1255) with
| (env, binder, pat) -> begin
(match (binder) with
| LetBinder (l, t) -> begin
(
# 701 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env t2)
in (
# 702 "FStar.Parser.ToSyntax.fst"
let fv = (let _152_442 = (incr_delta_qualifier t1)
in (FStar_Syntax_Syntax.lid_as_fv l _152_442 None))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]), body))))))
end
| LocalBinder (x, _63_1264) -> begin
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
(let _152_447 = (let _152_446 = (let _152_445 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _152_444 = (let _152_443 = (FStar_Syntax_Util.branch (pat, None, body))
in (_152_443)::[])
in (_152_445, _152_444)))
in FStar_Syntax_Syntax.Tm_match (_152_446))
in (FStar_Syntax_Syntax.mk _152_447 None body.FStar_Syntax_Syntax.pos))
end)
in (let _152_452 = (let _152_451 = (let _152_450 = (let _152_449 = (let _152_448 = (FStar_Syntax_Syntax.mk_binder x)
in (_152_448)::[])
in (FStar_Syntax_Subst.close _152_449 body))
in ((false, ((mk_lb (FStar_Util.Inl (x), x.FStar_Syntax_Syntax.sort, t1)))::[]), _152_450))
in FStar_Syntax_Syntax.Tm_let (_152_451))
in (FStar_All.pipe_left mk _152_452))))
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
in (let _152_463 = (let _152_462 = (let _152_461 = (desugar_term env t1)
in (let _152_460 = (let _152_459 = (let _152_454 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (let _152_453 = (desugar_term env t2)
in (_152_454, None, _152_453)))
in (let _152_458 = (let _152_457 = (let _152_456 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (let _152_455 = (desugar_term env t3)
in (_152_456, None, _152_455)))
in (_152_457)::[])
in (_152_459)::_152_458))
in (_152_461, _152_460)))
in FStar_Syntax_Syntax.Tm_match (_152_462))
in (mk _152_463)))
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
let desugar_branch = (fun _63_1304 -> (match (_63_1304) with
| (pat, wopt, b) -> begin
(
# 736 "FStar.Parser.ToSyntax.fst"
let _63_1307 = (desugar_match_pat env pat)
in (match (_63_1307) with
| (env, pat) -> begin
(
# 737 "FStar.Parser.ToSyntax.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _152_466 = (desugar_term env e)
in Some (_152_466))
end)
in (
# 740 "FStar.Parser.ToSyntax.fst"
let b = (desugar_term env b)
in (FStar_Syntax_Util.branch (pat, wopt, b))))
end))
end))
in (let _152_470 = (let _152_469 = (let _152_468 = (desugar_term env e)
in (let _152_467 = (FStar_List.map desugar_branch branches)
in (_152_468, _152_467)))
in FStar_Syntax_Syntax.Tm_match (_152_469))
in (FStar_All.pipe_left mk _152_470)))
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
in (let _152_473 = (let _152_472 = (let _152_471 = (desugar_term env e)
in (_152_471, annot, None))
in FStar_Syntax_Syntax.Tm_ascribed (_152_472))
in (FStar_All.pipe_left mk _152_473)))))
end
| FStar_Parser_AST.Record (_63_1321, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected empty record", top.FStar_Parser_AST.range))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(
# 756 "FStar.Parser.ToSyntax.fst"
let _63_1332 = (FStar_List.hd fields)
in (match (_63_1332) with
| (f, _63_1331) -> begin
(
# 757 "FStar.Parser.ToSyntax.fst"
let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (
# 758 "FStar.Parser.ToSyntax.fst"
let _63_1338 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_63_1338) with
| (record, _63_1337) -> begin
(
# 759 "FStar.Parser.ToSyntax.fst"
let get_field = (fun xopt f -> (
# 760 "FStar.Parser.ToSyntax.fst"
let fn = f.FStar_Ident.ident
in (
# 761 "FStar.Parser.ToSyntax.fst"
let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _63_1346 -> (match (_63_1346) with
| (g, _63_1345) -> begin
(
# 762 "FStar.Parser.ToSyntax.fst"
let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_63_1350, e) -> begin
(let _152_481 = (qfn fn)
in (_152_481, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _152_484 = (let _152_483 = (let _152_482 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in (_152_482, top.FStar_Parser_AST.range))
in FStar_Syntax_Syntax.Error (_152_483))
in (Prims.raise _152_484))
end
| Some (x) -> begin
(let _152_485 = (qfn fn)
in (_152_485, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Project ((x, f))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end))))
in (
# 773 "FStar.Parser.ToSyntax.fst"
let recterm = (match (eopt) with
| None -> begin
(let _152_490 = (let _152_489 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _63_1362 -> (match (_63_1362) with
| (f, _63_1361) -> begin
(let _152_488 = (let _152_487 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _152_487))
in (_152_488, FStar_Parser_AST.Nothing))
end))))
in (record.FStar_Parser_Env.constrname, _152_489))
in FStar_Parser_AST.Construct (_152_490))
end
| Some (e) -> begin
(
# 780 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (
# 781 "FStar.Parser.ToSyntax.fst"
let xterm = (let _152_492 = (let _152_491 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_152_491))
in (FStar_Parser_AST.mk_term _152_492 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (
# 782 "FStar.Parser.ToSyntax.fst"
let record = (let _152_495 = (let _152_494 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _63_1370 -> (match (_63_1370) with
| (f, _63_1369) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _152_494))
in FStar_Parser_AST.Record (_152_495))
in FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar ((x, None))) x.FStar_Ident.idRange), e))::[], (FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level))))))
end)
in (
# 785 "FStar.Parser.ToSyntax.fst"
let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (
# 786 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _63_1386; FStar_Syntax_Syntax.pos = _63_1384; FStar_Syntax_Syntax.vars = _63_1382}, args); FStar_Syntax_Syntax.tk = _63_1380; FStar_Syntax_Syntax.pos = _63_1378; FStar_Syntax_Syntax.vars = _63_1376}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(
# 789 "FStar.Parser.ToSyntax.fst"
let e = (let _152_503 = (let _152_502 = (let _152_501 = (let _152_500 = (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos)
in (let _152_499 = (let _152_498 = (let _152_497 = (let _152_496 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _152_496))
in FStar_Syntax_Syntax.Record_ctor (_152_497))
in Some (_152_498))
in (FStar_Syntax_Syntax.fvar _152_500 FStar_Syntax_Syntax.Delta_constant _152_499)))
in (_152_501, args))
in FStar_Syntax_Syntax.Tm_app (_152_502))
in (FStar_All.pipe_left mk _152_503))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end
| _63_1400 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(
# 797 "FStar.Parser.ToSyntax.fst"
let _63_1407 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_projector_by_field_name env) f)
in (match (_63_1407) with
| (fieldname, is_rec) -> begin
(
# 798 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env e)
in (
# 799 "FStar.Parser.ToSyntax.fst"
let fn = (
# 800 "FStar.Parser.ToSyntax.fst"
let _63_1412 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_63_1412) with
| (ns, _63_1411) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (
# 802 "FStar.Parser.ToSyntax.fst"
let qual = if is_rec then begin
Some (FStar_Syntax_Syntax.Record_projector (fn))
end else begin
None
end
in (let _152_509 = (let _152_508 = (let _152_507 = (let _152_504 = (FStar_Ident.set_lid_range fieldname (FStar_Ident.range_of_lid f))
in (FStar_Syntax_Syntax.fvar _152_504 FStar_Syntax_Syntax.Delta_equational qual))
in (let _152_506 = (let _152_505 = (FStar_Syntax_Syntax.as_arg e)
in (_152_505)::[])
in (_152_507, _152_506)))
in FStar_Syntax_Syntax.Tm_app (_152_508))
in (FStar_All.pipe_left mk _152_509)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| _63_1422 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _63_1424 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_args : FStar_Parser_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun _63_1429 -> (match (_63_1429) with
| (a, imp) -> begin
(let _152_513 = (desugar_term env a)
in (arg_withimp_e imp _152_513))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r default_ok env t -> (
# 819 "FStar.Parser.ToSyntax.fst"
let fail = (fun msg -> (Prims.raise (FStar_Syntax_Syntax.Error ((msg, r)))))
in (
# 820 "FStar.Parser.ToSyntax.fst"
let is_requires = (fun _63_1441 -> (match (_63_1441) with
| (t, _63_1440) -> begin
(match ((let _152_521 = (unparen t)
in _152_521.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Requires (_63_1443) -> begin
true
end
| _63_1446 -> begin
false
end)
end))
in (
# 823 "FStar.Parser.ToSyntax.fst"
let is_ensures = (fun _63_1451 -> (match (_63_1451) with
| (t, _63_1450) -> begin
(match ((let _152_524 = (unparen t)
in _152_524.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ensures (_63_1453) -> begin
true
end
| _63_1456 -> begin
false
end)
end))
in (
# 826 "FStar.Parser.ToSyntax.fst"
let is_app = (fun head _63_1462 -> (match (_63_1462) with
| (t, _63_1461) -> begin
(match ((let _152_529 = (unparen t)
in _152_529.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _63_1466; FStar_Parser_AST.level = _63_1464}, _63_1471, _63_1473) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| _63_1477 -> begin
false
end)
end))
in (
# 829 "FStar.Parser.ToSyntax.fst"
let is_decreases = (is_app "decreases")
in (
# 830 "FStar.Parser.ToSyntax.fst"
let pre_process_comp_typ = (fun t -> (
# 831 "FStar.Parser.ToSyntax.fst"
let _63_1483 = (head_and_args t)
in (match (_63_1483) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(
# 834 "FStar.Parser.ToSyntax.fst"
let unit_tm = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (
# 835 "FStar.Parser.ToSyntax.fst"
let nil_pat = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr), FStar_Parser_AST.Nothing)
in (
# 836 "FStar.Parser.ToSyntax.fst"
let req_true = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Requires (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.true_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Formula), None))) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (
# 837 "FStar.Parser.ToSyntax.fst"
let args = (match (args) with
| [] -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Not enough arguments to \'Lemma\'", t.FStar_Parser_AST.range))))
end
| ens::[] -> begin
(unit_tm)::(req_true)::(ens)::(nil_pat)::[]
end
| req::ens::[] when ((is_requires req) && (is_ensures ens)) -> begin
(unit_tm)::(req)::(ens)::(nil_pat)::[]
end
| ens::dec::[] when ((is_ensures ens) && (is_decreases dec)) -> begin
(unit_tm)::(req_true)::(ens)::(nil_pat)::(dec)::[]
end
| req::ens::dec::[] when (((is_requires req) && (is_ensures ens)) && (is_app "decreases" dec)) -> begin
(unit_tm)::(req)::(ens)::(nil_pat)::(dec)::[]
end
| more -> begin
(unit_tm)::more
end)
in (
# 844 "FStar.Parser.ToSyntax.fst"
let head = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_name env) lemma)
in (head, args))))))
end
| FStar_Parser_AST.Name (l) when (FStar_Parser_Env.is_effect_name env l) -> begin
(let _152_533 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_name env) l)
in (_152_533, args))
end
| FStar_Parser_AST.Name (l) when ((let _152_534 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _152_534 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(let _152_535 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in (_152_535, args))
end
| FStar_Parser_AST.Name (l) when ((let _152_536 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _152_536 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(let _152_537 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)
in (_152_537, args))
end
| FStar_Parser_AST.Name (l) when ((((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) && default_ok) -> begin
(let _152_538 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in (_152_538, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _63_1514 when default_ok -> begin
(let _152_539 = (FStar_Ident.set_lid_range env.FStar_Parser_Env.default_result_effect head.FStar_Parser_AST.range)
in (_152_539, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _63_1516 -> begin
(let _152_541 = (let _152_540 = (FStar_Parser_AST.term_to_string t)
in (FStar_Util.format1 "%s is not an effect" _152_540))
in (fail _152_541))
end)
end)))
in (
# 874 "FStar.Parser.ToSyntax.fst"
let _63_1519 = (pre_process_comp_typ t)
in (match (_63_1519) with
| (eff, args) -> begin
(
# 875 "FStar.Parser.ToSyntax.fst"
let _63_1520 = if ((FStar_List.length args) = 0) then begin
(let _152_543 = (let _152_542 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" _152_542))
in (fail _152_543))
end else begin
()
end
in (
# 877 "FStar.Parser.ToSyntax.fst"
let _63_1524 = (let _152_545 = (FStar_List.hd args)
in (let _152_544 = (FStar_List.tl args)
in (_152_545, _152_544)))
in (match (_63_1524) with
| (result_arg, rest) -> begin
(
# 878 "FStar.Parser.ToSyntax.fst"
let result_typ = (desugar_typ env (Prims.fst result_arg))
in (
# 879 "FStar.Parser.ToSyntax.fst"
let rest = (desugar_args env rest)
in (
# 880 "FStar.Parser.ToSyntax.fst"
let _63_1549 = (FStar_All.pipe_right rest (FStar_List.partition (fun _63_1530 -> (match (_63_1530) with
| (t, _63_1529) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _63_1536; FStar_Syntax_Syntax.pos = _63_1534; FStar_Syntax_Syntax.vars = _63_1532}, _63_1541::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| _63_1546 -> begin
false
end)
end))))
in (match (_63_1549) with
| (dec, rest) -> begin
(
# 886 "FStar.Parser.ToSyntax.fst"
let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _63_1553 -> (match (_63_1553) with
| (t, _63_1552) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_63_1555, (arg, _63_1558)::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| _63_1564 -> begin
(FStar_All.failwith "impos")
end)
end))))
in (
# 890 "FStar.Parser.ToSyntax.fst"
let no_additional_args = (((FStar_List.length decreases_clause) = 0) && ((FStar_List.length rest) = 0))
in if (no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid)) then begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end else begin
if (no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid)) then begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end else begin
(
# 898 "FStar.Parser.ToSyntax.fst"
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
# 904 "FStar.Parser.ToSyntax.fst"
let rest = if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid) then begin
(match (rest) with
| req::ens::(pat, aq)::[] -> begin
(
# 908 "FStar.Parser.ToSyntax.fst"
let pat = (match (pat.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
(
# 910 "FStar.Parser.ToSyntax.fst"
let nil = (FStar_Syntax_Syntax.mk_Tm_uinst pat ((FStar_Syntax_Syntax.U_succ (FStar_Syntax_Syntax.U_zero))::[]))
in (
# 911 "FStar.Parser.ToSyntax.fst"
let pattern = (let _152_549 = (let _152_548 = (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _152_548 FStar_Syntax_Syntax.Delta_constant None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _152_549 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app nil (((pattern, Some (FStar_Syntax_Syntax.imp_tag)))::[]) None pat.FStar_Syntax_Syntax.pos)))
end
| _63_1579 -> begin
pat
end)
in (let _152_553 = (let _152_552 = (let _152_551 = (let _152_550 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((pat, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)))) None pat.FStar_Syntax_Syntax.pos)
in (_152_550, aq))
in (_152_551)::[])
in (ens)::_152_552)
in (req)::_152_553))
end
| _63_1582 -> begin
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
# 924 "FStar.Parser.ToSyntax.fst"
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
| _63_1594 -> begin
None
end))
in (
# 931 "FStar.Parser.ToSyntax.fst"
let mk = (fun t -> (FStar_Syntax_Syntax.mk t None f.FStar_Parser_AST.range))
in (
# 932 "FStar.Parser.ToSyntax.fst"
let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (
# 933 "FStar.Parser.ToSyntax.fst"
let setpos = (fun t -> (
# 933 "FStar.Parser.ToSyntax.fst"
let _63_1601 = t
in {FStar_Syntax_Syntax.n = _63_1601.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _63_1601.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _63_1601.FStar_Syntax_Syntax.vars}))
in (
# 934 "FStar.Parser.ToSyntax.fst"
let desugar_quant = (fun q b pats body -> (
# 935 "FStar.Parser.ToSyntax.fst"
let tk = (desugar_binder env (
# 935 "FStar.Parser.ToSyntax.fst"
let _63_1608 = b
in {FStar_Parser_AST.b = _63_1608.FStar_Parser_AST.b; FStar_Parser_AST.brange = _63_1608.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _63_1608.FStar_Parser_AST.aqual}))
in (
# 936 "FStar.Parser.ToSyntax.fst"
let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _152_588 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _152_588)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(
# 939 "FStar.Parser.ToSyntax.fst"
let _63_1622 = (FStar_Parser_Env.push_bv env a)
in (match (_63_1622) with
| (env, a) -> begin
(
# 940 "FStar.Parser.ToSyntax.fst"
let a = (
# 940 "FStar.Parser.ToSyntax.fst"
let _63_1623 = a
in {FStar_Syntax_Syntax.ppname = _63_1623.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_1623.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (
# 941 "FStar.Parser.ToSyntax.fst"
let pats = (desugar_pats env pats)
in (
# 942 "FStar.Parser.ToSyntax.fst"
let body = (desugar_formula env body)
in (
# 943 "FStar.Parser.ToSyntax.fst"
let body = (match (pats) with
| [] -> begin
body
end
| _63_1630 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((body, FStar_Syntax_Syntax.Meta_pattern (pats)))))
end)
in (
# 946 "FStar.Parser.ToSyntax.fst"
let body = (let _152_591 = (let _152_590 = (let _152_589 = (FStar_Syntax_Syntax.mk_binder a)
in (_152_589)::[])
in (no_annot_abs _152_590 body))
in (FStar_All.pipe_left setpos _152_591))
in (let _152_597 = (let _152_596 = (let _152_595 = (let _152_592 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Syntax_Syntax.fvar _152_592 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (let _152_594 = (let _152_593 = (FStar_Syntax_Syntax.as_arg body)
in (_152_593)::[])
in (_152_595, _152_594)))
in FStar_Syntax_Syntax.Tm_app (_152_596))
in (FStar_All.pipe_left mk _152_597)))))))
end))
end
| _63_1634 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 951 "FStar.Parser.ToSyntax.fst"
let push_quant = (fun q binders pats body -> (match (binders) with
| b::b'::_rest -> begin
(
# 953 "FStar.Parser.ToSyntax.fst"
let rest = (b')::_rest
in (
# 954 "FStar.Parser.ToSyntax.fst"
let body = (let _152_612 = (q (rest, pats, body))
in (let _152_611 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _152_612 _152_611 FStar_Parser_AST.Formula)))
in (let _152_613 = (q ((b)::[], [], body))
in (FStar_Parser_AST.mk_term _152_613 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _63_1648 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _152_614 = (unparen f)
in _152_614.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(
# 960 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env f)
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta ((f, FStar_Syntax_Syntax.Meta_labeled ((l, f.FStar_Syntax_Syntax.pos, p)))))))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall (_1::_2::_3, pats, body) -> begin
(
# 967 "FStar.Parser.ToSyntax.fst"
let binders = (_1)::(_2)::_3
in (let _152_616 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _152_616)))
end
| FStar_Parser_AST.QExists (_1::_2::_3, pats, body) -> begin
(
# 971 "FStar.Parser.ToSyntax.fst"
let binders = (_1)::(_2)::_3
in (let _152_618 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _152_618)))
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
| _63_1706 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (
# 986 "FStar.Parser.ToSyntax.fst"
let _63_1730 = (FStar_List.fold_left (fun _63_1711 b -> (match (_63_1711) with
| (env, out) -> begin
(
# 987 "FStar.Parser.ToSyntax.fst"
let tk = (desugar_binder env (
# 987 "FStar.Parser.ToSyntax.fst"
let _63_1713 = b
in {FStar_Parser_AST.b = _63_1713.FStar_Parser_AST.b; FStar_Parser_AST.brange = _63_1713.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _63_1713.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(
# 990 "FStar.Parser.ToSyntax.fst"
let _63_1722 = (FStar_Parser_Env.push_bv env a)
in (match (_63_1722) with
| (env, a) -> begin
(
# 991 "FStar.Parser.ToSyntax.fst"
let a = (
# 991 "FStar.Parser.ToSyntax.fst"
let _63_1723 = a
in {FStar_Syntax_Syntax.ppname = _63_1723.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_1723.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (env, ((a, (trans_aqual b.FStar_Parser_AST.aqual)))::out))
end))
end
| _63_1727 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected binder", b.FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_63_1730) with
| (env, tpars) -> begin
(env, (FStar_List.rev tpars))
end)))
and desugar_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(let _152_625 = (desugar_typ env t)
in (Some (x), _152_625))
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _152_626 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None x.FStar_Ident.idRange)
in (Some (x), _152_626))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _152_627 = (desugar_typ env t)
in (None, _152_627))
end
| FStar_Parser_AST.Variable (x) -> begin
(Some (x), FStar_Syntax_Syntax.tun)
end))

# 1003 "FStar.Parser.ToSyntax.fst"
let mk_data_discriminators : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  FStar_Ident.lid  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun quals env t tps k datas -> (
# 1004 "FStar.Parser.ToSyntax.fst"
let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_Env.iface) || env.FStar_Parser_Env.admitted_iface) then begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (
# 1007 "FStar.Parser.ToSyntax.fst"
let binders = (let _152_643 = (let _152_642 = (FStar_Syntax_Util.arrow_formals k)
in (Prims.fst _152_642))
in (FStar_List.append tps _152_643))
in (
# 1008 "FStar.Parser.ToSyntax.fst"
let p = (FStar_Ident.range_of_lid t)
in (
# 1009 "FStar.Parser.ToSyntax.fst"
let _63_1757 = (FStar_Syntax_Util.args_of_binders binders)
in (match (_63_1757) with
| (binders, args) -> begin
(
# 1010 "FStar.Parser.ToSyntax.fst"
let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _63_1761 -> (match (_63_1761) with
| (x, _63_1760) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
in (
# 1011 "FStar.Parser.ToSyntax.fst"
let binders = (let _152_649 = (let _152_648 = (let _152_647 = (let _152_646 = (let _152_645 = (FStar_Syntax_Syntax.lid_as_fv t FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _152_645))
in (FStar_Syntax_Syntax.mk_Tm_app _152_646 args None p))
in (FStar_All.pipe_left FStar_Syntax_Syntax.null_binder _152_647))
in (_152_648)::[])
in (FStar_List.append imp_binders _152_649))
in (
# 1012 "FStar.Parser.ToSyntax.fst"
let disc_type = (let _152_652 = (let _152_651 = (let _152_650 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _152_650))
in (FStar_Syntax_Syntax.mk_Total _152_651))
in (FStar_Syntax_Util.arrow binders _152_652))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (
# 1014 "FStar.Parser.ToSyntax.fst"
let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (let _152_655 = (let _152_654 = (quals ((FStar_Syntax_Syntax.Logic)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in (disc_name, [], disc_type, _152_654, (FStar_Ident.range_of_lid disc_name)))
in FStar_Syntax_Syntax.Sig_declare_typ (_152_655)))))))))
end))))))

# 1017 "FStar.Parser.ToSyntax.fst"
let mk_indexed_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq refine_domain env tc lid inductive_tps imp_tps fields t -> (
# 1018 "FStar.Parser.ToSyntax.fst"
let p = (FStar_Ident.range_of_lid lid)
in (
# 1019 "FStar.Parser.ToSyntax.fst"
let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p))
in (
# 1020 "FStar.Parser.ToSyntax.fst"
let projectee = (fun ptyp -> (FStar_Syntax_Syntax.gen_bv "projectee" (Some (p)) ptyp))
in (
# 1021 "FStar.Parser.ToSyntax.fst"
let tps = (FStar_List.map2 (fun _63_1785 _63_1789 -> (match ((_63_1785, _63_1789)) with
| ((_63_1783, imp), (x, _63_1788)) -> begin
(x, imp)
end)) inductive_tps imp_tps)
in (
# 1022 "FStar.Parser.ToSyntax.fst"
let _63_1890 = (
# 1023 "FStar.Parser.ToSyntax.fst"
let _63_1793 = (FStar_Syntax_Util.head_and_args t)
in (match (_63_1793) with
| (head, args0) -> begin
(
# 1024 "FStar.Parser.ToSyntax.fst"
let args = (
# 1025 "FStar.Parser.ToSyntax.fst"
let rec arguments = (fun tps args -> (match ((tps, args)) with
| ([], _63_1799) -> begin
args
end
| (_63_1802, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Not enough arguments to type", (FStar_Ident.range_of_lid lid)))))
end
| ((_63_1807, Some (FStar_Syntax_Syntax.Implicit (_63_1809)))::tps', (_63_1816, Some (FStar_Syntax_Syntax.Implicit (_63_1818)))::args') -> begin
(arguments tps' args')
end
| ((_63_1826, Some (FStar_Syntax_Syntax.Implicit (_63_1828)))::tps', (_63_1836, _63_1838)::_63_1834) -> begin
(arguments tps' args)
end
| ((_63_1845, _63_1847)::_63_1843, (a, Some (FStar_Syntax_Syntax.Implicit (_63_1854)))::_63_1851) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected implicit annotation on argument", a.FStar_Syntax_Syntax.pos))))
end
| ((_63_1862, _63_1864)::tps', (_63_1869, _63_1871)::args') -> begin
(arguments tps' args')
end))
in (arguments inductive_tps args0))
in (
# 1034 "FStar.Parser.ToSyntax.fst"
let indices = (FStar_All.pipe_right args (FStar_List.map (fun _63_1876 -> (let _152_687 = (FStar_Syntax_Syntax.new_bv (Some (p)) FStar_Syntax_Syntax.tun)
in (FStar_All.pipe_right _152_687 FStar_Syntax_Syntax.mk_binder)))))
in (
# 1035 "FStar.Parser.ToSyntax.fst"
let arg_typ = (let _152_692 = (let _152_688 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _152_688))
in (let _152_691 = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _63_1881 -> (match (_63_1881) with
| (x, imp) -> begin
(let _152_690 = (FStar_Syntax_Syntax.bv_to_name x)
in (_152_690, imp))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app _152_692 _152_691 None p)))
in (
# 1037 "FStar.Parser.ToSyntax.fst"
let arg_binder = if (not (refine_domain)) then begin
(let _152_693 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder _152_693))
end else begin
(
# 1040 "FStar.Parser.ToSyntax.fst"
let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (
# 1041 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p)) arg_typ)
in (let _152_702 = (
# 1042 "FStar.Parser.ToSyntax.fst"
let _63_1885 = (projectee arg_typ)
in (let _152_701 = (let _152_700 = (let _152_699 = (let _152_698 = (let _152_694 = (FStar_Ident.set_lid_range disc_name p)
in (FStar_Syntax_Syntax.fvar _152_694 FStar_Syntax_Syntax.Delta_equational None))
in (let _152_697 = (let _152_696 = (let _152_695 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _152_695))
in (_152_696)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _152_698 _152_697 None p)))
in (FStar_Syntax_Util.b2t _152_699))
in (FStar_Syntax_Util.refine x _152_700))
in {FStar_Syntax_Syntax.ppname = _63_1885.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_1885.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _152_701}))
in (FStar_Syntax_Syntax.mk_binder _152_702))))
end
in (arg_binder, indices)))))
end))
in (match (_63_1890) with
| (arg_binder, indices) -> begin
(
# 1046 "FStar.Parser.ToSyntax.fst"
let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder))
in (
# 1047 "FStar.Parser.ToSyntax.fst"
let imp_binders = (let _152_704 = (FStar_All.pipe_right indices (FStar_List.map (fun _63_1895 -> (match (_63_1895) with
| (x, _63_1894) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
in (FStar_List.append imp_tps _152_704))
in (
# 1048 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (
# 1050 "FStar.Parser.ToSyntax.fst"
let arg = (FStar_Syntax_Util.arg_of_non_null_binder arg_binder)
in (
# 1052 "FStar.Parser.ToSyntax.fst"
let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _63_1903 -> (match (_63_1903) with
| (a, _63_1902) -> begin
(
# 1053 "FStar.Parser.ToSyntax.fst"
let _63_1907 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (_63_1907) with
| (field_name, _63_1906) -> begin
(
# 1054 "FStar.Parser.ToSyntax.fst"
let proj = (let _152_708 = (let _152_707 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.fv_to_tm _152_707))
in (FStar_Syntax_Syntax.mk_Tm_app _152_708 ((arg)::[]) None p))
in FStar_Syntax_Syntax.NT ((a, proj)))
end))
end))))
in (
# 1057 "FStar.Parser.ToSyntax.fst"
let ntps = (FStar_List.length tps)
in (
# 1058 "FStar.Parser.ToSyntax.fst"
let all_params = (FStar_List.append imp_tps fields)
in (let _152_744 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _63_1916 -> (match (_63_1916) with
| (x, _63_1915) -> begin
(
# 1061 "FStar.Parser.ToSyntax.fst"
let _63_1920 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_63_1920) with
| (field_name, _63_1919) -> begin
(
# 1062 "FStar.Parser.ToSyntax.fst"
let t = (let _152_712 = (let _152_711 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total _152_711))
in (FStar_Syntax_Util.arrow binders _152_712))
in (
# 1063 "FStar.Parser.ToSyntax.fst"
let only_decl = (((let _152_713 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _152_713)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _152_715 = (let _152_714 = (FStar_Parser_Env.current_module env)
in _152_714.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _152_715)))
in (
# 1067 "FStar.Parser.ToSyntax.fst"
let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (
# 1068 "FStar.Parser.ToSyntax.fst"
let quals = (fun q -> if only_decl then begin
(FStar_Syntax_Syntax.Assumption)::q
end else begin
q
end)
in (
# 1069 "FStar.Parser.ToSyntax.fst"
let quals = (quals ((FStar_Syntax_Syntax.Projector ((lid, x.FStar_Syntax_Syntax.ppname)))::iquals))
in (
# 1070 "FStar.Parser.ToSyntax.fst"
let decl = FStar_Syntax_Syntax.Sig_declare_typ ((field_name, [], t, quals, (FStar_Ident.range_of_lid field_name)))
in if only_decl then begin
(decl)::[]
end else begin
(
# 1073 "FStar.Parser.ToSyntax.fst"
let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (
# 1074 "FStar.Parser.ToSyntax.fst"
let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _63_1932 -> (match (_63_1932) with
| (x, imp) -> begin
(
# 1075 "FStar.Parser.ToSyntax.fst"
let b = (FStar_Syntax_Syntax.is_implicit imp)
in if ((i + ntps) = j) then begin
(let _152_720 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in (_152_720, b))
end else begin
if (b && (j < ntps)) then begin
(let _152_724 = (let _152_723 = (let _152_722 = (let _152_721 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (_152_721, FStar_Syntax_Syntax.tun))
in FStar_Syntax_Syntax.Pat_dot_term (_152_722))
in (pos _152_723))
in (_152_724, b))
end else begin
(let _152_727 = (let _152_726 = (let _152_725 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_152_725))
in (pos _152_726))
in (_152_727, b))
end
end)
end))))
in (
# 1081 "FStar.Parser.ToSyntax.fst"
let pat = (let _152_732 = (let _152_730 = (let _152_729 = (let _152_728 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in (_152_728, arg_pats))
in FStar_Syntax_Syntax.Pat_cons (_152_729))
in (FStar_All.pipe_right _152_730 pos))
in (let _152_731 = (FStar_Syntax_Syntax.bv_to_name projection)
in (_152_732, None, _152_731)))
in (
# 1082 "FStar.Parser.ToSyntax.fst"
let body = (let _152_736 = (let _152_735 = (let _152_734 = (let _152_733 = (FStar_Syntax_Util.branch pat)
in (_152_733)::[])
in (arg_exp, _152_734))
in FStar_Syntax_Syntax.Tm_match (_152_735))
in (FStar_Syntax_Syntax.mk _152_736 None p))
in (
# 1083 "FStar.Parser.ToSyntax.fst"
let imp = (no_annot_abs binders body)
in (
# 1084 "FStar.Parser.ToSyntax.fst"
let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end else begin
FStar_Syntax_Syntax.Delta_equational
end
in (
# 1087 "FStar.Parser.ToSyntax.fst"
let lb = (let _152_738 = (let _152_737 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (_152_737))
in {FStar_Syntax_Syntax.lbname = _152_738; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = imp})
in (
# 1092 "FStar.Parser.ToSyntax.fst"
let impl = (let _152_743 = (let _152_742 = (let _152_741 = (let _152_740 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _152_740 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_152_741)::[])
in ((false, (lb)::[]), p, _152_742, quals))
in FStar_Syntax_Syntax.Sig_let (_152_743))
in if no_decl then begin
(impl)::[]
end else begin
(decl)::(impl)::[]
end))))))))
end))))))
end))
end))))
in (FStar_All.pipe_right _152_744 FStar_List.flatten)))))))))
end)))))))

# 1095 "FStar.Parser.ToSyntax.fst"
let mk_data_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env _63_1946 -> (match (_63_1946) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _63_1949, t, l, n, quals, _63_1955, _63_1957) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(
# 1098 "FStar.Parser.ToSyntax.fst"
let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_10 -> (match (_63_10) with
| FStar_Syntax_Syntax.RecordConstructor (_63_1962) -> begin
true
end
| _63_1965 -> begin
false
end)))) then begin
false
end else begin
(match ((FStar_Parser_Env.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > 1)
end
| _63_1969 -> begin
true
end)
end
in (
# 1104 "FStar.Parser.ToSyntax.fst"
let _63_1973 = (FStar_Syntax_Util.arrow_formals t)
in (match (_63_1973) with
| (formals, cod) -> begin
(match (formals) with
| [] -> begin
[]
end
| _63_1976 -> begin
(
# 1108 "FStar.Parser.ToSyntax.fst"
let fv_qual = (match ((FStar_Util.find_map quals (fun _63_11 -> (match (_63_11) with
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((lid, fns)))
end
| _63_1981 -> begin
None
end)))) with
| None -> begin
FStar_Syntax_Syntax.Data_ctor
end
| Some (q) -> begin
q
end)
in (
# 1111 "FStar.Parser.ToSyntax.fst"
let iquals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract iquals) then begin
(FStar_Syntax_Syntax.Private)::iquals
end else begin
iquals
end
in (
# 1114 "FStar.Parser.ToSyntax.fst"
let _63_1989 = (FStar_Util.first_N n formals)
in (match (_63_1989) with
| (tps, rest) -> begin
(mk_indexed_projectors iquals fv_qual refine_domain env l lid inductive_tps tps rest cod)
end))))
end)
end)))
end
| _63_1991 -> begin
[]
end)
end))

# 1120 "FStar.Parser.ToSyntax.fst"
let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (
# 1121 "FStar.Parser.ToSyntax.fst"
let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _152_769 = (incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (_152_769))
end else begin
(incr_delta_qualifier t)
end
in (
# 1124 "FStar.Parser.ToSyntax.fst"
let lb = (let _152_774 = (let _152_770 = (FStar_Syntax_Syntax.lid_as_fv lid dd None)
in FStar_Util.Inr (_152_770))
in (let _152_773 = (let _152_771 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars _152_771))
in (let _152_772 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = _152_774; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = _152_773; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _152_772})))
in FStar_Syntax_Syntax.Sig_let (((false, (lb)::[]), rng, lids, quals)))))

# 1133 "FStar.Parser.ToSyntax.fst"
let rec desugar_tycon : FStar_Parser_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (
# 1134 "FStar.Parser.ToSyntax.fst"
let tycon_id = (fun _63_12 -> (match (_63_12) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (
# 1139 "FStar.Parser.ToSyntax.fst"
let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _152_788 = (let _152_787 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_152_787))
in (FStar_Parser_AST.mk_term _152_788 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| (FStar_Parser_AST.TAnnotated (a, _)) | (FStar_Parser_AST.TVariable (a)) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar (a)) a.FStar_Ident.idRange FStar_Parser_AST.Type)
end
| FStar_Parser_AST.NoName (t) -> begin
t
end))
in (
# 1145 "FStar.Parser.ToSyntax.fst"
let tot = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) rng FStar_Parser_AST.Expr)
in (
# 1146 "FStar.Parser.ToSyntax.fst"
let with_constructor_effect = (fun t -> (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((tot, t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level))
in (
# 1147 "FStar.Parser.ToSyntax.fst"
let apply_binders = (fun t binders -> (
# 1148 "FStar.Parser.ToSyntax.fst"
let imp_of_aqual = (fun b -> (match (b.FStar_Parser_AST.aqual) with
| Some (FStar_Parser_AST.Implicit) -> begin
FStar_Parser_AST.Hash
end
| _63_2066 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _152_801 = (let _152_800 = (let _152_799 = (binder_to_term b)
in (out, _152_799, (imp_of_aqual b)))
in FStar_Parser_AST.App (_152_800))
in (FStar_Parser_AST.mk_term _152_801 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (
# 1153 "FStar.Parser.ToSyntax.fst"
let tycon_record_as_variant = (fun _63_13 -> (match (_63_13) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(
# 1155 "FStar.Parser.ToSyntax.fst"
let constrName = (FStar_Ident.mk_ident ((Prims.strcat "Mk" id.FStar_Ident.idText), id.FStar_Ident.idRange))
in (
# 1156 "FStar.Parser.ToSyntax.fst"
let mfields = (FStar_List.map (fun _63_2079 -> (match (_63_2079) with
| (x, t) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated (((FStar_Syntax_Util.mangle_field_name x), t))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (
# 1157 "FStar.Parser.ToSyntax.fst"
let result = (let _152_807 = (let _152_806 = (let _152_805 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_152_805))
in (FStar_Parser_AST.mk_term _152_806 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _152_807 parms))
in (
# 1158 "FStar.Parser.ToSyntax.fst"
let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _152_809 = (FStar_All.pipe_right fields (FStar_List.map (fun _63_2086 -> (match (_63_2086) with
| (x, _63_2085) -> begin
(FStar_Parser_Env.qualify env x)
end))))
in (FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _152_809))))))
end
| _63_2088 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1162 "FStar.Parser.ToSyntax.fst"
let desugar_abstract_tc = (fun quals _env mutuals _63_14 -> (match (_63_14) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(
# 1164 "FStar.Parser.ToSyntax.fst"
let _63_2102 = (typars_of_binders _env binders)
in (match (_63_2102) with
| (_env', typars) -> begin
(
# 1165 "FStar.Parser.ToSyntax.fst"
let k = (match (kopt) with
| None -> begin
FStar_Syntax_Util.ktype
end
| Some (k) -> begin
(desugar_term _env' k)
end)
in (
# 1168 "FStar.Parser.ToSyntax.fst"
let tconstr = (let _152_820 = (let _152_819 = (let _152_818 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_152_818))
in (FStar_Parser_AST.mk_term _152_819 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _152_820 binders))
in (
# 1169 "FStar.Parser.ToSyntax.fst"
let qlid = (FStar_Parser_Env.qualify _env id)
in (
# 1170 "FStar.Parser.ToSyntax.fst"
let typars = (FStar_Syntax_Subst.close_binders typars)
in (
# 1171 "FStar.Parser.ToSyntax.fst"
let k = (FStar_Syntax_Subst.close typars k)
in (
# 1172 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_inductive_typ ((qlid, [], typars, k, mutuals, [], quals, rng))
in (
# 1173 "FStar.Parser.ToSyntax.fst"
let _env = (FStar_Parser_Env.push_top_level_rec_binding _env id FStar_Syntax_Syntax.Delta_constant)
in (
# 1174 "FStar.Parser.ToSyntax.fst"
let _env2 = (FStar_Parser_Env.push_top_level_rec_binding _env' id FStar_Syntax_Syntax.Delta_constant)
in (_env, _env2, se, tconstr)))))))))
end))
end
| _63_2115 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (
# 1177 "FStar.Parser.ToSyntax.fst"
let push_tparams = (fun env bs -> (
# 1178 "FStar.Parser.ToSyntax.fst"
let _63_2130 = (FStar_List.fold_left (fun _63_2121 _63_2124 -> (match ((_63_2121, _63_2124)) with
| ((env, tps), (x, imp)) -> begin
(
# 1179 "FStar.Parser.ToSyntax.fst"
let _63_2127 = (FStar_Parser_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (_63_2127) with
| (env, y) -> begin
(env, ((y, imp))::tps)
end))
end)) (env, []) bs)
in (match (_63_2130) with
| (env, bs) -> begin
(env, (FStar_List.rev bs))
end)))
in (match (tcs) with
| FStar_Parser_AST.TyconAbstract (id, bs, kopt)::[] -> begin
(
# 1184 "FStar.Parser.ToSyntax.fst"
let kopt = (match (kopt) with
| None -> begin
(let _152_827 = (tm_type_z id.FStar_Ident.idRange)
in Some (_152_827))
end
| _63_2139 -> begin
kopt
end)
in (
# 1187 "FStar.Parser.ToSyntax.fst"
let tc = FStar_Parser_AST.TyconAbstract ((id, bs, kopt))
in (
# 1188 "FStar.Parser.ToSyntax.fst"
let _63_2149 = (desugar_abstract_tc quals env [] tc)
in (match (_63_2149) with
| (_63_2143, _63_2145, se, _63_2148) -> begin
(
# 1189 "FStar.Parser.ToSyntax.fst"
let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _63_2152, typars, k, [], [], quals, rng) -> begin
(
# 1191 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
quals
end else begin
(
# 1193 "FStar.Parser.ToSyntax.fst"
let _63_2161 = (let _152_829 = (FStar_Range.string_of_range rng)
in (let _152_828 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" _152_829 _152_828)))
in (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals)
end
in (
# 1196 "FStar.Parser.ToSyntax.fst"
let t = (match (typars) with
| [] -> begin
k
end
| _63_2166 -> begin
(let _152_832 = (let _152_831 = (let _152_830 = (FStar_Syntax_Syntax.mk_Total k)
in (typars, _152_830))
in FStar_Syntax_Syntax.Tm_arrow (_152_831))
in (FStar_Syntax_Syntax.mk _152_832 None rng))
end)
in FStar_Syntax_Syntax.Sig_declare_typ ((l, [], t, quals, rng))))
end
| _63_2169 -> begin
se
end)
in (
# 1201 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))
end))))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t)::[] -> begin
(
# 1206 "FStar.Parser.ToSyntax.fst"
let _63_2181 = (typars_of_binders env binders)
in (match (_63_2181) with
| (env', typars) -> begin
(
# 1207 "FStar.Parser.ToSyntax.fst"
let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _63_15 -> (match (_63_15) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| _63_2186 -> begin
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
# 1213 "FStar.Parser.ToSyntax.fst"
let t0 = t
in (
# 1214 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _63_16 -> (match (_63_16) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| _63_2194 -> begin
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
# 1219 "FStar.Parser.ToSyntax.fst"
let se = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Effect)) then begin
(
# 1221 "FStar.Parser.ToSyntax.fst"
let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (
# 1222 "FStar.Parser.ToSyntax.fst"
let typars = (FStar_Syntax_Subst.close_binders typars)
in (
# 1223 "FStar.Parser.ToSyntax.fst"
let c = (FStar_Syntax_Subst.close_comp typars c)
in (let _152_838 = (let _152_837 = (FStar_Parser_Env.qualify env id)
in (let _152_836 = (FStar_All.pipe_right quals (FStar_List.filter (fun _63_17 -> (match (_63_17) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| _63_2202 -> begin
true
end))))
in (_152_837, [], typars, c, _152_836, rng)))
in FStar_Syntax_Syntax.Sig_effect_abbrev (_152_838)))))
end else begin
(
# 1225 "FStar.Parser.ToSyntax.fst"
let t = (desugar_typ env' t)
in (
# 1226 "FStar.Parser.ToSyntax.fst"
let nm = (FStar_Parser_Env.qualify env id)
in (mk_typ_abbrev nm [] typars k t ((nm)::[]) quals rng)))
end
in (
# 1229 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[]))))))
end))
end
| FStar_Parser_AST.TyconRecord (_63_2208)::[] -> begin
(
# 1233 "FStar.Parser.ToSyntax.fst"
let trec = (FStar_List.hd tcs)
in (
# 1234 "FStar.Parser.ToSyntax.fst"
let _63_2214 = (tycon_record_as_variant trec)
in (match (_63_2214) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| _63_2218::_63_2216 -> begin
(
# 1238 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1239 "FStar.Parser.ToSyntax.fst"
let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_Env.qualify env) (tycon_id x))) tcs)
in (
# 1240 "FStar.Parser.ToSyntax.fst"
let rec collect_tcs = (fun quals et tc -> (
# 1241 "FStar.Parser.ToSyntax.fst"
let _63_2229 = et
in (match (_63_2229) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_63_2231) -> begin
(
# 1244 "FStar.Parser.ToSyntax.fst"
let trec = tc
in (
# 1245 "FStar.Parser.ToSyntax.fst"
let _63_2236 = (tycon_record_as_variant trec)
in (match (_63_2236) with
| (t, fs) -> begin
(collect_tcs ((FStar_Syntax_Syntax.RecordType (fs))::quals) (env, tcs) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(
# 1248 "FStar.Parser.ToSyntax.fst"
let _63_2248 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_63_2248) with
| (env, _63_2245, se, tconstr) -> begin
(env, (FStar_Util.Inl ((se, constructors, tconstr, quals)))::tcs)
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(
# 1251 "FStar.Parser.ToSyntax.fst"
let _63_2260 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_63_2260) with
| (env, _63_2257, se, tconstr) -> begin
(env, (FStar_Util.Inr ((se, t, quals)))::tcs)
end))
end
| _63_2262 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (
# 1254 "FStar.Parser.ToSyntax.fst"
let _63_2265 = (FStar_List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_63_2265) with
| (env, tcs) -> begin
(
# 1255 "FStar.Parser.ToSyntax.fst"
let tcs = (FStar_List.rev tcs)
in (
# 1256 "FStar.Parser.ToSyntax.fst"
let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _63_19 -> (match (_63_19) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, _63_2273, _63_2275, _63_2277, _63_2279), t, quals) -> begin
(
# 1258 "FStar.Parser.ToSyntax.fst"
let _63_2289 = (push_tparams env tpars)
in (match (_63_2289) with
| (env_tps, _63_2288) -> begin
(
# 1259 "FStar.Parser.ToSyntax.fst"
let t = (desugar_term env_tps t)
in (let _152_848 = (let _152_847 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in ([], _152_847))
in (_152_848)::[]))
end))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, _63_2297, tags, _63_2300), constrs, tconstr, quals) -> begin
(
# 1263 "FStar.Parser.ToSyntax.fst"
let tycon = (tname, tpars, k)
in (
# 1264 "FStar.Parser.ToSyntax.fst"
let _63_2311 = (push_tparams env tpars)
in (match (_63_2311) with
| (env_tps, tps) -> begin
(
# 1265 "FStar.Parser.ToSyntax.fst"
let data_tpars = (FStar_List.map (fun _63_2315 -> (match (_63_2315) with
| (x, _63_2314) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end)) tps)
in (
# 1266 "FStar.Parser.ToSyntax.fst"
let _63_2339 = (let _152_860 = (FStar_All.pipe_right constrs (FStar_List.map (fun _63_2320 -> (match (_63_2320) with
| (id, topt, of_notation) -> begin
(
# 1268 "FStar.Parser.ToSyntax.fst"
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
# 1276 "FStar.Parser.ToSyntax.fst"
let t = (let _152_852 = (FStar_Parser_Env.default_total env_tps)
in (let _152_851 = (close env_tps t)
in (desugar_term _152_852 _152_851)))
in (
# 1277 "FStar.Parser.ToSyntax.fst"
let name = (FStar_Parser_Env.qualify env id)
in (
# 1278 "FStar.Parser.ToSyntax.fst"
let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _63_18 -> (match (_63_18) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| _63_2334 -> begin
[]
end))))
in (
# 1281 "FStar.Parser.ToSyntax.fst"
let ntps = (FStar_List.length data_tpars)
in (let _152_859 = (let _152_858 = (let _152_857 = (let _152_856 = (let _152_855 = (let _152_854 = (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total _152_854))
in (FStar_Syntax_Util.arrow data_tpars _152_855))
in (name, univs, _152_856, tname, ntps, quals, mutuals, rng))
in FStar_Syntax_Syntax.Sig_datacon (_152_857))
in (tps, _152_858))
in (name, _152_859)))))))
end))))
in (FStar_All.pipe_left FStar_List.split _152_860))
in (match (_63_2339) with
| (constrNames, constrs) -> begin
(([], FStar_Syntax_Syntax.Sig_inductive_typ ((tname, univs, tpars, k, mutuals, constrNames, tags, rng))))::constrs
end)))
end)))
end
| _63_2341 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1286 "FStar.Parser.ToSyntax.fst"
let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (
# 1287 "FStar.Parser.ToSyntax.fst"
let bundle = (let _152_862 = (let _152_861 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _152_861, rng))
in FStar_Syntax_Syntax.Sig_bundle (_152_862))
in (
# 1288 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 bundle)
in (
# 1289 "FStar.Parser.ToSyntax.fst"
let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projectors quals env)))
in (
# 1290 "FStar.Parser.ToSyntax.fst"
let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _63_20 -> (match (_63_20) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, _63_2350, tps, k, _63_2354, constrs, quals, _63_2358) when ((FStar_List.length constrs) > 1) -> begin
(
# 1292 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract quals) then begin
(FStar_Syntax_Syntax.Private)::quals
end else begin
quals
end
in (mk_data_discriminators quals env tname tps k constrs))
end
| _63_2363 -> begin
[]
end))))
in (
# 1297 "FStar.Parser.ToSyntax.fst"
let ops = (FStar_List.append discs data_ops)
in (
# 1298 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env ops)
in (env, (FStar_List.append ((bundle)::[]) ops)))))))))))
end)))))
end
| [] -> begin
(FStar_All.failwith "impossible")
end))))))))))

# 1303 "FStar.Parser.ToSyntax.fst"
let desugar_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.binder Prims.list) = (fun env binders -> (
# 1304 "FStar.Parser.ToSyntax.fst"
let _63_2387 = (FStar_List.fold_left (fun _63_2372 b -> (match (_63_2372) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| (Some (a), k) -> begin
(
# 1307 "FStar.Parser.ToSyntax.fst"
let _63_2380 = (FStar_Parser_Env.push_bv env a)
in (match (_63_2380) with
| (env, a) -> begin
(let _152_871 = (let _152_870 = (FStar_Syntax_Syntax.mk_binder (
# 1308 "FStar.Parser.ToSyntax.fst"
let _63_2381 = a
in {FStar_Syntax_Syntax.ppname = _63_2381.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _63_2381.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (_152_870)::binders)
in (env, _152_871))
end))
end
| _63_2384 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Missing name in binder", b.FStar_Parser_AST.brange))))
end)
end)) (env, []) binders)
in (match (_63_2387) with
| (env, binders) -> begin
(env, (FStar_List.rev binders))
end)))

# 1313 "FStar.Parser.ToSyntax.fst"
let rec desugar_effect : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.term  ->  (Prims.string  ->  (FStar_Ident.ident Prims.list * FStar_Syntax_Syntax.term))  ->  FStar_Syntax_Syntax.sigelt)  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_kind eff_decls mk -> (
# 1314 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1315 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.enter_monad_scope env eff_name)
in (
# 1316 "FStar.Parser.ToSyntax.fst"
let _63_2400 = (desugar_binders env eff_binders)
in (match (_63_2400) with
| (env, binders) -> begin
(
# 1317 "FStar.Parser.ToSyntax.fst"
let eff_k = (let _152_923 = (FStar_Parser_Env.default_total env)
in (desugar_term _152_923 eff_kind))
in (
# 1318 "FStar.Parser.ToSyntax.fst"
let _63_2411 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _63_2404 decl -> (match (_63_2404) with
| (env, out) -> begin
(
# 1319 "FStar.Parser.ToSyntax.fst"
let _63_2408 = (desugar_decl env decl)
in (match (_63_2408) with
| (env, ses) -> begin
(let _152_927 = (let _152_926 = (FStar_List.hd ses)
in (_152_926)::out)
in (env, _152_927))
end))
end)) (env, [])))
in (match (_63_2411) with
| (env, decls) -> begin
(
# 1321 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_Syntax_Subst.close_binders binders)
in (
# 1322 "FStar.Parser.ToSyntax.fst"
let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (
# 1323 "FStar.Parser.ToSyntax.fst"
let lookup = (fun s -> (
# 1324 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env (FStar_Ident.mk_ident (s, d.FStar_Parser_AST.drange)))
in (let _152_931 = (let _152_930 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) _152_930))
in ([], _152_931))))
in (
# 1326 "FStar.Parser.ToSyntax.fst"
let mname = (FStar_Parser_Env.qualify env0 eff_name)
in (
# 1327 "FStar.Parser.ToSyntax.fst"
let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange) quals)
in (
# 1328 "FStar.Parser.ToSyntax.fst"
let se = (mk mname qualifiers binders eff_k lookup)
in (
# 1329 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 se)
in (env, (se)::[]))))))))
end)))
end)))))
and desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (
# 1333 "FStar.Parser.ToSyntax.fst"
let trans_qual = (trans_qual d.FStar_Parser_AST.drange)
in (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(
# 1336 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_pragma (((trans_pragma p), d.FStar_Parser_AST.drange))
in (env, (se)::[]))
end
| FStar_Parser_AST.TopLevelModule (_63_2428) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Multiple modules in a file are no longer supported", d.FStar_Parser_AST.drange))))
end
| FStar_Parser_AST.Open (lid) -> begin
(
# 1343 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_namespace env lid)
in (env, []))
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(let _152_935 = (FStar_Parser_Env.push_module_abbrev env x l)
in (_152_935, []))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(let _152_936 = (FStar_List.map trans_qual qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _152_936 tcs))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _152_938 = (let _152_937 = (desugar_term_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((isrec, lets, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Syntax_Subst.compress _152_937))
in _152_938.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let (lbs, _63_2448) -> begin
(
# 1355 "FStar.Parser.ToSyntax.fst"
let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (
# 1356 "FStar.Parser.ToSyntax.fst"
let quals = (match (quals) with
| _63_2456::_63_2454 -> begin
(FStar_List.map trans_qual quals)
end
| _63_2459 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _63_21 -> (match (_63_21) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (_63_2470); FStar_Syntax_Syntax.lbunivs = _63_2468; FStar_Syntax_Syntax.lbtyp = _63_2466; FStar_Syntax_Syntax.lbeff = _63_2464; FStar_Syntax_Syntax.lbdef = _63_2462} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _63_2480; FStar_Syntax_Syntax.lbtyp = _63_2478; FStar_Syntax_Syntax.lbeff = _63_2476; FStar_Syntax_Syntax.lbdef = _63_2474} -> begin
(FStar_Parser_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (
# 1361 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right lets (FStar_Util.for_some (fun _63_2488 -> (match (_63_2488) with
| (_63_2486, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end)))) then begin
(FStar_Syntax_Syntax.Logic)::quals
end else begin
quals
end
in (
# 1365 "FStar.Parser.ToSyntax.fst"
let lbs = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _152_943 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 1367 "FStar.Parser.ToSyntax.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 1368 "FStar.Parser.ToSyntax.fst"
let _63_2492 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((
# 1368 "FStar.Parser.ToSyntax.fst"
let _63_2494 = fv
in {FStar_Syntax_Syntax.fv_name = _63_2494.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = _63_2494.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = _63_2492.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _63_2492.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _63_2492.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _63_2492.FStar_Syntax_Syntax.lbdef})))))
in ((Prims.fst lbs), _152_943))
end else begin
lbs
end
in (
# 1370 "FStar.Parser.ToSyntax.fst"
let s = (let _152_946 = (let _152_945 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (lbs, d.FStar_Parser_AST.drange, _152_945, quals))
in FStar_Syntax_Syntax.Sig_let (_152_946))
in (
# 1371 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env s)
in (env, (s)::[])))))))
end
| _63_2501 -> begin
(FStar_All.failwith "Desugaring a let did not produce a let")
end)
end
| FStar_Parser_AST.Main (t) -> begin
(
# 1377 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env t)
in (
# 1378 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, d.FStar_Parser_AST.drange))
in (env, (se)::[])))
end
| FStar_Parser_AST.Assume (atag, id, t) -> begin
(
# 1382 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env t)
in (let _152_950 = (let _152_949 = (let _152_948 = (let _152_947 = (FStar_Parser_Env.qualify env id)
in (_152_947, f, (FStar_Syntax_Syntax.Assumption)::[], d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Sig_assume (_152_948))
in (_152_949)::[])
in (env, _152_950)))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(
# 1386 "FStar.Parser.ToSyntax.fst"
let t = (let _152_951 = (close_fun env t)
in (desugar_term env _152_951))
in (
# 1387 "FStar.Parser.ToSyntax.fst"
let quals = if (env.FStar_Parser_Env.iface && env.FStar_Parser_Env.admitted_iface) then begin
(FStar_Parser_AST.Assumption)::quals
end else begin
quals
end
in (
# 1388 "FStar.Parser.ToSyntax.fst"
let se = (let _152_954 = (let _152_953 = (FStar_Parser_Env.qualify env id)
in (let _152_952 = (FStar_List.map trans_qual quals)
in (_152_953, [], t, _152_952, d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_declare_typ (_152_954))
in (
# 1389 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(
# 1393 "FStar.Parser.ToSyntax.fst"
let t = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (
# 1394 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env id)
in (
# 1395 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_datacon ((l, [], t, FStar_Syntax_Const.exn_lid, 0, (FStar_Syntax_Syntax.ExceptionConstructor)::[], (FStar_Syntax_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (
# 1396 "FStar.Parser.ToSyntax.fst"
let se' = FStar_Syntax_Syntax.Sig_bundle (((se)::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (
# 1397 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se')
in (
# 1398 "FStar.Parser.ToSyntax.fst"
let data_ops = (mk_data_projectors [] env ([], se))
in (
# 1399 "FStar.Parser.ToSyntax.fst"
let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (
# 1400 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops))))))))))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(
# 1404 "FStar.Parser.ToSyntax.fst"
let t = (desugar_term env term)
in (
# 1405 "FStar.Parser.ToSyntax.fst"
let t = (let _152_958 = (let _152_955 = (FStar_Syntax_Syntax.null_binder t)
in (_152_955)::[])
in (let _152_957 = (let _152_956 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _152_956))
in (FStar_Syntax_Util.arrow _152_958 _152_957)))
in (
# 1406 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env id)
in (
# 1407 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_datacon ((l, [], t, FStar_Syntax_Const.exn_lid, 0, (FStar_Syntax_Syntax.ExceptionConstructor)::[], (FStar_Syntax_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (
# 1408 "FStar.Parser.ToSyntax.fst"
let se' = FStar_Syntax_Syntax.Sig_bundle (((se)::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (
# 1409 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se')
in (
# 1410 "FStar.Parser.ToSyntax.fst"
let data_ops = (mk_data_projectors [] env ([], se))
in (
# 1411 "FStar.Parser.ToSyntax.fst"
let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (
# 1412 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops)))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(
# 1416 "FStar.Parser.ToSyntax.fst"
let _63_2554 = (desugar_binders env binders)
in (match (_63_2554) with
| (env_k, binders) -> begin
(
# 1417 "FStar.Parser.ToSyntax.fst"
let k = (desugar_term env_k k)
in (
# 1418 "FStar.Parser.ToSyntax.fst"
let name = (FStar_Parser_Env.qualify env id)
in (
# 1419 "FStar.Parser.ToSyntax.fst"
let se = (mk_typ_abbrev name [] binders FStar_Syntax_Syntax.tun k ((name)::[]) [] d.FStar_Parser_AST.drange)
in (
# 1420 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))))
end))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(
# 1424 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1425 "FStar.Parser.ToSyntax.fst"
let _63_2570 = (desugar_binders env eff_binders)
in (match (_63_2570) with
| (env, binders) -> begin
(
# 1426 "FStar.Parser.ToSyntax.fst"
let _63_2581 = (
# 1427 "FStar.Parser.ToSyntax.fst"
let _63_2573 = (head_and_args defn)
in (match (_63_2573) with
| (head, args) -> begin
(
# 1428 "FStar.Parser.ToSyntax.fst"
let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_defn env) l)
end
| _63_2577 -> begin
(let _152_963 = (let _152_962 = (let _152_961 = (let _152_960 = (let _152_959 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat "Effect " _152_959))
in (Prims.strcat _152_960 " not found"))
in (_152_961, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_152_962))
in (Prims.raise _152_963))
end)
in (let _152_964 = (desugar_args env args)
in (ed, _152_964)))
end))
in (match (_63_2581) with
| (ed, args) -> begin
(
# 1432 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_Syntax_Subst.close_binders binders)
in (
# 1433 "FStar.Parser.ToSyntax.fst"
let sub = (fun _63_2587 -> (match (_63_2587) with
| (_63_2585, x) -> begin
(
# 1434 "FStar.Parser.ToSyntax.fst"
let _63_2590 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (_63_2590) with
| (edb, x) -> begin
(
# 1435 "FStar.Parser.ToSyntax.fst"
let s = (FStar_Syntax_Util.subst_of_list edb args)
in (let _152_968 = (let _152_967 = (FStar_Syntax_Subst.subst s x)
in (FStar_Syntax_Subst.close binders _152_967))
in ([], _152_968)))
end))
end))
in (
# 1437 "FStar.Parser.ToSyntax.fst"
let ed = (let _152_985 = (FStar_List.map trans_qual quals)
in (let _152_984 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _152_983 = (let _152_969 = (sub ([], ed.FStar_Syntax_Syntax.signature))
in (Prims.snd _152_969))
in (let _152_982 = (sub ed.FStar_Syntax_Syntax.ret)
in (let _152_981 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (let _152_980 = (sub ed.FStar_Syntax_Syntax.bind_wlp)
in (let _152_979 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (let _152_978 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (let _152_977 = (sub ed.FStar_Syntax_Syntax.ite_wlp)
in (let _152_976 = (sub ed.FStar_Syntax_Syntax.wp_binop)
in (let _152_975 = (sub ed.FStar_Syntax_Syntax.wp_as_type)
in (let _152_974 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (let _152_973 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (let _152_972 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (let _152_971 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (let _152_970 = (sub ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _152_985; FStar_Syntax_Syntax.mname = _152_984; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = _152_983; FStar_Syntax_Syntax.ret = _152_982; FStar_Syntax_Syntax.bind_wp = _152_981; FStar_Syntax_Syntax.bind_wlp = _152_980; FStar_Syntax_Syntax.if_then_else = _152_979; FStar_Syntax_Syntax.ite_wp = _152_978; FStar_Syntax_Syntax.ite_wlp = _152_977; FStar_Syntax_Syntax.wp_binop = _152_976; FStar_Syntax_Syntax.wp_as_type = _152_975; FStar_Syntax_Syntax.close_wp = _152_974; FStar_Syntax_Syntax.assert_p = _152_973; FStar_Syntax_Syntax.assume_p = _152_972; FStar_Syntax_Syntax.null_wp = _152_971; FStar_Syntax_Syntax.trivial = _152_970}))))))))))))))))
in (
# 1457 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (
# 1458 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 se)
in (env, (se)::[]))))))
end))
end)))
end
| FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.RedefineEffect (_63_2596)) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.NewEffectForFree (FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls)) -> begin
(desugar_effect env d [] eff_name eff_binders eff_kind eff_decls (fun mname qualifiers binders eff_k lookup -> (
# 1468 "FStar.Parser.ToSyntax.fst"
let dummy_tscheme = (let _152_995 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in ([], _152_995))
in (let _152_1005 = (let _152_1004 = (let _152_1003 = (lookup "return")
in (let _152_1002 = (lookup "bind_wp")
in (let _152_1001 = (lookup "bind_wlp")
in (let _152_1000 = (lookup "ite_wp")
in (let _152_999 = (lookup "ite_wlp")
in (let _152_998 = (lookup "wp_as_type")
in (let _152_997 = (lookup "null_wp")
in (let _152_996 = (lookup "trivial")
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret = _152_1003; FStar_Syntax_Syntax.bind_wp = _152_1002; FStar_Syntax_Syntax.bind_wlp = _152_1001; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = _152_1000; FStar_Syntax_Syntax.ite_wlp = _152_999; FStar_Syntax_Syntax.wp_binop = dummy_tscheme; FStar_Syntax_Syntax.wp_as_type = _152_998; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = _152_997; FStar_Syntax_Syntax.trivial = _152_996}))))))))
in (_152_1004, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (_152_1005)))))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls)) -> begin
(desugar_effect env d quals eff_name eff_binders eff_kind eff_decls (fun mname qualifiers binders eff_k lookup -> (let _152_1029 = (let _152_1028 = (let _152_1027 = (lookup "return")
in (let _152_1026 = (lookup "bind_wp")
in (let _152_1025 = (lookup "bind_wlp")
in (let _152_1024 = (lookup "if_then_else")
in (let _152_1023 = (lookup "ite_wp")
in (let _152_1022 = (lookup "ite_wlp")
in (let _152_1021 = (lookup "wp_binop")
in (let _152_1020 = (lookup "wp_as_type")
in (let _152_1019 = (lookup "close_wp")
in (let _152_1018 = (lookup "assert_p")
in (let _152_1017 = (lookup "assume_p")
in (let _152_1016 = (lookup "null_wp")
in (let _152_1015 = (lookup "trivial")
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret = _152_1027; FStar_Syntax_Syntax.bind_wp = _152_1026; FStar_Syntax_Syntax.bind_wlp = _152_1025; FStar_Syntax_Syntax.if_then_else = _152_1024; FStar_Syntax_Syntax.ite_wp = _152_1023; FStar_Syntax_Syntax.ite_wlp = _152_1022; FStar_Syntax_Syntax.wp_binop = _152_1021; FStar_Syntax_Syntax.wp_as_type = _152_1020; FStar_Syntax_Syntax.close_wp = _152_1019; FStar_Syntax_Syntax.assert_p = _152_1018; FStar_Syntax_Syntax.assume_p = _152_1017; FStar_Syntax_Syntax.null_wp = _152_1016; FStar_Syntax_Syntax.trivial = _152_1015})))))))))))))
in (_152_1028, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Sig_new_effect (_152_1029))))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(
# 1516 "FStar.Parser.ToSyntax.fst"
let lookup = (fun l -> (match ((FStar_Parser_Env.try_lookup_effect_name env l)) with
| None -> begin
(let _152_1036 = (let _152_1035 = (let _152_1034 = (let _152_1033 = (let _152_1032 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat "Effect name " _152_1032))
in (Prims.strcat _152_1033 " not found"))
in (_152_1034, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_152_1035))
in (Prims.raise _152_1036))
end
| Some (l) -> begin
l
end))
in (
# 1519 "FStar.Parser.ToSyntax.fst"
let src = (lookup l.FStar_Parser_AST.msource)
in (
# 1520 "FStar.Parser.ToSyntax.fst"
let dst = (lookup l.FStar_Parser_AST.mdest)
in (
# 1521 "FStar.Parser.ToSyntax.fst"
let lift = (let _152_1037 = (desugar_term env l.FStar_Parser_AST.lift_op)
in ([], _152_1037))
in (
# 1522 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect (({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift = lift}, d.FStar_Parser_AST.drange))
in (env, (se)::[]))))))
end)))

# 1525 "FStar.Parser.ToSyntax.fst"
let desugar_decls : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _63_2641 d -> (match (_63_2641) with
| (env, sigelts) -> begin
(
# 1527 "FStar.Parser.ToSyntax.fst"
let _63_2645 = (desugar_decl env d)
in (match (_63_2645) with
| (env, se) -> begin
(env, (FStar_List.append sigelts se))
end))
end)) (env, []) decls))

# 1530 "FStar.Parser.ToSyntax.fst"
let open_prims_all : FStar_Parser_AST.decl Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.all_lid)) FStar_Range.dummyRange))::[]

# 1537 "FStar.Parser.ToSyntax.fst"
let desugar_modul_common : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (
# 1538 "FStar.Parser.ToSyntax.fst"
let open_ns = (fun mname d -> (
# 1539 "FStar.Parser.ToSyntax.fst"
let d = if ((FStar_List.length mname.FStar_Ident.ns) <> 0) then begin
(let _152_1056 = (let _152_1055 = (let _152_1054 = (FStar_Ident.lid_of_ids mname.FStar_Ident.ns)
in FStar_Parser_AST.Open (_152_1054))
in (FStar_Parser_AST.mk_decl _152_1055 (FStar_Ident.range_of_lid mname)))
in (_152_1056)::d)
end else begin
d
end
in d))
in (
# 1543 "FStar.Parser.ToSyntax.fst"
let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod) -> begin
(FStar_Parser_Env.finish_module_or_interface env prev_mod)
end)
in (
# 1546 "FStar.Parser.ToSyntax.fst"
let _63_2672 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _152_1058 = (FStar_Parser_Env.prepare_module_or_interface true admitted env mname)
in (let _152_1057 = (open_ns mname decls)
in (_152_1058, mname, _152_1057, true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _152_1060 = (FStar_Parser_Env.prepare_module_or_interface false false env mname)
in (let _152_1059 = (open_ns mname decls)
in (_152_1060, mname, _152_1059, false)))
end)
in (match (_63_2672) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(
# 1551 "FStar.Parser.ToSyntax.fst"
let _63_2675 = (desugar_decls env decls)
in (match (_63_2675) with
| (env, sigelts) -> begin
(
# 1552 "FStar.Parser.ToSyntax.fst"
let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in (env, modul, pop_when_done))
end))
end)))))

# 1560 "FStar.Parser.ToSyntax.fst"
let desugar_partial_modul : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (
# 1561 "FStar.Parser.ToSyntax.fst"
let m = if (FStar_ST.read FStar_Options.interactive_fsi) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface ((mname, decls, true))
end
| FStar_Parser_AST.Interface (mname, _63_2686, _63_2688) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (
# 1568 "FStar.Parser.ToSyntax.fst"
let _63_2696 = (desugar_modul_common curmod env m)
in (match (_63_2696) with
| (x, y, _63_2695) -> begin
(x, y)
end))))

# 1571 "FStar.Parser.ToSyntax.fst"
let desugar_modul : FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (
# 1572 "FStar.Parser.ToSyntax.fst"
let _63_2702 = (desugar_modul_common None env m)
in (match (_63_2702) with
| (env, modul, pop_when_done) -> begin
(
# 1573 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.finish_module_or_interface env modul)
in (
# 1574 "FStar.Parser.ToSyntax.fst"
let _63_2704 = if (FStar_Options.should_dump modul.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _152_1071 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _152_1071))
end else begin
()
end
in (let _152_1072 = if pop_when_done then begin
(FStar_Parser_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end else begin
env
end
in (_152_1072, modul))))
end)))

# 1578 "FStar.Parser.ToSyntax.fst"
let desugar_file : FStar_Parser_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (
# 1579 "FStar.Parser.ToSyntax.fst"
let _63_2717 = (FStar_List.fold_left (fun _63_2710 m -> (match (_63_2710) with
| (env, mods) -> begin
(
# 1580 "FStar.Parser.ToSyntax.fst"
let _63_2714 = (desugar_modul env m)
in (match (_63_2714) with
| (env, m) -> begin
(env, (m)::mods)
end))
end)) (env, []) f)
in (match (_63_2717) with
| (env, mods) -> begin
(env, (FStar_List.rev mods))
end)))

# 1584 "FStar.Parser.ToSyntax.fst"
let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Parser_Env.env  ->  FStar_Parser_Env.env = (fun m en -> (
# 1585 "FStar.Parser.ToSyntax.fst"
let _63_2722 = (FStar_Parser_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (_63_2722) with
| (en, pop_when_done) -> begin
(
# 1586 "FStar.Parser.ToSyntax.fst"
let en = (FStar_List.fold_left FStar_Parser_Env.push_sigelt (
# 1586 "FStar.Parser.ToSyntax.fst"
let _63_2723 = en
in {FStar_Parser_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_Parser_Env.modules = _63_2723.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _63_2723.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _63_2723.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _63_2723.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _63_2723.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _63_2723.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _63_2723.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _63_2723.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _63_2723.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _63_2723.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = _63_2723.FStar_Parser_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (
# 1587 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_Env.export_interface m.FStar_Syntax_Syntax.name env)
end else begin
env
end))
end)))




