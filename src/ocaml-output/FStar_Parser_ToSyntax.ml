
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
let tm_type_z : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _145_23 = (let _145_22 = (FStar_Ident.lid_of_path (("Type0")::[]) r)
in FStar_Parser_AST.Name (_145_22))
in (FStar_Parser_AST.mk_term _145_23 r FStar_Parser_AST.Kind)))

# 83 "FStar.Parser.ToSyntax.fst"
let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _145_27 = (let _145_26 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_145_26))
in (FStar_Parser_AST.mk_term _145_27 r FStar_Parser_AST.Kind)))

# 85 "FStar.Parser.ToSyntax.fst"
let rec delta_qualifier : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.delta_depth = (fun t -> (
# 86 "FStar.Parser.ToSyntax.fst"
let t = (FStar_Syntax_Subst.compress t)
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (_56_76) -> begin
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
| _56_171 -> begin
"UNKNOWN"
end))
in (
# 135 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _145_47 = (let _145_45 = (FStar_Util.char_at s i)
in (name_of_char _145_45))
in (let _145_46 = (aux (i + 1))
in (_145_47)::_145_46))
end)
in (let _145_49 = (let _145_48 = (aux 0)
in (FStar_String.concat "_" _145_48))
in (Prims.strcat "op_" _145_49)))))

# 141 "FStar.Parser.ToSyntax.fst"
let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _145_59 = (let _145_58 = (let _145_57 = (let _145_56 = (compile_op n s)
in (_145_56, r))
in (FStar_Ident.mk_ident _145_57))
in (_145_58)::[])
in (FStar_All.pipe_right _145_59 FStar_Ident.lid_of_ids)))

# 143 "FStar.Parser.ToSyntax.fst"
let op_as_term : FStar_Parser_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.term Prims.option = (fun env arity rng s -> (
# 144 "FStar.Parser.ToSyntax.fst"
let r = (fun l dd -> (let _145_74 = (let _145_73 = (let _145_72 = (FStar_Ident.set_lid_range l rng)
in (FStar_Syntax_Syntax.lid_as_fv _145_72 dd None))
in (FStar_All.pipe_right _145_73 FStar_Syntax_Syntax.fv_to_tm))
in Some (_145_74)))
in (
# 145 "FStar.Parser.ToSyntax.fst"
let fallback = (fun _56_186 -> (match (()) with
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
| _56_214 -> begin
None
end)
end))
in (match ((let _145_77 = (compile_op_lid arity s rng)
in (FStar_Parser_Env.try_lookup_lid env _145_77))) with
| Some (t) -> begin
Some (t)
end
| _56_218 -> begin
(fallback ())
end))))

# 179 "FStar.Parser.ToSyntax.fst"
let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _145_84 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _145_84)))

# 183 "FStar.Parser.ToSyntax.fst"
let rec free_type_vars_b : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_56_227) -> begin
(env, [])
end
| FStar_Parser_AST.TVariable (x) -> begin
(
# 186 "FStar.Parser.ToSyntax.fst"
let _56_234 = (FStar_Parser_Env.push_bv env x)
in (match (_56_234) with
| (env, _56_233) -> begin
(env, (x)::[])
end))
end
| FStar_Parser_AST.Annotated (_56_236, term) -> begin
(let _145_91 = (free_type_vars env term)
in (env, _145_91))
end
| FStar_Parser_AST.TAnnotated (id, _56_242) -> begin
(
# 191 "FStar.Parser.ToSyntax.fst"
let _56_248 = (FStar_Parser_Env.push_bv env id)
in (match (_56_248) with
| (env, _56_247) -> begin
(env, [])
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _145_92 = (free_type_vars env t)
in (env, _145_92))
end))
and free_type_vars : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _145_95 = (unparen t)
in _145_95.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (_56_254) -> begin
(FStar_All.failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_Env.try_lookup_id env a)) with
| None -> begin
(a)::[]
end
| _56_260 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_56_290, ts) -> begin
(FStar_List.collect (fun _56_297 -> (match (_56_297) with
| (t, _56_296) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_56_299, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _56_306) -> begin
(let _145_98 = (free_type_vars env t1)
in (let _145_97 = (free_type_vars env t2)
in (FStar_List.append _145_98 _145_97)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(
# 221 "FStar.Parser.ToSyntax.fst"
let _56_315 = (free_type_vars_b env b)
in (match (_56_315) with
| (env, f) -> begin
(let _145_99 = (free_type_vars env t)
in (FStar_List.append f _145_99))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(
# 226 "FStar.Parser.ToSyntax.fst"
let _56_331 = (FStar_List.fold_left (fun _56_324 binder -> (match (_56_324) with
| (env, free) -> begin
(
# 227 "FStar.Parser.ToSyntax.fst"
let _56_328 = (free_type_vars_b env binder)
in (match (_56_328) with
| (env, f) -> begin
(env, (FStar_List.append f free))
end))
end)) (env, []) binders)
in (match (_56_331) with
| (env, free) -> begin
(let _145_102 = (free_type_vars env body)
in (FStar_List.append free _145_102))
end))
end
| FStar_Parser_AST.Project (t, _56_334) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
[]
end))

# 244 "FStar.Parser.ToSyntax.fst"
let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (
# 245 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun args t -> (match ((let _145_109 = (unparen t)
in _145_109.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _56_378 -> begin
(t, args)
end))
in (aux [] t)))

# 251 "FStar.Parser.ToSyntax.fst"
let close : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 252 "FStar.Parser.ToSyntax.fst"
let ftv = (let _145_114 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _145_114))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 255 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _145_118 = (let _145_117 = (let _145_116 = (tm_type x.FStar_Ident.idRange)
in (x, _145_116))
in FStar_Parser_AST.TAnnotated (_145_117))
in (FStar_Parser_AST.mk_binder _145_118 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 256 "FStar.Parser.ToSyntax.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))

# 259 "FStar.Parser.ToSyntax.fst"
let close_fun : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 260 "FStar.Parser.ToSyntax.fst"
let ftv = (let _145_123 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _145_123))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 263 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _145_127 = (let _145_126 = (let _145_125 = (tm_type x.FStar_Ident.idRange)
in (x, _145_125))
in FStar_Parser_AST.TAnnotated (_145_126))
in (FStar_Parser_AST.mk_binder _145_127 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 264 "FStar.Parser.ToSyntax.fst"
let t = (match ((let _145_128 = (unparen t)
in _145_128.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_56_391) -> begin
t
end
| _56_394 -> begin
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
| _56_404 -> begin
(bs, t)
end))

# 274 "FStar.Parser.ToSyntax.fst"
let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _56_408) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_56_414); FStar_Parser_AST.prange = _56_412}, _56_418) -> begin
true
end
| _56_422 -> begin
false
end))

# 279 "FStar.Parser.ToSyntax.fst"
let rec destruct_app_pattern : FStar_Parser_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 281 "FStar.Parser.ToSyntax.fst"
let _56_434 = (destruct_app_pattern env is_top_level p)
in (match (_56_434) with
| (name, args, _56_433) -> begin
(name, args, Some (t))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _56_439); FStar_Parser_AST.prange = _56_436}, args) when is_top_level -> begin
(let _145_142 = (let _145_141 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_145_141))
in (_145_142, args, None))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _56_450); FStar_Parser_AST.prange = _56_447}, args) -> begin
(FStar_Util.Inl (id), args, None)
end
| _56_458 -> begin
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
| LocalBinder (_56_461) -> begin
_56_461
end))

# 292 "FStar.Parser.ToSyntax.fst"
let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_56_464) -> begin
_56_464
end))

# 293 "FStar.Parser.ToSyntax.fst"
let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun _56_6 -> (match (_56_6) with
| LocalBinder (a, aq) -> begin
(a, aq)
end
| _56_471 -> begin
(FStar_All.failwith "Impossible")
end))

# 296 "FStar.Parser.ToSyntax.fst"
let as_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_Parser_Env.env) = (fun env imp _56_7 -> (match (_56_7) with
| (None, k) -> begin
(let _145_179 = (FStar_Syntax_Syntax.null_binder k)
in (_145_179, env))
end
| (Some (a), k) -> begin
(
# 299 "FStar.Parser.ToSyntax.fst"
let _56_484 = (FStar_Parser_Env.push_bv env a)
in (match (_56_484) with
| (env, a) -> begin
(((
# 300 "FStar.Parser.ToSyntax.fst"
let _56_485 = a
in {FStar_Syntax_Syntax.ppname = _56_485.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_485.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}), (trans_aqual imp)), env)
end))
end))

# 302 "FStar.Parser.ToSyntax.fst"
type env_t =
FStar_Parser_Env.env

# 303 "FStar.Parser.ToSyntax.fst"
type lenv_t =
FStar_Syntax_Syntax.bv Prims.list

# 305 "FStar.Parser.ToSyntax.fst"
let mk_lb : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.letbinding = (fun _56_490 -> (match (_56_490) with
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
| FStar_Syntax_Syntax.Pat_cons (_56_511, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out _56_519 -> (match (_56_519) with
| (p, _56_518) -> begin
(let _145_225 = (pat_vars p)
in (FStar_Util.set_union out _145_225))
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
| _56_537 -> begin
(
# 331 "FStar.Parser.ToSyntax.fst"
let _56_540 = (FStar_Parser_Env.push_bv e x)
in (match (_56_540) with
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
| _56_549 -> begin
(
# 337 "FStar.Parser.ToSyntax.fst"
let _56_552 = (FStar_Parser_Env.push_bv e a)
in (match (_56_552) with
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
let _56_574 = (aux loc env p)
in (match (_56_574) with
| (loc, env, var, p, _56_573) -> begin
(
# 346 "FStar.Parser.ToSyntax.fst"
let _56_591 = (FStar_List.fold_left (fun _56_578 p -> (match (_56_578) with
| (loc, env, ps) -> begin
(
# 347 "FStar.Parser.ToSyntax.fst"
let _56_587 = (aux loc env p)
in (match (_56_587) with
| (loc, env, _56_583, p, _56_586) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_56_591) with
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
let _56_602 = (aux loc env p)
in (match (_56_602) with
| (loc, env', binder, p, imp) -> begin
(
# 354 "FStar.Parser.ToSyntax.fst"
let binder = (match (binder) with
| LetBinder (_56_604) -> begin
(FStar_All.failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(
# 357 "FStar.Parser.ToSyntax.fst"
let t = (let _145_255 = (close_fun env t)
in (desugar_term env _145_255))
in LocalBinder (((
# 358 "FStar.Parser.ToSyntax.fst"
let _56_611 = x
in {FStar_Syntax_Syntax.ppname = _56_611.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_611.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), aq)))
end)
in (loc, env', binder, p, imp))
end))
end
| FStar_Parser_AST.PatWild -> begin
(
# 362 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _145_256 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in (loc, env, LocalBinder ((x, None)), _145_256, false)))
end
| FStar_Parser_AST.PatConst (c) -> begin
(
# 366 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _145_257 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in (loc, env, LocalBinder ((x, None)), _145_257, false)))
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
let _56_630 = (resolvex loc env x)
in (match (_56_630) with
| (loc, env, xbv) -> begin
(let _145_258 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in (loc, env, LocalBinder ((xbv, aq)), _145_258, imp))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(
# 377 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_datacon env) l)
in (
# 378 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _145_259 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, []))))
in (loc, env, LocalBinder ((x, None)), _145_259, false))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _56_636}, args) -> begin
(
# 382 "FStar.Parser.ToSyntax.fst"
let _56_658 = (FStar_List.fold_right (fun arg _56_647 -> (match (_56_647) with
| (loc, env, args) -> begin
(
# 383 "FStar.Parser.ToSyntax.fst"
let _56_654 = (aux loc env arg)
in (match (_56_654) with
| (loc, env, _56_651, arg, imp) -> begin
(loc, env, ((arg, imp))::args)
end))
end)) args (loc, env, []))
in (match (_56_658) with
| (loc, env, args) -> begin
(
# 385 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_datacon env) l)
in (
# 386 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _145_262 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _145_262, false))))
end))
end
| FStar_Parser_AST.PatApp (_56_662) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(
# 392 "FStar.Parser.ToSyntax.fst"
let _56_682 = (FStar_List.fold_right (fun pat _56_670 -> (match (_56_670) with
| (loc, env, pats) -> begin
(
# 393 "FStar.Parser.ToSyntax.fst"
let _56_678 = (aux loc env pat)
in (match (_56_678) with
| (loc, env, _56_674, pat, _56_677) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_56_682) with
| (loc, env, pats) -> begin
(
# 395 "FStar.Parser.ToSyntax.fst"
let pat = (let _145_275 = (let _145_274 = (let _145_270 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _145_270))
in (let _145_273 = (let _145_272 = (let _145_271 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_145_271, []))
in FStar_Syntax_Syntax.Pat_cons (_145_272))
in (FStar_All.pipe_left _145_274 _145_273)))
in (FStar_List.fold_right (fun hd tl -> (
# 396 "FStar.Parser.ToSyntax.fst"
let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (let _145_269 = (let _145_268 = (let _145_267 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in (_145_267, ((hd, false))::((tl, false))::[]))
in FStar_Syntax_Syntax.Pat_cons (_145_268))
in (FStar_All.pipe_left (pos_r r) _145_269)))) pats _145_275))
in (
# 399 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (loc, env, LocalBinder ((x, None)), pat, false)))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(
# 403 "FStar.Parser.ToSyntax.fst"
let _56_708 = (FStar_List.fold_left (fun _56_695 p -> (match (_56_695) with
| (loc, env, pats) -> begin
(
# 404 "FStar.Parser.ToSyntax.fst"
let _56_704 = (aux loc env p)
in (match (_56_704) with
| (loc, env, _56_700, pat, _56_703) -> begin
(loc, env, ((pat, false))::pats)
end))
end)) (loc, env, []) args)
in (match (_56_708) with
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
| _56_715 -> begin
(FStar_All.failwith "impossible")
end)
in (
# 413 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _145_278 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons ((l, args))))
in (loc, env, LocalBinder ((x, None)), _145_278, false)))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(
# 420 "FStar.Parser.ToSyntax.fst"
let _56_725 = (FStar_List.hd fields)
in (match (_56_725) with
| (f, _56_724) -> begin
(
# 421 "FStar.Parser.ToSyntax.fst"
let _56_729 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_56_729) with
| (record, _56_728) -> begin
(
# 422 "FStar.Parser.ToSyntax.fst"
let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _56_732 -> (match (_56_732) with
| (f, p) -> begin
(let _145_280 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.qualify_field_to_record env record) f)
in (_145_280, p))
end))))
in (
# 424 "FStar.Parser.ToSyntax.fst"
let args = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _56_737 -> (match (_56_737) with
| (f, _56_736) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _56_741 -> (match (_56_741) with
| (g, _56_740) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_56_744, p) -> begin
p
end)
end))))
in (
# 428 "FStar.Parser.ToSyntax.fst"
let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_Env.constrname)) p.FStar_Parser_AST.prange), args))) p.FStar_Parser_AST.prange)
in (
# 429 "FStar.Parser.ToSyntax.fst"
let _56_756 = (aux loc env app)
in (match (_56_756) with
| (env, e, b, p, _56_755) -> begin
(
# 430 "FStar.Parser.ToSyntax.fst"
let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(let _145_289 = (let _145_288 = (let _145_287 = (
# 431 "FStar.Parser.ToSyntax.fst"
let _56_761 = fv
in (let _145_286 = (let _145_285 = (let _145_284 = (let _145_283 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _145_283))
in FStar_Syntax_Syntax.Record_ctor (_145_284))
in Some (_145_285))
in {FStar_Syntax_Syntax.fv_name = _56_761.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = _56_761.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _145_286}))
in (_145_287, args))
in FStar_Syntax_Syntax.Pat_cons (_145_288))
in (FStar_All.pipe_left pos _145_289))
end
| _56_764 -> begin
p
end)
in (env, e, b, p, false))
end)))))
end))
end))
end))))
in (
# 435 "FStar.Parser.ToSyntax.fst"
let _56_773 = (aux [] env p)
in (match (_56_773) with
| (_56_767, env, b, p, _56_772) -> begin
(
# 436 "FStar.Parser.ToSyntax.fst"
let _56_774 = (let _145_290 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore _145_290))
in (env, b, p))
end)))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _56_781) -> begin
(let _145_296 = (let _145_295 = (let _145_294 = (FStar_Parser_Env.qualify env x)
in (_145_294, FStar_Syntax_Syntax.tun))
in LetBinder (_145_295))
in (env, _145_296, None))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _56_788); FStar_Parser_AST.prange = _56_785}, t) -> begin
(let _145_300 = (let _145_299 = (let _145_298 = (FStar_Parser_Env.qualify env x)
in (let _145_297 = (desugar_term env t)
in (_145_298, _145_297)))
in LetBinder (_145_299))
in (env, _145_300, None))
end
| _56_796 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected pattern at the top-level", p.FStar_Parser_AST.prange))))
end)
end else begin
(
# 447 "FStar.Parser.ToSyntax.fst"
let _56_800 = (desugar_data_pat env p)
in (match (_56_800) with
| (env, binder, p) -> begin
(
# 448 "FStar.Parser.ToSyntax.fst"
let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| _56_808 -> begin
Some (p)
end)
in (env, binder, p))
end))
end)
and desugar_binding_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun _56_812 env pat -> (
# 457 "FStar.Parser.ToSyntax.fst"
let _56_820 = (desugar_data_pat env pat)
in (match (_56_820) with
| (env, _56_818, pat) -> begin
(env, pat)
end)))
and desugar_match_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (
# 463 "FStar.Parser.ToSyntax.fst"
let env = (
# 463 "FStar.Parser.ToSyntax.fst"
let _56_825 = env
in {FStar_Parser_Env.curmodule = _56_825.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _56_825.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _56_825.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _56_825.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _56_825.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _56_825.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _56_825.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _56_825.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _56_825.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _56_825.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _56_825.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (
# 467 "FStar.Parser.ToSyntax.fst"
let env = (
# 467 "FStar.Parser.ToSyntax.fst"
let _56_830 = env
in {FStar_Parser_Env.curmodule = _56_830.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _56_830.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _56_830.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _56_830.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _56_830.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _56_830.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _56_830.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _56_830.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _56_830.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _56_830.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _56_830.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (
# 471 "FStar.Parser.ToSyntax.fst"
let mk = (fun e -> (FStar_Syntax_Syntax.mk e None top.FStar_Parser_AST.range))
in (
# 472 "FStar.Parser.ToSyntax.fst"
let setpos = (fun e -> (
# 472 "FStar.Parser.ToSyntax.fst"
let _56_840 = e
in {FStar_Syntax_Syntax.n = _56_840.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _56_840.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _56_840.FStar_Syntax_Syntax.vars}))
in (match ((let _145_319 = (unparen top)
in _145_319.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (_56_844) -> begin
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
| FStar_Parser_AST.Op ("*", _56_864::_56_862::[]) when (let _145_320 = (op_as_term env 2 top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right _145_320 FStar_Option.isNone)) -> begin
(
# 490 "FStar.Parser.ToSyntax.fst"
let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", t1::t2::[]) -> begin
(
# 492 "FStar.Parser.ToSyntax.fst"
let rest = (flatten t2)
in (t1)::rest)
end
| _56_878 -> begin
(t)::[]
end))
in (
# 495 "FStar.Parser.ToSyntax.fst"
let targs = (let _145_326 = (let _145_323 = (unparen top)
in (flatten _145_323))
in (FStar_All.pipe_right _145_326 (FStar_List.map (fun t -> (let _145_325 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg _145_325))))))
in (
# 496 "FStar.Parser.ToSyntax.fst"
let tup = (let _145_327 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) _145_327))
in (mk (FStar_Syntax_Syntax.Tm_app ((tup, targs)))))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _145_328 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) a)
in (FStar_All.pipe_left setpos _145_328))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (((Prims.strcat "Unexpected operator: " s), top.FStar_Parser_AST.range))))
end
| Some (op) -> begin
(
# 506 "FStar.Parser.ToSyntax.fst"
let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _145_330 = (desugar_term env t)
in (_145_330, None)))))
in (mk (FStar_Syntax_Syntax.Tm_app ((op, args)))))
end)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _56_899; FStar_Ident.ident = _56_897; FStar_Ident.nsstr = _56_895; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _56_908; FStar_Ident.ident = _56_906; FStar_Ident.nsstr = _56_904; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _56_917; FStar_Ident.ident = _56_915; FStar_Ident.nsstr = _56_913; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _56_926; FStar_Ident.ident = _56_924; FStar_Ident.nsstr = _56_922; FStar_Ident.str = "True"}) -> begin
(let _145_331 = (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _145_331 FStar_Syntax_Syntax.Delta_constant None))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _56_935; FStar_Ident.ident = _56_933; FStar_Ident.nsstr = _56_931; FStar_Ident.str = "False"}) -> begin
(let _145_332 = (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.fvar _145_332 FStar_Syntax_Syntax.Delta_constant None))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(let _145_333 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (FStar_All.pipe_left setpos _145_333))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(
# 521 "FStar.Parser.ToSyntax.fst"
let _56_950 = (match ((FStar_Parser_Env.try_lookup_datacon env l)) with
| None -> begin
(let _145_334 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) l)
in (_145_334, false))
end
| Some (head) -> begin
(let _145_335 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in (_145_335, true))
end)
in (match (_56_950) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| _56_953 -> begin
(
# 527 "FStar.Parser.ToSyntax.fst"
let args = (FStar_List.map (fun _56_956 -> (match (_56_956) with
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
let _56_984 = (FStar_List.fold_left (fun _56_967 b -> (match (_56_967) with
| (env, tparams, typs) -> begin
(
# 538 "FStar.Parser.ToSyntax.fst"
let _56_971 = (desugar_binder env b)
in (match (_56_971) with
| (xopt, t) -> begin
(
# 539 "FStar.Parser.ToSyntax.fst"
let _56_977 = (match (xopt) with
| None -> begin
(let _145_339 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (env, _145_339))
end
| Some (x) -> begin
(FStar_Parser_Env.push_bv env x)
end)
in (match (_56_977) with
| (env, x) -> begin
(let _145_343 = (let _145_342 = (let _145_341 = (let _145_340 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _145_340))
in (_145_341)::[])
in (FStar_List.append typs _145_342))
in (env, (FStar_List.append tparams ((((
# 543 "FStar.Parser.ToSyntax.fst"
let _56_978 = x
in {FStar_Syntax_Syntax.ppname = _56_978.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_978.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), None))::[])), _145_343))
end))
end))
end)) (env, [], []) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_56_984) with
| (env, _56_982, targs) -> begin
(
# 546 "FStar.Parser.ToSyntax.fst"
let tup = (let _145_344 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) _145_344))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app ((tup, targs)))))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(
# 550 "FStar.Parser.ToSyntax.fst"
let _56_992 = (uncurry binders t)
in (match (_56_992) with
| (bs, t) -> begin
(
# 551 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun env bs _56_8 -> (match (_56_8) with
| [] -> begin
(
# 553 "FStar.Parser.ToSyntax.fst"
let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (let _145_351 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos _145_351)))
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
let _56_1006 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_56_1006) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_binder env b)) with
| (None, _56_1013) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(
# 568 "FStar.Parser.ToSyntax.fst"
let _56_1021 = (as_binder env None b)
in (match (_56_1021) with
| ((x, _56_1018), env) -> begin
(
# 569 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env f)
in (let _145_352 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos _145_352)))
end))
end)
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(
# 574 "FStar.Parser.ToSyntax.fst"
let _56_1041 = (FStar_List.fold_left (fun _56_1029 pat -> (match (_56_1029) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (_56_1032, t) -> begin
(let _145_356 = (let _145_355 = (free_type_vars env t)
in (FStar_List.append _145_355 ftvs))
in (env, _145_356))
end
| _56_1037 -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_56_1041) with
| (_56_1039, ftv) -> begin
(
# 578 "FStar.Parser.ToSyntax.fst"
let ftv = (sort_ftv ftv)
in (
# 579 "FStar.Parser.ToSyntax.fst"
let binders = (let _145_358 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar ((a, Some (FStar_Parser_AST.Implicit)))) top.FStar_Parser_AST.range))))
in (FStar_List.append _145_358 binders))
in (
# 588 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun env bs sc_pat_opt _56_9 -> (match (_56_9) with
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
let body = (let _145_368 = (let _145_367 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right _145_367 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close _145_368 body))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match ((sc, ((pat, None, body))::[]))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (let _145_369 = (no_annot_abs (FStar_List.rev bs) body)
in (setpos _145_369))))
end
| p::rest -> begin
(
# 599 "FStar.Parser.ToSyntax.fst"
let _56_1065 = (desugar_binding_pat env p)
in (match (_56_1065) with
| (env, b, pat) -> begin
(
# 600 "FStar.Parser.ToSyntax.fst"
let _56_1116 = (match (b) with
| LetBinder (_56_1067) -> begin
(FStar_All.failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(
# 603 "FStar.Parser.ToSyntax.fst"
let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _56_1075) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _145_371 = (let _145_370 = (FStar_Syntax_Syntax.bv_to_name x)
in (_145_370, p))
in Some (_145_371))
end
| (Some (p), Some (sc, p')) -> begin
(match ((sc.FStar_Syntax_Syntax.n, p'.FStar_Syntax_Syntax.v)) with
| (FStar_Syntax_Syntax.Tm_name (_56_1089), _56_1092) -> begin
(
# 609 "FStar.Parser.ToSyntax.fst"
let tup2 = (let _145_372 = (FStar_Syntax_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _145_372 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (
# 610 "FStar.Parser.ToSyntax.fst"
let sc = (let _145_380 = (let _145_379 = (let _145_378 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (let _145_377 = (let _145_376 = (FStar_Syntax_Syntax.as_arg sc)
in (let _145_375 = (let _145_374 = (let _145_373 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _145_373))
in (_145_374)::[])
in (_145_376)::_145_375))
in (_145_378, _145_377)))
in FStar_Syntax_Syntax.Tm_app (_145_379))
in (FStar_Syntax_Syntax.mk _145_380 None top.FStar_Parser_AST.range))
in (
# 611 "FStar.Parser.ToSyntax.fst"
let p = (let _145_381 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tup2, ((p', false))::((p, false))::[]))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _145_381))
in Some ((sc, p)))))
end
| (FStar_Syntax_Syntax.Tm_app (_56_1098, args), FStar_Syntax_Syntax.Pat_cons (_56_1103, pats)) -> begin
(
# 614 "FStar.Parser.ToSyntax.fst"
let tupn = (let _145_382 = (FStar_Syntax_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _145_382 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (
# 615 "FStar.Parser.ToSyntax.fst"
let sc = (let _145_389 = (let _145_388 = (let _145_387 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (let _145_386 = (let _145_385 = (let _145_384 = (let _145_383 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _145_383))
in (_145_384)::[])
in (FStar_List.append args _145_385))
in (_145_387, _145_386)))
in FStar_Syntax_Syntax.Tm_app (_145_388))
in (mk _145_389))
in (
# 616 "FStar.Parser.ToSyntax.fst"
let p = (let _145_390 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons ((tupn, (FStar_List.append pats (((p, false))::[]))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _145_390))
in Some ((sc, p)))))
end
| _56_1112 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((x, aq), sc_pat_opt))
end)
in (match (_56_1116) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _56_1120; FStar_Parser_AST.level = _56_1118}, phi, _56_1126) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(
# 627 "FStar.Parser.ToSyntax.fst"
let phi = (desugar_formula env phi)
in (let _145_398 = (let _145_397 = (let _145_396 = (FStar_Syntax_Syntax.fvar a FStar_Syntax_Syntax.Delta_equational None)
in (let _145_395 = (let _145_394 = (FStar_Syntax_Syntax.as_arg phi)
in (let _145_393 = (let _145_392 = (let _145_391 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _145_391))
in (_145_392)::[])
in (_145_394)::_145_393))
in (_145_396, _145_395)))
in FStar_Syntax_Syntax.Tm_app (_145_397))
in (mk _145_398)))
end
| FStar_Parser_AST.App (_56_1131) -> begin
(
# 633 "FStar.Parser.ToSyntax.fst"
let rec aux = (fun args e -> (match ((let _145_403 = (unparen e)
in _145_403.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(
# 635 "FStar.Parser.ToSyntax.fst"
let arg = (let _145_404 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _145_404))
in (aux ((arg)::args) e))
end
| _56_1143 -> begin
(
# 638 "FStar.Parser.ToSyntax.fst"
let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app ((head, args)))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _145_407 = (let _145_406 = (let _145_405 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range), t1))::[], t2))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in (_145_405, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence)))
in FStar_Syntax_Syntax.Tm_meta (_145_406))
in (mk _145_407))
end
| FStar_Parser_AST.Let (is_rec, (pat, _snd)::_tl, body) -> begin
(
# 647 "FStar.Parser.ToSyntax.fst"
let ds_let_rec_or_app = (fun _56_1159 -> (match (()) with
| () -> begin
(
# 648 "FStar.Parser.ToSyntax.fst"
let bindings = ((pat, _snd))::_tl
in (
# 649 "FStar.Parser.ToSyntax.fst"
let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _56_1163 -> (match (_56_1163) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _145_411 = (destruct_app_pattern env top_level p)
in (_145_411, def))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _145_412 = (destruct_app_pattern env top_level p)
in (_145_412, def))
end
| _56_1169 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _56_1174); FStar_Parser_AST.prange = _56_1171}, t) -> begin
if top_level then begin
(let _145_415 = (let _145_414 = (let _145_413 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_145_413))
in (_145_414, [], Some (t)))
in (_145_415, def))
end else begin
((FStar_Util.Inl (id), [], Some (t)), def)
end
end
| FStar_Parser_AST.PatVar (id, _56_1183) -> begin
if top_level then begin
(let _145_418 = (let _145_417 = (let _145_416 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_145_416))
in (_145_417, [], None))
in (_145_418, def))
end else begin
((FStar_Util.Inl (id), [], None), def)
end
end
| _56_1187 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected let binding", p.FStar_Parser_AST.prange))))
end)
end)
end
end))))
in (
# 666 "FStar.Parser.ToSyntax.fst"
let _56_1216 = (FStar_List.fold_left (fun _56_1192 _56_1201 -> (match ((_56_1192, _56_1201)) with
| ((env, fnames, rec_bindings), ((f, _56_1195, _56_1197), _56_1200)) -> begin
(
# 668 "FStar.Parser.ToSyntax.fst"
let _56_1212 = (match (f) with
| FStar_Util.Inl (x) -> begin
(
# 670 "FStar.Parser.ToSyntax.fst"
let _56_1206 = (FStar_Parser_Env.push_bv env x)
in (match (_56_1206) with
| (env, xx) -> begin
(let _145_422 = (let _145_421 = (FStar_Syntax_Syntax.mk_binder xx)
in (_145_421)::rec_bindings)
in (env, FStar_Util.Inl (xx), _145_422))
end))
end
| FStar_Util.Inr (l) -> begin
(let _145_423 = (FStar_Parser_Env.push_top_level_rec_binding env l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in (_145_423, FStar_Util.Inr (l), rec_bindings))
end)
in (match (_56_1212) with
| (env, lbname, rec_bindings) -> begin
(env, (lbname)::fnames, rec_bindings)
end))
end)) (env, [], []) funs)
in (match (_56_1216) with
| (env', fnames, rec_bindings) -> begin
(
# 676 "FStar.Parser.ToSyntax.fst"
let fnames = (FStar_List.rev fnames)
in (
# 678 "FStar.Parser.ToSyntax.fst"
let desugar_one_def = (fun env lbname _56_1227 -> (match (_56_1227) with
| ((_56_1222, args, result_t), def) -> begin
(
# 679 "FStar.Parser.ToSyntax.fst"
let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _145_430 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed ((def, t))) _145_430 FStar_Parser_AST.Expr))
end)
in (
# 682 "FStar.Parser.ToSyntax.fst"
let def = (match (args) with
| [] -> begin
def
end
| _56_1234 -> begin
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
(let _145_432 = (let _145_431 = (incr_delta_qualifier body)
in (FStar_Syntax_Syntax.lid_as_fv l _145_431 None))
in FStar_Util.Inr (_145_432))
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
in (let _145_435 = (let _145_434 = (let _145_433 = (FStar_Syntax_Subst.close rec_bindings body)
in ((is_rec, lbs), _145_433))
in FStar_Syntax_Syntax.Tm_let (_145_434))
in (FStar_All.pipe_left mk _145_435))))))
end))))
end))
in (
# 696 "FStar.Parser.ToSyntax.fst"
let ds_non_rec = (fun pat t1 t2 -> (
# 697 "FStar.Parser.ToSyntax.fst"
let t1 = (desugar_term env t1)
in (
# 698 "FStar.Parser.ToSyntax.fst"
let _56_1253 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_56_1253) with
| (env, binder, pat) -> begin
(match (binder) with
| LetBinder (l, t) -> begin
(
# 701 "FStar.Parser.ToSyntax.fst"
let body = (desugar_term env t2)
in (
# 702 "FStar.Parser.ToSyntax.fst"
let fv = (let _145_442 = (incr_delta_qualifier t1)
in (FStar_Syntax_Syntax.lid_as_fv l _145_442 None))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]), body))))))
end
| LocalBinder (x, _56_1262) -> begin
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
(let _145_447 = (let _145_446 = (let _145_445 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _145_444 = (let _145_443 = (FStar_Syntax_Util.branch (pat, None, body))
in (_145_443)::[])
in (_145_445, _145_444)))
in FStar_Syntax_Syntax.Tm_match (_145_446))
in (FStar_Syntax_Syntax.mk _145_447 None body.FStar_Syntax_Syntax.pos))
end)
in (let _145_452 = (let _145_451 = (let _145_450 = (let _145_449 = (let _145_448 = (FStar_Syntax_Syntax.mk_binder x)
in (_145_448)::[])
in (FStar_Syntax_Subst.close _145_449 body))
in ((false, ((mk_lb (FStar_Util.Inl (x), x.FStar_Syntax_Syntax.sort, t1)))::[]), _145_450))
in FStar_Syntax_Syntax.Tm_let (_145_451))
in (FStar_All.pipe_left mk _145_452))))
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
in (let _145_463 = (let _145_462 = (let _145_461 = (desugar_term env t1)
in (let _145_460 = (let _145_459 = (let _145_454 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (let _145_453 = (desugar_term env t2)
in (_145_454, None, _145_453)))
in (let _145_458 = (let _145_457 = (let _145_456 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (let _145_455 = (desugar_term env t3)
in (_145_456, None, _145_455)))
in (_145_457)::[])
in (_145_459)::_145_458))
in (_145_461, _145_460)))
in FStar_Syntax_Syntax.Tm_match (_145_462))
in (mk _145_463)))
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
let desugar_branch = (fun _56_1302 -> (match (_56_1302) with
| (pat, wopt, b) -> begin
(
# 736 "FStar.Parser.ToSyntax.fst"
let _56_1305 = (desugar_match_pat env pat)
in (match (_56_1305) with
| (env, pat) -> begin
(
# 737 "FStar.Parser.ToSyntax.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _145_466 = (desugar_term env e)
in Some (_145_466))
end)
in (
# 740 "FStar.Parser.ToSyntax.fst"
let b = (desugar_term env b)
in (FStar_Syntax_Util.branch (pat, wopt, b))))
end))
end))
in (let _145_470 = (let _145_469 = (let _145_468 = (desugar_term env e)
in (let _145_467 = (FStar_List.map desugar_branch branches)
in (_145_468, _145_467)))
in FStar_Syntax_Syntax.Tm_match (_145_469))
in (FStar_All.pipe_left mk _145_470)))
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
in (let _145_473 = (let _145_472 = (let _145_471 = (desugar_term env e)
in (_145_471, annot, None))
in FStar_Syntax_Syntax.Tm_ascribed (_145_472))
in (FStar_All.pipe_left mk _145_473)))))
end
| FStar_Parser_AST.Record (_56_1319, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected empty record", top.FStar_Parser_AST.range))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(
# 756 "FStar.Parser.ToSyntax.fst"
let _56_1330 = (FStar_List.hd fields)
in (match (_56_1330) with
| (f, _56_1329) -> begin
(
# 757 "FStar.Parser.ToSyntax.fst"
let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (
# 758 "FStar.Parser.ToSyntax.fst"
let _56_1336 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_56_1336) with
| (record, _56_1335) -> begin
(
# 759 "FStar.Parser.ToSyntax.fst"
let get_field = (fun xopt f -> (
# 760 "FStar.Parser.ToSyntax.fst"
let fn = f.FStar_Ident.ident
in (
# 761 "FStar.Parser.ToSyntax.fst"
let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _56_1344 -> (match (_56_1344) with
| (g, _56_1343) -> begin
(
# 762 "FStar.Parser.ToSyntax.fst"
let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_56_1348, e) -> begin
(let _145_481 = (qfn fn)
in (_145_481, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _145_484 = (let _145_483 = (let _145_482 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in (_145_482, top.FStar_Parser_AST.range))
in FStar_Syntax_Syntax.Error (_145_483))
in (Prims.raise _145_484))
end
| Some (x) -> begin
(let _145_485 = (qfn fn)
in (_145_485, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Project ((x, f))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end))))
in (
# 773 "FStar.Parser.ToSyntax.fst"
let recterm = (match (eopt) with
| None -> begin
(let _145_490 = (let _145_489 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _56_1360 -> (match (_56_1360) with
| (f, _56_1359) -> begin
(let _145_488 = (let _145_487 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _145_487))
in (_145_488, FStar_Parser_AST.Nothing))
end))))
in (record.FStar_Parser_Env.constrname, _145_489))
in FStar_Parser_AST.Construct (_145_490))
end
| Some (e) -> begin
(
# 780 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (
# 781 "FStar.Parser.ToSyntax.fst"
let xterm = (let _145_492 = (let _145_491 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_145_491))
in (FStar_Parser_AST.mk_term _145_492 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (
# 782 "FStar.Parser.ToSyntax.fst"
let record = (let _145_495 = (let _145_494 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _56_1368 -> (match (_56_1368) with
| (f, _56_1367) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _145_494))
in FStar_Parser_AST.Record (_145_495))
in FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar ((x, None))) x.FStar_Ident.idRange), e))::[], (FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level))))))
end)
in (
# 785 "FStar.Parser.ToSyntax.fst"
let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (
# 786 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _56_1384; FStar_Syntax_Syntax.pos = _56_1382; FStar_Syntax_Syntax.vars = _56_1380}, args); FStar_Syntax_Syntax.tk = _56_1378; FStar_Syntax_Syntax.pos = _56_1376; FStar_Syntax_Syntax.vars = _56_1374}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(
# 789 "FStar.Parser.ToSyntax.fst"
let e = (let _145_503 = (let _145_502 = (let _145_501 = (let _145_500 = (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos)
in (let _145_499 = (let _145_498 = (let _145_497 = (let _145_496 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_Env.typename, _145_496))
in FStar_Syntax_Syntax.Record_ctor (_145_497))
in Some (_145_498))
in (FStar_Syntax_Syntax.fvar _145_500 FStar_Syntax_Syntax.Delta_constant _145_499)))
in (_145_501, args))
in FStar_Syntax_Syntax.Tm_app (_145_502))
in (FStar_All.pipe_left mk _145_503))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta ((e, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end
| _56_1398 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(
# 797 "FStar.Parser.ToSyntax.fst"
let _56_1405 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_projector_by_field_name env) f)
in (match (_56_1405) with
| (fieldname, is_rec) -> begin
(
# 798 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env e)
in (
# 799 "FStar.Parser.ToSyntax.fst"
let fn = (
# 800 "FStar.Parser.ToSyntax.fst"
let _56_1410 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_56_1410) with
| (ns, _56_1409) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (
# 802 "FStar.Parser.ToSyntax.fst"
let qual = if is_rec then begin
Some (FStar_Syntax_Syntax.Record_projector (fn))
end else begin
None
end
in (let _145_509 = (let _145_508 = (let _145_507 = (let _145_504 = (FStar_Ident.set_lid_range fieldname (FStar_Ident.range_of_lid f))
in (FStar_Syntax_Syntax.fvar _145_504 FStar_Syntax_Syntax.Delta_equational qual))
in (let _145_506 = (let _145_505 = (FStar_Syntax_Syntax.as_arg e)
in (_145_505)::[])
in (_145_507, _145_506)))
in FStar_Syntax_Syntax.Tm_app (_145_508))
in (FStar_All.pipe_left mk _145_509)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| _56_1420 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _56_1422 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_args : FStar_Parser_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun _56_1427 -> (match (_56_1427) with
| (a, imp) -> begin
(let _145_513 = (desugar_term env a)
in (arg_withimp_e imp _145_513))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r default_ok env t -> (
# 819 "FStar.Parser.ToSyntax.fst"
let fail = (fun msg -> (Prims.raise (FStar_Syntax_Syntax.Error ((msg, r)))))
in (
# 820 "FStar.Parser.ToSyntax.fst"
let is_requires = (fun _56_1439 -> (match (_56_1439) with
| (t, _56_1438) -> begin
(match ((let _145_521 = (unparen t)
in _145_521.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Requires (_56_1441) -> begin
true
end
| _56_1444 -> begin
false
end)
end))
in (
# 823 "FStar.Parser.ToSyntax.fst"
let is_ensures = (fun _56_1449 -> (match (_56_1449) with
| (t, _56_1448) -> begin
(match ((let _145_524 = (unparen t)
in _145_524.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ensures (_56_1451) -> begin
true
end
| _56_1454 -> begin
false
end)
end))
in (
# 826 "FStar.Parser.ToSyntax.fst"
let is_app = (fun head _56_1460 -> (match (_56_1460) with
| (t, _56_1459) -> begin
(match ((let _145_529 = (unparen t)
in _145_529.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _56_1464; FStar_Parser_AST.level = _56_1462}, _56_1469, _56_1471) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| _56_1475 -> begin
false
end)
end))
in (
# 829 "FStar.Parser.ToSyntax.fst"
let pre_process_comp_typ = (fun t -> (
# 830 "FStar.Parser.ToSyntax.fst"
let _56_1480 = (head_and_args t)
in (match (_56_1480) with
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
(let _145_532 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_name env) l)
in (_145_532, args))
end
| FStar_Parser_AST.Name (l) when ((let _145_533 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _145_533 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(let _145_534 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in (_145_534, args))
end
| FStar_Parser_AST.Name (l) when ((let _145_535 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _145_535 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(let _145_536 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)
in (_145_536, args))
end
| FStar_Parser_AST.Name (l) when ((((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) && default_ok) -> begin
(let _145_537 = (FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)
in (_145_537, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _56_1508 when default_ok -> begin
(let _145_538 = (FStar_Ident.set_lid_range env.FStar_Parser_Env.default_result_effect head.FStar_Parser_AST.range)
in (_145_538, ((t, FStar_Parser_AST.Nothing))::[]))
end
| _56_1510 -> begin
(let _145_540 = (let _145_539 = (FStar_Parser_AST.term_to_string t)
in (FStar_Util.format1 "%s is not an effect" _145_539))
in (fail _145_540))
end)
end)))
in (
# 873 "FStar.Parser.ToSyntax.fst"
let _56_1513 = (pre_process_comp_typ t)
in (match (_56_1513) with
| (eff, args) -> begin
(
# 874 "FStar.Parser.ToSyntax.fst"
let _56_1514 = if ((FStar_List.length args) = 0) then begin
(let _145_542 = (let _145_541 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" _145_541))
in (fail _145_542))
end else begin
()
end
in (
# 876 "FStar.Parser.ToSyntax.fst"
let _56_1518 = (let _145_544 = (FStar_List.hd args)
in (let _145_543 = (FStar_List.tl args)
in (_145_544, _145_543)))
in (match (_56_1518) with
| (result_arg, rest) -> begin
(
# 877 "FStar.Parser.ToSyntax.fst"
let result_typ = (desugar_typ env (Prims.fst result_arg))
in (
# 878 "FStar.Parser.ToSyntax.fst"
let rest = (desugar_args env rest)
in (
# 879 "FStar.Parser.ToSyntax.fst"
let _56_1543 = (FStar_All.pipe_right rest (FStar_List.partition (fun _56_1524 -> (match (_56_1524) with
| (t, _56_1523) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _56_1530; FStar_Syntax_Syntax.pos = _56_1528; FStar_Syntax_Syntax.vars = _56_1526}, _56_1535::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| _56_1540 -> begin
false
end)
end))))
in (match (_56_1543) with
| (dec, rest) -> begin
(
# 885 "FStar.Parser.ToSyntax.fst"
let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _56_1547 -> (match (_56_1547) with
| (t, _56_1546) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_56_1549, (arg, _56_1552)::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| _56_1558 -> begin
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
let pattern = (let _145_548 = (let _145_547 = (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.fvar _145_547 FStar_Syntax_Syntax.Delta_constant None))
in (FStar_Syntax_Syntax.mk_Tm_uinst _145_548 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app nil (((pattern, Some (FStar_Syntax_Syntax.imp_tag)))::[]) None pat.FStar_Syntax_Syntax.pos)))
end
| _56_1573 -> begin
pat
end)
in (let _145_552 = (let _145_551 = (let _145_550 = (let _145_549 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta ((pat, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat)))) None pat.FStar_Syntax_Syntax.pos)
in (_145_549, aq))
in (_145_550)::[])
in (ens)::_145_551)
in (req)::_145_552))
end
| _56_1576 -> begin
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
| _56_1588 -> begin
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
let _56_1595 = t
in {FStar_Syntax_Syntax.n = _56_1595.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _56_1595.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _56_1595.FStar_Syntax_Syntax.vars}))
in (
# 933 "FStar.Parser.ToSyntax.fst"
let desugar_quant = (fun q b pats body -> (
# 934 "FStar.Parser.ToSyntax.fst"
let tk = (desugar_binder env (
# 934 "FStar.Parser.ToSyntax.fst"
let _56_1602 = b
in {FStar_Parser_AST.b = _56_1602.FStar_Parser_AST.b; FStar_Parser_AST.brange = _56_1602.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _56_1602.FStar_Parser_AST.aqual}))
in (
# 935 "FStar.Parser.ToSyntax.fst"
let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _145_587 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _145_587)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(
# 938 "FStar.Parser.ToSyntax.fst"
let _56_1616 = (FStar_Parser_Env.push_bv env a)
in (match (_56_1616) with
| (env, a) -> begin
(
# 939 "FStar.Parser.ToSyntax.fst"
let a = (
# 939 "FStar.Parser.ToSyntax.fst"
let _56_1617 = a
in {FStar_Syntax_Syntax.ppname = _56_1617.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1617.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
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
| _56_1624 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta ((body, FStar_Syntax_Syntax.Meta_pattern (pats)))))
end)
in (
# 945 "FStar.Parser.ToSyntax.fst"
let body = (let _145_590 = (let _145_589 = (let _145_588 = (FStar_Syntax_Syntax.mk_binder a)
in (_145_588)::[])
in (no_annot_abs _145_589 body))
in (FStar_All.pipe_left setpos _145_590))
in (let _145_596 = (let _145_595 = (let _145_594 = (let _145_591 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Syntax_Syntax.fvar _145_591 (FStar_Syntax_Syntax.Delta_unfoldable (1)) None))
in (let _145_593 = (let _145_592 = (FStar_Syntax_Syntax.as_arg body)
in (_145_592)::[])
in (_145_594, _145_593)))
in FStar_Syntax_Syntax.Tm_app (_145_595))
in (FStar_All.pipe_left mk _145_596)))))))
end))
end
| _56_1628 -> begin
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
let body = (let _145_611 = (q (rest, pats, body))
in (let _145_610 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _145_611 _145_610 FStar_Parser_AST.Formula)))
in (let _145_612 = (q ((b)::[], [], body))
in (FStar_Parser_AST.mk_term _145_612 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _56_1642 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _145_613 = (unparen f)
in _145_613.FStar_Parser_AST.tm)) with
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
in (let _145_615 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _145_615)))
end
| FStar_Parser_AST.QExists (_1::_2::_3, pats, body) -> begin
(
# 970 "FStar.Parser.ToSyntax.fst"
let binders = (_1)::(_2)::_3
in (let _145_617 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _145_617)))
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
| _56_1700 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (
# 985 "FStar.Parser.ToSyntax.fst"
let _56_1724 = (FStar_List.fold_left (fun _56_1705 b -> (match (_56_1705) with
| (env, out) -> begin
(
# 986 "FStar.Parser.ToSyntax.fst"
let tk = (desugar_binder env (
# 986 "FStar.Parser.ToSyntax.fst"
let _56_1707 = b
in {FStar_Parser_AST.b = _56_1707.FStar_Parser_AST.b; FStar_Parser_AST.brange = _56_1707.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _56_1707.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(
# 989 "FStar.Parser.ToSyntax.fst"
let _56_1716 = (FStar_Parser_Env.push_bv env a)
in (match (_56_1716) with
| (env, a) -> begin
(
# 990 "FStar.Parser.ToSyntax.fst"
let a = (
# 990 "FStar.Parser.ToSyntax.fst"
let _56_1717 = a
in {FStar_Syntax_Syntax.ppname = _56_1717.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1717.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (env, ((a, (trans_aqual b.FStar_Parser_AST.aqual)))::out))
end))
end
| _56_1721 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected binder", b.FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_56_1724) with
| (env, tpars) -> begin
(env, (FStar_List.rev tpars))
end)))
and desugar_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(let _145_624 = (desugar_typ env t)
in (Some (x), _145_624))
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _145_625 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None x.FStar_Ident.idRange)
in (Some (x), _145_625))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _145_626 = (desugar_typ env t)
in (None, _145_626))
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
let binders = (let _145_642 = (let _145_641 = (FStar_Syntax_Util.arrow_formals k)
in (Prims.fst _145_641))
in (FStar_List.append tps _145_642))
in (
# 1007 "FStar.Parser.ToSyntax.fst"
let p = (FStar_Ident.range_of_lid t)
in (
# 1008 "FStar.Parser.ToSyntax.fst"
let _56_1751 = (FStar_Syntax_Util.args_of_binders binders)
in (match (_56_1751) with
| (binders, args) -> begin
(
# 1009 "FStar.Parser.ToSyntax.fst"
let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _56_1755 -> (match (_56_1755) with
| (x, _56_1754) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
in (
# 1010 "FStar.Parser.ToSyntax.fst"
let binders = (let _145_648 = (let _145_647 = (let _145_646 = (let _145_645 = (let _145_644 = (FStar_Syntax_Syntax.lid_as_fv t FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _145_644))
in (FStar_Syntax_Syntax.mk_Tm_app _145_645 args None p))
in (FStar_All.pipe_left FStar_Syntax_Syntax.null_binder _145_646))
in (_145_647)::[])
in (FStar_List.append imp_binders _145_648))
in (
# 1011 "FStar.Parser.ToSyntax.fst"
let disc_type = (let _145_651 = (let _145_650 = (let _145_649 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _145_649))
in (FStar_Syntax_Syntax.mk_Total _145_650))
in (FStar_Syntax_Util.arrow binders _145_651))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (
# 1013 "FStar.Parser.ToSyntax.fst"
let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (let _145_654 = (let _145_653 = (quals ((FStar_Syntax_Syntax.Logic)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in (disc_name, [], disc_type, _145_653, (FStar_Ident.range_of_lid disc_name)))
in FStar_Syntax_Syntax.Sig_declare_typ (_145_654)))))))))
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
let tps = (FStar_List.map2 (fun _56_1779 _56_1783 -> (match ((_56_1779, _56_1783)) with
| ((_56_1777, imp), (x, _56_1782)) -> begin
(x, imp)
end)) inductive_tps imp_tps)
in (
# 1021 "FStar.Parser.ToSyntax.fst"
let _56_1884 = (
# 1022 "FStar.Parser.ToSyntax.fst"
let _56_1787 = (FStar_Syntax_Util.head_and_args t)
in (match (_56_1787) with
| (head, args0) -> begin
(
# 1023 "FStar.Parser.ToSyntax.fst"
let args = (
# 1024 "FStar.Parser.ToSyntax.fst"
let rec arguments = (fun tps args -> (match ((tps, args)) with
| ([], _56_1793) -> begin
args
end
| (_56_1796, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Not enough arguments to type", (FStar_Ident.range_of_lid lid)))))
end
| ((_56_1801, Some (FStar_Syntax_Syntax.Implicit (_56_1803)))::tps', (_56_1810, Some (FStar_Syntax_Syntax.Implicit (_56_1812)))::args') -> begin
(arguments tps' args')
end
| ((_56_1820, Some (FStar_Syntax_Syntax.Implicit (_56_1822)))::tps', (_56_1830, _56_1832)::_56_1828) -> begin
(arguments tps' args)
end
| ((_56_1839, _56_1841)::_56_1837, (a, Some (FStar_Syntax_Syntax.Implicit (_56_1848)))::_56_1845) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Unexpected implicit annotation on argument", a.FStar_Syntax_Syntax.pos))))
end
| ((_56_1856, _56_1858)::tps', (_56_1863, _56_1865)::args') -> begin
(arguments tps' args')
end))
in (arguments inductive_tps args0))
in (
# 1033 "FStar.Parser.ToSyntax.fst"
let indices = (FStar_All.pipe_right args (FStar_List.map (fun _56_1870 -> (let _145_686 = (FStar_Syntax_Syntax.new_bv (Some (p)) FStar_Syntax_Syntax.tun)
in (FStar_All.pipe_right _145_686 FStar_Syntax_Syntax.mk_binder)))))
in (
# 1034 "FStar.Parser.ToSyntax.fst"
let arg_typ = (let _145_691 = (let _145_687 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _145_687))
in (let _145_690 = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _56_1875 -> (match (_56_1875) with
| (x, imp) -> begin
(let _145_689 = (FStar_Syntax_Syntax.bv_to_name x)
in (_145_689, imp))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app _145_691 _145_690 None p)))
in (
# 1036 "FStar.Parser.ToSyntax.fst"
let arg_binder = if (not (refine_domain)) then begin
(let _145_692 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder _145_692))
end else begin
(
# 1039 "FStar.Parser.ToSyntax.fst"
let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (
# 1040 "FStar.Parser.ToSyntax.fst"
let x = (FStar_Syntax_Syntax.new_bv (Some (p)) arg_typ)
in (let _145_701 = (
# 1041 "FStar.Parser.ToSyntax.fst"
let _56_1879 = (projectee arg_typ)
in (let _145_700 = (let _145_699 = (let _145_698 = (let _145_697 = (let _145_693 = (FStar_Ident.set_lid_range disc_name p)
in (FStar_Syntax_Syntax.fvar _145_693 FStar_Syntax_Syntax.Delta_equational None))
in (let _145_696 = (let _145_695 = (let _145_694 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _145_694))
in (_145_695)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _145_697 _145_696 None p)))
in (FStar_Syntax_Util.b2t _145_698))
in (FStar_Syntax_Util.refine x _145_699))
in {FStar_Syntax_Syntax.ppname = _56_1879.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_1879.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _145_700}))
in (FStar_Syntax_Syntax.mk_binder _145_701))))
end
in (arg_binder, indices)))))
end))
in (match (_56_1884) with
| (arg_binder, indices) -> begin
(
# 1045 "FStar.Parser.ToSyntax.fst"
let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder))
in (
# 1046 "FStar.Parser.ToSyntax.fst"
let imp_binders = (let _145_703 = (FStar_All.pipe_right indices (FStar_List.map (fun _56_1889 -> (match (_56_1889) with
| (x, _56_1888) -> begin
(x, Some (FStar_Syntax_Syntax.imp_tag))
end))))
in (FStar_List.append imp_tps _145_703))
in (
# 1047 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (
# 1049 "FStar.Parser.ToSyntax.fst"
let arg = (FStar_Syntax_Util.arg_of_non_null_binder arg_binder)
in (
# 1051 "FStar.Parser.ToSyntax.fst"
let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _56_1897 -> (match (_56_1897) with
| (a, _56_1896) -> begin
(
# 1052 "FStar.Parser.ToSyntax.fst"
let _56_1901 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (_56_1901) with
| (field_name, _56_1900) -> begin
(
# 1053 "FStar.Parser.ToSyntax.fst"
let proj = (let _145_707 = (let _145_706 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.fv_to_tm _145_706))
in (FStar_Syntax_Syntax.mk_Tm_app _145_707 ((arg)::[]) None p))
in FStar_Syntax_Syntax.NT ((a, proj)))
end))
end))))
in (
# 1056 "FStar.Parser.ToSyntax.fst"
let ntps = (FStar_List.length tps)
in (
# 1057 "FStar.Parser.ToSyntax.fst"
let all_params = (FStar_List.append imp_tps fields)
in (let _145_743 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _56_1910 -> (match (_56_1910) with
| (x, _56_1909) -> begin
(
# 1060 "FStar.Parser.ToSyntax.fst"
let _56_1914 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_56_1914) with
| (field_name, _56_1913) -> begin
(
# 1061 "FStar.Parser.ToSyntax.fst"
let t = (let _145_711 = (let _145_710 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total _145_710))
in (FStar_Syntax_Util.arrow binders _145_711))
in (
# 1062 "FStar.Parser.ToSyntax.fst"
let only_decl = (((let _145_712 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _145_712)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _145_714 = (let _145_713 = (FStar_Parser_Env.current_module env)
in _145_713.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _145_714)))
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
let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _56_1926 -> (match (_56_1926) with
| (x, imp) -> begin
(
# 1074 "FStar.Parser.ToSyntax.fst"
let b = (FStar_Syntax_Syntax.is_implicit imp)
in if ((i + ntps) = j) then begin
(let _145_719 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in (_145_719, b))
end else begin
if (b && (j < ntps)) then begin
(let _145_723 = (let _145_722 = (let _145_721 = (let _145_720 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (_145_720, FStar_Syntax_Syntax.tun))
in FStar_Syntax_Syntax.Pat_dot_term (_145_721))
in (pos _145_722))
in (_145_723, b))
end else begin
(let _145_726 = (let _145_725 = (let _145_724 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_145_724))
in (pos _145_725))
in (_145_726, b))
end
end)
end))))
in (
# 1080 "FStar.Parser.ToSyntax.fst"
let pat = (let _145_731 = (let _145_729 = (let _145_728 = (let _145_727 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in (_145_727, arg_pats))
in FStar_Syntax_Syntax.Pat_cons (_145_728))
in (FStar_All.pipe_right _145_729 pos))
in (let _145_730 = (FStar_Syntax_Syntax.bv_to_name projection)
in (_145_731, None, _145_730)))
in (
# 1081 "FStar.Parser.ToSyntax.fst"
let body = (let _145_735 = (let _145_734 = (let _145_733 = (let _145_732 = (FStar_Syntax_Util.branch pat)
in (_145_732)::[])
in (arg_exp, _145_733))
in FStar_Syntax_Syntax.Tm_match (_145_734))
in (FStar_Syntax_Syntax.mk _145_735 None p))
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
let lb = (let _145_737 = (let _145_736 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (_145_736))
in {FStar_Syntax_Syntax.lbname = _145_737; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = imp})
in (
# 1091 "FStar.Parser.ToSyntax.fst"
let impl = (let _145_742 = (let _145_741 = (let _145_740 = (let _145_739 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _145_739 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_145_740)::[])
in ((false, (lb)::[]), p, _145_741, quals))
in FStar_Syntax_Syntax.Sig_let (_145_742))
in if no_decl then begin
(impl)::[]
end else begin
(decl)::(impl)::[]
end))))))))
end))))))
end))
end))))
in (FStar_All.pipe_right _145_743 FStar_List.flatten)))))))))
end)))))))

# 1094 "FStar.Parser.ToSyntax.fst"
let mk_data_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env _56_1940 -> (match (_56_1940) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _56_1943, t, l, n, quals, _56_1949, _56_1951) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(
# 1097 "FStar.Parser.ToSyntax.fst"
let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _56_10 -> (match (_56_10) with
| FStar_Syntax_Syntax.RecordConstructor (_56_1956) -> begin
true
end
| _56_1959 -> begin
false
end)))) then begin
false
end else begin
(match ((FStar_Parser_Env.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > 1)
end
| _56_1963 -> begin
true
end)
end
in (
# 1103 "FStar.Parser.ToSyntax.fst"
let _56_1967 = (FStar_Syntax_Util.arrow_formals t)
in (match (_56_1967) with
| (formals, cod) -> begin
(match (formals) with
| [] -> begin
[]
end
| _56_1970 -> begin
(
# 1107 "FStar.Parser.ToSyntax.fst"
let fv_qual = (match ((FStar_Util.find_map quals (fun _56_11 -> (match (_56_11) with
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor ((lid, fns)))
end
| _56_1975 -> begin
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
let _56_1983 = (FStar_Util.first_N n formals)
in (match (_56_1983) with
| (tps, rest) -> begin
(mk_indexed_projectors iquals fv_qual refine_domain env l lid inductive_tps tps rest cod)
end))))
end)
end)))
end
| _56_1985 -> begin
[]
end)
end))

# 1119 "FStar.Parser.ToSyntax.fst"
let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (
# 1120 "FStar.Parser.ToSyntax.fst"
let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _145_768 = (incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (_145_768))
end else begin
(incr_delta_qualifier t)
end
in (
# 1123 "FStar.Parser.ToSyntax.fst"
let lb = (let _145_773 = (let _145_769 = (FStar_Syntax_Syntax.lid_as_fv lid dd None)
in FStar_Util.Inr (_145_769))
in (let _145_772 = (let _145_770 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars _145_770))
in (let _145_771 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = _145_773; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = _145_772; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _145_771})))
in FStar_Syntax_Syntax.Sig_let (((false, (lb)::[]), rng, lids, quals)))))

# 1132 "FStar.Parser.ToSyntax.fst"
let rec desugar_tycon : FStar_Parser_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (
# 1133 "FStar.Parser.ToSyntax.fst"
let tycon_id = (fun _56_12 -> (match (_56_12) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (
# 1138 "FStar.Parser.ToSyntax.fst"
let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _145_787 = (let _145_786 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_145_786))
in (FStar_Parser_AST.mk_term _145_787 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
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
| _56_2060 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _145_800 = (let _145_799 = (let _145_798 = (binder_to_term b)
in (out, _145_798, (imp_of_aqual b)))
in FStar_Parser_AST.App (_145_799))
in (FStar_Parser_AST.mk_term _145_800 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (
# 1152 "FStar.Parser.ToSyntax.fst"
let tycon_record_as_variant = (fun _56_13 -> (match (_56_13) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(
# 1154 "FStar.Parser.ToSyntax.fst"
let constrName = (FStar_Ident.mk_ident ((Prims.strcat "Mk" id.FStar_Ident.idText), id.FStar_Ident.idRange))
in (
# 1155 "FStar.Parser.ToSyntax.fst"
let mfields = (FStar_List.map (fun _56_2073 -> (match (_56_2073) with
| (x, t) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated (((FStar_Syntax_Util.mangle_field_name x), t))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (
# 1156 "FStar.Parser.ToSyntax.fst"
let result = (let _145_806 = (let _145_805 = (let _145_804 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_145_804))
in (FStar_Parser_AST.mk_term _145_805 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _145_806 parms))
in (
# 1157 "FStar.Parser.ToSyntax.fst"
let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _145_808 = (FStar_All.pipe_right fields (FStar_List.map (fun _56_2080 -> (match (_56_2080) with
| (x, _56_2079) -> begin
(FStar_Parser_Env.qualify env x)
end))))
in (FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _145_808))))))
end
| _56_2082 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1161 "FStar.Parser.ToSyntax.fst"
let desugar_abstract_tc = (fun quals _env mutuals _56_14 -> (match (_56_14) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(
# 1163 "FStar.Parser.ToSyntax.fst"
let _56_2096 = (typars_of_binders _env binders)
in (match (_56_2096) with
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
let tconstr = (let _145_819 = (let _145_818 = (let _145_817 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_145_817))
in (FStar_Parser_AST.mk_term _145_818 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _145_819 binders))
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
| _56_2109 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (
# 1176 "FStar.Parser.ToSyntax.fst"
let push_tparams = (fun env bs -> (
# 1177 "FStar.Parser.ToSyntax.fst"
let _56_2124 = (FStar_List.fold_left (fun _56_2115 _56_2118 -> (match ((_56_2115, _56_2118)) with
| ((env, tps), (x, imp)) -> begin
(
# 1178 "FStar.Parser.ToSyntax.fst"
let _56_2121 = (FStar_Parser_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (_56_2121) with
| (env, y) -> begin
(env, ((y, imp))::tps)
end))
end)) (env, []) bs)
in (match (_56_2124) with
| (env, bs) -> begin
(env, (FStar_List.rev bs))
end)))
in (match (tcs) with
| FStar_Parser_AST.TyconAbstract (id, bs, kopt)::[] -> begin
(
# 1183 "FStar.Parser.ToSyntax.fst"
let kopt = (match (kopt) with
| None -> begin
(let _145_826 = (tm_type_z id.FStar_Ident.idRange)
in Some (_145_826))
end
| _56_2133 -> begin
kopt
end)
in (
# 1186 "FStar.Parser.ToSyntax.fst"
let tc = FStar_Parser_AST.TyconAbstract ((id, bs, kopt))
in (
# 1187 "FStar.Parser.ToSyntax.fst"
let _56_2143 = (desugar_abstract_tc quals env [] tc)
in (match (_56_2143) with
| (_56_2137, _56_2139, se, _56_2142) -> begin
(
# 1188 "FStar.Parser.ToSyntax.fst"
let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _56_2146, typars, k, [], [], quals, rng) -> begin
(
# 1190 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
quals
end else begin
(
# 1192 "FStar.Parser.ToSyntax.fst"
let _56_2155 = (let _145_828 = (FStar_Range.string_of_range rng)
in (let _145_827 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" _145_828 _145_827)))
in (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals)
end
in (
# 1195 "FStar.Parser.ToSyntax.fst"
let t = (match (typars) with
| [] -> begin
k
end
| _56_2160 -> begin
(let _145_831 = (let _145_830 = (let _145_829 = (FStar_Syntax_Syntax.mk_Total k)
in (typars, _145_829))
in FStar_Syntax_Syntax.Tm_arrow (_145_830))
in (FStar_Syntax_Syntax.mk _145_831 None rng))
end)
in FStar_Syntax_Syntax.Sig_declare_typ ((l, [], t, quals, rng))))
end
| _56_2163 -> begin
se
end)
in (
# 1200 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))
end))))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t)::[] -> begin
(
# 1205 "FStar.Parser.ToSyntax.fst"
let _56_2175 = (typars_of_binders env binders)
in (match (_56_2175) with
| (env', typars) -> begin
(
# 1206 "FStar.Parser.ToSyntax.fst"
let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _56_15 -> (match (_56_15) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| _56_2180 -> begin
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
# 1212 "FStar.Parser.ToSyntax.fst"
let t0 = t
in (
# 1213 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _56_16 -> (match (_56_16) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| _56_2188 -> begin
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
# 1218 "FStar.Parser.ToSyntax.fst"
let se = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Effect)) then begin
(
# 1220 "FStar.Parser.ToSyntax.fst"
let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (
# 1221 "FStar.Parser.ToSyntax.fst"
let typars = (FStar_Syntax_Subst.close_binders typars)
in (
# 1222 "FStar.Parser.ToSyntax.fst"
let c = (FStar_Syntax_Subst.close_comp typars c)
in (let _145_837 = (let _145_836 = (FStar_Parser_Env.qualify env id)
in (let _145_835 = (FStar_All.pipe_right quals (FStar_List.filter (fun _56_17 -> (match (_56_17) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| _56_2196 -> begin
true
end))))
in (_145_836, [], typars, c, _145_835, rng)))
in FStar_Syntax_Syntax.Sig_effect_abbrev (_145_837)))))
end else begin
(
# 1224 "FStar.Parser.ToSyntax.fst"
let t = (desugar_typ env' t)
in (
# 1225 "FStar.Parser.ToSyntax.fst"
let nm = (FStar_Parser_Env.qualify env id)
in (mk_typ_abbrev nm [] typars k t ((nm)::[]) quals rng)))
end
in (
# 1228 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[]))))))
end))
end
| FStar_Parser_AST.TyconRecord (_56_2202)::[] -> begin
(
# 1232 "FStar.Parser.ToSyntax.fst"
let trec = (FStar_List.hd tcs)
in (
# 1233 "FStar.Parser.ToSyntax.fst"
let _56_2208 = (tycon_record_as_variant trec)
in (match (_56_2208) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| _56_2212::_56_2210 -> begin
(
# 1237 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1238 "FStar.Parser.ToSyntax.fst"
let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_Env.qualify env) (tycon_id x))) tcs)
in (
# 1239 "FStar.Parser.ToSyntax.fst"
let rec collect_tcs = (fun quals et tc -> (
# 1240 "FStar.Parser.ToSyntax.fst"
let _56_2223 = et
in (match (_56_2223) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_56_2225) -> begin
(
# 1243 "FStar.Parser.ToSyntax.fst"
let trec = tc
in (
# 1244 "FStar.Parser.ToSyntax.fst"
let _56_2230 = (tycon_record_as_variant trec)
in (match (_56_2230) with
| (t, fs) -> begin
(collect_tcs ((FStar_Syntax_Syntax.RecordType (fs))::quals) (env, tcs) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(
# 1247 "FStar.Parser.ToSyntax.fst"
let _56_2242 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_56_2242) with
| (env, _56_2239, se, tconstr) -> begin
(env, (FStar_Util.Inl ((se, constructors, tconstr, quals)))::tcs)
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(
# 1250 "FStar.Parser.ToSyntax.fst"
let _56_2254 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_56_2254) with
| (env, _56_2251, se, tconstr) -> begin
(env, (FStar_Util.Inr ((se, t, quals)))::tcs)
end))
end
| _56_2256 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (
# 1253 "FStar.Parser.ToSyntax.fst"
let _56_2259 = (FStar_List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_56_2259) with
| (env, tcs) -> begin
(
# 1254 "FStar.Parser.ToSyntax.fst"
let tcs = (FStar_List.rev tcs)
in (
# 1255 "FStar.Parser.ToSyntax.fst"
let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _56_19 -> (match (_56_19) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, _56_2267, _56_2269, _56_2271, _56_2273), t, quals) -> begin
(
# 1257 "FStar.Parser.ToSyntax.fst"
let _56_2283 = (push_tparams env tpars)
in (match (_56_2283) with
| (env_tps, _56_2282) -> begin
(
# 1258 "FStar.Parser.ToSyntax.fst"
let t = (desugar_term env_tps t)
in (let _145_847 = (let _145_846 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in ([], _145_846))
in (_145_847)::[]))
end))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, _56_2291, tags, _56_2294), constrs, tconstr, quals) -> begin
(
# 1262 "FStar.Parser.ToSyntax.fst"
let tycon = (tname, tpars, k)
in (
# 1263 "FStar.Parser.ToSyntax.fst"
let _56_2305 = (push_tparams env tpars)
in (match (_56_2305) with
| (env_tps, tps) -> begin
(
# 1264 "FStar.Parser.ToSyntax.fst"
let data_tpars = (FStar_List.map (fun _56_2309 -> (match (_56_2309) with
| (x, _56_2308) -> begin
(x, Some (FStar_Syntax_Syntax.Implicit (true)))
end)) tps)
in (
# 1265 "FStar.Parser.ToSyntax.fst"
let _56_2333 = (let _145_859 = (FStar_All.pipe_right constrs (FStar_List.map (fun _56_2314 -> (match (_56_2314) with
| (id, topt, of_notation) -> begin
(
# 1267 "FStar.Parser.ToSyntax.fst"
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
# 1275 "FStar.Parser.ToSyntax.fst"
let t = (let _145_851 = (FStar_Parser_Env.default_total env_tps)
in (let _145_850 = (close env_tps t)
in (desugar_term _145_851 _145_850)))
in (
# 1276 "FStar.Parser.ToSyntax.fst"
let name = (FStar_Parser_Env.qualify env id)
in (
# 1277 "FStar.Parser.ToSyntax.fst"
let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _56_18 -> (match (_56_18) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| _56_2328 -> begin
[]
end))))
in (
# 1280 "FStar.Parser.ToSyntax.fst"
let ntps = (FStar_List.length data_tpars)
in (let _145_858 = (let _145_857 = (let _145_856 = (let _145_855 = (let _145_854 = (let _145_853 = (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total _145_853))
in (FStar_Syntax_Util.arrow data_tpars _145_854))
in (name, univs, _145_855, tname, ntps, quals, mutuals, rng))
in FStar_Syntax_Syntax.Sig_datacon (_145_856))
in (tps, _145_857))
in (name, _145_858)))))))
end))))
in (FStar_All.pipe_left FStar_List.split _145_859))
in (match (_56_2333) with
| (constrNames, constrs) -> begin
(([], FStar_Syntax_Syntax.Sig_inductive_typ ((tname, univs, tpars, k, mutuals, constrNames, tags, rng))))::constrs
end)))
end)))
end
| _56_2335 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1285 "FStar.Parser.ToSyntax.fst"
let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (
# 1286 "FStar.Parser.ToSyntax.fst"
let bundle = (let _145_861 = (let _145_860 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _145_860, rng))
in FStar_Syntax_Syntax.Sig_bundle (_145_861))
in (
# 1287 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 bundle)
in (
# 1288 "FStar.Parser.ToSyntax.fst"
let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projectors quals env)))
in (
# 1289 "FStar.Parser.ToSyntax.fst"
let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _56_20 -> (match (_56_20) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, _56_2344, tps, k, _56_2348, constrs, quals, _56_2352) when ((FStar_List.length constrs) > 1) -> begin
(
# 1291 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract quals) then begin
(FStar_Syntax_Syntax.Private)::quals
end else begin
quals
end
in (mk_data_discriminators quals env tname tps k constrs))
end
| _56_2357 -> begin
[]
end))))
in (
# 1296 "FStar.Parser.ToSyntax.fst"
let ops = (FStar_List.append discs data_ops)
in (
# 1297 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env ops)
in (env, (FStar_List.append ((bundle)::[]) ops)))))))))))
end)))))
end
| [] -> begin
(FStar_All.failwith "impossible")
end))))))))))

# 1302 "FStar.Parser.ToSyntax.fst"
let desugar_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.binder Prims.list) = (fun env binders -> (
# 1303 "FStar.Parser.ToSyntax.fst"
let _56_2381 = (FStar_List.fold_left (fun _56_2366 b -> (match (_56_2366) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| (Some (a), k) -> begin
(
# 1306 "FStar.Parser.ToSyntax.fst"
let _56_2374 = (FStar_Parser_Env.push_bv env a)
in (match (_56_2374) with
| (env, a) -> begin
(let _145_870 = (let _145_869 = (FStar_Syntax_Syntax.mk_binder (
# 1307 "FStar.Parser.ToSyntax.fst"
let _56_2375 = a
in {FStar_Syntax_Syntax.ppname = _56_2375.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _56_2375.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (_145_869)::binders)
in (env, _145_870))
end))
end
| _56_2378 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Missing name in binder", b.FStar_Parser_AST.brange))))
end)
end)) (env, []) binders)
in (match (_56_2381) with
| (env, binders) -> begin
(env, (FStar_List.rev binders))
end)))

# 1312 "FStar.Parser.ToSyntax.fst"
let rec desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (
# 1313 "FStar.Parser.ToSyntax.fst"
let trans_qual = (trans_qual d.FStar_Parser_AST.drange)
in (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(
# 1316 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_pragma (((trans_pragma p), d.FStar_Parser_AST.drange))
in (env, (se)::[]))
end
| FStar_Parser_AST.TopLevelModule (_56_2389) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Multiple modules in a file are no longer supported", d.FStar_Parser_AST.drange))))
end
| FStar_Parser_AST.Open (lid) -> begin
(
# 1323 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_namespace env lid)
in (env, []))
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(let _145_876 = (FStar_Parser_Env.push_module_abbrev env x l)
in (_145_876, []))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(let _145_877 = (FStar_List.map trans_qual qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _145_877 tcs))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _145_879 = (let _145_878 = (desugar_term_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((isrec, lets, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Syntax_Subst.compress _145_878))
in _145_879.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let (lbs, _56_2409) -> begin
(
# 1335 "FStar.Parser.ToSyntax.fst"
let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (
# 1336 "FStar.Parser.ToSyntax.fst"
let quals = (match (quals) with
| _56_2417::_56_2415 -> begin
(FStar_List.map trans_qual quals)
end
| _56_2420 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _56_21 -> (match (_56_21) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (_56_2431); FStar_Syntax_Syntax.lbunivs = _56_2429; FStar_Syntax_Syntax.lbtyp = _56_2427; FStar_Syntax_Syntax.lbeff = _56_2425; FStar_Syntax_Syntax.lbdef = _56_2423} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _56_2441; FStar_Syntax_Syntax.lbtyp = _56_2439; FStar_Syntax_Syntax.lbeff = _56_2437; FStar_Syntax_Syntax.lbdef = _56_2435} -> begin
(FStar_Parser_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (
# 1341 "FStar.Parser.ToSyntax.fst"
let quals = if (FStar_All.pipe_right lets (FStar_Util.for_some (fun _56_2449 -> (match (_56_2449) with
| (_56_2447, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end)))) then begin
(FStar_Syntax_Syntax.Logic)::quals
end else begin
quals
end
in (
# 1345 "FStar.Parser.ToSyntax.fst"
let lbs = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _145_884 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (
# 1347 "FStar.Parser.ToSyntax.fst"
let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (
# 1348 "FStar.Parser.ToSyntax.fst"
let _56_2453 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((
# 1348 "FStar.Parser.ToSyntax.fst"
let _56_2455 = fv
in {FStar_Syntax_Syntax.fv_name = _56_2455.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = _56_2455.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = _56_2453.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _56_2453.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _56_2453.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _56_2453.FStar_Syntax_Syntax.lbdef})))))
in ((Prims.fst lbs), _145_884))
end else begin
lbs
end
in (
# 1350 "FStar.Parser.ToSyntax.fst"
let s = (let _145_887 = (let _145_886 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (lbs, d.FStar_Parser_AST.drange, _145_886, quals))
in FStar_Syntax_Syntax.Sig_let (_145_887))
in (
# 1351 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env s)
in (env, (s)::[])))))))
end
| _56_2462 -> begin
(FStar_All.failwith "Desugaring a let did not produce a let")
end)
end
| FStar_Parser_AST.Main (t) -> begin
(
# 1357 "FStar.Parser.ToSyntax.fst"
let e = (desugar_term env t)
in (
# 1358 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_main ((e, d.FStar_Parser_AST.drange))
in (env, (se)::[])))
end
| FStar_Parser_AST.Assume (atag, id, t) -> begin
(
# 1362 "FStar.Parser.ToSyntax.fst"
let f = (desugar_formula env t)
in (let _145_891 = (let _145_890 = (let _145_889 = (let _145_888 = (FStar_Parser_Env.qualify env id)
in (_145_888, f, (FStar_Syntax_Syntax.Assumption)::[], d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Sig_assume (_145_889))
in (_145_890)::[])
in (env, _145_891)))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(
# 1366 "FStar.Parser.ToSyntax.fst"
let t = (let _145_892 = (close_fun env t)
in (desugar_term env _145_892))
in (
# 1367 "FStar.Parser.ToSyntax.fst"
let quals = if (env.FStar_Parser_Env.iface && env.FStar_Parser_Env.admitted_iface) then begin
(FStar_Parser_AST.Assumption)::quals
end else begin
quals
end
in (
# 1368 "FStar.Parser.ToSyntax.fst"
let se = (let _145_895 = (let _145_894 = (FStar_Parser_Env.qualify env id)
in (let _145_893 = (FStar_List.map trans_qual quals)
in (_145_894, [], t, _145_893, d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_declare_typ (_145_895))
in (
# 1369 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(
# 1373 "FStar.Parser.ToSyntax.fst"
let t = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
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
in (env, (FStar_List.append ((se')::discs) data_ops))))))))))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(
# 1384 "FStar.Parser.ToSyntax.fst"
let t = (desugar_term env term)
in (
# 1385 "FStar.Parser.ToSyntax.fst"
let t = (let _145_899 = (let _145_896 = (FStar_Syntax_Syntax.null_binder t)
in (_145_896)::[])
in (let _145_898 = (let _145_897 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _145_897))
in (FStar_Syntax_Util.arrow _145_899 _145_898)))
in (
# 1386 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env id)
in (
# 1387 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_datacon ((l, [], t, FStar_Syntax_Const.exn_lid, 0, (FStar_Syntax_Syntax.ExceptionConstructor)::[], (FStar_Syntax_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (
# 1388 "FStar.Parser.ToSyntax.fst"
let se' = FStar_Syntax_Syntax.Sig_bundle (((se)::[], (FStar_Syntax_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (
# 1389 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se')
in (
# 1390 "FStar.Parser.ToSyntax.fst"
let data_ops = (mk_data_projectors [] env ([], se))
in (
# 1391 "FStar.Parser.ToSyntax.fst"
let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (
# 1392 "FStar.Parser.ToSyntax.fst"
let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops)))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(
# 1396 "FStar.Parser.ToSyntax.fst"
let _56_2515 = (desugar_binders env binders)
in (match (_56_2515) with
| (env_k, binders) -> begin
(
# 1397 "FStar.Parser.ToSyntax.fst"
let k = (desugar_term env_k k)
in (
# 1398 "FStar.Parser.ToSyntax.fst"
let name = (FStar_Parser_Env.qualify env id)
in (
# 1399 "FStar.Parser.ToSyntax.fst"
let se = (mk_typ_abbrev name [] binders FStar_Syntax_Syntax.tun k ((name)::[]) [] d.FStar_Parser_AST.drange)
in (
# 1400 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env se)
in (env, (se)::[])))))
end))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(
# 1404 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1405 "FStar.Parser.ToSyntax.fst"
let _56_2531 = (desugar_binders env eff_binders)
in (match (_56_2531) with
| (env, binders) -> begin
(
# 1406 "FStar.Parser.ToSyntax.fst"
let _56_2542 = (
# 1407 "FStar.Parser.ToSyntax.fst"
let _56_2534 = (head_and_args defn)
in (match (_56_2534) with
| (head, args) -> begin
(
# 1408 "FStar.Parser.ToSyntax.fst"
let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_effect_defn env) l)
end
| _56_2538 -> begin
(let _145_904 = (let _145_903 = (let _145_902 = (let _145_901 = (let _145_900 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat "Effect " _145_900))
in (Prims.strcat _145_901 " not found"))
in (_145_902, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_145_903))
in (Prims.raise _145_904))
end)
in (let _145_905 = (desugar_args env args)
in (ed, _145_905)))
end))
in (match (_56_2542) with
| (ed, args) -> begin
(
# 1412 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_Syntax_Subst.close_binders binders)
in (
# 1413 "FStar.Parser.ToSyntax.fst"
let sub = (fun _56_2548 -> (match (_56_2548) with
| (_56_2546, x) -> begin
(
# 1414 "FStar.Parser.ToSyntax.fst"
let _56_2551 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (_56_2551) with
| (edb, x) -> begin
(
# 1415 "FStar.Parser.ToSyntax.fst"
let s = (FStar_Syntax_Util.subst_of_list edb args)
in (let _145_909 = (let _145_908 = (FStar_Syntax_Subst.subst s x)
in (FStar_Syntax_Subst.close binders _145_908))
in ([], _145_909)))
end))
end))
in (
# 1417 "FStar.Parser.ToSyntax.fst"
let ed = (let _145_926 = (FStar_List.map trans_qual quals)
in (let _145_925 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _145_924 = (let _145_910 = (sub ([], ed.FStar_Syntax_Syntax.signature))
in (Prims.snd _145_910))
in (let _145_923 = (sub ed.FStar_Syntax_Syntax.ret)
in (let _145_922 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (let _145_921 = (sub ed.FStar_Syntax_Syntax.bind_wlp)
in (let _145_920 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (let _145_919 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (let _145_918 = (sub ed.FStar_Syntax_Syntax.ite_wlp)
in (let _145_917 = (sub ed.FStar_Syntax_Syntax.wp_binop)
in (let _145_916 = (sub ed.FStar_Syntax_Syntax.wp_as_type)
in (let _145_915 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (let _145_914 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (let _145_913 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (let _145_912 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (let _145_911 = (sub ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _145_926; FStar_Syntax_Syntax.mname = _145_925; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = _145_924; FStar_Syntax_Syntax.ret = _145_923; FStar_Syntax_Syntax.bind_wp = _145_922; FStar_Syntax_Syntax.bind_wlp = _145_921; FStar_Syntax_Syntax.if_then_else = _145_920; FStar_Syntax_Syntax.ite_wp = _145_919; FStar_Syntax_Syntax.ite_wlp = _145_918; FStar_Syntax_Syntax.wp_binop = _145_917; FStar_Syntax_Syntax.wp_as_type = _145_916; FStar_Syntax_Syntax.close_wp = _145_915; FStar_Syntax_Syntax.assert_p = _145_914; FStar_Syntax_Syntax.assume_p = _145_913; FStar_Syntax_Syntax.null_wp = _145_912; FStar_Syntax_Syntax.trivial = _145_911}))))))))))))))))
in (
# 1437 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (
# 1438 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 se)
in (env, (se)::[]))))))
end))
end)))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls)) -> begin
(
# 1442 "FStar.Parser.ToSyntax.fst"
let env0 = env
in (
# 1443 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.enter_monad_scope env eff_name)
in (
# 1444 "FStar.Parser.ToSyntax.fst"
let _56_2569 = (desugar_binders env eff_binders)
in (match (_56_2569) with
| (env, binders) -> begin
(
# 1445 "FStar.Parser.ToSyntax.fst"
let eff_k = (let _145_927 = (FStar_Parser_Env.default_total env)
in (desugar_term _145_927 eff_kind))
in (
# 1446 "FStar.Parser.ToSyntax.fst"
let _56_2580 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _56_2573 decl -> (match (_56_2573) with
| (env, out) -> begin
(
# 1447 "FStar.Parser.ToSyntax.fst"
let _56_2577 = (desugar_decl env decl)
in (match (_56_2577) with
| (env, ses) -> begin
(let _145_931 = (let _145_930 = (FStar_List.hd ses)
in (_145_930)::out)
in (env, _145_931))
end))
end)) (env, [])))
in (match (_56_2580) with
| (env, decls) -> begin
(
# 1449 "FStar.Parser.ToSyntax.fst"
let binders = (FStar_Syntax_Subst.close_binders binders)
in (
# 1450 "FStar.Parser.ToSyntax.fst"
let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (
# 1451 "FStar.Parser.ToSyntax.fst"
let lookup = (fun s -> (
# 1452 "FStar.Parser.ToSyntax.fst"
let l = (FStar_Parser_Env.qualify env (FStar_Ident.mk_ident (s, d.FStar_Parser_AST.drange)))
in (let _145_935 = (let _145_934 = (FStar_Parser_Env.fail_or (FStar_Parser_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) _145_934))
in ([], _145_935))))
in (
# 1454 "FStar.Parser.ToSyntax.fst"
let ed = (let _145_950 = (FStar_List.map trans_qual quals)
in (let _145_949 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _145_948 = (lookup "return")
in (let _145_947 = (lookup "bind_wp")
in (let _145_946 = (lookup "bind_wlp")
in (let _145_945 = (lookup "if_then_else")
in (let _145_944 = (lookup "ite_wp")
in (let _145_943 = (lookup "ite_wlp")
in (let _145_942 = (lookup "wp_binop")
in (let _145_941 = (lookup "wp_as_type")
in (let _145_940 = (lookup "close_wp")
in (let _145_939 = (lookup "assert_p")
in (let _145_938 = (lookup "assume_p")
in (let _145_937 = (lookup "null_wp")
in (let _145_936 = (lookup "trivial")
in {FStar_Syntax_Syntax.qualifiers = _145_950; FStar_Syntax_Syntax.mname = _145_949; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret = _145_948; FStar_Syntax_Syntax.bind_wp = _145_947; FStar_Syntax_Syntax.bind_wlp = _145_946; FStar_Syntax_Syntax.if_then_else = _145_945; FStar_Syntax_Syntax.ite_wp = _145_944; FStar_Syntax_Syntax.ite_wlp = _145_943; FStar_Syntax_Syntax.wp_binop = _145_942; FStar_Syntax_Syntax.wp_as_type = _145_941; FStar_Syntax_Syntax.close_wp = _145_940; FStar_Syntax_Syntax.assert_p = _145_939; FStar_Syntax_Syntax.assume_p = _145_938; FStar_Syntax_Syntax.null_wp = _145_937; FStar_Syntax_Syntax.trivial = _145_936})))))))))))))))
in (
# 1474 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (
# 1475 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.push_sigelt env0 se)
in (env, (se)::[])))))))
end)))
end))))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(
# 1479 "FStar.Parser.ToSyntax.fst"
let lookup = (fun l -> (match ((FStar_Parser_Env.try_lookup_effect_name env l)) with
| None -> begin
(let _145_957 = (let _145_956 = (let _145_955 = (let _145_954 = (let _145_953 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat "Effect name " _145_953))
in (Prims.strcat _145_954 " not found"))
in (_145_955, d.FStar_Parser_AST.drange))
in FStar_Syntax_Syntax.Error (_145_956))
in (Prims.raise _145_957))
end
| Some (l) -> begin
l
end))
in (
# 1482 "FStar.Parser.ToSyntax.fst"
let src = (lookup l.FStar_Parser_AST.msource)
in (
# 1483 "FStar.Parser.ToSyntax.fst"
let dst = (lookup l.FStar_Parser_AST.mdest)
in (
# 1484 "FStar.Parser.ToSyntax.fst"
let lift = (let _145_958 = (desugar_term env l.FStar_Parser_AST.lift_op)
in ([], _145_958))
in (
# 1485 "FStar.Parser.ToSyntax.fst"
let se = FStar_Syntax_Syntax.Sig_sub_effect (({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift = lift}, d.FStar_Parser_AST.drange))
in (env, (se)::[]))))))
end)))

# 1488 "FStar.Parser.ToSyntax.fst"
let desugar_decls : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _56_2604 d -> (match (_56_2604) with
| (env, sigelts) -> begin
(
# 1490 "FStar.Parser.ToSyntax.fst"
let _56_2608 = (desugar_decl env d)
in (match (_56_2608) with
| (env, se) -> begin
(env, (FStar_List.append sigelts se))
end))
end)) (env, []) decls))

# 1493 "FStar.Parser.ToSyntax.fst"
let open_prims_all : FStar_Parser_AST.decl Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.all_lid)) FStar_Range.dummyRange))::[]

# 1500 "FStar.Parser.ToSyntax.fst"
let desugar_modul_common : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (
# 1501 "FStar.Parser.ToSyntax.fst"
let open_ns = (fun mname d -> (
# 1502 "FStar.Parser.ToSyntax.fst"
let d = if ((FStar_List.length mname.FStar_Ident.ns) <> 0) then begin
(let _145_977 = (let _145_976 = (let _145_975 = (FStar_Ident.lid_of_ids mname.FStar_Ident.ns)
in FStar_Parser_AST.Open (_145_975))
in (FStar_Parser_AST.mk_decl _145_976 (FStar_Ident.range_of_lid mname)))
in (_145_977)::d)
end else begin
d
end
in d))
in (
# 1506 "FStar.Parser.ToSyntax.fst"
let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod) -> begin
(FStar_Parser_Env.finish_module_or_interface env prev_mod)
end)
in (
# 1509 "FStar.Parser.ToSyntax.fst"
let _56_2635 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _145_979 = (FStar_Parser_Env.prepare_module_or_interface true admitted env mname)
in (let _145_978 = (open_ns mname decls)
in (_145_979, mname, _145_978, true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _145_981 = (FStar_Parser_Env.prepare_module_or_interface false false env mname)
in (let _145_980 = (open_ns mname decls)
in (_145_981, mname, _145_980, false)))
end)
in (match (_56_2635) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(
# 1514 "FStar.Parser.ToSyntax.fst"
let _56_2638 = (desugar_decls env decls)
in (match (_56_2638) with
| (env, sigelts) -> begin
(
# 1515 "FStar.Parser.ToSyntax.fst"
let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in (env, modul, pop_when_done))
end))
end)))))

# 1523 "FStar.Parser.ToSyntax.fst"
let desugar_partial_modul : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (
# 1524 "FStar.Parser.ToSyntax.fst"
let m = if (FStar_ST.read FStar_Options.interactive_fsi) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface ((mname, decls, true))
end
| FStar_Parser_AST.Interface (mname, _56_2649, _56_2651) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (
# 1531 "FStar.Parser.ToSyntax.fst"
let _56_2659 = (desugar_modul_common curmod env m)
in (match (_56_2659) with
| (x, y, _56_2658) -> begin
(x, y)
end))))

# 1534 "FStar.Parser.ToSyntax.fst"
let desugar_modul : FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (
# 1535 "FStar.Parser.ToSyntax.fst"
let _56_2665 = (desugar_modul_common None env m)
in (match (_56_2665) with
| (env, modul, pop_when_done) -> begin
(
# 1536 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.finish_module_or_interface env modul)
in (
# 1537 "FStar.Parser.ToSyntax.fst"
let _56_2667 = if (FStar_Options.should_dump modul.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _145_992 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _145_992))
end else begin
()
end
in (let _145_993 = if pop_when_done then begin
(FStar_Parser_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end else begin
env
end
in (_145_993, modul))))
end)))

# 1541 "FStar.Parser.ToSyntax.fst"
let desugar_file : FStar_Parser_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (
# 1542 "FStar.Parser.ToSyntax.fst"
let _56_2680 = (FStar_List.fold_left (fun _56_2673 m -> (match (_56_2673) with
| (env, mods) -> begin
(
# 1543 "FStar.Parser.ToSyntax.fst"
let _56_2677 = (desugar_modul env m)
in (match (_56_2677) with
| (env, m) -> begin
(env, (m)::mods)
end))
end)) (env, []) f)
in (match (_56_2680) with
| (env, mods) -> begin
(env, (FStar_List.rev mods))
end)))

# 1547 "FStar.Parser.ToSyntax.fst"
let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Parser_Env.env  ->  FStar_Parser_Env.env = (fun m en -> (
# 1548 "FStar.Parser.ToSyntax.fst"
let _56_2685 = (FStar_Parser_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (_56_2685) with
| (en, pop_when_done) -> begin
(
# 1549 "FStar.Parser.ToSyntax.fst"
let en = (FStar_List.fold_left FStar_Parser_Env.push_sigelt (
# 1549 "FStar.Parser.ToSyntax.fst"
let _56_2686 = en
in {FStar_Parser_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_Parser_Env.modules = _56_2686.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _56_2686.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _56_2686.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _56_2686.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _56_2686.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _56_2686.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _56_2686.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _56_2686.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _56_2686.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _56_2686.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = _56_2686.FStar_Parser_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (
# 1550 "FStar.Parser.ToSyntax.fst"
let env = (FStar_Parser_Env.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_Env.export_interface m.FStar_Syntax_Syntax.name env)
end else begin
env
end))
end)))




