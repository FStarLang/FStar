
open Prims
# 33 "FStar.Parser.Desugar.fst"
let imp_tag : FStar_Absyn_Syntax.arg_qualifier = FStar_Absyn_Syntax.Implicit (false)

# 35 "FStar.Parser.Desugar.fst"
let as_imp : FStar_Parser_AST.imp  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option = (fun _53_1 -> (match (_53_1) with
| (FStar_Parser_AST.Hash) | (FStar_Parser_AST.FsTypApp) -> begin
Some (imp_tag)
end
| _53_35 -> begin
None
end))

# 39 "FStar.Parser.Desugar.fst"
let arg_withimp_e = (fun imp t -> (t, (as_imp imp)))

# 41 "FStar.Parser.Desugar.fst"
let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
(t, Some (imp_tag))
end
| _53_42 -> begin
(t, None)
end))

# 45 "FStar.Parser.Desugar.fst"
let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_53_46) -> begin
true
end
| _53_49 -> begin
false
end)))))

# 50 "FStar.Parser.Desugar.fst"
let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _53_54 -> begin
t
end))

# 54 "FStar.Parser.Desugar.fst"
let rec unlabel : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unlabel t)
end
| FStar_Parser_AST.Labeled (t, _53_60, _53_62) -> begin
(unlabel t)
end
| _53_66 -> begin
t
end))

# 58 "FStar.Parser.Desugar.fst"
let kind_star : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _142_17 = (let _142_16 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_142_16))
in (FStar_Parser_AST.mk_term _142_17 r FStar_Parser_AST.Kind)))

# 60 "FStar.Parser.Desugar.fst"
let compile_op : Prims.int  ->  Prims.string  ->  Prims.string = (fun arity s -> (
# 64 "FStar.Parser.Desugar.fst"
let name_of_char = (fun _53_2 -> (match (_53_2) with
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
| _53_89 -> begin
"UNKNOWN"
end))
in (
# 83 "FStar.Parser.Desugar.fst"
let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _142_28 = (let _142_26 = (FStar_Util.char_at s i)
in (name_of_char _142_26))
in (let _142_27 = (aux (i + 1))
in (_142_28)::_142_27))
end)
in (let _142_30 = (let _142_29 = (aux 0)
in (FStar_String.concat "_" _142_29))
in (Prims.strcat "op_" _142_30)))))

# 87 "FStar.Parser.Desugar.fst"
let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.lident = (fun n s r -> (let _142_40 = (let _142_39 = (let _142_38 = (let _142_37 = (compile_op n s)
in (_142_37, r))
in (FStar_Absyn_Syntax.mk_ident _142_38))
in (_142_39)::[])
in (FStar_All.pipe_right _142_40 FStar_Absyn_Syntax.lid_of_ids)))

# 89 "FStar.Parser.Desugar.fst"
let op_as_vlid : FStar_Parser_DesugarEnv.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Ident.lident Prims.option = (fun env arity rng s -> (
# 92 "FStar.Parser.Desugar.fst"
let r = (fun l -> (let _142_51 = (FStar_Ident.set_lid_range l rng)
in Some (_142_51)))
in (
# 93 "FStar.Parser.Desugar.fst"
let fallback = (fun _53_103 -> (match (()) with
| () -> begin
(match (s) with
| "=" -> begin
(r FStar_Absyn_Const.op_Eq)
end
| ":=" -> begin
(r FStar_Absyn_Const.op_ColonEq)
end
| "<" -> begin
(r FStar_Absyn_Const.op_LT)
end
| "<=" -> begin
(r FStar_Absyn_Const.op_LTE)
end
| ">" -> begin
(r FStar_Absyn_Const.op_GT)
end
| ">=" -> begin
(r FStar_Absyn_Const.op_GTE)
end
| "&&" -> begin
(r FStar_Absyn_Const.op_And)
end
| "||" -> begin
(r FStar_Absyn_Const.op_Or)
end
| "*" -> begin
(r FStar_Absyn_Const.op_Multiply)
end
| "+" -> begin
(r FStar_Absyn_Const.op_Addition)
end
| "-" when (arity = 1) -> begin
(r FStar_Absyn_Const.op_Minus)
end
| "-" -> begin
(r FStar_Absyn_Const.op_Subtraction)
end
| "/" -> begin
(r FStar_Absyn_Const.op_Division)
end
| "%" -> begin
(r FStar_Absyn_Const.op_Modulus)
end
| "!" -> begin
(r FStar_Absyn_Const.read_lid)
end
| "@" -> begin
(r FStar_Absyn_Const.list_append_lid)
end
| "^" -> begin
(r FStar_Absyn_Const.strcat_lid)
end
| "|>" -> begin
(r FStar_Absyn_Const.pipe_right_lid)
end
| "<|" -> begin
(r FStar_Absyn_Const.pipe_left_lid)
end
| "<>" -> begin
(r FStar_Absyn_Const.op_notEq)
end
| _53_125 -> begin
None
end)
end))
in (match ((let _142_54 = (compile_op_lid arity s rng)
in (FStar_Parser_DesugarEnv.try_lookup_lid env _142_54))) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _53_136); FStar_Absyn_Syntax.tk = _53_133; FStar_Absyn_Syntax.pos = _53_131; FStar_Absyn_Syntax.fvs = _53_129; FStar_Absyn_Syntax.uvs = _53_127}) -> begin
Some (fv.FStar_Absyn_Syntax.v)
end
| _53_142 -> begin
(fallback ())
end))))

# 119 "FStar.Parser.Desugar.fst"
let op_as_tylid : FStar_Parser_DesugarEnv.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Ident.lident Prims.option = (fun env arity rng s -> (
# 122 "FStar.Parser.Desugar.fst"
let r = (fun l -> (let _142_65 = (FStar_Ident.set_lid_range l rng)
in Some (_142_65)))
in (match (s) with
| "~" -> begin
(r FStar_Absyn_Const.not_lid)
end
| "==" -> begin
(r FStar_Absyn_Const.eq2_lid)
end
| "=!=" -> begin
(r FStar_Absyn_Const.neq2_lid)
end
| "<<" -> begin
(r FStar_Absyn_Const.precedes_lid)
end
| "/\\" -> begin
(r FStar_Absyn_Const.and_lid)
end
| "\\/" -> begin
(r FStar_Absyn_Const.or_lid)
end
| "==>" -> begin
(r FStar_Absyn_Const.imp_lid)
end
| "<==>" -> begin
(r FStar_Absyn_Const.iff_lid)
end
| s -> begin
(match ((let _142_66 = (compile_op_lid arity s rng)
in (FStar_Parser_DesugarEnv.try_lookup_typ_name env _142_66))) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ftv); FStar_Absyn_Syntax.tk = _53_165; FStar_Absyn_Syntax.pos = _53_163; FStar_Absyn_Syntax.fvs = _53_161; FStar_Absyn_Syntax.uvs = _53_159}) -> begin
Some (ftv.FStar_Absyn_Syntax.v)
end
| _53_171 -> begin
None
end)
end)))

# 136 "FStar.Parser.Desugar.fst"
let rec is_type : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> if (t.FStar_Parser_AST.level = FStar_Parser_AST.Type) then begin
true
end else begin
(match ((let _142_73 = (unparen t)
in _142_73.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
true
end
| FStar_Parser_AST.Labeled (_53_176) -> begin
true
end
| FStar_Parser_AST.Op ("*", hd::_53_180) -> begin
(is_type env hd)
end
| (FStar_Parser_AST.Op ("==", _)) | (FStar_Parser_AST.Op ("=!=", _)) | (FStar_Parser_AST.Op ("~", _)) | (FStar_Parser_AST.Op ("/\\", _)) | (FStar_Parser_AST.Op ("\\/", _)) | (FStar_Parser_AST.Op ("==>", _)) | (FStar_Parser_AST.Op ("<==>", _)) | (FStar_Parser_AST.Op ("<<", _)) -> begin
true
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_tylid env (FStar_List.length args) t.FStar_Parser_AST.range s)) with
| None -> begin
false
end
| _53_231 -> begin
true
end)
end
| (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.NamedTyp (_)) -> begin
true
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) when ((FStar_List.length l.FStar_Ident.ns) = 0) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env l.FStar_Ident.ident)) with
| Some (_53_254) -> begin
true
end
| _53_257 -> begin
(FStar_Parser_DesugarEnv.is_type_lid env l)
end)
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) | (FStar_Parser_AST.Construct (l, _)) -> begin
(FStar_Parser_DesugarEnv.is_type_lid env l)
end
| (FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (l); FStar_Parser_AST.range = _; FStar_Parser_AST.level = _}, arg, FStar_Parser_AST.Nothing)) | (FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = _; FStar_Parser_AST.level = _}, arg, FStar_Parser_AST.Nothing)) when (l.FStar_Ident.str = "ref") -> begin
(is_type env arg)
end
| (FStar_Parser_AST.App (t, _, _)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(is_type env t)
end
| FStar_Parser_AST.Product (_53_298, t) -> begin
(not ((is_kind env t)))
end
| FStar_Parser_AST.If (t, t1, t2) -> begin
(((is_type env t) || (is_type env t1)) || (is_type env t2))
end
| FStar_Parser_AST.Abs (pats, t) -> begin
(
# 179 "FStar.Parser.Desugar.fst"
let rec aux = (fun env pats -> (match (pats) with
| [] -> begin
(is_type env t)
end
| hd::pats -> begin
(match (hd.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatWild) | (FStar_Parser_AST.PatVar (_)) -> begin
(aux env pats)
end
| FStar_Parser_AST.PatTvar (id, _53_324) -> begin
(
# 186 "FStar.Parser.Desugar.fst"
let _53_330 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_53_330) with
| (env, _53_329) -> begin
(aux env pats)
end))
end
| FStar_Parser_AST.PatAscribed (p, tm) -> begin
(
# 189 "FStar.Parser.Desugar.fst"
let env = if (is_kind env tm) then begin
(match (p.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatVar (id, _)) | (FStar_Parser_AST.PatTvar (id, _)) -> begin
(let _142_78 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (FStar_All.pipe_right _142_78 Prims.fst))
end
| _53_345 -> begin
env
end)
end else begin
env
end
in (aux env pats))
end
| _53_348 -> begin
false
end)
end))
in (aux env pats))
end
| FStar_Parser_AST.Let (false, ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_53_353); FStar_Parser_AST.prange = _53_351}, _53_357)::[], t) -> begin
(is_type env t)
end
| FStar_Parser_AST.Let (false, ({FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_53_369); FStar_Parser_AST.prange = _53_367}, _53_373); FStar_Parser_AST.prange = _53_365}, _53_378)::[], t) -> begin
(is_type env t)
end
| FStar_Parser_AST.Let (false, ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_53_388); FStar_Parser_AST.prange = _53_386}, _53_392)::[], t) -> begin
(is_type env t)
end
| _53_399 -> begin
false
end)
end)
and is_kind : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> if (t.FStar_Parser_AST.level = FStar_Parser_AST.Kind) then begin
true
end else begin
(match ((let _142_81 = (unparen t)
in _142_81.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Name ({FStar_Ident.ns = _53_408; FStar_Ident.ident = _53_406; FStar_Ident.nsstr = _53_404; FStar_Ident.str = "Type"}) -> begin
true
end
| FStar_Parser_AST.Product (_53_412, t) -> begin
(is_kind env t)
end
| FStar_Parser_AST.Paren (t) -> begin
(is_kind env t)
end
| (FStar_Parser_AST.Construct (l, _)) | (FStar_Parser_AST.Name (l)) -> begin
(FStar_Parser_DesugarEnv.is_kind_abbrev env l)
end
| _53_425 -> begin
false
end)
end)

# 213 "FStar.Parser.Desugar.fst"
let rec is_type_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  Prims.bool = (fun env b -> if (b.FStar_Parser_AST.blevel = FStar_Parser_AST.Formula) then begin
(match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_53_429) -> begin
false
end
| (FStar_Parser_AST.TAnnotated (_)) | (FStar_Parser_AST.TVariable (_)) -> begin
true
end
| (FStar_Parser_AST.Annotated (_, t)) | (FStar_Parser_AST.NoName (t)) -> begin
(is_kind env t)
end)
end else begin
(match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_53_444) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected binder without annotation", b.FStar_Parser_AST.brange))))
end
| FStar_Parser_AST.TVariable (_53_447) -> begin
false
end
| FStar_Parser_AST.TAnnotated (_53_450) -> begin
true
end
| (FStar_Parser_AST.Annotated (_, t)) | (FStar_Parser_AST.NoName (t)) -> begin
(is_kind env t)
end)
end)

# 228 "FStar.Parser.Desugar.fst"
let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _142_92 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _142_92)))

# 232 "FStar.Parser.Desugar.fst"
let rec free_type_vars_b : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_DesugarEnv.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_53_466) -> begin
(env, [])
end
| FStar_Parser_AST.TVariable (x) -> begin
(
# 237 "FStar.Parser.Desugar.fst"
let _53_473 = (FStar_Parser_DesugarEnv.push_local_tbinding env x)
in (match (_53_473) with
| (env, _53_472) -> begin
(env, (x)::[])
end))
end
| FStar_Parser_AST.Annotated (_53_475, term) -> begin
(let _142_99 = (free_type_vars env term)
in (env, _142_99))
end
| FStar_Parser_AST.TAnnotated (id, _53_481) -> begin
(
# 242 "FStar.Parser.Desugar.fst"
let _53_487 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_53_487) with
| (env, _53_486) -> begin
(env, [])
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _142_100 = (free_type_vars env t)
in (env, _142_100))
end))
and free_type_vars : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _142_103 = (unparen t)
in _142_103.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env a)) with
| None -> begin
(a)::[]
end
| _53_496 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.Labeled (t, _, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_53_532, ts) -> begin
(FStar_List.collect (fun _53_539 -> (match (_53_539) with
| (t, _53_538) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_53_541, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _53_548) -> begin
(let _142_106 = (free_type_vars env t1)
in (let _142_105 = (free_type_vars env t2)
in (FStar_List.append _142_106 _142_105)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(
# 271 "FStar.Parser.Desugar.fst"
let _53_557 = (free_type_vars_b env b)
in (match (_53_557) with
| (env, f) -> begin
(let _142_107 = (free_type_vars env t)
in (FStar_List.append f _142_107))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(
# 276 "FStar.Parser.Desugar.fst"
let _53_573 = (FStar_List.fold_left (fun _53_566 binder -> (match (_53_566) with
| (env, free) -> begin
(
# 277 "FStar.Parser.Desugar.fst"
let _53_570 = (free_type_vars_b env binder)
in (match (_53_570) with
| (env, f) -> begin
(env, (FStar_List.append f free))
end))
end)) (env, []) binders)
in (match (_53_573) with
| (env, free) -> begin
(let _142_110 = (free_type_vars env body)
in (FStar_List.append free _142_110))
end))
end
| FStar_Parser_AST.Project (t, _53_576) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) -> begin
[]
end
| (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
(FStar_Parser_AST.error "Unexpected type in free_type_vars computation" t t.FStar_Parser_AST.range)
end))

# 292 "FStar.Parser.Desugar.fst"
let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (
# 295 "FStar.Parser.Desugar.fst"
let rec aux = (fun args t -> (match ((let _142_117 = (unparen t)
in _142_117.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _53_620 -> begin
(t, args)
end))
in (aux [] t)))

# 299 "FStar.Parser.Desugar.fst"
let close : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 302 "FStar.Parser.Desugar.fst"
let ftv = (let _142_122 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _142_122))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 305 "FStar.Parser.Desugar.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _142_126 = (let _142_125 = (let _142_124 = (kind_star x.FStar_Ident.idRange)
in (x, _142_124))
in FStar_Parser_AST.TAnnotated (_142_125))
in (FStar_Parser_AST.mk_binder _142_126 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 306 "FStar.Parser.Desugar.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))

# 307 "FStar.Parser.Desugar.fst"
let close_fun : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 310 "FStar.Parser.Desugar.fst"
let ftv = (let _142_131 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _142_131))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 313 "FStar.Parser.Desugar.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _142_135 = (let _142_134 = (let _142_133 = (kind_star x.FStar_Ident.idRange)
in (x, _142_133))
in FStar_Parser_AST.TAnnotated (_142_134))
in (FStar_Parser_AST.mk_binder _142_135 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 314 "FStar.Parser.Desugar.fst"
let t = (match ((let _142_136 = (unlabel t)
in _142_136.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_53_633) -> begin
t
end
| _53_636 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level), t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end)
in (
# 317 "FStar.Parser.Desugar.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result)))
end))

# 318 "FStar.Parser.Desugar.fst"
let rec uncurry : FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term) = (fun bs t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (binders, t) -> begin
(uncurry (FStar_List.append bs binders) t)
end
| _53_646 -> begin
(bs, t)
end))

# 322 "FStar.Parser.Desugar.fst"
let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _53_650) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_53_656); FStar_Parser_AST.prange = _53_654}, _53_660) -> begin
true
end
| _53_664 -> begin
false
end))

# 327 "FStar.Parser.Desugar.fst"
let rec destruct_app_pattern : FStar_Parser_DesugarEnv.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 331 "FStar.Parser.Desugar.fst"
let _53_676 = (destruct_app_pattern env is_top_level p)
in (match (_53_676) with
| (name, args, _53_675) -> begin
(name, args, Some (t))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _53_681); FStar_Parser_AST.prange = _53_678}, args) when is_top_level -> begin
(let _142_150 = (let _142_149 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_142_149))
in (_142_150, args, None))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _53_692); FStar_Parser_AST.prange = _53_689}, args) -> begin
(FStar_Util.Inl (id), args, None)
end
| _53_700 -> begin
(FStar_All.failwith "Not an app pattern")
end))

# 338 "FStar.Parser.Desugar.fst"
type bnd =
| TBinder of (FStar_Absyn_Syntax.btvdef * FStar_Absyn_Syntax.knd * FStar_Absyn_Syntax.aqual)
| VBinder of (FStar_Absyn_Syntax.bvvdef * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * FStar_Absyn_Syntax.typ)

# 341 "FStar.Parser.Desugar.fst"
let is_TBinder = (fun _discr_ -> (match (_discr_) with
| TBinder (_) -> begin
true
end
| _ -> begin
false
end))

# 342 "FStar.Parser.Desugar.fst"
let is_VBinder = (fun _discr_ -> (match (_discr_) with
| VBinder (_) -> begin
true
end
| _ -> begin
false
end))

# 343 "FStar.Parser.Desugar.fst"
let is_LetBinder = (fun _discr_ -> (match (_discr_) with
| LetBinder (_) -> begin
true
end
| _ -> begin
false
end))

# 341 "FStar.Parser.Desugar.fst"
let ___TBinder____0 = (fun projectee -> (match (projectee) with
| TBinder (_53_703) -> begin
_53_703
end))

# 342 "FStar.Parser.Desugar.fst"
let ___VBinder____0 = (fun projectee -> (match (projectee) with
| VBinder (_53_706) -> begin
_53_706
end))

# 343 "FStar.Parser.Desugar.fst"
let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_53_709) -> begin
_53_709
end))

# 343 "FStar.Parser.Desugar.fst"
let binder_of_bnd : bnd  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.aqual) = (fun _53_3 -> (match (_53_3) with
| TBinder (a, k, aq) -> begin
(FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k)), aq)
end
| VBinder (x, t, aq) -> begin
(FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), aq)
end
| _53_722 -> begin
(FStar_All.failwith "Impossible")
end))

# 347 "FStar.Parser.Desugar.fst"
let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option = (fun _53_4 -> (match (_53_4) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Absyn_Syntax.Equality)
end
| _53_729 -> begin
None
end))

# 351 "FStar.Parser.Desugar.fst"
let as_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  ((FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd), (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ)) FStar_Util.either  ->  (FStar_Absyn_Syntax.binder * FStar_Parser_DesugarEnv.env) = (fun env imp _53_5 -> (match (_53_5) with
| FStar_Util.Inl (None, k) -> begin
(let _142_203 = (FStar_Absyn_Syntax.null_t_binder k)
in (_142_203, env))
end
| FStar_Util.Inr (None, t) -> begin
(let _142_204 = (FStar_Absyn_Syntax.null_v_binder t)
in (_142_204, env))
end
| FStar_Util.Inl (Some (a), k) -> begin
(
# 356 "FStar.Parser.Desugar.fst"
let _53_748 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_53_748) with
| (env, a) -> begin
((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k)), (trans_aqual imp)), env)
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(
# 359 "FStar.Parser.Desugar.fst"
let _53_756 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_53_756) with
| (env, x) -> begin
((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), (trans_aqual imp)), env)
end))
end))

# 360 "FStar.Parser.Desugar.fst"
type env_t =
FStar_Parser_DesugarEnv.env

# 362 "FStar.Parser.Desugar.fst"
type lenv_t =
(FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either Prims.list

# 363 "FStar.Parser.Desugar.fst"
let label_conjuncts : Prims.string  ->  Prims.bool  ->  Prims.string Prims.option  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun tag polarity label_opt f -> (
# 366 "FStar.Parser.Desugar.fst"
let label = (fun f -> (
# 367 "FStar.Parser.Desugar.fst"
let msg = (match (label_opt) with
| Some (l) -> begin
l
end
| _53_766 -> begin
(let _142_215 = (FStar_Range.string_of_range f.FStar_Parser_AST.range)
in (FStar_Util.format2 "%s at %s" tag _142_215))
end)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled ((f, msg, polarity))) f.FStar_Parser_AST.range f.FStar_Parser_AST.level)))
in (
# 373 "FStar.Parser.Desugar.fst"
let rec aux = (fun f -> (match (f.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (g) -> begin
(let _142_219 = (let _142_218 = (aux g)
in FStar_Parser_AST.Paren (_142_218))
in (FStar_Parser_AST.mk_term _142_219 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op ("/\\", f1::f2::[]) -> begin
(let _142_225 = (let _142_224 = (let _142_223 = (let _142_222 = (aux f1)
in (let _142_221 = (let _142_220 = (aux f2)
in (_142_220)::[])
in (_142_222)::_142_221))
in ("/\\", _142_223))
in FStar_Parser_AST.Op (_142_224))
in (FStar_Parser_AST.mk_term _142_225 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _142_229 = (let _142_228 = (let _142_227 = (aux f2)
in (let _142_226 = (aux f3)
in (f1, _142_227, _142_226)))
in FStar_Parser_AST.If (_142_228))
in (FStar_Parser_AST.mk_term _142_229 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Abs (binders, g) -> begin
(let _142_232 = (let _142_231 = (let _142_230 = (aux g)
in (binders, _142_230))
in FStar_Parser_AST.Abs (_142_231))
in (FStar_Parser_AST.mk_term _142_232 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| _53_788 -> begin
(label f)
end))
in (aux f))))

# 389 "FStar.Parser.Desugar.fst"
let mk_lb : (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.exp)  ->  FStar_Absyn_Syntax.letbinding = (fun _53_792 -> (match (_53_792) with
| (n, t, e) -> begin
{FStar_Absyn_Syntax.lbname = n; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = e}
end))

# 391 "FStar.Parser.Desugar.fst"
let rec desugar_data_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat) = (fun env p -> (
# 394 "FStar.Parser.Desugar.fst"
let resolvex = (fun l e x -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun _53_6 -> (match (_53_6) with
| FStar_Util.Inr (y) -> begin
(y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText)
end
| _53_803 -> begin
false
end))))) with
| Some (FStar_Util.Inr (y)) -> begin
(l, e, y)
end
| _53_808 -> begin
(
# 398 "FStar.Parser.Desugar.fst"
let _53_811 = (FStar_Parser_DesugarEnv.push_local_vbinding e x)
in (match (_53_811) with
| (e, x) -> begin
((FStar_Util.Inr (x))::l, e, x)
end))
end))
in (
# 400 "FStar.Parser.Desugar.fst"
let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun _53_7 -> (match (_53_7) with
| FStar_Util.Inl (b) -> begin
(b.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText)
end
| _53_820 -> begin
false
end))))) with
| Some (FStar_Util.Inl (b)) -> begin
(l, e, b)
end
| _53_825 -> begin
(
# 404 "FStar.Parser.Desugar.fst"
let _53_828 = (FStar_Parser_DesugarEnv.push_local_tbinding e a)
in (match (_53_828) with
| (e, a) -> begin
((FStar_Util.Inl (a))::l, e, a)
end))
end))
in (
# 406 "FStar.Parser.Desugar.fst"
let rec aux = (fun loc env p -> (
# 407 "FStar.Parser.Desugar.fst"
let pos = (fun q -> (FStar_Absyn_Syntax.withinfo q None p.FStar_Parser_AST.prange))
in (
# 408 "FStar.Parser.Desugar.fst"
let pos_r = (fun r q -> (FStar_Absyn_Syntax.withinfo q None r))
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOr ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.PatOr (p::ps) -> begin
(
# 412 "FStar.Parser.Desugar.fst"
let _53_850 = (aux loc env p)
in (match (_53_850) with
| (loc, env, var, p, _53_849) -> begin
(
# 413 "FStar.Parser.Desugar.fst"
let _53_867 = (FStar_List.fold_left (fun _53_854 p -> (match (_53_854) with
| (loc, env, ps) -> begin
(
# 414 "FStar.Parser.Desugar.fst"
let _53_863 = (aux loc env p)
in (match (_53_863) with
| (loc, env, _53_859, p, _53_862) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_53_867) with
| (loc, env, ps) -> begin
(
# 416 "FStar.Parser.Desugar.fst"
let pat = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in (
# 417 "FStar.Parser.Desugar.fst"
let _53_869 = (let _142_304 = (FStar_Absyn_Syntax.pat_vars pat)
in (Prims.ignore _142_304))
in (loc, env, var, pat, false)))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 421 "FStar.Parser.Desugar.fst"
let p = if (is_kind env t) then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTvar (_53_876) -> begin
p
end
| FStar_Parser_AST.PatVar (x, imp) -> begin
(
# 424 "FStar.Parser.Desugar.fst"
let _53_882 = p
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar ((x, imp)); FStar_Parser_AST.prange = _53_882.FStar_Parser_AST.prange})
end
| _53_885 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end)
end else begin
p
end
in (
# 427 "FStar.Parser.Desugar.fst"
let _53_892 = (aux loc env p)
in (match (_53_892) with
| (loc, env', binder, p, imp) -> begin
(
# 428 "FStar.Parser.Desugar.fst"
let binder = (match (binder) with
| LetBinder (_53_894) -> begin
(FStar_All.failwith "impossible")
end
| TBinder (x, _53_898, aq) -> begin
(let _142_306 = (let _142_305 = (desugar_kind env t)
in (x, _142_305, aq))
in TBinder (_142_306))
end
| VBinder (x, _53_904, aq) -> begin
(
# 432 "FStar.Parser.Desugar.fst"
let t = (close_fun env t)
in (let _142_308 = (let _142_307 = (desugar_typ env t)
in (x, _142_307, aq))
in VBinder (_142_308)))
end)
in (loc, env', binder, p, imp))
end)))
end
| FStar_Parser_AST.PatTvar (a, aq) -> begin
(
# 437 "FStar.Parser.Desugar.fst"
let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (
# 438 "FStar.Parser.Desugar.fst"
let aq = (trans_aqual aq)
in if (a.FStar_Ident.idText = "\'_") then begin
(
# 440 "FStar.Parser.Desugar.fst"
let a = (FStar_All.pipe_left FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _142_309 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_twild ((FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((a, FStar_Absyn_Syntax.kun, aq)), _142_309, imp)))
end else begin
(
# 442 "FStar.Parser.Desugar.fst"
let _53_920 = (resolvea loc env a)
in (match (_53_920) with
| (loc, env, abvd) -> begin
(let _142_310 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_tvar ((FStar_Absyn_Util.bvd_to_bvar_s abvd FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((abvd, FStar_Absyn_Syntax.kun, aq)), _142_310, imp))
end))
end))
end
| FStar_Parser_AST.PatWild -> begin
(
# 446 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (
# 447 "FStar.Parser.Desugar.fst"
let y = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _142_311 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_wild ((FStar_Absyn_Util.bvd_to_bvar_s y FStar_Absyn_Syntax.tun))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _142_311, false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(
# 451 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _142_312 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_constant (c)))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _142_312, false)))
end
| FStar_Parser_AST.PatVar (x, aq) -> begin
(
# 455 "FStar.Parser.Desugar.fst"
let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (
# 456 "FStar.Parser.Desugar.fst"
let aq = (trans_aqual aq)
in (
# 457 "FStar.Parser.Desugar.fst"
let _53_936 = (resolvex loc env x)
in (match (_53_936) with
| (loc, env, xbvd) -> begin
(let _142_313 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_var ((FStar_Absyn_Util.bvd_to_bvar_s xbvd FStar_Absyn_Syntax.tun))))
in (loc, env, VBinder ((xbvd, FStar_Absyn_Syntax.tun, aq)), _142_313, imp))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(
# 461 "FStar.Parser.Desugar.fst"
let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (
# 462 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _142_314 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons ((l, Some (FStar_Absyn_Syntax.Data_ctor), []))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _142_314, false))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _53_942}, args) -> begin
(
# 466 "FStar.Parser.Desugar.fst"
let _53_964 = (FStar_List.fold_right (fun arg _53_953 -> (match (_53_953) with
| (loc, env, args) -> begin
(
# 467 "FStar.Parser.Desugar.fst"
let _53_960 = (aux loc env arg)
in (match (_53_960) with
| (loc, env, _53_957, arg, imp) -> begin
(loc, env, ((arg, imp))::args)
end))
end)) args (loc, env, []))
in (match (_53_964) with
| (loc, env, args) -> begin
(
# 469 "FStar.Parser.Desugar.fst"
let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (
# 470 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _142_317 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons ((l, Some (FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _142_317, false))))
end))
end
| FStar_Parser_AST.PatApp (_53_968) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(
# 476 "FStar.Parser.Desugar.fst"
let _53_988 = (FStar_List.fold_right (fun pat _53_976 -> (match (_53_976) with
| (loc, env, pats) -> begin
(
# 477 "FStar.Parser.Desugar.fst"
let _53_984 = (aux loc env pat)
in (match (_53_984) with
| (loc, env, _53_980, pat, _53_983) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_53_988) with
| (loc, env, pats) -> begin
(
# 479 "FStar.Parser.Desugar.fst"
let pat = (let _142_324 = (let _142_323 = (let _142_322 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _142_322))
in (FStar_All.pipe_left _142_323 (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv FStar_Absyn_Const.nil_lid), Some (FStar_Absyn_Syntax.Data_ctor), [])))))
in (FStar_List.fold_right (fun hd tl -> (
# 480 "FStar.Parser.Desugar.fst"
let r = (FStar_Range.union_ranges hd.FStar_Absyn_Syntax.p tl.FStar_Absyn_Syntax.p)
in (FStar_All.pipe_left (pos_r r) (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv FStar_Absyn_Const.cons_lid), Some (FStar_Absyn_Syntax.Data_ctor), ((hd, false))::((tl, false))::[])))))) pats _142_324))
in (
# 483 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), pat, false)))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(
# 487 "FStar.Parser.Desugar.fst"
let _53_1014 = (FStar_List.fold_left (fun _53_1001 p -> (match (_53_1001) with
| (loc, env, pats) -> begin
(
# 488 "FStar.Parser.Desugar.fst"
let _53_1010 = (aux loc env p)
in (match (_53_1010) with
| (loc, env, _53_1006, pat, _53_1009) -> begin
(loc, env, ((pat, false))::pats)
end))
end)) (loc, env, []) args)
in (match (_53_1014) with
| (loc, env, args) -> begin
(
# 490 "FStar.Parser.Desugar.fst"
let args = (FStar_List.rev args)
in (
# 491 "FStar.Parser.Desugar.fst"
let l = if dep then begin
(FStar_Absyn_Util.mk_dtuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end else begin
(FStar_Absyn_Util.mk_tuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end
in (
# 493 "FStar.Parser.Desugar.fst"
let constr = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (
# 494 "FStar.Parser.Desugar.fst"
let l = (match (constr.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (v, _53_1020) -> begin
v
end
| _53_1024 -> begin
(FStar_All.failwith "impossible")
end)
in (
# 497 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _142_327 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons ((l, Some (FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _142_327, false)))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(
# 504 "FStar.Parser.Desugar.fst"
let _53_1034 = (FStar_List.hd fields)
in (match (_53_1034) with
| (f, _53_1033) -> begin
(
# 505 "FStar.Parser.Desugar.fst"
let _53_1038 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_53_1038) with
| (record, _53_1037) -> begin
(
# 506 "FStar.Parser.Desugar.fst"
let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _53_1041 -> (match (_53_1041) with
| (f, p) -> begin
(let _142_329 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.qualify_field_to_record env record) f)
in (_142_329, p))
end))))
in (
# 508 "FStar.Parser.Desugar.fst"
let args = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _53_1046 -> (match (_53_1046) with
| (f, _53_1045) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _53_1050 -> (match (_53_1050) with
| (g, _53_1049) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_53_1053, p) -> begin
p
end)
end))))
in (
# 512 "FStar.Parser.Desugar.fst"
let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_DesugarEnv.constrname)) p.FStar_Parser_AST.prange), args))) p.FStar_Parser_AST.prange)
in (
# 513 "FStar.Parser.Desugar.fst"
let _53_1065 = (aux loc env app)
in (match (_53_1065) with
| (env, e, b, p, _53_1064) -> begin
(
# 514 "FStar.Parser.Desugar.fst"
let p = (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (fv, _53_1068, args) -> begin
(let _142_337 = (let _142_336 = (let _142_335 = (let _142_334 = (let _142_333 = (let _142_332 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_DesugarEnv.typename, _142_332))
in FStar_Absyn_Syntax.Record_ctor (_142_333))
in Some (_142_334))
in (fv, _142_335, args))
in FStar_Absyn_Syntax.Pat_cons (_142_336))
in (FStar_All.pipe_left pos _142_337))
end
| _53_1073 -> begin
p
end)
in (env, e, b, p, false))
end)))))
end))
end))
end))))
in (
# 519 "FStar.Parser.Desugar.fst"
let _53_1082 = (aux [] env p)
in (match (_53_1082) with
| (_53_1076, env, b, p, _53_1081) -> begin
(env, b, p)
end))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat Prims.option) = (fun top env p -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _53_1088) -> begin
(let _142_343 = (let _142_342 = (let _142_341 = (FStar_Parser_DesugarEnv.qualify env x)
in (_142_341, FStar_Absyn_Syntax.tun))
in LetBinder (_142_342))
in (env, _142_343, None))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _53_1095); FStar_Parser_AST.prange = _53_1092}, t) -> begin
(let _142_347 = (let _142_346 = (let _142_345 = (FStar_Parser_DesugarEnv.qualify env x)
in (let _142_344 = (desugar_typ env t)
in (_142_345, _142_344)))
in LetBinder (_142_346))
in (env, _142_347, None))
end
| _53_1103 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern at the top-level", p.FStar_Parser_AST.prange))))
end)
end else begin
(
# 530 "FStar.Parser.Desugar.fst"
let _53_1107 = (desugar_data_pat env p)
in (match (_53_1107) with
| (env, binder, p) -> begin
(
# 531 "FStar.Parser.Desugar.fst"
let p = (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_var (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) -> begin
None
end
| _53_1118 -> begin
Some (p)
end)
in (env, binder, p))
end))
end)
and desugar_binding_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Absyn_Syntax.pat) = (fun _53_1122 env pat -> (
# 541 "FStar.Parser.Desugar.fst"
let _53_1130 = (desugar_data_pat env pat)
in (match (_53_1130) with
| (env, _53_1128, pat) -> begin
(env, pat)
end)))
and desugar_match_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Absyn_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_typ_or_exp : env_t  ->  FStar_Parser_AST.term  ->  (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either = (fun env t -> if (is_type env t) then begin
(let _142_357 = (desugar_typ env t)
in FStar_Util.Inl (_142_357))
end else begin
(let _142_358 = (desugar_exp env t)
in FStar_Util.Inr (_142_358))
end)
and desugar_exp : env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.exp = (fun env e -> (desugar_exp_maybe_top false env e))
and desugar_exp_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.exp = (fun top_level env top -> (
# 554 "FStar.Parser.Desugar.fst"
let pos = (fun e -> (e None top.FStar_Parser_AST.range))
in (
# 555 "FStar.Parser.Desugar.fst"
let setpos = (fun e -> (
# 555 "FStar.Parser.Desugar.fst"
let _53_1144 = e
in {FStar_Absyn_Syntax.n = _53_1144.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _53_1144.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _53_1144.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _53_1144.FStar_Absyn_Syntax.uvs}))
in (match ((let _142_378 = (unparen top)
in _142_378.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Const (c) -> begin
(FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_constant c))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_vlid env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat "Unexpected operator: " s), top.FStar_Parser_AST.range))))
end
| Some (l) -> begin
(
# 563 "FStar.Parser.Desugar.fst"
let op = (FStar_Absyn_Util.fvar None l (FStar_Ident.range_of_lid l))
in (
# 564 "FStar.Parser.Desugar.fst"
let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _142_382 = (desugar_typ_or_exp env t)
in (_142_382, None)))))
in (let _142_383 = (FStar_Absyn_Util.mk_exp_app op args)
in (FStar_All.pipe_left setpos _142_383))))
end)
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
if (l.FStar_Ident.str = "ref") then begin
(match ((FStar_Parser_DesugarEnv.try_lookup_lid env FStar_Absyn_Const.alloc_lid)) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Identifier \'ref\' not found; include lib/FStar.ST.fst in your path", (FStar_Ident.range_of_lid l)))))
end
| Some (e) -> begin
(setpos e)
end)
end else begin
(let _142_384 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (FStar_All.pipe_left setpos _142_384))
end
end
| FStar_Parser_AST.Construct (l, args) -> begin
(
# 579 "FStar.Parser.Desugar.fst"
let dt = (let _142_389 = (let _142_388 = (let _142_387 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (_142_387, Some (FStar_Absyn_Syntax.Data_ctor)))
in (FStar_Absyn_Syntax.mk_Exp_fvar _142_388))
in (FStar_All.pipe_left pos _142_389))
in (match (args) with
| [] -> begin
dt
end
| _53_1171 -> begin
(
# 583 "FStar.Parser.Desugar.fst"
let args = (FStar_List.map (fun _53_1174 -> (match (_53_1174) with
| (t, imp) -> begin
(
# 584 "FStar.Parser.Desugar.fst"
let te = (desugar_typ_or_exp env t)
in (arg_withimp_e imp te))
end)) args)
in (let _142_394 = (let _142_393 = (let _142_392 = (let _142_391 = (FStar_Absyn_Util.mk_exp_app dt args)
in (_142_391, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_142_392))
in (FStar_Absyn_Syntax.mk_Exp_meta _142_393))
in (FStar_All.pipe_left setpos _142_394)))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(
# 590 "FStar.Parser.Desugar.fst"
let _53_1211 = (FStar_List.fold_left (fun _53_1183 pat -> (match (_53_1183) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar (a, imp); FStar_Parser_AST.prange = _53_1186}, t) -> begin
(
# 593 "FStar.Parser.Desugar.fst"
let ftvs = (let _142_397 = (free_type_vars env t)
in (FStar_List.append _142_397 ftvs))
in (let _142_399 = (let _142_398 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _142_398))
in (_142_399, ftvs)))
end
| FStar_Parser_AST.PatTvar (a, _53_1198) -> begin
(let _142_401 = (let _142_400 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _142_400))
in (_142_401, ftvs))
end
| FStar_Parser_AST.PatAscribed (_53_1202, t) -> begin
(let _142_403 = (let _142_402 = (free_type_vars env t)
in (FStar_List.append _142_402 ftvs))
in (env, _142_403))
end
| _53_1207 -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_53_1211) with
| (_53_1209, ftv) -> begin
(
# 598 "FStar.Parser.Desugar.fst"
let ftv = (sort_ftv ftv)
in (
# 599 "FStar.Parser.Desugar.fst"
let binders = (let _142_405 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar ((a, Some (FStar_Parser_AST.Implicit)))) top.FStar_Parser_AST.range))))
in (FStar_List.append _142_405 binders))
in (
# 601 "FStar.Parser.Desugar.fst"
let rec aux = (fun env bs sc_pat_opt _53_8 -> (match (_53_8) with
| [] -> begin
(
# 603 "FStar.Parser.Desugar.fst"
let body = (desugar_exp env body)
in (
# 604 "FStar.Parser.Desugar.fst"
let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(FStar_Absyn_Syntax.mk_Exp_match (sc, ((pat, None, body))::[]) None body.FStar_Absyn_Syntax.pos)
end
| None -> begin
body
end)
in (FStar_Absyn_Syntax.mk_Exp_abs' ((FStar_List.rev bs), body) None top.FStar_Parser_AST.range)))
end
| p::rest -> begin
(
# 610 "FStar.Parser.Desugar.fst"
let _53_1234 = (desugar_binding_pat env p)
in (match (_53_1234) with
| (env, b, pat) -> begin
(
# 611 "FStar.Parser.Desugar.fst"
let _53_1294 = (match (b) with
| LetBinder (_53_1236) -> begin
(FStar_All.failwith "Impossible")
end
| TBinder (a, k, aq) -> begin
(let _142_414 = (binder_of_bnd b)
in (_142_414, sc_pat_opt))
end
| VBinder (x, t, aq) -> begin
(
# 615 "FStar.Parser.Desugar.fst"
let b = (FStar_Absyn_Util.bvd_to_bvar_s x t)
in (
# 616 "FStar.Parser.Desugar.fst"
let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _53_1251) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _142_416 = (let _142_415 = (FStar_Absyn_Util.bvar_to_exp b)
in (_142_415, p))
in Some (_142_416))
end
| (Some (p), Some (sc, p')) -> begin
(match ((sc.FStar_Absyn_Syntax.n, p'.FStar_Absyn_Syntax.v)) with
| (FStar_Absyn_Syntax.Exp_bvar (_53_1265), _53_1268) -> begin
(
# 622 "FStar.Parser.Desugar.fst"
let tup = (FStar_Absyn_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (
# 623 "FStar.Parser.Desugar.fst"
let sc = (let _142_423 = (let _142_422 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _142_421 = (let _142_420 = (FStar_Absyn_Syntax.varg sc)
in (let _142_419 = (let _142_418 = (let _142_417 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _142_417))
in (_142_418)::[])
in (_142_420)::_142_419))
in (_142_422, _142_421)))
in (FStar_Absyn_Syntax.mk_Exp_app _142_423 None top.FStar_Parser_AST.range))
in (
# 624 "FStar.Parser.Desugar.fst"
let p = (let _142_424 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv tup), Some (FStar_Absyn_Syntax.Data_ctor), ((p', false))::((p, false))::[]))) None _142_424))
in Some ((sc, p)))))
end
| (FStar_Absyn_Syntax.Exp_app (_53_1274, args), FStar_Absyn_Syntax.Pat_cons (_53_1279, _53_1281, pats)) -> begin
(
# 627 "FStar.Parser.Desugar.fst"
let tup = (FStar_Absyn_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (
# 628 "FStar.Parser.Desugar.fst"
let sc = (let _142_430 = (let _142_429 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _142_428 = (let _142_427 = (let _142_426 = (let _142_425 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _142_425))
in (_142_426)::[])
in (FStar_List.append args _142_427))
in (_142_429, _142_428)))
in (FStar_Absyn_Syntax.mk_Exp_app _142_430 None top.FStar_Parser_AST.range))
in (
# 629 "FStar.Parser.Desugar.fst"
let p = (let _142_431 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv tup), Some (FStar_Absyn_Syntax.Data_ctor), (FStar_List.append pats (((p, false))::[]))))) None _142_431))
in Some ((sc, p)))))
end
| _53_1290 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((FStar_Util.Inr (b), aq), sc_pat_opt)))
end)
in (match (_53_1294) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _53_1298; FStar_Parser_AST.level = _53_1296}, arg, _53_1304) when ((FStar_Ident.lid_equals a FStar_Absyn_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Absyn_Const.assume_lid)) -> begin
(
# 640 "FStar.Parser.Desugar.fst"
let phi = (desugar_formula env arg)
in (let _142_441 = (let _142_440 = (let _142_439 = (FStar_Absyn_Util.fvar None a (FStar_Ident.range_of_lid a))
in (let _142_438 = (let _142_437 = (FStar_All.pipe_left FStar_Absyn_Syntax.targ phi)
in (let _142_436 = (let _142_435 = (let _142_434 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit None top.FStar_Parser_AST.range)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _142_434))
in (_142_435)::[])
in (_142_437)::_142_436))
in (_142_439, _142_438)))
in (FStar_Absyn_Syntax.mk_Exp_app _142_440))
in (FStar_All.pipe_left pos _142_441)))
end
| FStar_Parser_AST.App (_53_1309) -> begin
(
# 646 "FStar.Parser.Desugar.fst"
let rec aux = (fun args e -> (match ((let _142_446 = (unparen e)
in _142_446.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(
# 648 "FStar.Parser.Desugar.fst"
let arg = (let _142_447 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _142_447))
in (aux ((arg)::args) e))
end
| _53_1321 -> begin
(
# 651 "FStar.Parser.Desugar.fst"
let head = (desugar_exp env e)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_app (head, args))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _142_453 = (let _142_452 = (let _142_451 = (let _142_450 = (desugar_exp env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range), t1))::[], t2))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in (_142_450, FStar_Absyn_Syntax.Sequence))
in FStar_Absyn_Syntax.Meta_desugared (_142_451))
in (FStar_Absyn_Syntax.mk_Exp_meta _142_452))
in (FStar_All.pipe_left setpos _142_453))
end
| FStar_Parser_AST.Let (is_rec, (pat, _snd)::_tl, body) -> begin
(
# 660 "FStar.Parser.Desugar.fst"
let ds_let_rec = (fun _53_1337 -> (match (()) with
| () -> begin
(
# 661 "FStar.Parser.Desugar.fst"
let bindings = ((pat, _snd))::_tl
in (
# 662 "FStar.Parser.Desugar.fst"
let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _53_1341 -> (match (_53_1341) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _142_457 = (destruct_app_pattern env top_level p)
in (_142_457, def))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _142_458 = (destruct_app_pattern env top_level p)
in (_142_458, def))
end
| _53_1347 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _53_1352); FStar_Parser_AST.prange = _53_1349}, t) -> begin
if top_level then begin
(let _142_461 = (let _142_460 = (let _142_459 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_142_459))
in (_142_460, [], Some (t)))
in (_142_461, def))
end else begin
((FStar_Util.Inl (id), [], Some (t)), def)
end
end
| FStar_Parser_AST.PatVar (id, _53_1361) -> begin
if top_level then begin
(let _142_464 = (let _142_463 = (let _142_462 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_142_462))
in (_142_463, [], None))
in (_142_464, def))
end else begin
((FStar_Util.Inl (id), [], None), def)
end
end
| _53_1365 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected let binding", p.FStar_Parser_AST.prange))))
end)
end)
end
end))))
in (
# 678 "FStar.Parser.Desugar.fst"
let _53_1391 = (FStar_List.fold_left (fun _53_1369 _53_1378 -> (match ((_53_1369, _53_1378)) with
| ((env, fnames), ((f, _53_1372, _53_1374), _53_1377)) -> begin
(
# 680 "FStar.Parser.Desugar.fst"
let _53_1388 = (match (f) with
| FStar_Util.Inl (x) -> begin
(
# 682 "FStar.Parser.Desugar.fst"
let _53_1383 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_53_1383) with
| (env, xx) -> begin
(env, FStar_Util.Inl (xx))
end))
end
| FStar_Util.Inr (l) -> begin
(let _142_467 = (FStar_Parser_DesugarEnv.push_rec_binding env (FStar_Parser_DesugarEnv.Binding_let (l)))
in (_142_467, FStar_Util.Inr (l)))
end)
in (match (_53_1388) with
| (env, lbname) -> begin
(env, (lbname)::fnames)
end))
end)) (env, []) funs)
in (match (_53_1391) with
| (env', fnames) -> begin
(
# 687 "FStar.Parser.Desugar.fst"
let fnames = (FStar_List.rev fnames)
in (
# 688 "FStar.Parser.Desugar.fst"
let desugar_one_def = (fun env lbname _53_1402 -> (match (_53_1402) with
| ((_53_1397, args, result_t), def) -> begin
(
# 689 "FStar.Parser.Desugar.fst"
let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _142_474 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed ((def, t))) _142_474 FStar_Parser_AST.Expr))
end)
in (
# 692 "FStar.Parser.Desugar.fst"
let def = (match (args) with
| [] -> begin
def
end
| _53_1409 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.un_curry_abs args def) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
end)
in (
# 695 "FStar.Parser.Desugar.fst"
let body = (desugar_exp env def)
in (mk_lb (lbname, FStar_Absyn_Syntax.tun, body)))))
end))
in (
# 697 "FStar.Parser.Desugar.fst"
let lbs = (FStar_List.map2 (desugar_one_def (if is_rec then begin
env'
end else begin
env
end)) fnames funs)
in (
# 698 "FStar.Parser.Desugar.fst"
let body = (desugar_exp env' body)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs), body)))))))
end))))
end))
in (
# 701 "FStar.Parser.Desugar.fst"
let ds_non_rec = (fun pat t1 t2 -> (
# 702 "FStar.Parser.Desugar.fst"
let t1 = (desugar_exp env t1)
in (
# 703 "FStar.Parser.Desugar.fst"
let _53_1422 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_53_1422) with
| (env, binder, pat) -> begin
(match (binder) with
| TBinder (_53_1424) -> begin
(FStar_All.failwith "Unexpected type binder in let")
end
| LetBinder (l, t) -> begin
(
# 707 "FStar.Parser.Desugar.fst"
let body = (desugar_exp env t2)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((false, ({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = t1})::[]), body))))
end
| VBinder (x, t, _53_1434) -> begin
(
# 710 "FStar.Parser.Desugar.fst"
let body = (desugar_exp env t2)
in (
# 711 "FStar.Parser.Desugar.fst"
let body = (match (pat) with
| (None) | (Some ({FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_wild (_); FStar_Absyn_Syntax.sort = _; FStar_Absyn_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _142_486 = (let _142_485 = (FStar_Absyn_Util.bvd_to_exp x t)
in (_142_485, ((pat, None, body))::[]))
in (FStar_Absyn_Syntax.mk_Exp_match _142_486 None body.FStar_Absyn_Syntax.pos))
end)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((false, ((mk_lb (FStar_Util.Inl (x), t, t1)))::[]), body)))))
end)
end))))
in if (is_rec || (is_app_pattern pat)) then begin
(ds_let_rec ())
end else begin
(ds_non_rec pat _snd body)
end))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(let _142_499 = (let _142_498 = (let _142_497 = (desugar_exp env t1)
in (let _142_496 = (let _142_495 = (let _142_491 = (desugar_exp env t2)
in ((FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true))) None t2.FStar_Parser_AST.range), None, _142_491))
in (let _142_494 = (let _142_493 = (let _142_492 = (desugar_exp env t3)
in ((FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false))) None t3.FStar_Parser_AST.range), None, _142_492))
in (_142_493)::[])
in (_142_495)::_142_494))
in (_142_497, _142_496)))
in (FStar_Absyn_Syntax.mk_Exp_match _142_498))
in (FStar_All.pipe_left pos _142_499))
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(
# 728 "FStar.Parser.Desugar.fst"
let r = top.FStar_Parser_AST.range
in (
# 729 "FStar.Parser.Desugar.fst"
let handler = (FStar_Parser_AST.mk_function branches r r)
in (
# 730 "FStar.Parser.Desugar.fst"
let body = (FStar_Parser_AST.mk_function ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatConst (FStar_Const.Const_unit)) r), None, e))::[]) r r)
in (
# 731 "FStar.Parser.Desugar.fst"
let a1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (FStar_Absyn_Const.try_with_lid)) r top.FStar_Parser_AST.level), body, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (
# 732 "FStar.Parser.Desugar.fst"
let a2 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((a1, handler, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (desugar_exp env a2))))))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(
# 736 "FStar.Parser.Desugar.fst"
let desugar_branch = (fun _53_1473 -> (match (_53_1473) with
| (pat, wopt, b) -> begin
(
# 737 "FStar.Parser.Desugar.fst"
let _53_1476 = (desugar_match_pat env pat)
in (match (_53_1476) with
| (env, pat) -> begin
(
# 738 "FStar.Parser.Desugar.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _142_502 = (desugar_exp env e)
in Some (_142_502))
end)
in (
# 741 "FStar.Parser.Desugar.fst"
let b = (desugar_exp env b)
in (pat, wopt, b)))
end))
end))
in (let _142_508 = (let _142_507 = (let _142_506 = (desugar_exp env e)
in (let _142_505 = (FStar_List.map desugar_branch branches)
in (_142_506, _142_505)))
in (FStar_Absyn_Syntax.mk_Exp_match _142_507))
in (FStar_All.pipe_left pos _142_508)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _142_514 = (let _142_513 = (let _142_512 = (desugar_exp env e)
in (let _142_511 = (desugar_typ env t)
in (_142_512, _142_511, None)))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _142_513))
in (FStar_All.pipe_left pos _142_514))
end
| FStar_Parser_AST.Record (_53_1487, []) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected empty record", top.FStar_Parser_AST.range))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(
# 752 "FStar.Parser.Desugar.fst"
let _53_1498 = (FStar_List.hd fields)
in (match (_53_1498) with
| (f, _53_1497) -> begin
(
# 753 "FStar.Parser.Desugar.fst"
let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (
# 754 "FStar.Parser.Desugar.fst"
let _53_1504 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_53_1504) with
| (record, _53_1503) -> begin
(
# 755 "FStar.Parser.Desugar.fst"
let get_field = (fun xopt f -> (
# 756 "FStar.Parser.Desugar.fst"
let fn = f.FStar_Ident.ident
in (
# 757 "FStar.Parser.Desugar.fst"
let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _53_1512 -> (match (_53_1512) with
| (g, _53_1511) -> begin
(
# 758 "FStar.Parser.Desugar.fst"
let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_53_1516, e) -> begin
(let _142_522 = (qfn fn)
in (_142_522, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _142_525 = (let _142_524 = (let _142_523 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in (_142_523, top.FStar_Parser_AST.range))
in FStar_Absyn_Syntax.Error (_142_524))
in (Prims.raise _142_525))
end
| Some (x) -> begin
(let _142_526 = (qfn fn)
in (_142_526, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Project ((x, f))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end))))
in (
# 768 "FStar.Parser.Desugar.fst"
let recterm = (match (eopt) with
| None -> begin
(let _142_531 = (let _142_530 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _53_1528 -> (match (_53_1528) with
| (f, _53_1527) -> begin
(let _142_529 = (let _142_528 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _142_528))
in (_142_529, FStar_Parser_AST.Nothing))
end))))
in (record.FStar_Parser_DesugarEnv.constrname, _142_530))
in FStar_Parser_AST.Construct (_142_531))
end
| Some (e) -> begin
(
# 775 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.genident (Some (e.FStar_Parser_AST.range)))
in (
# 776 "FStar.Parser.Desugar.fst"
let xterm = (let _142_533 = (let _142_532 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_142_532))
in (FStar_Parser_AST.mk_term _142_533 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (
# 777 "FStar.Parser.Desugar.fst"
let record = (let _142_536 = (let _142_535 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _53_1536 -> (match (_53_1536) with
| (f, _53_1535) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _142_535))
in FStar_Parser_AST.Record (_142_536))
in FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar ((x, None))) x.FStar_Ident.idRange), e))::[], (FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level))))))
end)
in (
# 780 "FStar.Parser.Desugar.fst"
let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (
# 781 "FStar.Parser.Desugar.fst"
let e = (desugar_exp env recterm)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _53_1559); FStar_Absyn_Syntax.tk = _53_1556; FStar_Absyn_Syntax.pos = _53_1554; FStar_Absyn_Syntax.fvs = _53_1552; FStar_Absyn_Syntax.uvs = _53_1550}, args); FStar_Absyn_Syntax.tk = _53_1548; FStar_Absyn_Syntax.pos = _53_1546; FStar_Absyn_Syntax.fvs = _53_1544; FStar_Absyn_Syntax.uvs = _53_1542}, FStar_Absyn_Syntax.Data_app)) -> begin
(
# 784 "FStar.Parser.Desugar.fst"
let e = (let _142_546 = (let _142_545 = (let _142_544 = (let _142_543 = (let _142_542 = (let _142_541 = (let _142_540 = (let _142_539 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_DesugarEnv.typename, _142_539))
in FStar_Absyn_Syntax.Record_ctor (_142_540))
in Some (_142_541))
in (fv, _142_542))
in (FStar_Absyn_Syntax.mk_Exp_fvar _142_543 None e.FStar_Absyn_Syntax.pos))
in (_142_544, args))
in (FStar_Absyn_Syntax.mk_Exp_app _142_545))
in (FStar_All.pipe_left pos _142_546))
in (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e, FStar_Absyn_Syntax.Data_app)))))
end
| _53_1573 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(
# 792 "FStar.Parser.Desugar.fst"
let _53_1580 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_projector_by_field_name env) f)
in (match (_53_1580) with
| (fieldname, is_rec) -> begin
(
# 793 "FStar.Parser.Desugar.fst"
let e = (desugar_exp env e)
in (
# 794 "FStar.Parser.Desugar.fst"
let fn = (
# 795 "FStar.Parser.Desugar.fst"
let _53_1585 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_53_1585) with
| (ns, _53_1584) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (
# 797 "FStar.Parser.Desugar.fst"
let qual = if is_rec then begin
Some (FStar_Absyn_Syntax.Record_projector (fn))
end else begin
None
end
in (let _142_553 = (let _142_552 = (let _142_551 = (FStar_Absyn_Util.fvar qual fieldname (FStar_Ident.range_of_lid f))
in (let _142_550 = (let _142_549 = (FStar_Absyn_Syntax.varg e)
in (_142_549)::[])
in (_142_551, _142_550)))
in (FStar_Absyn_Syntax.mk_Exp_app _142_552))
in (FStar_All.pipe_left pos _142_553)))))
end))
end
| FStar_Parser_AST.Paren (e) -> begin
(desugar_exp env e)
end
| _53_1591 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_typ : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env top -> (
# 808 "FStar.Parser.Desugar.fst"
let wpos = (fun t -> (t None top.FStar_Parser_AST.range))
in (
# 809 "FStar.Parser.Desugar.fst"
let setpos = (fun t -> (
# 809 "FStar.Parser.Desugar.fst"
let _53_1598 = t
in {FStar_Absyn_Syntax.n = _53_1598.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _53_1598.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _53_1598.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _53_1598.FStar_Absyn_Syntax.uvs}))
in (
# 810 "FStar.Parser.Desugar.fst"
let top = (unparen top)
in (
# 811 "FStar.Parser.Desugar.fst"
let head_and_args = (fun t -> (
# 812 "FStar.Parser.Desugar.fst"
let rec aux = (fun args t -> (match ((let _142_576 = (unparen t)
in _142_576.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _53_1616 -> begin
(t, args)
end))
in (aux [] t)))
in (match (top.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Absyn_Syntax.tun)
end
| FStar_Parser_AST.Requires (t, lopt) -> begin
(
# 821 "FStar.Parser.Desugar.fst"
let t = (label_conjuncts "pre-condition" true lopt t)
in if (is_type env t) then begin
(desugar_typ env t)
end else begin
(let _142_577 = (desugar_exp env t)
in (FStar_All.pipe_right _142_577 FStar_Absyn_Util.b2t))
end)
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(
# 827 "FStar.Parser.Desugar.fst"
let t = (label_conjuncts "post-condition" false lopt t)
in if (is_type env t) then begin
(desugar_typ env t)
end else begin
(let _142_578 = (desugar_exp env t)
in (FStar_All.pipe_right _142_578 FStar_Absyn_Util.b2t))
end)
end
| FStar_Parser_AST.Op ("*", t1::_53_1630::[]) -> begin
if (is_type env t1) then begin
(
# 833 "FStar.Parser.Desugar.fst"
let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", t1::t2::[]) -> begin
(
# 835 "FStar.Parser.Desugar.fst"
let rest = (flatten t2)
in (t1)::rest)
end
| _53_1645 -> begin
(t)::[]
end))
in (
# 838 "FStar.Parser.Desugar.fst"
let targs = (let _142_583 = (flatten top)
in (FStar_All.pipe_right _142_583 (FStar_List.map (fun t -> (let _142_582 = (desugar_typ env t)
in (FStar_Absyn_Syntax.targ _142_582))))))
in (
# 839 "FStar.Parser.Desugar.fst"
let tup = (let _142_584 = (FStar_Absyn_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _142_584))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))))
end else begin
(let _142_590 = (let _142_589 = (let _142_588 = (let _142_587 = (FStar_Parser_AST.term_to_string t1)
in (FStar_Util.format1 "The operator \"*\" is resolved here as multiplication since \"%s\" is a term, although a type was expected" _142_587))
in (_142_588, top.FStar_Parser_AST.range))
in FStar_Absyn_Syntax.Error (_142_589))
in (Prims.raise _142_590))
end
end
| FStar_Parser_AST.Op ("=!=", args) -> begin
(desugar_typ env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Op (("~", ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Op (("==", args))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))::[]))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_tylid env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(let _142_591 = (desugar_exp env top)
in (FStar_All.pipe_right _142_591 FStar_Absyn_Util.b2t))
end
| Some (l) -> begin
(
# 850 "FStar.Parser.Desugar.fst"
let args = (FStar_List.map (fun t -> (let _142_593 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _142_593))) args)
in (let _142_594 = (FStar_Absyn_Util.ftv l FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _142_594 args)))
end)
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _142_595 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) a)
in (FStar_All.pipe_left setpos _142_595))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) when ((FStar_List.length l.FStar_Ident.ns) = 0) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env l.FStar_Ident.ident)) with
| Some (t) -> begin
(setpos t)
end
| None -> begin
(let _142_596 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _142_596))
end)
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(
# 866 "FStar.Parser.Desugar.fst"
let l = (FStar_Absyn_Util.set_lid_range l top.FStar_Parser_AST.range)
in (let _142_597 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _142_597)))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(
# 870 "FStar.Parser.Desugar.fst"
let t = (let _142_598 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _142_598))
in (
# 871 "FStar.Parser.Desugar.fst"
let args = (FStar_List.map (fun _53_1681 -> (match (_53_1681) with
| (t, imp) -> begin
(let _142_600 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _142_600))
end)) args)
in (FStar_Absyn_Util.mk_typ_app t args)))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(
# 875 "FStar.Parser.Desugar.fst"
let rec aux = (fun env bs _53_9 -> (match (_53_9) with
| [] -> begin
(
# 877 "FStar.Parser.Desugar.fst"
let body = (desugar_typ env body)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_lam ((FStar_List.rev bs), body))))
end
| hd::tl -> begin
(
# 880 "FStar.Parser.Desugar.fst"
let _53_1699 = (desugar_binding_pat env hd)
in (match (_53_1699) with
| (env, bnd, pat) -> begin
(match (pat) with
| Some (q) -> begin
(let _142_612 = (let _142_611 = (let _142_610 = (let _142_609 = (FStar_Absyn_Print.pat_to_string q)
in (FStar_Util.format1 "Pattern matching at the type level is not supported; got %s\n" _142_609))
in (_142_610, hd.FStar_Parser_AST.prange))
in FStar_Absyn_Syntax.Error (_142_611))
in (Prims.raise _142_612))
end
| None -> begin
(
# 884 "FStar.Parser.Desugar.fst"
let b = (binder_of_bnd bnd)
in (aux env ((b)::bs) tl))
end)
end))
end))
in (aux env [] binders))
end
| FStar_Parser_AST.App (_53_1705) -> begin
(
# 889 "FStar.Parser.Desugar.fst"
let rec aux = (fun args e -> (match ((let _142_617 = (unparen e)
in _142_617.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, arg, imp) -> begin
(
# 891 "FStar.Parser.Desugar.fst"
let arg = (let _142_618 = (desugar_typ_or_exp env arg)
in (FStar_All.pipe_left (arg_withimp_t imp) _142_618))
in (aux ((arg)::args) e))
end
| _53_1717 -> begin
(
# 894 "FStar.Parser.Desugar.fst"
let head = (desugar_typ env e)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app (head, args))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Product ([], t) -> begin
(FStar_All.failwith "Impossible: product with no binders")
end
| FStar_Parser_AST.Product (binders, t) -> begin
(
# 902 "FStar.Parser.Desugar.fst"
let _53_1729 = (uncurry binders t)
in (match (_53_1729) with
| (bs, t) -> begin
(
# 903 "FStar.Parser.Desugar.fst"
let rec aux = (fun env bs _53_10 -> (match (_53_10) with
| [] -> begin
(
# 905 "FStar.Parser.Desugar.fst"
let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_fun ((FStar_List.rev bs), cod))))
end
| hd::tl -> begin
(
# 908 "FStar.Parser.Desugar.fst"
let mlenv = (FStar_Parser_DesugarEnv.default_ml env)
in (
# 909 "FStar.Parser.Desugar.fst"
let bb = (desugar_binder mlenv hd)
in (
# 910 "FStar.Parser.Desugar.fst"
let _53_1743 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_53_1743) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_exp_binder env b)) with
| (None, _53_1750) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(
# 918 "FStar.Parser.Desugar.fst"
let _53_1764 = (match ((as_binder env None (FStar_Util.Inr (b)))) with
| ((FStar_Util.Inr (x), _53_1756), env) -> begin
(x, env)
end
| _53_1761 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_53_1764) with
| (b, env) -> begin
(
# 921 "FStar.Parser.Desugar.fst"
let f = if (is_type env f) then begin
(desugar_formula env f)
end else begin
(let _142_629 = (desugar_exp env f)
in (FStar_All.pipe_right _142_629 FStar_Absyn_Util.b2t))
end
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_refine (b, f))))
end))
end)
end
| (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) -> begin
(desugar_typ env t)
end
| FStar_Parser_AST.Ascribed (t, k) -> begin
(let _142_637 = (let _142_636 = (let _142_635 = (desugar_typ env t)
in (let _142_634 = (desugar_kind env k)
in (_142_635, _142_634)))
in (FStar_Absyn_Syntax.mk_Typ_ascribed' _142_636))
in (FStar_All.pipe_left wpos _142_637))
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(
# 933 "FStar.Parser.Desugar.fst"
let _53_1798 = (FStar_List.fold_left (fun _53_1783 b -> (match (_53_1783) with
| (env, tparams, typs) -> begin
(
# 934 "FStar.Parser.Desugar.fst"
let _53_1787 = (desugar_exp_binder env b)
in (match (_53_1787) with
| (xopt, t) -> begin
(
# 935 "FStar.Parser.Desugar.fst"
let _53_1793 = (match (xopt) with
| None -> begin
(let _142_640 = (FStar_Absyn_Util.new_bvd (Some (top.FStar_Parser_AST.range)))
in (env, _142_640))
end
| Some (x) -> begin
(FStar_Parser_DesugarEnv.push_local_vbinding env x)
end)
in (match (_53_1793) with
| (env, x) -> begin
(let _142_644 = (let _142_643 = (let _142_642 = (let _142_641 = (FStar_Absyn_Util.close_with_lam tparams t)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _142_641))
in (_142_642)::[])
in (FStar_List.append typs _142_643))
in (env, (FStar_List.append tparams (((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), None))::[])), _142_644))
end))
end))
end)) (env, [], []) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_53_1798) with
| (env, _53_1796, targs) -> begin
(
# 940 "FStar.Parser.Desugar.fst"
let tup = (let _142_645 = (FStar_Absyn_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _142_645))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))
end))
end
| FStar_Parser_AST.Record (_53_1801) -> begin
(FStar_All.failwith "Unexpected record type")
end
| FStar_Parser_AST.Let (false, (x, v)::[], t) -> begin
(
# 947 "FStar.Parser.Desugar.fst"
let let_v = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.let_in_typ)) top.FStar_Parser_AST.range top.FStar_Parser_AST.level), v, FStar_Parser_AST.Nothing))) v.FStar_Parser_AST.range v.FStar_Parser_AST.level)
in (
# 948 "FStar.Parser.Desugar.fst"
let t' = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((let_v, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs (((x)::[], t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level), FStar_Parser_AST.Nothing))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (desugar_typ env t')))
end
| (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Labeled (_)) -> begin
(desugar_formula env top)
end
| _53_1820 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _53_1822 -> begin
(FStar_Parser_AST.error "Expected a type" top top.FStar_Parser_AST.range)
end))))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.comp = (fun r default_ok env t -> (
# 958 "FStar.Parser.Desugar.fst"
let fail = (fun msg -> (Prims.raise (FStar_Absyn_Syntax.Error ((msg, r)))))
in (
# 959 "FStar.Parser.Desugar.fst"
let pre_process_comp_typ = (fun t -> (
# 960 "FStar.Parser.Desugar.fst"
let _53_1833 = (head_and_args t)
in (match (_53_1833) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(
# 963 "FStar.Parser.Desugar.fst"
let unit = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (
# 964 "FStar.Parser.Desugar.fst"
let nil_pat = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr), FStar_Parser_AST.Nothing)
in (
# 965 "FStar.Parser.Desugar.fst"
let _53_1859 = (FStar_All.pipe_right args (FStar_List.partition (fun _53_1841 -> (match (_53_1841) with
| (arg, _53_1840) -> begin
(match ((let _142_657 = (unparen arg)
in _142_657.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _53_1845; FStar_Parser_AST.level = _53_1843}, _53_1850, _53_1852) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = "decreases")
end
| _53_1856 -> begin
false
end)
end))))
in (match (_53_1859) with
| (decreases_clause, args) -> begin
(
# 969 "FStar.Parser.Desugar.fst"
let args = (match (args) with
| [] -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Not enough arguments to \'Lemma\'", t.FStar_Parser_AST.range))))
end
| ens::[] -> begin
(
# 972 "FStar.Parser.Desugar.fst"
let req_true = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Requires (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.true_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Formula), None))) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (unit)::(req_true)::(ens)::(nil_pat)::[])
end
| req::ens::[] -> begin
(unit)::(req)::(ens)::(nil_pat)::[]
end
| more -> begin
(unit)::more
end)
in (
# 976 "FStar.Parser.Desugar.fst"
let t = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct ((lemma, (FStar_List.append args decreases_clause)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in (desugar_typ env t)))
end))))
end
| FStar_Parser_AST.Name (tot) when (((tot.FStar_Ident.ident.FStar_Ident.idText = "Tot") && (not ((FStar_Parser_DesugarEnv.is_effect_name env FStar_Absyn_Const.effect_Tot_lid)))) && (let _142_658 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Ident.lid_equals _142_658 FStar_Absyn_Const.prims_lid))) -> begin
(
# 983 "FStar.Parser.Desugar.fst"
let args = (FStar_List.map (fun _53_1874 -> (match (_53_1874) with
| (t, imp) -> begin
(let _142_660 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _142_660))
end)) args)
in (let _142_661 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.effect_Tot_lid FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _142_661 args)))
end
| _53_1877 -> begin
(desugar_typ env t)
end)
end)))
in (
# 988 "FStar.Parser.Desugar.fst"
let t = (pre_process_comp_typ t)
in (
# 989 "FStar.Parser.Desugar.fst"
let _53_1881 = (FStar_Absyn_Util.head_and_args t)
in (match (_53_1881) with
| (head, args) -> begin
(match ((let _142_663 = (let _142_662 = (FStar_Absyn_Util.compress_typ head)
in _142_662.FStar_Absyn_Syntax.n)
in (_142_663, args))) with
| (FStar_Absyn_Syntax.Typ_const (eff), (FStar_Util.Inl (result_typ), _53_1888)::rest) -> begin
(
# 992 "FStar.Parser.Desugar.fst"
let _53_1928 = (FStar_All.pipe_right rest (FStar_List.partition (fun _53_11 -> (match (_53_11) with
| (FStar_Util.Inr (_53_1894), _53_1897) -> begin
false
end
| (FStar_Util.Inl (t), _53_1902) -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (fv); FStar_Absyn_Syntax.tk = _53_1911; FStar_Absyn_Syntax.pos = _53_1909; FStar_Absyn_Syntax.fvs = _53_1907; FStar_Absyn_Syntax.uvs = _53_1905}, (FStar_Util.Inr (_53_1916), _53_1919)::[]) -> begin
(FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.decreases_lid)
end
| _53_1925 -> begin
false
end)
end))))
in (match (_53_1928) with
| (dec, rest) -> begin
(
# 1000 "FStar.Parser.Desugar.fst"
let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _53_12 -> (match (_53_12) with
| (FStar_Util.Inl (t), _53_1933) -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (_53_1936, (FStar_Util.Inr (arg), _53_1940)::[]) -> begin
FStar_Absyn_Syntax.DECREASES (arg)
end
| _53_1946 -> begin
(FStar_All.failwith "impos")
end)
end
| _53_1948 -> begin
(FStar_All.failwith "impos")
end))))
in if ((FStar_Parser_DesugarEnv.is_effect_name env eff.FStar_Absyn_Syntax.v) || (FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Tot_lid)) then begin
if ((FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Tot_lid) && ((FStar_List.length decreases_clause) = 0)) then begin
(FStar_Absyn_Syntax.mk_Total result_typ)
end else begin
(
# 1011 "FStar.Parser.Desugar.fst"
let flags = if (FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Lemma_lid) then begin
(FStar_Absyn_Syntax.LEMMA)::[]
end else begin
if (FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Tot_lid) then begin
(FStar_Absyn_Syntax.TOTAL)::[]
end else begin
if (FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_ML_lid) then begin
(FStar_Absyn_Syntax.MLEFFECT)::[]
end else begin
[]
end
end
end
in (
# 1016 "FStar.Parser.Desugar.fst"
let rest = if (FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Lemma_lid) then begin
(match (rest) with
| req::ens::(FStar_Util.Inr (pat), aq)::[] -> begin
(let _142_670 = (let _142_669 = (let _142_668 = (let _142_667 = (let _142_666 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((pat, FStar_Absyn_Syntax.Meta_smt_pat))))
in FStar_Util.Inr (_142_666))
in (_142_667, aq))
in (_142_668)::[])
in (ens)::_142_669)
in (req)::_142_670)
end
| _53_1959 -> begin
rest
end)
end else begin
rest
end
in (FStar_Absyn_Syntax.mk_Comp {FStar_Absyn_Syntax.effect_name = eff.FStar_Absyn_Syntax.v; FStar_Absyn_Syntax.result_typ = result_typ; FStar_Absyn_Syntax.effect_args = rest; FStar_Absyn_Syntax.flags = (FStar_List.append flags decreases_clause)})))
end
end else begin
if default_ok then begin
(env.FStar_Parser_DesugarEnv.default_result_effect t r)
end else begin
(let _142_672 = (let _142_671 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _142_671))
in (fail _142_672))
end
end)
end))
end
| _53_1962 -> begin
if default_ok then begin
(env.FStar_Parser_DesugarEnv.default_result_effect t r)
end else begin
(let _142_674 = (let _142_673 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _142_673))
in (fail _142_674))
end
end)
end))))))
and desugar_kind : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.knd = (fun env k -> (
# 1035 "FStar.Parser.Desugar.fst"
let pos = (fun f -> (f k.FStar_Parser_AST.range))
in (
# 1036 "FStar.Parser.Desugar.fst"
let setpos = (fun kk -> (
# 1036 "FStar.Parser.Desugar.fst"
let _53_1969 = kk
in {FStar_Absyn_Syntax.n = _53_1969.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _53_1969.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = k.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _53_1969.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _53_1969.FStar_Absyn_Syntax.uvs}))
in (
# 1037 "FStar.Parser.Desugar.fst"
let k = (unparen k)
in (match (k.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name ({FStar_Ident.ns = _53_1978; FStar_Ident.ident = _53_1976; FStar_Ident.nsstr = _53_1974; FStar_Ident.str = "Type"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_type)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _53_1987; FStar_Ident.ident = _53_1985; FStar_Ident.nsstr = _53_1983; FStar_Ident.str = "Effect"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_effect)
end
| FStar_Parser_AST.Name (l) -> begin
(match ((let _142_686 = (FStar_Parser_DesugarEnv.qualify_lid env l)
in (FStar_Parser_DesugarEnv.find_kind_abbrev env _142_686))) with
| Some (l) -> begin
(FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, []), FStar_Absyn_Syntax.mk_Kind_unknown)))
end
| _53_1995 -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end)
end
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Absyn_Syntax.kun)
end
| FStar_Parser_AST.Product (bs, k) -> begin
(
# 1048 "FStar.Parser.Desugar.fst"
let _53_2003 = (uncurry bs k)
in (match (_53_2003) with
| (bs, k) -> begin
(
# 1049 "FStar.Parser.Desugar.fst"
let rec aux = (fun env bs _53_13 -> (match (_53_13) with
| [] -> begin
(let _142_697 = (let _142_696 = (let _142_695 = (desugar_kind env k)
in ((FStar_List.rev bs), _142_695))
in (FStar_Absyn_Syntax.mk_Kind_arrow _142_696))
in (FStar_All.pipe_left pos _142_697))
end
| hd::tl -> begin
(
# 1053 "FStar.Parser.Desugar.fst"
let _53_2014 = (let _142_699 = (let _142_698 = (FStar_Parser_DesugarEnv.default_ml env)
in (desugar_binder _142_698 hd))
in (FStar_All.pipe_right _142_699 (as_binder env hd.FStar_Parser_AST.aqual)))
in (match (_53_2014) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(match ((FStar_Parser_DesugarEnv.find_kind_abbrev env l)) with
| None -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end
| Some (l) -> begin
(
# 1061 "FStar.Parser.Desugar.fst"
let args = (FStar_List.map (fun _53_2024 -> (match (_53_2024) with
| (t, b) -> begin
(
# 1062 "FStar.Parser.Desugar.fst"
let qual = if (b = FStar_Parser_AST.Hash) then begin
Some (imp_tag)
end else begin
None
end
in (let _142_701 = (desugar_typ_or_exp env t)
in (_142_701, qual)))
end)) args)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), FStar_Absyn_Syntax.mk_Kind_unknown))))
end)
end
| _53_2028 -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end)))))
and desugar_formula' : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env f -> (
# 1069 "FStar.Parser.Desugar.fst"
let connective = (fun s -> (match (s) with
| "/\\" -> begin
Some (FStar_Absyn_Const.and_lid)
end
| "\\/" -> begin
Some (FStar_Absyn_Const.or_lid)
end
| "==>" -> begin
Some (FStar_Absyn_Const.imp_lid)
end
| "<==>" -> begin
Some (FStar_Absyn_Const.iff_lid)
end
| "~" -> begin
Some (FStar_Absyn_Const.not_lid)
end
| _53_2039 -> begin
None
end))
in (
# 1076 "FStar.Parser.Desugar.fst"
let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (
# 1077 "FStar.Parser.Desugar.fst"
let setpos = (fun t -> (
# 1077 "FStar.Parser.Desugar.fst"
let _53_2044 = t
in {FStar_Absyn_Syntax.n = _53_2044.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _53_2044.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = f.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _53_2044.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _53_2044.FStar_Absyn_Syntax.uvs}))
in (
# 1078 "FStar.Parser.Desugar.fst"
let desugar_quant = (fun q qt b pats body -> (
# 1079 "FStar.Parser.Desugar.fst"
let tk = (desugar_binder env (
# 1079 "FStar.Parser.Desugar.fst"
let _53_2052 = b
in {FStar_Parser_AST.b = _53_2052.FStar_Parser_AST.b; FStar_Parser_AST.brange = _53_2052.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _53_2052.FStar_Parser_AST.aqual}))
in (
# 1080 "FStar.Parser.Desugar.fst"
let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _142_737 = (desugar_typ_or_exp env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _142_737)))))) pats))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(
# 1083 "FStar.Parser.Desugar.fst"
let _53_2067 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_53_2067) with
| (env, a) -> begin
(
# 1084 "FStar.Parser.Desugar.fst"
let pats = (desugar_pats env pats)
in (
# 1085 "FStar.Parser.Desugar.fst"
let body = (desugar_formula env body)
in (
# 1086 "FStar.Parser.Desugar.fst"
let body = (match (pats) with
| [] -> begin
body
end
| _53_2072 -> begin
(let _142_738 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
in (FStar_All.pipe_left setpos _142_738))
end)
in (
# 1089 "FStar.Parser.Desugar.fst"
let body = (let _142_744 = (let _142_743 = (let _142_742 = (let _142_741 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_142_741)::[])
in (_142_742, body))
in (FStar_Absyn_Syntax.mk_Typ_lam _142_743))
in (FStar_All.pipe_left pos _142_744))
in (let _142_749 = (let _142_748 = (let _142_745 = (FStar_Ident.set_lid_range qt b.FStar_Parser_AST.brange)
in (FStar_Absyn_Util.ftv _142_745 FStar_Absyn_Syntax.kun))
in (let _142_747 = (let _142_746 = (FStar_Absyn_Syntax.targ body)
in (_142_746)::[])
in (FStar_Absyn_Util.mk_typ_app _142_748 _142_747)))
in (FStar_All.pipe_left setpos _142_749))))))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(
# 1093 "FStar.Parser.Desugar.fst"
let _53_2082 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_53_2082) with
| (env, x) -> begin
(
# 1094 "FStar.Parser.Desugar.fst"
let pats = (desugar_pats env pats)
in (
# 1095 "FStar.Parser.Desugar.fst"
let body = (desugar_formula env body)
in (
# 1096 "FStar.Parser.Desugar.fst"
let body = (match (pats) with
| [] -> begin
body
end
| _53_2087 -> begin
(FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
end)
in (
# 1099 "FStar.Parser.Desugar.fst"
let body = (let _142_755 = (let _142_754 = (let _142_753 = (let _142_752 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_142_752)::[])
in (_142_753, body))
in (FStar_Absyn_Syntax.mk_Typ_lam _142_754))
in (FStar_All.pipe_left pos _142_755))
in (let _142_760 = (let _142_759 = (let _142_756 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Absyn_Util.ftv _142_756 FStar_Absyn_Syntax.kun))
in (let _142_758 = (let _142_757 = (FStar_Absyn_Syntax.targ body)
in (_142_757)::[])
in (FStar_Absyn_Util.mk_typ_app _142_759 _142_758)))
in (FStar_All.pipe_left setpos _142_760))))))
end))
end
| _53_2091 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1104 "FStar.Parser.Desugar.fst"
let push_quant = (fun q binders pats body -> (match (binders) with
| b::b'::_rest -> begin
(
# 1106 "FStar.Parser.Desugar.fst"
let rest = (b')::_rest
in (
# 1107 "FStar.Parser.Desugar.fst"
let body = (let _142_775 = (q (rest, pats, body))
in (let _142_774 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _142_775 _142_774 FStar_Parser_AST.Formula)))
in (let _142_776 = (q ((b)::[], [], body))
in (FStar_Parser_AST.mk_term _142_776 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _53_2105 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _142_777 = (unparen f)
in _142_777.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(
# 1113 "FStar.Parser.Desugar.fst"
let f = (desugar_formula env f)
in (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled ((f, l, FStar_Absyn_Syntax.dummyRange, p)))))
end
| FStar_Parser_AST.Op ("==", hd::_args) -> begin
(
# 1117 "FStar.Parser.Desugar.fst"
let args = (hd)::_args
in (
# 1118 "FStar.Parser.Desugar.fst"
let args = (FStar_List.map (fun t -> (let _142_779 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _142_779))) args)
in (
# 1119 "FStar.Parser.Desugar.fst"
let eq = if (is_type env hd) then begin
(let _142_780 = (FStar_Ident.set_lid_range FStar_Absyn_Const.eqT_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _142_780 FStar_Absyn_Syntax.kun))
end else begin
(let _142_781 = (FStar_Ident.set_lid_range FStar_Absyn_Const.eq2_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _142_781 FStar_Absyn_Syntax.kun))
end
in (FStar_Absyn_Util.mk_typ_app eq args))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match (((connective s), args)) with
| (Some (conn), _53_2131::_53_2129::[]) -> begin
(let _142_786 = (let _142_782 = (FStar_Ident.set_lid_range conn f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _142_782 FStar_Absyn_Syntax.kun))
in (let _142_785 = (FStar_List.map (fun x -> (let _142_784 = (desugar_formula env x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _142_784))) args)
in (FStar_Absyn_Util.mk_typ_app _142_786 _142_785)))
end
| _53_2136 -> begin
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(let _142_787 = (desugar_exp env f)
in (FStar_All.pipe_right _142_787 FStar_Absyn_Util.b2t))
end
end)
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _142_792 = (let _142_788 = (FStar_Ident.set_lid_range FStar_Absyn_Const.ite_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _142_788 FStar_Absyn_Syntax.kun))
in (let _142_791 = (FStar_List.map (fun x -> (match ((desugar_typ_or_exp env x)) with
| FStar_Util.Inl (t) -> begin
(FStar_Absyn_Syntax.targ t)
end
| FStar_Util.Inr (v) -> begin
(let _142_790 = (FStar_Absyn_Util.b2t v)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _142_790))
end)) ((f1)::(f2)::(f3)::[]))
in (FStar_Absyn_Util.mk_typ_app _142_792 _142_791)))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall (_1::_2::_3, pats, body) -> begin
(
# 1147 "FStar.Parser.Desugar.fst"
let binders = (_1)::(_2)::_3
in (let _142_794 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _142_794)))
end
| FStar_Parser_AST.QExists (_1::_2::_3, pats, body) -> begin
(
# 1151 "FStar.Parser.Desugar.fst"
let binders = (_1)::(_2)::_3
in (let _142_796 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _142_796)))
end
| FStar_Parser_AST.QForall (b::[], pats, body) -> begin
(desugar_quant FStar_Absyn_Const.forall_lid FStar_Absyn_Const.allTyp_lid b pats body)
end
| FStar_Parser_AST.QExists (b::[], pats, body) -> begin
(desugar_quant FStar_Absyn_Const.exists_lid FStar_Absyn_Const.allTyp_lid b pats body)
end
| FStar_Parser_AST.Paren (f) -> begin
(desugar_formula env f)
end
| _53_2198 -> begin
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(let _142_797 = (desugar_exp env f)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _142_797))
end
end)))))))
and desugar_formula : env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env t -> (desugar_formula' (
# 1168 "FStar.Parser.Desugar.fst"
let _53_2201 = env
in {FStar_Parser_DesugarEnv.curmodule = _53_2201.FStar_Parser_DesugarEnv.curmodule; FStar_Parser_DesugarEnv.modules = _53_2201.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _53_2201.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.modul_abbrevs = _53_2201.FStar_Parser_DesugarEnv.modul_abbrevs; FStar_Parser_DesugarEnv.sigaccum = _53_2201.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _53_2201.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _53_2201.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = FStar_Parser_AST.Formula; FStar_Parser_DesugarEnv.sigmap = _53_2201.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _53_2201.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _53_2201.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _53_2201.FStar_Parser_DesugarEnv.admitted_iface}) t))
and desugar_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  ((FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd), (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ)) FStar_Util.either = (fun env b -> if (is_type_binder env b) then begin
(let _142_802 = (desugar_type_binder env b)
in FStar_Util.Inl (_142_802))
end else begin
(let _142_803 = (desugar_exp_binder env b)
in FStar_Util.Inr (_142_803))
end)
and typars_of_binders : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_DesugarEnv.env * ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (
# 1176 "FStar.Parser.Desugar.fst"
let _53_2234 = (FStar_List.fold_left (fun _53_2209 b -> (match (_53_2209) with
| (env, out) -> begin
(
# 1177 "FStar.Parser.Desugar.fst"
let tk = (desugar_binder env (
# 1177 "FStar.Parser.Desugar.fst"
let _53_2211 = b
in {FStar_Parser_AST.b = _53_2211.FStar_Parser_AST.b; FStar_Parser_AST.brange = _53_2211.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _53_2211.FStar_Parser_AST.aqual}))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(
# 1180 "FStar.Parser.Desugar.fst"
let _53_2221 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_53_2221) with
| (env, a) -> begin
(env, ((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k)), (trans_aqual b.FStar_Parser_AST.aqual)))::out)
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(
# 1183 "FStar.Parser.Desugar.fst"
let _53_2229 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_53_2229) with
| (env, x) -> begin
(env, ((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), (trans_aqual b.FStar_Parser_AST.aqual)))::out)
end))
end
| _53_2231 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected binder", b.FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_53_2234) with
| (env, tpars) -> begin
(env, (FStar_List.rev tpars))
end)))
and desugar_exp_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (x, t) -> begin
(let _142_810 = (desugar_typ env t)
in (Some (x), _142_810))
end
| FStar_Parser_AST.TVariable (t) -> begin
(let _142_811 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) t)
in (None, _142_811))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _142_812 = (desugar_typ env t)
in (None, _142_812))
end
| FStar_Parser_AST.Variable (x) -> begin
(Some (x), FStar_Absyn_Syntax.tun)
end
| _53_2248 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a type)", b.FStar_Parser_AST.brange))))
end))
and desugar_type_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd) = (fun env b -> (
# 1196 "FStar.Parser.Desugar.fst"
let fail = (fun _53_2252 -> (match (()) with
| () -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a kind)", b.FStar_Parser_AST.brange))))
end))
in (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, t)) | (FStar_Parser_AST.TAnnotated (x, t)) -> begin
(let _142_817 = (desugar_kind env t)
in (Some (x), _142_817))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _142_818 = (desugar_kind env t)
in (None, _142_818))
end
| FStar_Parser_AST.TVariable (x) -> begin
(Some (x), (
# 1201 "FStar.Parser.Desugar.fst"
let _53_2263 = FStar_Absyn_Syntax.mk_Kind_type
in {FStar_Absyn_Syntax.n = _53_2263.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _53_2263.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = b.FStar_Parser_AST.brange; FStar_Absyn_Syntax.fvs = _53_2263.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _53_2263.FStar_Absyn_Syntax.uvs}))
end
| _53_2266 -> begin
(fail ())
end)))

# 1202 "FStar.Parser.Desugar.fst"
let gather_tc_binders : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun tps k -> (
# 1205 "FStar.Parser.Desugar.fst"
let rec aux = (fun bs k -> (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(aux (FStar_List.append bs binders) k)
end
| FStar_Absyn_Syntax.Kind_abbrev (_53_2277, k) -> begin
(aux bs k)
end
| _53_2282 -> begin
bs
end))
in (let _142_827 = (aux tps k)
in (FStar_All.pipe_right _142_827 FStar_Absyn_Util.name_binders))))

# 1209 "FStar.Parser.Desugar.fst"
let mk_data_discriminators : FStar_Absyn_Syntax.qualifier Prims.list  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Ident.lid  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident Prims.list  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun quals env t tps k datas -> (
# 1214 "FStar.Parser.Desugar.fst"
let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_DesugarEnv.iface) || env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(FStar_List.append ((FStar_Absyn_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (
# 1215 "FStar.Parser.Desugar.fst"
let binders = (gather_tc_binders tps k)
in (
# 1216 "FStar.Parser.Desugar.fst"
let p = (FStar_Ident.range_of_lid t)
in (
# 1217 "FStar.Parser.Desugar.fst"
let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _53_2296 -> (match (_53_2296) with
| (x, _53_2295) -> begin
(x, Some (imp_tag))
end))))
in (
# 1218 "FStar.Parser.Desugar.fst"
let binders = (let _142_848 = (let _142_847 = (let _142_846 = (let _142_845 = (let _142_844 = (FStar_Absyn_Util.ftv t FStar_Absyn_Syntax.kun)
in (let _142_843 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (_142_844, _142_843)))
in (FStar_Absyn_Syntax.mk_Typ_app' _142_845 None p))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_v_binder _142_846))
in (_142_847)::[])
in (FStar_List.append imp_binders _142_848))
in (
# 1219 "FStar.Parser.Desugar.fst"
let disc_type = (let _142_851 = (let _142_850 = (let _142_849 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.bool_lid FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.total_comp _142_849 p))
in (binders, _142_850))
in (FStar_Absyn_Syntax.mk_Typ_fun _142_851 None p))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (
# 1221 "FStar.Parser.Desugar.fst"
let disc_name = (FStar_Absyn_Util.mk_discriminator d)
in (let _142_854 = (let _142_853 = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Discriminator (d))::[]))
in (disc_name, disc_type, _142_853, (FStar_Ident.range_of_lid disc_name)))
in FStar_Absyn_Syntax.Sig_val_decl (_142_854)))))))))))))

# 1223 "FStar.Parser.Desugar.fst"
let mk_indexed_projectors = (fun fvq refine_domain env _53_2308 lid formals t -> (match (_53_2308) with
| (tc, tps, k) -> begin
(
# 1226 "FStar.Parser.Desugar.fst"
let binders = (gather_tc_binders tps k)
in (
# 1227 "FStar.Parser.Desugar.fst"
let p = (FStar_Ident.range_of_lid lid)
in (
# 1228 "FStar.Parser.Desugar.fst"
let pos = (fun q -> (FStar_Absyn_Syntax.withinfo q None p))
in (
# 1229 "FStar.Parser.Desugar.fst"
let projectee = (let _142_865 = (FStar_Absyn_Syntax.mk_ident ("projectee", p))
in (let _142_864 = (FStar_Absyn_Util.genident (Some (p)))
in {FStar_Absyn_Syntax.ppname = _142_865; FStar_Absyn_Syntax.realname = _142_864}))
in (
# 1231 "FStar.Parser.Desugar.fst"
let arg_exp = (FStar_Absyn_Util.bvd_to_exp projectee FStar_Absyn_Syntax.tun)
in (
# 1232 "FStar.Parser.Desugar.fst"
let arg_binder = (
# 1233 "FStar.Parser.Desugar.fst"
let arg_typ = (let _142_868 = (let _142_867 = (FStar_Absyn_Util.ftv tc FStar_Absyn_Syntax.kun)
in (let _142_866 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (_142_867, _142_866)))
in (FStar_Absyn_Syntax.mk_Typ_app' _142_868 None p))
in if (not (refine_domain)) then begin
(FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s projectee arg_typ))
end else begin
(
# 1236 "FStar.Parser.Desugar.fst"
let disc_name = (FStar_Absyn_Util.mk_discriminator lid)
in (
# 1237 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.gen_bvar arg_typ)
in (let _142_878 = (let _142_877 = (let _142_876 = (let _142_875 = (let _142_874 = (let _142_873 = (let _142_872 = (FStar_Absyn_Util.fvar None disc_name p)
in (let _142_871 = (let _142_870 = (let _142_869 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _142_869))
in (_142_870)::[])
in (_142_872, _142_871)))
in (FStar_Absyn_Syntax.mk_Exp_app _142_873 None p))
in (FStar_Absyn_Util.b2t _142_874))
in (x, _142_875))
in (FStar_Absyn_Syntax.mk_Typ_refine _142_876 None p))
in (FStar_All.pipe_left (FStar_Absyn_Util.bvd_to_bvar_s projectee) _142_877))
in (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder _142_878))))
end)
in (
# 1239 "FStar.Parser.Desugar.fst"
let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _53_2325 -> (match (_53_2325) with
| (x, _53_2324) -> begin
(x, Some (imp_tag))
end))))
in (
# 1240 "FStar.Parser.Desugar.fst"
let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (
# 1241 "FStar.Parser.Desugar.fst"
let arg = (FStar_Absyn_Util.arg_of_non_null_binder arg_binder)
in (
# 1242 "FStar.Parser.Desugar.fst"
let subst = (let _142_886 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i f -> (match ((Prims.fst f)) with
| FStar_Util.Inl (a) -> begin
(
# 1244 "FStar.Parser.Desugar.fst"
let _53_2336 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_53_2336) with
| (field_name, _53_2335) -> begin
(
# 1245 "FStar.Parser.Desugar.fst"
let proj = (let _142_883 = (let _142_882 = (FStar_Absyn_Util.ftv field_name FStar_Absyn_Syntax.kun)
in (_142_882, (arg)::[]))
in (FStar_Absyn_Syntax.mk_Typ_app _142_883 None p))
in (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, proj)))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(
# 1249 "FStar.Parser.Desugar.fst"
let _53_2343 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_53_2343) with
| (field_name, _53_2342) -> begin
(
# 1250 "FStar.Parser.Desugar.fst"
let proj = (let _142_885 = (let _142_884 = (FStar_Absyn_Util.fvar None field_name p)
in (_142_884, (arg)::[]))
in (FStar_Absyn_Syntax.mk_Exp_app _142_885 None p))
in (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, proj)))::[])
end))
end))))
in (FStar_All.pipe_right _142_886 FStar_List.flatten))
in (
# 1253 "FStar.Parser.Desugar.fst"
let ntps = (FStar_List.length tps)
in (
# 1254 "FStar.Parser.Desugar.fst"
let all_params = (let _142_888 = (FStar_All.pipe_right tps (FStar_List.map (fun _53_2350 -> (match (_53_2350) with
| (b, _53_2349) -> begin
(b, Some (imp_tag))
end))))
in (FStar_List.append _142_888 formals))
in (let _142_918 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i ax -> (match ((Prims.fst ax)) with
| FStar_Util.Inl (a) -> begin
(
# 1258 "FStar.Parser.Desugar.fst"
let _53_2359 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_53_2359) with
| (field_name, _53_2358) -> begin
(
# 1259 "FStar.Parser.Desugar.fst"
let kk = (let _142_892 = (let _142_891 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (binders, _142_891))
in (FStar_Absyn_Syntax.mk_Kind_arrow _142_892 p))
in (FStar_Absyn_Syntax.Sig_tycon ((field_name, [], kk, [], [], (FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector ((lid, FStar_Util.Inl (a.FStar_Absyn_Syntax.v))))::[], (FStar_Ident.range_of_lid field_name))))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(
# 1263 "FStar.Parser.Desugar.fst"
let _53_2366 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_53_2366) with
| (field_name, _53_2365) -> begin
(
# 1264 "FStar.Parser.Desugar.fst"
let t = (let _142_895 = (let _142_894 = (let _142_893 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Absyn_Util.total_comp _142_893 p))
in (binders, _142_894))
in (FStar_Absyn_Syntax.mk_Typ_fun _142_895 None p))
in (
# 1265 "FStar.Parser.Desugar.fst"
let quals = (fun q -> if ((not (env.FStar_Parser_DesugarEnv.iface)) || env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(FStar_Absyn_Syntax.Assumption)::q
end else begin
q
end)
in (
# 1266 "FStar.Parser.Desugar.fst"
let quals = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector ((lid, FStar_Util.Inr (x.FStar_Absyn_Syntax.v))))::[]))
in (
# 1267 "FStar.Parser.Desugar.fst"
let impl = if (((let _142_898 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Ident.lid_equals FStar_Absyn_Const.prims_lid _142_898)) || (fvq <> FStar_Absyn_Syntax.Data_ctor)) || (let _142_900 = (let _142_899 = (FStar_Parser_DesugarEnv.current_module env)
in _142_899.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _142_900))) then begin
[]
end else begin
(
# 1272 "FStar.Parser.Desugar.fst"
let projection = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in (
# 1273 "FStar.Parser.Desugar.fst"
let as_imp = (fun _53_14 -> (match (_53_14) with
| Some (FStar_Absyn_Syntax.Implicit (_53_2374)) -> begin
true
end
| _53_2378 -> begin
false
end))
in (
# 1276 "FStar.Parser.Desugar.fst"
let arg_pats = (let _142_915 = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j by -> (match (by) with
| (FStar_Util.Inl (_53_2383), imp) -> begin
if (j < ntps) then begin
[]
end else begin
(let _142_908 = (let _142_907 = (let _142_906 = (let _142_905 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.kun)
in FStar_Absyn_Syntax.Pat_tvar (_142_905))
in (pos _142_906))
in (_142_907, (as_imp imp)))
in (_142_908)::[])
end
end
| (FStar_Util.Inr (_53_2388), imp) -> begin
if ((i + ntps) = j) then begin
(let _142_910 = (let _142_909 = (pos (FStar_Absyn_Syntax.Pat_var (projection)))
in (_142_909, (as_imp imp)))
in (_142_910)::[])
end else begin
if (j < ntps) then begin
[]
end else begin
(let _142_914 = (let _142_913 = (let _142_912 = (let _142_911 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in FStar_Absyn_Syntax.Pat_wild (_142_911))
in (pos _142_912))
in (_142_913, (as_imp imp)))
in (_142_914)::[])
end
end
end))))
in (FStar_All.pipe_right _142_915 FStar_List.flatten))
in (
# 1285 "FStar.Parser.Desugar.fst"
let pat = (let _142_917 = (FStar_All.pipe_right (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv lid), Some (fvq), arg_pats))) pos)
in (let _142_916 = (FStar_Absyn_Util.bvar_to_exp projection)
in (_142_917, None, _142_916)))
in (
# 1286 "FStar.Parser.Desugar.fst"
let body = (FStar_Absyn_Syntax.mk_Exp_match (arg_exp, (pat)::[]) None p)
in (
# 1287 "FStar.Parser.Desugar.fst"
let imp = (FStar_Absyn_Syntax.mk_Exp_abs (binders, body) None (FStar_Ident.range_of_lid field_name))
in (
# 1288 "FStar.Parser.Desugar.fst"
let lb = {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (field_name); FStar_Absyn_Syntax.lbtyp = FStar_Absyn_Syntax.tun; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_Tot_lid; FStar_Absyn_Syntax.lbdef = imp}
in (FStar_Absyn_Syntax.Sig_let (((false, (lb)::[]), p, [], quals)))::[])))))))
end
in (FStar_Absyn_Syntax.Sig_val_decl ((field_name, t, quals, (FStar_Ident.range_of_lid field_name))))::impl))))
end))
end))))
in (FStar_All.pipe_right _142_918 FStar_List.flatten))))))))))))))
end))

# 1295 "FStar.Parser.Desugar.fst"
let mk_data_projectors : FStar_Parser_DesugarEnv.env  ->  FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun env _53_17 -> (match (_53_17) with
| FStar_Absyn_Syntax.Sig_datacon (lid, t, tycon, quals, _53_2405, _53_2407) when (not ((FStar_Ident.lid_equals lid FStar_Absyn_Const.lexcons_lid))) -> begin
(
# 1300 "FStar.Parser.Desugar.fst"
let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_15 -> (match (_53_15) with
| FStar_Absyn_Syntax.RecordConstructor (_53_2412) -> begin
true
end
| _53_2415 -> begin
false
end)))) then begin
false
end else begin
(
# 1303 "FStar.Parser.Desugar.fst"
let _53_2421 = tycon
in (match (_53_2421) with
| (l, _53_2418, _53_2420) -> begin
(match ((FStar_Parser_DesugarEnv.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > 1)
end
| _53_2425 -> begin
true
end)
end))
end
in (match ((FStar_Absyn_Util.function_formals t)) with
| Some (formals, cod) -> begin
(
# 1309 "FStar.Parser.Desugar.fst"
let cod = (FStar_Absyn_Util.comp_result cod)
in (
# 1310 "FStar.Parser.Desugar.fst"
let qual = (match ((FStar_Util.find_map quals (fun _53_16 -> (match (_53_16) with
| FStar_Absyn_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Absyn_Syntax.Record_ctor ((lid, fns)))
end
| _53_2436 -> begin
None
end)))) with
| None -> begin
FStar_Absyn_Syntax.Data_ctor
end
| Some (q) -> begin
q
end)
in (mk_indexed_projectors qual refine_domain env tycon lid formals cod)))
end
| _53_2442 -> begin
[]
end))
end
| _53_2444 -> begin
[]
end))

# 1318 "FStar.Parser.Desugar.fst"
let rec desugar_tycon : FStar_Parser_DesugarEnv.env  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Absyn_Syntax.sigelts) = (fun env rng quals tcs -> (
# 1321 "FStar.Parser.Desugar.fst"
let tycon_id = (fun _53_18 -> (match (_53_18) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (
# 1326 "FStar.Parser.Desugar.fst"
let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _142_938 = (let _142_937 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_142_937))
in (FStar_Parser_AST.mk_term _142_938 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| (FStar_Parser_AST.TAnnotated (a, _)) | (FStar_Parser_AST.TVariable (a)) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar (a)) a.FStar_Ident.idRange FStar_Parser_AST.Type)
end
| FStar_Parser_AST.NoName (t) -> begin
t
end))
in (
# 1332 "FStar.Parser.Desugar.fst"
let tot = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.effect_Tot_lid)) rng FStar_Parser_AST.Expr)
in (
# 1333 "FStar.Parser.Desugar.fst"
let with_constructor_effect = (fun t -> (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((tot, t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level))
in (
# 1334 "FStar.Parser.Desugar.fst"
let apply_binders = (fun t binders -> (
# 1335 "FStar.Parser.Desugar.fst"
let imp_of_aqual = (fun b -> (match (b.FStar_Parser_AST.aqual) with
| Some (FStar_Parser_AST.Implicit) -> begin
FStar_Parser_AST.Hash
end
| _53_2509 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _142_951 = (let _142_950 = (let _142_949 = (binder_to_term b)
in (out, _142_949, (imp_of_aqual b)))
in FStar_Parser_AST.App (_142_950))
in (FStar_Parser_AST.mk_term _142_951 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (
# 1340 "FStar.Parser.Desugar.fst"
let tycon_record_as_variant = (fun _53_19 -> (match (_53_19) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(
# 1342 "FStar.Parser.Desugar.fst"
let constrName = (FStar_Ident.mk_ident ((Prims.strcat "Mk" id.FStar_Ident.idText), id.FStar_Ident.idRange))
in (
# 1343 "FStar.Parser.Desugar.fst"
let mfields = (FStar_List.map (fun _53_2522 -> (match (_53_2522) with
| (x, t) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated (((FStar_Absyn_Util.mangle_field_name x), t))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (
# 1344 "FStar.Parser.Desugar.fst"
let result = (let _142_957 = (let _142_956 = (let _142_955 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_142_955))
in (FStar_Parser_AST.mk_term _142_956 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _142_957 parms))
in (
# 1345 "FStar.Parser.Desugar.fst"
let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _142_959 = (FStar_All.pipe_right fields (FStar_List.map (fun _53_2529 -> (match (_53_2529) with
| (x, _53_2528) -> begin
(FStar_Parser_DesugarEnv.qualify env x)
end))))
in (FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _142_959))))))
end
| _53_2531 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1349 "FStar.Parser.Desugar.fst"
let desugar_abstract_tc = (fun quals _env mutuals _53_20 -> (match (_53_20) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(
# 1351 "FStar.Parser.Desugar.fst"
let _53_2545 = (typars_of_binders _env binders)
in (match (_53_2545) with
| (_env', typars) -> begin
(
# 1352 "FStar.Parser.Desugar.fst"
let k = (match (kopt) with
| None -> begin
FStar_Absyn_Syntax.kun
end
| Some (k) -> begin
(desugar_kind _env' k)
end)
in (
# 1355 "FStar.Parser.Desugar.fst"
let tconstr = (let _142_970 = (let _142_969 = (let _142_968 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_142_968))
in (FStar_Parser_AST.mk_term _142_969 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _142_970 binders))
in (
# 1356 "FStar.Parser.Desugar.fst"
let qlid = (FStar_Parser_DesugarEnv.qualify _env id)
in (
# 1357 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_tycon ((qlid, typars, k, mutuals, [], quals, rng))
in (
# 1358 "FStar.Parser.Desugar.fst"
let _env = (FStar_Parser_DesugarEnv.push_rec_binding _env (FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in (
# 1359 "FStar.Parser.Desugar.fst"
let _env2 = (FStar_Parser_DesugarEnv.push_rec_binding _env' (FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in (_env, _env2, se, tconstr)))))))
end))
end
| _53_2556 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (
# 1362 "FStar.Parser.Desugar.fst"
let push_tparam = (fun env _53_21 -> (match (_53_21) with
| (FStar_Util.Inr (x), _53_2563) -> begin
(FStar_Parser_DesugarEnv.push_bvvdef env x.FStar_Absyn_Syntax.v)
end
| (FStar_Util.Inl (a), _53_2568) -> begin
(FStar_Parser_DesugarEnv.push_btvdef env a.FStar_Absyn_Syntax.v)
end))
in (
# 1365 "FStar.Parser.Desugar.fst"
let push_tparams = (FStar_List.fold_left push_tparam)
in (match (tcs) with
| FStar_Parser_AST.TyconAbstract (_53_2572)::[] -> begin
(
# 1368 "FStar.Parser.Desugar.fst"
let tc = (FStar_List.hd tcs)
in (
# 1369 "FStar.Parser.Desugar.fst"
let _53_2583 = (desugar_abstract_tc quals env [] tc)
in (match (_53_2583) with
| (_53_2577, _53_2579, se, _53_2582) -> begin
(
# 1370 "FStar.Parser.Desugar.fst"
let quals = if ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.New))) then begin
quals
end else begin
(
# 1373 "FStar.Parser.Desugar.fst"
let _53_2584 = (let _142_980 = (FStar_Range.string_of_range rng)
in (let _142_979 = (let _142_978 = (let _142_977 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _142_977 (FStar_List.map FStar_Absyn_Print.sli)))
in (FStar_All.pipe_right _142_978 (FStar_String.concat ", ")))
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'new\' qualifier on %s\n" _142_980 _142_979)))
in (FStar_Absyn_Syntax.New)::quals)
end
in (
# 1376 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[])))
end)))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t)::[] -> begin
(
# 1381 "FStar.Parser.Desugar.fst"
let _53_2597 = (typars_of_binders env binders)
in (match (_53_2597) with
| (env', typars) -> begin
(
# 1382 "FStar.Parser.Desugar.fst"
let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _53_22 -> (match (_53_22) with
| FStar_Absyn_Syntax.Effect -> begin
true
end
| _53_2602 -> begin
false
end)) quals) then begin
FStar_Absyn_Syntax.mk_Kind_effect
end else begin
FStar_Absyn_Syntax.kun
end
end
| Some (k) -> begin
(desugar_kind env' k)
end)
in (
# 1388 "FStar.Parser.Desugar.fst"
let t0 = t
in (
# 1389 "FStar.Parser.Desugar.fst"
let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _53_23 -> (match (_53_23) with
| FStar_Absyn_Syntax.Logic -> begin
true
end
| _53_2610 -> begin
false
end)))) then begin
quals
end else begin
if (t0.FStar_Parser_AST.level = FStar_Parser_AST.Formula) then begin
(FStar_Absyn_Syntax.Logic)::quals
end else begin
quals
end
end
in (
# 1394 "FStar.Parser.Desugar.fst"
let se = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Effect)) then begin
(
# 1396 "FStar.Parser.Desugar.fst"
let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (let _142_986 = (let _142_985 = (FStar_Parser_DesugarEnv.qualify env id)
in (let _142_984 = (FStar_All.pipe_right quals (FStar_List.filter (fun _53_24 -> (match (_53_24) with
| FStar_Absyn_Syntax.Effect -> begin
false
end
| _53_2616 -> begin
true
end))))
in (_142_985, typars, c, _142_984, rng)))
in FStar_Absyn_Syntax.Sig_effect_abbrev (_142_986)))
end else begin
(
# 1398 "FStar.Parser.Desugar.fst"
let t = (desugar_typ env' t)
in (let _142_988 = (let _142_987 = (FStar_Parser_DesugarEnv.qualify env id)
in (_142_987, typars, k, t, quals, rng))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_142_988)))
end
in (
# 1400 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[]))))))
end))
end
| FStar_Parser_AST.TyconRecord (_53_2621)::[] -> begin
(
# 1404 "FStar.Parser.Desugar.fst"
let trec = (FStar_List.hd tcs)
in (
# 1405 "FStar.Parser.Desugar.fst"
let _53_2627 = (tycon_record_as_variant trec)
in (match (_53_2627) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Absyn_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| _53_2631::_53_2629 -> begin
(
# 1409 "FStar.Parser.Desugar.fst"
let env0 = env
in (
# 1410 "FStar.Parser.Desugar.fst"
let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_DesugarEnv.qualify env) (tycon_id x))) tcs)
in (
# 1411 "FStar.Parser.Desugar.fst"
let rec collect_tcs = (fun quals et tc -> (
# 1412 "FStar.Parser.Desugar.fst"
let _53_2642 = et
in (match (_53_2642) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_53_2644) -> begin
(
# 1415 "FStar.Parser.Desugar.fst"
let trec = tc
in (
# 1416 "FStar.Parser.Desugar.fst"
let _53_2649 = (tycon_record_as_variant trec)
in (match (_53_2649) with
| (t, fs) -> begin
(collect_tcs ((FStar_Absyn_Syntax.RecordType (fs))::quals) (env, tcs) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(
# 1419 "FStar.Parser.Desugar.fst"
let _53_2661 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_53_2661) with
| (env, _53_2658, se, tconstr) -> begin
(env, (FStar_Util.Inl ((se, constructors, tconstr, quals)))::tcs)
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(
# 1422 "FStar.Parser.Desugar.fst"
let _53_2673 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_53_2673) with
| (env, _53_2670, se, tconstr) -> begin
(env, (FStar_Util.Inr ((se, t, quals)))::tcs)
end))
end
| _53_2675 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (
# 1425 "FStar.Parser.Desugar.fst"
let _53_2678 = (FStar_List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_53_2678) with
| (env, tcs) -> begin
(
# 1426 "FStar.Parser.Desugar.fst"
let tcs = (FStar_List.rev tcs)
in (
# 1427 "FStar.Parser.Desugar.fst"
let sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _53_26 -> (match (_53_26) with
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (id, tpars, k, _53_2685, _53_2687, _53_2689, _53_2691), t, quals) -> begin
(
# 1429 "FStar.Parser.Desugar.fst"
let env_tps = (push_tparams env tpars)
in (
# 1430 "FStar.Parser.Desugar.fst"
let t = (desugar_typ env_tps t)
in (FStar_Absyn_Syntax.Sig_typ_abbrev ((id, tpars, k, t, [], rng)))::[]))
end
| FStar_Util.Inl (FStar_Absyn_Syntax.Sig_tycon (tname, tpars, k, mutuals, _53_2705, tags, _53_2708), constrs, tconstr, quals) -> begin
(
# 1434 "FStar.Parser.Desugar.fst"
let tycon = (tname, tpars, k)
in (
# 1435 "FStar.Parser.Desugar.fst"
let env_tps = (push_tparams env tpars)
in (
# 1436 "FStar.Parser.Desugar.fst"
let _53_2739 = (let _142_1004 = (FStar_All.pipe_right constrs (FStar_List.map (fun _53_2721 -> (match (_53_2721) with
| (id, topt, of_notation) -> begin
(
# 1438 "FStar.Parser.Desugar.fst"
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
# 1446 "FStar.Parser.Desugar.fst"
let t = (let _142_999 = (FStar_Parser_DesugarEnv.default_total env_tps)
in (let _142_998 = (close env_tps t)
in (desugar_typ _142_999 _142_998)))
in (
# 1447 "FStar.Parser.Desugar.fst"
let name = (FStar_Parser_DesugarEnv.qualify env id)
in (
# 1448 "FStar.Parser.Desugar.fst"
let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _53_25 -> (match (_53_25) with
| FStar_Absyn_Syntax.RecordType (fns) -> begin
(FStar_Absyn_Syntax.RecordConstructor (fns))::[]
end
| _53_2735 -> begin
[]
end))))
in (let _142_1003 = (let _142_1002 = (let _142_1001 = (FStar_All.pipe_right t FStar_Absyn_Util.name_function_binders)
in (name, _142_1001, tycon, quals, mutuals, rng))
in FStar_Absyn_Syntax.Sig_datacon (_142_1002))
in (name, _142_1003))))))
end))))
in (FStar_All.pipe_left FStar_List.split _142_1004))
in (match (_53_2739) with
| (constrNames, constrs) -> begin
(FStar_Absyn_Syntax.Sig_tycon ((tname, tpars, k, mutuals, constrNames, tags, rng)))::constrs
end))))
end
| _53_2741 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1454 "FStar.Parser.Desugar.fst"
let bundle = (let _142_1006 = (let _142_1005 = (FStar_List.collect FStar_Absyn_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _142_1005, rng))
in FStar_Absyn_Syntax.Sig_bundle (_142_1006))
in (
# 1455 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env0 bundle)
in (
# 1456 "FStar.Parser.Desugar.fst"
let data_ops = (FStar_All.pipe_right sigelts (FStar_List.collect (mk_data_projectors env)))
in (
# 1457 "FStar.Parser.Desugar.fst"
let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _53_27 -> (match (_53_27) with
| FStar_Absyn_Syntax.Sig_tycon (tname, tps, k, _53_2751, constrs, quals, _53_2755) -> begin
(mk_data_discriminators quals env tname tps k constrs)
end
| _53_2759 -> begin
[]
end))))
in (
# 1461 "FStar.Parser.Desugar.fst"
let ops = (FStar_List.append discs data_ops)
in (
# 1462 "FStar.Parser.Desugar.fst"
let env = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt env ops)
in (env, (FStar_List.append ((bundle)::[]) ops))))))))))
end)))))
end
| [] -> begin
(FStar_All.failwith "impossible")
end)))))))))))

# 1465 "FStar.Parser.Desugar.fst"
let desugar_binders : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.binder Prims.list) = (fun env binders -> (
# 1468 "FStar.Parser.Desugar.fst"
let _53_2790 = (FStar_List.fold_left (fun _53_2768 b -> (match (_53_2768) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| FStar_Util.Inl (Some (a), k) -> begin
(
# 1471 "FStar.Parser.Desugar.fst"
let _53_2777 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_53_2777) with
| (env, a) -> begin
(let _142_1015 = (let _142_1014 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_142_1014)::binders)
in (env, _142_1015))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(
# 1475 "FStar.Parser.Desugar.fst"
let _53_2785 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_53_2785) with
| (env, x) -> begin
(let _142_1017 = (let _142_1016 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_142_1016)::binders)
in (env, _142_1017))
end))
end
| _53_2787 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Missing name in binder", b.FStar_Parser_AST.brange))))
end)
end)) (env, []) binders)
in (match (_53_2790) with
| (env, binders) -> begin
(env, (FStar_List.rev binders))
end)))

# 1479 "FStar.Parser.Desugar.fst"
let trans_qual : FStar_Range.range  ->  FStar_Parser_AST.qualifier  ->  FStar_Absyn_Syntax.qualifier = (fun r _53_28 -> (match (_53_28) with
| FStar_Parser_AST.Private -> begin
FStar_Absyn_Syntax.Private
end
| FStar_Parser_AST.Assumption -> begin
FStar_Absyn_Syntax.Assumption
end
| FStar_Parser_AST.Opaque -> begin
FStar_Absyn_Syntax.Opaque
end
| FStar_Parser_AST.Logic -> begin
FStar_Absyn_Syntax.Logic
end
| FStar_Parser_AST.Abstract -> begin
FStar_Absyn_Syntax.Abstract
end
| FStar_Parser_AST.New -> begin
FStar_Absyn_Syntax.New
end
| FStar_Parser_AST.TotalEffect -> begin
FStar_Absyn_Syntax.TotalEffect
end
| FStar_Parser_AST.DefaultEffect -> begin
FStar_Absyn_Syntax.DefaultEffect (None)
end
| FStar_Parser_AST.Effect -> begin
FStar_Absyn_Syntax.Effect
end
| (FStar_Parser_AST.Inline) | (FStar_Parser_AST.Irreducible) | (FStar_Parser_AST.Unfoldable) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("This qualifier is supported only with the --universes option", r))))
end))

# 1493 "FStar.Parser.Desugar.fst"
let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Absyn_Syntax.pragma = (fun _53_29 -> (match (_53_29) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Absyn_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (s) -> begin
FStar_Absyn_Syntax.ResetOptions (s)
end))

# 1497 "FStar.Parser.Desugar.fst"
let trans_quals : FStar_Range.range  ->  FStar_Parser_AST.qualifier Prims.list  ->  FStar_Absyn_Syntax.qualifier Prims.list = (fun r -> (FStar_List.map (trans_qual r)))

# 1499 "FStar.Parser.Desugar.fst"
let rec desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Absyn_Syntax.sigelts) = (fun env d -> (
# 1502 "FStar.Parser.Desugar.fst"
let trans_quals = (trans_quals d.FStar_Parser_AST.drange)
in (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(
# 1505 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_pragma (((trans_pragma p), d.FStar_Parser_AST.drange))
in (env, (se)::[]))
end
| FStar_Parser_AST.TopLevelModule (_53_2818) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Multiple modules in a file are no longer supported", d.FStar_Parser_AST.drange))))
end
| FStar_Parser_AST.Open (lid) -> begin
(
# 1512 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_namespace env lid)
in (env, []))
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(let _142_1035 = (FStar_Parser_DesugarEnv.push_module_abbrev env x l)
in (_142_1035, []))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(let _142_1036 = (trans_quals qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _142_1036 tcs))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _142_1038 = (let _142_1037 = (desugar_exp_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((isrec, lets, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Absyn_Util.compress_exp _142_1037))
in _142_1038.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_let (lbs, _53_2838) -> begin
(
# 1524 "FStar.Parser.Desugar.fst"
let lids = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inr (l) -> begin
l
end
| _53_2845 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1527 "FStar.Parser.Desugar.fst"
let quals = (match (quals) with
| _53_2850::_53_2848 -> begin
(trans_quals quals)
end
| _53_2853 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _53_30 -> (match (_53_30) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_53_2862); FStar_Absyn_Syntax.lbtyp = _53_2860; FStar_Absyn_Syntax.lbeff = _53_2858; FStar_Absyn_Syntax.lbdef = _53_2856} -> begin
[]
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = _53_2870; FStar_Absyn_Syntax.lbeff = _53_2868; FStar_Absyn_Syntax.lbdef = _53_2866} -> begin
(FStar_Parser_DesugarEnv.lookup_letbinding_quals env l)
end))))
end)
in (
# 1532 "FStar.Parser.Desugar.fst"
let s = FStar_Absyn_Syntax.Sig_let ((lbs, d.FStar_Parser_AST.drange, lids, quals))
in (
# 1533 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env s)
in (env, (s)::[])))))
end
| _53_2878 -> begin
(FStar_All.failwith "Desugaring a let did not produce a let")
end)
end
| FStar_Parser_AST.Main (t) -> begin
(
# 1539 "FStar.Parser.Desugar.fst"
let e = (desugar_exp env t)
in (
# 1540 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_main ((e, d.FStar_Parser_AST.drange))
in (env, (se)::[])))
end
| FStar_Parser_AST.Assume (atag, id, t) -> begin
(
# 1544 "FStar.Parser.Desugar.fst"
let f = (desugar_formula env t)
in (let _142_1044 = (let _142_1043 = (let _142_1042 = (let _142_1041 = (FStar_Parser_DesugarEnv.qualify env id)
in (_142_1041, f, (FStar_Absyn_Syntax.Assumption)::[], d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Sig_assume (_142_1042))
in (_142_1043)::[])
in (env, _142_1044)))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(
# 1548 "FStar.Parser.Desugar.fst"
let t = (let _142_1045 = (close_fun env t)
in (desugar_typ env _142_1045))
in (
# 1549 "FStar.Parser.Desugar.fst"
let quals = if (env.FStar_Parser_DesugarEnv.iface && env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(let _142_1046 = (trans_quals quals)
in (FStar_Absyn_Syntax.Assumption)::_142_1046)
end else begin
(trans_quals quals)
end
in (
# 1550 "FStar.Parser.Desugar.fst"
let se = (let _142_1048 = (let _142_1047 = (FStar_Parser_DesugarEnv.qualify env id)
in (_142_1047, t, quals, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Sig_val_decl (_142_1048))
in (
# 1551 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[])))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(
# 1555 "FStar.Parser.Desugar.fst"
let t = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) FStar_Absyn_Const.exn_lid)
in (
# 1556 "FStar.Parser.Desugar.fst"
let l = (FStar_Parser_DesugarEnv.qualify env id)
in (
# 1557 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_datacon ((l, t, (FStar_Absyn_Const.exn_lid, [], FStar_Absyn_Syntax.ktype), (FStar_Absyn_Syntax.ExceptionConstructor)::[], (FStar_Absyn_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (
# 1558 "FStar.Parser.Desugar.fst"
let se' = FStar_Absyn_Syntax.Sig_bundle (((se)::[], (FStar_Absyn_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (
# 1559 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env se')
in (
# 1560 "FStar.Parser.Desugar.fst"
let data_ops = (mk_data_projectors env se)
in (
# 1561 "FStar.Parser.Desugar.fst"
let discs = (mk_data_discriminators [] env FStar_Absyn_Const.exn_lid [] FStar_Absyn_Syntax.ktype ((l)::[]))
in (
# 1562 "FStar.Parser.Desugar.fst"
let env = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops))))))))))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(
# 1566 "FStar.Parser.Desugar.fst"
let t = (desugar_typ env term)
in (
# 1567 "FStar.Parser.Desugar.fst"
let t = (let _142_1053 = (let _142_1052 = (let _142_1049 = (FStar_Absyn_Syntax.null_v_binder t)
in (_142_1049)::[])
in (let _142_1051 = (let _142_1050 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) FStar_Absyn_Const.exn_lid)
in (FStar_Absyn_Syntax.mk_Total _142_1050))
in (_142_1052, _142_1051)))
in (FStar_Absyn_Syntax.mk_Typ_fun _142_1053 None d.FStar_Parser_AST.drange))
in (
# 1568 "FStar.Parser.Desugar.fst"
let l = (FStar_Parser_DesugarEnv.qualify env id)
in (
# 1569 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_datacon ((l, t, (FStar_Absyn_Const.exn_lid, [], FStar_Absyn_Syntax.ktype), (FStar_Absyn_Syntax.ExceptionConstructor)::[], (FStar_Absyn_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (
# 1570 "FStar.Parser.Desugar.fst"
let se' = FStar_Absyn_Syntax.Sig_bundle (((se)::[], (FStar_Absyn_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (
# 1571 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env se')
in (
# 1572 "FStar.Parser.Desugar.fst"
let data_ops = (mk_data_projectors env se)
in (
# 1573 "FStar.Parser.Desugar.fst"
let discs = (mk_data_discriminators [] env FStar_Absyn_Const.exn_lid [] FStar_Absyn_Syntax.ktype ((l)::[]))
in (
# 1574 "FStar.Parser.Desugar.fst"
let env = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops)))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(
# 1578 "FStar.Parser.Desugar.fst"
let _53_2931 = (desugar_binders env binders)
in (match (_53_2931) with
| (env_k, binders) -> begin
(
# 1579 "FStar.Parser.Desugar.fst"
let k = (desugar_kind env_k k)
in (
# 1580 "FStar.Parser.Desugar.fst"
let name = (FStar_Parser_DesugarEnv.qualify env id)
in (
# 1581 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_kind_abbrev ((name, binders, k, d.FStar_Parser_AST.drange))
in (
# 1582 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[])))))
end))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(
# 1586 "FStar.Parser.Desugar.fst"
let env0 = env
in (
# 1587 "FStar.Parser.Desugar.fst"
let _53_2947 = (desugar_binders env eff_binders)
in (match (_53_2947) with
| (env, binders) -> begin
(
# 1588 "FStar.Parser.Desugar.fst"
let defn = (desugar_typ env defn)
in (
# 1589 "FStar.Parser.Desugar.fst"
let _53_2951 = (FStar_Absyn_Util.head_and_args defn)
in (match (_53_2951) with
| (head, args) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (eff) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_effect_defn env eff.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _142_1058 = (let _142_1057 = (let _142_1056 = (let _142_1055 = (let _142_1054 = (FStar_Absyn_Print.sli eff.FStar_Absyn_Syntax.v)
in (Prims.strcat "Effect " _142_1054))
in (Prims.strcat _142_1055 " not found"))
in (_142_1056, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Error (_142_1057))
in (Prims.raise _142_1058))
end
| Some (ed) -> begin
(
# 1595 "FStar.Parser.Desugar.fst"
let subst = (FStar_Absyn_Util.subst_of_list ed.FStar_Absyn_Syntax.binders args)
in (
# 1596 "FStar.Parser.Desugar.fst"
let sub = (FStar_Absyn_Util.subst_typ subst)
in (
# 1597 "FStar.Parser.Desugar.fst"
let ed = (let _142_1076 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _142_1075 = (trans_quals quals)
in (let _142_1074 = (FStar_Absyn_Util.subst_kind subst ed.FStar_Absyn_Syntax.signature)
in (let _142_1073 = (sub ed.FStar_Absyn_Syntax.ret)
in (let _142_1072 = (sub ed.FStar_Absyn_Syntax.bind_wp)
in (let _142_1071 = (sub ed.FStar_Absyn_Syntax.bind_wlp)
in (let _142_1070 = (sub ed.FStar_Absyn_Syntax.if_then_else)
in (let _142_1069 = (sub ed.FStar_Absyn_Syntax.ite_wp)
in (let _142_1068 = (sub ed.FStar_Absyn_Syntax.ite_wlp)
in (let _142_1067 = (sub ed.FStar_Absyn_Syntax.wp_binop)
in (let _142_1066 = (sub ed.FStar_Absyn_Syntax.wp_as_type)
in (let _142_1065 = (sub ed.FStar_Absyn_Syntax.close_wp)
in (let _142_1064 = (sub ed.FStar_Absyn_Syntax.close_wp_t)
in (let _142_1063 = (sub ed.FStar_Absyn_Syntax.assert_p)
in (let _142_1062 = (sub ed.FStar_Absyn_Syntax.assume_p)
in (let _142_1061 = (sub ed.FStar_Absyn_Syntax.null_wp)
in (let _142_1060 = (sub ed.FStar_Absyn_Syntax.trivial)
in {FStar_Absyn_Syntax.mname = _142_1076; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = _142_1075; FStar_Absyn_Syntax.signature = _142_1074; FStar_Absyn_Syntax.ret = _142_1073; FStar_Absyn_Syntax.bind_wp = _142_1072; FStar_Absyn_Syntax.bind_wlp = _142_1071; FStar_Absyn_Syntax.if_then_else = _142_1070; FStar_Absyn_Syntax.ite_wp = _142_1069; FStar_Absyn_Syntax.ite_wlp = _142_1068; FStar_Absyn_Syntax.wp_binop = _142_1067; FStar_Absyn_Syntax.wp_as_type = _142_1066; FStar_Absyn_Syntax.close_wp = _142_1065; FStar_Absyn_Syntax.close_wp_t = _142_1064; FStar_Absyn_Syntax.assert_p = _142_1063; FStar_Absyn_Syntax.assume_p = _142_1062; FStar_Absyn_Syntax.null_wp = _142_1061; FStar_Absyn_Syntax.trivial = _142_1060})))))))))))))))))
in (
# 1617 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (
# 1618 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)
end
| _53_2963 -> begin
(let _142_1080 = (let _142_1079 = (let _142_1078 = (let _142_1077 = (FStar_Absyn_Print.typ_to_string head)
in (Prims.strcat _142_1077 " is not an effect"))
in (_142_1078, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Error (_142_1079))
in (Prims.raise _142_1080))
end)
end)))
end)))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls)) -> begin
(
# 1625 "FStar.Parser.Desugar.fst"
let env0 = env
in (
# 1626 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.enter_monad_scope env eff_name)
in (
# 1627 "FStar.Parser.Desugar.fst"
let _53_2977 = (desugar_binders env eff_binders)
in (match (_53_2977) with
| (env, binders) -> begin
(
# 1628 "FStar.Parser.Desugar.fst"
let eff_k = (desugar_kind env eff_kind)
in (
# 1629 "FStar.Parser.Desugar.fst"
let _53_2988 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _53_2981 decl -> (match (_53_2981) with
| (env, out) -> begin
(
# 1630 "FStar.Parser.Desugar.fst"
let _53_2985 = (desugar_decl env decl)
in (match (_53_2985) with
| (env, ses) -> begin
(let _142_1084 = (let _142_1083 = (FStar_List.hd ses)
in (_142_1083)::out)
in (env, _142_1084))
end))
end)) (env, [])))
in (match (_53_2988) with
| (env, decls) -> begin
(
# 1632 "FStar.Parser.Desugar.fst"
let decls = (FStar_List.rev decls)
in (
# 1633 "FStar.Parser.Desugar.fst"
let lookup = (fun s -> (match ((let _142_1088 = (let _142_1087 = (FStar_Absyn_Syntax.mk_ident (s, d.FStar_Parser_AST.drange))
in (FStar_Parser_DesugarEnv.qualify env _142_1087))
in (FStar_Parser_DesugarEnv.try_resolve_typ_abbrev env _142_1088))) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat (Prims.strcat (Prims.strcat "Monad " eff_name.FStar_Ident.idText) " expects definition of ") s), d.FStar_Parser_AST.drange))))
end
| Some (t) -> begin
t
end))
in (
# 1636 "FStar.Parser.Desugar.fst"
let ed = (let _142_1104 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _142_1103 = (trans_quals quals)
in (let _142_1102 = (lookup "return")
in (let _142_1101 = (lookup "bind_wp")
in (let _142_1100 = (lookup "bind_wlp")
in (let _142_1099 = (lookup "if_then_else")
in (let _142_1098 = (lookup "ite_wp")
in (let _142_1097 = (lookup "ite_wlp")
in (let _142_1096 = (lookup "wp_binop")
in (let _142_1095 = (lookup "wp_as_type")
in (let _142_1094 = (lookup "close_wp")
in (let _142_1093 = (lookup "close_wp_t")
in (let _142_1092 = (lookup "assert_p")
in (let _142_1091 = (lookup "assume_p")
in (let _142_1090 = (lookup "null_wp")
in (let _142_1089 = (lookup "trivial")
in {FStar_Absyn_Syntax.mname = _142_1104; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = _142_1103; FStar_Absyn_Syntax.signature = eff_k; FStar_Absyn_Syntax.ret = _142_1102; FStar_Absyn_Syntax.bind_wp = _142_1101; FStar_Absyn_Syntax.bind_wlp = _142_1100; FStar_Absyn_Syntax.if_then_else = _142_1099; FStar_Absyn_Syntax.ite_wp = _142_1098; FStar_Absyn_Syntax.ite_wlp = _142_1097; FStar_Absyn_Syntax.wp_binop = _142_1096; FStar_Absyn_Syntax.wp_as_type = _142_1095; FStar_Absyn_Syntax.close_wp = _142_1094; FStar_Absyn_Syntax.close_wp_t = _142_1093; FStar_Absyn_Syntax.assert_p = _142_1092; FStar_Absyn_Syntax.assume_p = _142_1091; FStar_Absyn_Syntax.null_wp = _142_1090; FStar_Absyn_Syntax.trivial = _142_1089}))))))))))))))))
in (
# 1656 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (
# 1657 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)))
end))))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(
# 1661 "FStar.Parser.Desugar.fst"
let lookup = (fun l -> (match ((FStar_Parser_DesugarEnv.try_lookup_effect_name env l)) with
| None -> begin
(let _142_1111 = (let _142_1110 = (let _142_1109 = (let _142_1108 = (let _142_1107 = (FStar_Absyn_Print.sli l)
in (Prims.strcat "Effect name " _142_1107))
in (Prims.strcat _142_1108 " not found"))
in (_142_1109, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Error (_142_1110))
in (Prims.raise _142_1111))
end
| Some (l) -> begin
l
end))
in (
# 1664 "FStar.Parser.Desugar.fst"
let src = (lookup l.FStar_Parser_AST.msource)
in (
# 1665 "FStar.Parser.Desugar.fst"
let dst = (lookup l.FStar_Parser_AST.mdest)
in (
# 1666 "FStar.Parser.Desugar.fst"
let lift = (desugar_typ env l.FStar_Parser_AST.lift_op)
in (
# 1667 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_sub_effect (({FStar_Absyn_Syntax.source = src; FStar_Absyn_Syntax.target = dst; FStar_Absyn_Syntax.lift = lift}, d.FStar_Parser_AST.drange))
in (env, (se)::[]))))))
end)))

# 1668 "FStar.Parser.Desugar.fst"
let desugar_decls : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _53_3013 d -> (match (_53_3013) with
| (env, sigelts) -> begin
(
# 1672 "FStar.Parser.Desugar.fst"
let _53_3017 = (desugar_decl env d)
in (match (_53_3017) with
| (env, se) -> begin
(env, (FStar_List.append sigelts se))
end))
end)) (env, []) decls))

# 1673 "FStar.Parser.Desugar.fst"
let open_prims_all : FStar_Parser_AST.decl Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.prims_lid)) FStar_Absyn_Syntax.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.all_lid)) FStar_Absyn_Syntax.dummyRange))::[]

# 1677 "FStar.Parser.Desugar.fst"
let desugar_modul_common : FStar_Absyn_Syntax.modul Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Absyn_Syntax.modul * Prims.bool) = (fun curmod env m -> (
# 1683 "FStar.Parser.Desugar.fst"
let open_ns = (fun mname d -> (
# 1684 "FStar.Parser.Desugar.fst"
let d = if ((FStar_List.length mname.FStar_Ident.ns) <> 0) then begin
(let _142_1131 = (let _142_1130 = (let _142_1128 = (FStar_Absyn_Syntax.lid_of_ids mname.FStar_Ident.ns)
in FStar_Parser_AST.Open (_142_1128))
in (let _142_1129 = (FStar_Absyn_Syntax.range_of_lid mname)
in (FStar_Parser_AST.mk_decl _142_1130 _142_1129)))
in (_142_1131)::d)
end else begin
d
end
in d))
in (
# 1688 "FStar.Parser.Desugar.fst"
let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod) -> begin
(FStar_Parser_DesugarEnv.finish_module_or_interface env prev_mod)
end)
in (
# 1691 "FStar.Parser.Desugar.fst"
let _53_3044 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _142_1133 = (FStar_Parser_DesugarEnv.prepare_module_or_interface true admitted env mname)
in (let _142_1132 = (open_ns mname decls)
in (_142_1133, mname, _142_1132, true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _142_1135 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false env mname)
in (let _142_1134 = (open_ns mname decls)
in (_142_1135, mname, _142_1134, false)))
end)
in (match (_53_3044) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(
# 1696 "FStar.Parser.Desugar.fst"
let _53_3047 = (desugar_decls env decls)
in (match (_53_3047) with
| (env, sigelts) -> begin
(
# 1697 "FStar.Parser.Desugar.fst"
let modul = {FStar_Absyn_Syntax.name = mname; FStar_Absyn_Syntax.declarations = sigelts; FStar_Absyn_Syntax.exports = []; FStar_Absyn_Syntax.is_interface = intf; FStar_Absyn_Syntax.is_deserialized = false}
in (env, modul, pop_when_done))
end))
end)))))

# 1704 "FStar.Parser.Desugar.fst"
let desugar_partial_modul : FStar_Absyn_Syntax.modul Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul) = (fun curmod env m -> (
# 1707 "FStar.Parser.Desugar.fst"
let m = if (FStar_ST.read FStar_Options.interactive_fsi) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface ((mname, decls, true))
end
| FStar_Parser_AST.Interface (mname, _53_3058, _53_3060) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (
# 1714 "FStar.Parser.Desugar.fst"
let _53_3068 = (desugar_modul_common curmod env m)
in (match (_53_3068) with
| (x, y, _53_3067) -> begin
(x, y)
end))))

# 1715 "FStar.Parser.Desugar.fst"
let desugar_modul : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Absyn_Syntax.modul) = (fun env m -> (
# 1718 "FStar.Parser.Desugar.fst"
let _53_3074 = (desugar_modul_common None env m)
in (match (_53_3074) with
| (env, modul, pop_when_done) -> begin
(
# 1719 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.finish_module_or_interface env modul)
in (
# 1720 "FStar.Parser.Desugar.fst"
let _53_3076 = if (FStar_Options.should_dump modul.FStar_Absyn_Syntax.name.FStar_Ident.str) then begin
(let _142_1146 = (FStar_Absyn_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _142_1146))
end else begin
()
end
in (let _142_1147 = if pop_when_done then begin
(FStar_Parser_DesugarEnv.export_interface modul.FStar_Absyn_Syntax.name env)
end else begin
env
end
in (_142_1147, modul))))
end)))

# 1721 "FStar.Parser.Desugar.fst"
let desugar_file : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul Prims.list) = (fun env f -> (
# 1724 "FStar.Parser.Desugar.fst"
let _53_3089 = (FStar_List.fold_left (fun _53_3082 m -> (match (_53_3082) with
| (env, mods) -> begin
(
# 1725 "FStar.Parser.Desugar.fst"
let _53_3086 = (desugar_modul env m)
in (match (_53_3086) with
| (env, m) -> begin
(env, (m)::mods)
end))
end)) (env, []) f)
in (match (_53_3089) with
| (env, mods) -> begin
(env, (FStar_List.rev mods))
end)))

# 1727 "FStar.Parser.Desugar.fst"
let add_modul_to_env : FStar_Absyn_Syntax.modul  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_DesugarEnv.env = (fun m en -> (
# 1730 "FStar.Parser.Desugar.fst"
let _53_3094 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false en m.FStar_Absyn_Syntax.name)
in (match (_53_3094) with
| (en, pop_when_done) -> begin
(
# 1731 "FStar.Parser.Desugar.fst"
let en = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt (
# 1731 "FStar.Parser.Desugar.fst"
let _53_3095 = en
in {FStar_Parser_DesugarEnv.curmodule = Some (m.FStar_Absyn_Syntax.name); FStar_Parser_DesugarEnv.modules = _53_3095.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _53_3095.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.modul_abbrevs = _53_3095.FStar_Parser_DesugarEnv.modul_abbrevs; FStar_Parser_DesugarEnv.sigaccum = _53_3095.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _53_3095.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _53_3095.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = _53_3095.FStar_Parser_DesugarEnv.phase; FStar_Parser_DesugarEnv.sigmap = _53_3095.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _53_3095.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _53_3095.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _53_3095.FStar_Parser_DesugarEnv.admitted_iface}) m.FStar_Absyn_Syntax.exports)
in (
# 1732 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_DesugarEnv.export_interface m.FStar_Absyn_Syntax.name env)
end else begin
env
end))
end)))




