
open Prims
# 35 "FStar.Parser.Desugar.fst"
let imp_tag : FStar_Absyn_Syntax.arg_qualifier = FStar_Absyn_Syntax.Implicit (false)

# 36 "FStar.Parser.Desugar.fst"
let as_imp : FStar_Parser_AST.imp  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option = (fun _49_1 -> (match (_49_1) with
| (FStar_Parser_AST.Hash) | (FStar_Parser_AST.FsTypApp) -> begin
Some (imp_tag)
end
| _49_35 -> begin
None
end))

# 40 "FStar.Parser.Desugar.fst"
let arg_withimp_e = (fun imp t -> (t, (as_imp imp)))

# 42 "FStar.Parser.Desugar.fst"
let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
(t, Some (imp_tag))
end
| _49_42 -> begin
(t, None)
end))

# 47 "FStar.Parser.Desugar.fst"
let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_49_46) -> begin
true
end
| _49_49 -> begin
false
end)))))

# 52 "FStar.Parser.Desugar.fst"
let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _49_54 -> begin
t
end))

# 55 "FStar.Parser.Desugar.fst"
let rec unlabel : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unlabel t)
end
| FStar_Parser_AST.Labeled (t, _49_60, _49_62) -> begin
(unlabel t)
end
| _49_66 -> begin
t
end))

# 60 "FStar.Parser.Desugar.fst"
let kind_star : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _130_17 = (let _130_16 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_130_16))
in (FStar_Parser_AST.mk_term _130_17 r FStar_Parser_AST.Kind)))

# 63 "FStar.Parser.Desugar.fst"
let compile_op : Prims.int  ->  Prims.string  ->  Prims.string = (fun arity s -> (
# 64 "FStar.Parser.Desugar.fst"
let name_of_char = (fun _49_2 -> (match (_49_2) with
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
| _49_89 -> begin
"UNKNOWN"
end))
in (
# 83 "FStar.Parser.Desugar.fst"
let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _130_28 = (let _130_26 = (FStar_Util.char_at s i)
in (name_of_char _130_26))
in (let _130_27 = (aux (i + 1))
in (_130_28)::_130_27))
end)
in (let _130_30 = (let _130_29 = (aux 0)
in (FStar_String.concat "_" _130_29))
in (Prims.strcat "op_" _130_30)))))

# 89 "FStar.Parser.Desugar.fst"
let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.lident = (fun n s r -> (let _130_40 = (let _130_39 = (let _130_38 = (let _130_37 = (compile_op n s)
in (_130_37, r))
in (FStar_Absyn_Syntax.mk_ident _130_38))
in (_130_39)::[])
in (FStar_All.pipe_right _130_40 FStar_Absyn_Syntax.lid_of_ids)))

# 91 "FStar.Parser.Desugar.fst"
let op_as_vlid : FStar_Parser_DesugarEnv.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Ident.lident Prims.option = (fun env arity rng s -> (
# 92 "FStar.Parser.Desugar.fst"
let r = (fun l -> (let _130_51 = (FStar_Ident.set_lid_range l rng)
in Some (_130_51)))
in (
# 93 "FStar.Parser.Desugar.fst"
let fallback = (fun _49_103 -> (match (()) with
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
| _49_125 -> begin
None
end)
end))
in (match ((let _130_54 = (compile_op_lid arity s rng)
in (FStar_Parser_DesugarEnv.try_lookup_lid env _130_54))) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _49_136); FStar_Absyn_Syntax.tk = _49_133; FStar_Absyn_Syntax.pos = _49_131; FStar_Absyn_Syntax.fvs = _49_129; FStar_Absyn_Syntax.uvs = _49_127}) -> begin
Some (fv.FStar_Absyn_Syntax.v)
end
| _49_142 -> begin
(fallback ())
end))))

# 121 "FStar.Parser.Desugar.fst"
let op_as_tylid : FStar_Parser_DesugarEnv.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Ident.lident Prims.option = (fun env arity rng s -> (
# 122 "FStar.Parser.Desugar.fst"
let r = (fun l -> (let _130_65 = (FStar_Ident.set_lid_range l rng)
in Some (_130_65)))
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
(match ((let _130_66 = (compile_op_lid arity s rng)
in (FStar_Parser_DesugarEnv.try_lookup_typ_name env _130_66))) with
| Some ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (ftv); FStar_Absyn_Syntax.tk = _49_165; FStar_Absyn_Syntax.pos = _49_163; FStar_Absyn_Syntax.fvs = _49_161; FStar_Absyn_Syntax.uvs = _49_159}) -> begin
Some (ftv.FStar_Absyn_Syntax.v)
end
| _49_171 -> begin
None
end)
end)))

# 138 "FStar.Parser.Desugar.fst"
let rec is_type : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> if (t.FStar_Parser_AST.level = FStar_Parser_AST.Type) then begin
true
end else begin
(match ((let _130_73 = (unparen t)
in _130_73.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
true
end
| FStar_Parser_AST.Labeled (_49_176) -> begin
true
end
| FStar_Parser_AST.Op ("*", hd::_49_180) -> begin
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
| _49_231 -> begin
true
end)
end
| (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Sum (_)) | (FStar_Parser_AST.Refine (_)) | (FStar_Parser_AST.Tvar (_)) | (FStar_Parser_AST.NamedTyp (_)) -> begin
true
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) when ((FStar_List.length l.FStar_Ident.ns) = 0) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env l.FStar_Ident.ident)) with
| Some (_49_254) -> begin
true
end
| _49_257 -> begin
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
| FStar_Parser_AST.Product (_49_298, t) -> begin
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
| FStar_Parser_AST.PatTvar (id, _49_324) -> begin
(
# 186 "FStar.Parser.Desugar.fst"
let _49_330 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_49_330) with
| (env, _49_329) -> begin
(aux env pats)
end))
end
| FStar_Parser_AST.PatAscribed (p, tm) -> begin
(
# 189 "FStar.Parser.Desugar.fst"
let env = if (is_kind env tm) then begin
(match (p.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatVar (id, _)) | (FStar_Parser_AST.PatTvar (id, _)) -> begin
(let _130_78 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (FStar_All.pipe_right _130_78 Prims.fst))
end
| _49_345 -> begin
env
end)
end else begin
env
end
in (aux env pats))
end
| _49_348 -> begin
false
end)
end))
in (aux env pats))
end
| FStar_Parser_AST.Let (false, ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_49_353); FStar_Parser_AST.prange = _49_351}, _49_357)::[], t) -> begin
(is_type env t)
end
| FStar_Parser_AST.Let (false, ({FStar_Parser_AST.pat = FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_49_369); FStar_Parser_AST.prange = _49_367}, _49_373); FStar_Parser_AST.prange = _49_365}, _49_378)::[], t) -> begin
(is_type env t)
end
| FStar_Parser_AST.Let (false, ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_49_388); FStar_Parser_AST.prange = _49_386}, _49_392)::[], t) -> begin
(is_type env t)
end
| _49_399 -> begin
false
end)
end)
and is_kind : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> if (t.FStar_Parser_AST.level = FStar_Parser_AST.Kind) then begin
true
end else begin
(match ((let _130_81 = (unparen t)
in _130_81.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Name ({FStar_Ident.ns = _49_408; FStar_Ident.ident = _49_406; FStar_Ident.nsstr = _49_404; FStar_Ident.str = "Type"}) -> begin
true
end
| FStar_Parser_AST.Product (_49_412, t) -> begin
(is_kind env t)
end
| FStar_Parser_AST.Paren (t) -> begin
(is_kind env t)
end
| (FStar_Parser_AST.Construct (l, _)) | (FStar_Parser_AST.Name (l)) -> begin
(FStar_Parser_DesugarEnv.is_kind_abbrev env l)
end
| _49_425 -> begin
false
end)
end)

# 215 "FStar.Parser.Desugar.fst"
let rec is_type_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  Prims.bool = (fun env b -> if (b.FStar_Parser_AST.blevel = FStar_Parser_AST.Formula) then begin
(match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_49_429) -> begin
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
| FStar_Parser_AST.Variable (_49_444) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected binder without annotation", b.FStar_Parser_AST.brange))))
end
| FStar_Parser_AST.TVariable (_49_447) -> begin
false
end
| FStar_Parser_AST.TAnnotated (_49_450) -> begin
true
end
| (FStar_Parser_AST.Annotated (_, t)) | (FStar_Parser_AST.NoName (t)) -> begin
(is_kind env t)
end)
end)

# 230 "FStar.Parser.Desugar.fst"
let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _130_92 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _130_92)))

# 234 "FStar.Parser.Desugar.fst"
let rec free_type_vars_b : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_DesugarEnv.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_49_466) -> begin
(env, [])
end
| FStar_Parser_AST.TVariable (x) -> begin
(
# 237 "FStar.Parser.Desugar.fst"
let _49_473 = (FStar_Parser_DesugarEnv.push_local_tbinding env x)
in (match (_49_473) with
| (env, _49_472) -> begin
(env, (x)::[])
end))
end
| FStar_Parser_AST.Annotated (_49_475, term) -> begin
(let _130_99 = (free_type_vars env term)
in (env, _130_99))
end
| FStar_Parser_AST.TAnnotated (id, _49_481) -> begin
(
# 242 "FStar.Parser.Desugar.fst"
let _49_487 = (FStar_Parser_DesugarEnv.push_local_tbinding env id)
in (match (_49_487) with
| (env, _49_486) -> begin
(env, [])
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _130_100 = (free_type_vars env t)
in (env, _130_100))
end))
and free_type_vars : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _130_103 = (unparen t)
in _130_103.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env a)) with
| None -> begin
(a)::[]
end
| _49_496 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.Labeled (t, _, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_49_532, ts) -> begin
(FStar_List.collect (fun _49_539 -> (match (_49_539) with
| (t, _49_538) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_49_541, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _49_548) -> begin
(let _130_106 = (free_type_vars env t1)
in (let _130_105 = (free_type_vars env t2)
in (FStar_List.append _130_106 _130_105)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(
# 271 "FStar.Parser.Desugar.fst"
let _49_557 = (free_type_vars_b env b)
in (match (_49_557) with
| (env, f) -> begin
(let _130_107 = (free_type_vars env t)
in (FStar_List.append f _130_107))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(
# 276 "FStar.Parser.Desugar.fst"
let _49_573 = (FStar_List.fold_left (fun _49_566 binder -> (match (_49_566) with
| (env, free) -> begin
(
# 277 "FStar.Parser.Desugar.fst"
let _49_570 = (free_type_vars_b env binder)
in (match (_49_570) with
| (env, f) -> begin
(env, (FStar_List.append f free))
end))
end)) (env, []) binders)
in (match (_49_573) with
| (env, free) -> begin
(let _130_110 = (free_type_vars env body)
in (FStar_List.append free _130_110))
end))
end
| FStar_Parser_AST.Project (t, _49_576) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) -> begin
[]
end
| (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
(FStar_Parser_AST.error "Unexpected type in free_type_vars computation" t t.FStar_Parser_AST.range)
end))

# 294 "FStar.Parser.Desugar.fst"
let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (
# 295 "FStar.Parser.Desugar.fst"
let rec aux = (fun args t -> (match ((let _130_117 = (unparen t)
in _130_117.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _49_620 -> begin
(t, args)
end))
in (aux [] t)))

# 301 "FStar.Parser.Desugar.fst"
let close : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 302 "FStar.Parser.Desugar.fst"
let ftv = (let _130_122 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _130_122))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 305 "FStar.Parser.Desugar.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _130_126 = (let _130_125 = (let _130_124 = (kind_star x.FStar_Ident.idRange)
in (x, _130_124))
in FStar_Parser_AST.TAnnotated (_130_125))
in (FStar_Parser_AST.mk_binder _130_126 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 306 "FStar.Parser.Desugar.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))

# 309 "FStar.Parser.Desugar.fst"
let close_fun : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (
# 310 "FStar.Parser.Desugar.fst"
let ftv = (let _130_131 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _130_131))
in if ((FStar_List.length ftv) = 0) then begin
t
end else begin
(
# 313 "FStar.Parser.Desugar.fst"
let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _130_135 = (let _130_134 = (let _130_133 = (kind_star x.FStar_Ident.idRange)
in (x, _130_133))
in FStar_Parser_AST.TAnnotated (_130_134))
in (FStar_Parser_AST.mk_binder _130_135 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (
# 314 "FStar.Parser.Desugar.fst"
let t = (match ((let _130_136 = (unlabel t)
in _130_136.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_49_633) -> begin
t
end
| _49_636 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level), t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end)
in (
# 317 "FStar.Parser.Desugar.fst"
let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((binders, t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result)))
end))

# 320 "FStar.Parser.Desugar.fst"
let rec uncurry : FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term) = (fun bs t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (binders, t) -> begin
(uncurry (FStar_List.append bs binders) t)
end
| _49_646 -> begin
(bs, t)
end))

# 324 "FStar.Parser.Desugar.fst"
let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _49_650) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_49_656); FStar_Parser_AST.prange = _49_654}, _49_660) -> begin
true
end
| _49_664 -> begin
false
end))

# 329 "FStar.Parser.Desugar.fst"
let rec destruct_app_pattern : FStar_Parser_DesugarEnv.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 331 "FStar.Parser.Desugar.fst"
let _49_676 = (destruct_app_pattern env is_top_level p)
in (match (_49_676) with
| (name, args, _49_675) -> begin
(name, args, Some (t))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _49_681); FStar_Parser_AST.prange = _49_678}, args) when is_top_level -> begin
(let _130_150 = (let _130_149 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_130_149))
in (_130_150, args, None))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _49_692); FStar_Parser_AST.prange = _49_689}, args) -> begin
(FStar_Util.Inl (id), args, None)
end
| _49_700 -> begin
(FStar_All.failwith "Not an app pattern")
end))

# 340 "FStar.Parser.Desugar.fst"
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
| TBinder (_49_703) -> begin
_49_703
end))

# 342 "FStar.Parser.Desugar.fst"
let ___VBinder____0 = (fun projectee -> (match (projectee) with
| VBinder (_49_706) -> begin
_49_706
end))

# 343 "FStar.Parser.Desugar.fst"
let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_49_709) -> begin
_49_709
end))

# 344 "FStar.Parser.Desugar.fst"
let binder_of_bnd : bnd  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.aqual) = (fun _49_3 -> (match (_49_3) with
| TBinder (a, k, aq) -> begin
(FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k)), aq)
end
| VBinder (x, t, aq) -> begin
(FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), aq)
end
| _49_722 -> begin
(FStar_All.failwith "Impossible")
end))

# 348 "FStar.Parser.Desugar.fst"
let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Absyn_Syntax.arg_qualifier Prims.option = (fun _49_4 -> (match (_49_4) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Absyn_Syntax.Equality)
end
| _49_729 -> begin
None
end))

# 352 "FStar.Parser.Desugar.fst"
let as_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  ((FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd), (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ)) FStar_Util.either  ->  (FStar_Absyn_Syntax.binder * FStar_Parser_DesugarEnv.env) = (fun env imp _49_5 -> (match (_49_5) with
| FStar_Util.Inl (None, k) -> begin
(let _130_203 = (FStar_Absyn_Syntax.null_t_binder k)
in (_130_203, env))
end
| FStar_Util.Inr (None, t) -> begin
(let _130_204 = (FStar_Absyn_Syntax.null_v_binder t)
in (_130_204, env))
end
| FStar_Util.Inl (Some (a), k) -> begin
(
# 356 "FStar.Parser.Desugar.fst"
let _49_748 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_49_748) with
| (env, a) -> begin
((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k)), (trans_aqual imp)), env)
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(
# 359 "FStar.Parser.Desugar.fst"
let _49_756 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_49_756) with
| (env, x) -> begin
((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), (trans_aqual imp)), env)
end))
end))

# 362 "FStar.Parser.Desugar.fst"
type env_t =
FStar_Parser_DesugarEnv.env

# 363 "FStar.Parser.Desugar.fst"
type lenv_t =
(FStar_Absyn_Syntax.btvdef, FStar_Absyn_Syntax.bvvdef) FStar_Util.either Prims.list

# 365 "FStar.Parser.Desugar.fst"
let label_conjuncts : Prims.string  ->  Prims.bool  ->  Prims.string Prims.option  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun tag polarity label_opt f -> (
# 366 "FStar.Parser.Desugar.fst"
let label = (fun f -> (
# 367 "FStar.Parser.Desugar.fst"
let msg = (match (label_opt) with
| Some (l) -> begin
l
end
| _49_766 -> begin
(let _130_215 = (FStar_Range.string_of_range f.FStar_Parser_AST.range)
in (FStar_Util.format2 "%s at %s" tag _130_215))
end)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Labeled ((f, msg, polarity))) f.FStar_Parser_AST.range f.FStar_Parser_AST.level)))
in (
# 373 "FStar.Parser.Desugar.fst"
let rec aux = (fun f -> (match (f.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (g) -> begin
(let _130_219 = (let _130_218 = (aux g)
in FStar_Parser_AST.Paren (_130_218))
in (FStar_Parser_AST.mk_term _130_219 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op ("/\\", f1::f2::[]) -> begin
(let _130_225 = (let _130_224 = (let _130_223 = (let _130_222 = (aux f1)
in (let _130_221 = (let _130_220 = (aux f2)
in (_130_220)::[])
in (_130_222)::_130_221))
in ("/\\", _130_223))
in FStar_Parser_AST.Op (_130_224))
in (FStar_Parser_AST.mk_term _130_225 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _130_229 = (let _130_228 = (let _130_227 = (aux f2)
in (let _130_226 = (aux f3)
in (f1, _130_227, _130_226)))
in FStar_Parser_AST.If (_130_228))
in (FStar_Parser_AST.mk_term _130_229 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Abs (binders, g) -> begin
(let _130_232 = (let _130_231 = (let _130_230 = (aux g)
in (binders, _130_230))
in FStar_Parser_AST.Abs (_130_231))
in (FStar_Parser_AST.mk_term _130_232 f.FStar_Parser_AST.range f.FStar_Parser_AST.level))
end
| _49_788 -> begin
(label f)
end))
in (aux f))))

# 391 "FStar.Parser.Desugar.fst"
let mk_lb : (FStar_Absyn_Syntax.lbname * FStar_Absyn_Syntax.typ * FStar_Absyn_Syntax.exp)  ->  FStar_Absyn_Syntax.letbinding = (fun _49_792 -> (match (_49_792) with
| (n, t, e) -> begin
{FStar_Absyn_Syntax.lbname = n; FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = e}
end))

# 393 "FStar.Parser.Desugar.fst"
let rec desugar_data_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat) = (fun env p -> (
# 394 "FStar.Parser.Desugar.fst"
let resolvex = (fun l e x -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun _49_6 -> (match (_49_6) with
| FStar_Util.Inr (y) -> begin
(y.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText)
end
| _49_803 -> begin
false
end))))) with
| Some (FStar_Util.Inr (y)) -> begin
(l, e, y)
end
| _49_808 -> begin
(
# 398 "FStar.Parser.Desugar.fst"
let _49_811 = (FStar_Parser_DesugarEnv.push_local_vbinding e x)
in (match (_49_811) with
| (e, x) -> begin
((FStar_Util.Inr (x))::l, e, x)
end))
end))
in (
# 400 "FStar.Parser.Desugar.fst"
let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun _49_7 -> (match (_49_7) with
| FStar_Util.Inl (b) -> begin
(b.FStar_Absyn_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText)
end
| _49_820 -> begin
false
end))))) with
| Some (FStar_Util.Inl (b)) -> begin
(l, e, b)
end
| _49_825 -> begin
(
# 404 "FStar.Parser.Desugar.fst"
let _49_828 = (FStar_Parser_DesugarEnv.push_local_tbinding e a)
in (match (_49_828) with
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
let _49_850 = (aux loc env p)
in (match (_49_850) with
| (loc, env, var, p, _49_849) -> begin
(
# 413 "FStar.Parser.Desugar.fst"
let _49_867 = (FStar_List.fold_left (fun _49_854 p -> (match (_49_854) with
| (loc, env, ps) -> begin
(
# 414 "FStar.Parser.Desugar.fst"
let _49_863 = (aux loc env p)
in (match (_49_863) with
| (loc, env, _49_859, p, _49_862) -> begin
(loc, env, (p)::ps)
end))
end)) (loc, env, []) ps)
in (match (_49_867) with
| (loc, env, ps) -> begin
(
# 416 "FStar.Parser.Desugar.fst"
let pat = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in (
# 417 "FStar.Parser.Desugar.fst"
let _49_869 = (let _130_304 = (FStar_Absyn_Syntax.pat_vars pat)
in (Prims.ignore _130_304))
in (loc, env, var, pat, false)))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(
# 421 "FStar.Parser.Desugar.fst"
let p = if (is_kind env t) then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatTvar (_49_876) -> begin
p
end
| FStar_Parser_AST.PatVar (x, imp) -> begin
(
# 424 "FStar.Parser.Desugar.fst"
let _49_882 = p
in {FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar ((x, imp)); FStar_Parser_AST.prange = _49_882.FStar_Parser_AST.prange})
end
| _49_885 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end)
end else begin
p
end
in (
# 427 "FStar.Parser.Desugar.fst"
let _49_892 = (aux loc env p)
in (match (_49_892) with
| (loc, env', binder, p, imp) -> begin
(
# 428 "FStar.Parser.Desugar.fst"
let binder = (match (binder) with
| LetBinder (_49_894) -> begin
(FStar_All.failwith "impossible")
end
| TBinder (x, _49_898, aq) -> begin
(let _130_306 = (let _130_305 = (desugar_kind env t)
in (x, _130_305, aq))
in TBinder (_130_306))
end
| VBinder (x, _49_904, aq) -> begin
(
# 432 "FStar.Parser.Desugar.fst"
let t = (close_fun env t)
in (let _130_308 = (let _130_307 = (desugar_typ env t)
in (x, _130_307, aq))
in VBinder (_130_308)))
end)
in (loc, env', binder, p, imp))
end)))
end
| FStar_Parser_AST.PatTvar (a, imp) -> begin
(
# 437 "FStar.Parser.Desugar.fst"
let aq = if imp then begin
Some (imp_tag)
end else begin
None
end
in if (a.FStar_Ident.idText = "\'_") then begin
(
# 439 "FStar.Parser.Desugar.fst"
let a = (FStar_All.pipe_left FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _130_309 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_twild ((FStar_Absyn_Util.bvd_to_bvar_s a FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((a, FStar_Absyn_Syntax.kun, aq)), _130_309, imp)))
end else begin
(
# 441 "FStar.Parser.Desugar.fst"
let _49_919 = (resolvea loc env a)
in (match (_49_919) with
| (loc, env, abvd) -> begin
(let _130_310 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_tvar ((FStar_Absyn_Util.bvd_to_bvar_s abvd FStar_Absyn_Syntax.kun))))
in (loc, env, TBinder ((abvd, FStar_Absyn_Syntax.kun, aq)), _130_310, imp))
end))
end)
end
| FStar_Parser_AST.PatWild -> begin
(
# 445 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (
# 446 "FStar.Parser.Desugar.fst"
let y = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _130_311 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_wild ((FStar_Absyn_Util.bvd_to_bvar_s y FStar_Absyn_Syntax.tun))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _130_311, false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(
# 450 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _130_312 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_constant (c)))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _130_312, false)))
end
| FStar_Parser_AST.PatVar (x, imp) -> begin
(
# 454 "FStar.Parser.Desugar.fst"
let aq = if imp then begin
Some (imp_tag)
end else begin
None
end
in (
# 455 "FStar.Parser.Desugar.fst"
let _49_934 = (resolvex loc env x)
in (match (_49_934) with
| (loc, env, xbvd) -> begin
(let _130_313 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_var ((FStar_Absyn_Util.bvd_to_bvar_s xbvd FStar_Absyn_Syntax.tun))))
in (loc, env, VBinder ((xbvd, FStar_Absyn_Syntax.tun, aq)), _130_313, imp))
end)))
end
| FStar_Parser_AST.PatName (l) -> begin
(
# 459 "FStar.Parser.Desugar.fst"
let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (
# 460 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _130_314 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons ((l, Some (FStar_Absyn_Syntax.Data_ctor), []))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _130_314, false))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _49_940}, args) -> begin
(
# 464 "FStar.Parser.Desugar.fst"
let _49_962 = (FStar_List.fold_right (fun arg _49_951 -> (match (_49_951) with
| (loc, env, args) -> begin
(
# 465 "FStar.Parser.Desugar.fst"
let _49_958 = (aux loc env arg)
in (match (_49_958) with
| (loc, env, _49_955, arg, imp) -> begin
(loc, env, ((arg, imp))::args)
end))
end)) args (loc, env, []))
in (match (_49_962) with
| (loc, env, args) -> begin
(
# 467 "FStar.Parser.Desugar.fst"
let l = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (
# 468 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _130_317 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons ((l, Some (FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _130_317, false))))
end))
end
| FStar_Parser_AST.PatApp (_49_966) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(
# 474 "FStar.Parser.Desugar.fst"
let _49_986 = (FStar_List.fold_right (fun pat _49_974 -> (match (_49_974) with
| (loc, env, pats) -> begin
(
# 475 "FStar.Parser.Desugar.fst"
let _49_982 = (aux loc env pat)
in (match (_49_982) with
| (loc, env, _49_978, pat, _49_981) -> begin
(loc, env, (pat)::pats)
end))
end)) pats (loc, env, []))
in (match (_49_986) with
| (loc, env, pats) -> begin
(
# 477 "FStar.Parser.Desugar.fst"
let pat = (let _130_324 = (let _130_323 = (let _130_322 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _130_322))
in (FStar_All.pipe_left _130_323 (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv FStar_Absyn_Const.nil_lid), Some (FStar_Absyn_Syntax.Data_ctor), [])))))
in (FStar_List.fold_right (fun hd tl -> (
# 478 "FStar.Parser.Desugar.fst"
let r = (FStar_Range.union_ranges hd.FStar_Absyn_Syntax.p tl.FStar_Absyn_Syntax.p)
in (FStar_All.pipe_left (pos_r r) (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv FStar_Absyn_Const.cons_lid), Some (FStar_Absyn_Syntax.Data_ctor), ((hd, false))::((tl, false))::[])))))) pats _130_324))
in (
# 481 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), pat, false)))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(
# 485 "FStar.Parser.Desugar.fst"
let _49_1012 = (FStar_List.fold_left (fun _49_999 p -> (match (_49_999) with
| (loc, env, pats) -> begin
(
# 486 "FStar.Parser.Desugar.fst"
let _49_1008 = (aux loc env p)
in (match (_49_1008) with
| (loc, env, _49_1004, pat, _49_1007) -> begin
(loc, env, ((pat, false))::pats)
end))
end)) (loc, env, []) args)
in (match (_49_1012) with
| (loc, env, args) -> begin
(
# 488 "FStar.Parser.Desugar.fst"
let args = (FStar_List.rev args)
in (
# 489 "FStar.Parser.Desugar.fst"
let l = if dep then begin
(FStar_Absyn_Util.mk_dtuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end else begin
(FStar_Absyn_Util.mk_tuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end
in (
# 491 "FStar.Parser.Desugar.fst"
let constr = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (
# 492 "FStar.Parser.Desugar.fst"
let l = (match (constr.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_fvar (v, _49_1018) -> begin
v
end
| _49_1022 -> begin
(FStar_All.failwith "impossible")
end)
in (
# 495 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.new_bvd (Some (p.FStar_Parser_AST.prange)))
in (let _130_327 = (FStar_All.pipe_left pos (FStar_Absyn_Syntax.Pat_cons ((l, Some (FStar_Absyn_Syntax.Data_ctor), args))))
in (loc, env, VBinder ((x, FStar_Absyn_Syntax.tun, None)), _130_327, false)))))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern", p.FStar_Parser_AST.prange))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(
# 502 "FStar.Parser.Desugar.fst"
let _49_1032 = (FStar_List.hd fields)
in (match (_49_1032) with
| (f, _49_1031) -> begin
(
# 503 "FStar.Parser.Desugar.fst"
let _49_1036 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_49_1036) with
| (record, _49_1035) -> begin
(
# 504 "FStar.Parser.Desugar.fst"
let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _49_1039 -> (match (_49_1039) with
| (f, p) -> begin
(let _130_329 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.qualify_field_to_record env record) f)
in (_130_329, p))
end))))
in (
# 506 "FStar.Parser.Desugar.fst"
let args = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _49_1044 -> (match (_49_1044) with
| (f, _49_1043) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _49_1048 -> (match (_49_1048) with
| (g, _49_1047) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_49_1051, p) -> begin
p
end)
end))))
in (
# 510 "FStar.Parser.Desugar.fst"
let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_DesugarEnv.constrname)) p.FStar_Parser_AST.prange), args))) p.FStar_Parser_AST.prange)
in (
# 511 "FStar.Parser.Desugar.fst"
let _49_1063 = (aux loc env app)
in (match (_49_1063) with
| (env, e, b, p, _49_1062) -> begin
(
# 512 "FStar.Parser.Desugar.fst"
let p = (match (p.FStar_Absyn_Syntax.v) with
| FStar_Absyn_Syntax.Pat_cons (fv, _49_1066, args) -> begin
(let _130_337 = (let _130_336 = (let _130_335 = (let _130_334 = (let _130_333 = (let _130_332 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_DesugarEnv.typename, _130_332))
in FStar_Absyn_Syntax.Record_ctor (_130_333))
in Some (_130_334))
in (fv, _130_335, args))
in FStar_Absyn_Syntax.Pat_cons (_130_336))
in (FStar_All.pipe_left pos _130_337))
end
| _49_1071 -> begin
p
end)
in (env, e, b, p, false))
end)))))
end))
end))
end))))
in (
# 517 "FStar.Parser.Desugar.fst"
let _49_1080 = (aux [] env p)
in (match (_49_1080) with
| (_49_1074, env, b, p, _49_1079) -> begin
(env, b, p)
end))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat Prims.option) = (fun top env p -> if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatVar (x, _49_1086) -> begin
(let _130_343 = (let _130_342 = (let _130_341 = (FStar_Parser_DesugarEnv.qualify env x)
in (_130_341, FStar_Absyn_Syntax.tun))
in LetBinder (_130_342))
in (env, _130_343, None))
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _49_1093); FStar_Parser_AST.prange = _49_1090}, t) -> begin
(let _130_347 = (let _130_346 = (let _130_345 = (FStar_Parser_DesugarEnv.qualify env x)
in (let _130_344 = (desugar_typ env t)
in (_130_345, _130_344)))
in LetBinder (_130_346))
in (env, _130_347, None))
end
| _49_1101 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected pattern at the top-level", p.FStar_Parser_AST.prange))))
end)
end else begin
(
# 528 "FStar.Parser.Desugar.fst"
let _49_1105 = (desugar_data_pat env p)
in (match (_49_1105) with
| (env, binder, p) -> begin
(
# 529 "FStar.Parser.Desugar.fst"
let p = (match (p.FStar_Absyn_Syntax.v) with
| (FStar_Absyn_Syntax.Pat_var (_)) | (FStar_Absyn_Syntax.Pat_tvar (_)) | (FStar_Absyn_Syntax.Pat_wild (_)) -> begin
None
end
| _49_1116 -> begin
Some (p)
end)
in (env, binder, p))
end))
end)
and desugar_binding_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Absyn_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Absyn_Syntax.pat) = (fun _49_1120 env pat -> (
# 539 "FStar.Parser.Desugar.fst"
let _49_1128 = (desugar_data_pat env pat)
in (match (_49_1128) with
| (env, _49_1126, pat) -> begin
(env, pat)
end)))
and desugar_match_pat : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Absyn_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_typ_or_exp : env_t  ->  FStar_Parser_AST.term  ->  (FStar_Absyn_Syntax.typ, FStar_Absyn_Syntax.exp) FStar_Util.either = (fun env t -> if (is_type env t) then begin
(let _130_357 = (desugar_typ env t)
in FStar_Util.Inl (_130_357))
end else begin
(let _130_358 = (desugar_exp env t)
in FStar_Util.Inr (_130_358))
end)
and desugar_exp : env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.exp = (fun env e -> (desugar_exp_maybe_top false env e))
and desugar_exp_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.exp = (fun top_level env top -> (
# 552 "FStar.Parser.Desugar.fst"
let pos = (fun e -> (e None top.FStar_Parser_AST.range))
in (
# 553 "FStar.Parser.Desugar.fst"
let setpos = (fun e -> (
# 553 "FStar.Parser.Desugar.fst"
let _49_1142 = e
in {FStar_Absyn_Syntax.n = _49_1142.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _49_1142.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _49_1142.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _49_1142.FStar_Absyn_Syntax.uvs}))
in (match ((let _130_378 = (unparen top)
in _130_378.FStar_Parser_AST.tm)) with
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
# 561 "FStar.Parser.Desugar.fst"
let op = (FStar_Absyn_Util.fvar None l (FStar_Ident.range_of_lid l))
in (
# 562 "FStar.Parser.Desugar.fst"
let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _130_382 = (desugar_typ_or_exp env t)
in (_130_382, None)))))
in (let _130_383 = (FStar_Absyn_Util.mk_exp_app op args)
in (FStar_All.pipe_left setpos _130_383))))
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
(let _130_384 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_lid env) l)
in (FStar_All.pipe_left setpos _130_384))
end
end
| FStar_Parser_AST.Construct (l, args) -> begin
(
# 577 "FStar.Parser.Desugar.fst"
let dt = (let _130_389 = (let _130_388 = (let _130_387 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_datacon env) l)
in (_130_387, Some (FStar_Absyn_Syntax.Data_ctor)))
in (FStar_Absyn_Syntax.mk_Exp_fvar _130_388))
in (FStar_All.pipe_left pos _130_389))
in (match (args) with
| [] -> begin
dt
end
| _49_1169 -> begin
(
# 581 "FStar.Parser.Desugar.fst"
let args = (FStar_List.map (fun _49_1172 -> (match (_49_1172) with
| (t, imp) -> begin
(
# 582 "FStar.Parser.Desugar.fst"
let te = (desugar_typ_or_exp env t)
in (arg_withimp_e imp te))
end)) args)
in (let _130_394 = (let _130_393 = (let _130_392 = (let _130_391 = (FStar_Absyn_Util.mk_exp_app dt args)
in (_130_391, FStar_Absyn_Syntax.Data_app))
in FStar_Absyn_Syntax.Meta_desugared (_130_392))
in (FStar_Absyn_Syntax.mk_Exp_meta _130_393))
in (FStar_All.pipe_left setpos _130_394)))
end))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(
# 588 "FStar.Parser.Desugar.fst"
let _49_1209 = (FStar_List.fold_left (fun _49_1181 pat -> (match (_49_1181) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatTvar (a, imp); FStar_Parser_AST.prange = _49_1184}, t) -> begin
(
# 591 "FStar.Parser.Desugar.fst"
let ftvs = (let _130_397 = (free_type_vars env t)
in (FStar_List.append _130_397 ftvs))
in (let _130_399 = (let _130_398 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _130_398))
in (_130_399, ftvs)))
end
| FStar_Parser_AST.PatTvar (a, _49_1196) -> begin
(let _130_401 = (let _130_400 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (FStar_All.pipe_left Prims.fst _130_400))
in (_130_401, ftvs))
end
| FStar_Parser_AST.PatAscribed (_49_1200, t) -> begin
(let _130_403 = (let _130_402 = (free_type_vars env t)
in (FStar_List.append _130_402 ftvs))
in (env, _130_403))
end
| _49_1205 -> begin
(env, ftvs)
end)
end)) (env, []) binders)
in (match (_49_1209) with
| (_49_1207, ftv) -> begin
(
# 596 "FStar.Parser.Desugar.fst"
let ftv = (sort_ftv ftv)
in (
# 597 "FStar.Parser.Desugar.fst"
let binders = (let _130_405 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar ((a, true))) top.FStar_Parser_AST.range))))
in (FStar_List.append _130_405 binders))
in (
# 599 "FStar.Parser.Desugar.fst"
let rec aux = (fun env bs sc_pat_opt _49_8 -> (match (_49_8) with
| [] -> begin
(
# 601 "FStar.Parser.Desugar.fst"
let body = (desugar_exp env body)
in (
# 602 "FStar.Parser.Desugar.fst"
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
# 608 "FStar.Parser.Desugar.fst"
let _49_1232 = (desugar_binding_pat env p)
in (match (_49_1232) with
| (env, b, pat) -> begin
(
# 609 "FStar.Parser.Desugar.fst"
let _49_1292 = (match (b) with
| LetBinder (_49_1234) -> begin
(FStar_All.failwith "Impossible")
end
| TBinder (a, k, aq) -> begin
(let _130_414 = (binder_of_bnd b)
in (_130_414, sc_pat_opt))
end
| VBinder (x, t, aq) -> begin
(
# 613 "FStar.Parser.Desugar.fst"
let b = (FStar_Absyn_Util.bvd_to_bvar_s x t)
in (
# 614 "FStar.Parser.Desugar.fst"
let sc_pat_opt = (match ((pat, sc_pat_opt)) with
| (None, _49_1249) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _130_416 = (let _130_415 = (FStar_Absyn_Util.bvar_to_exp b)
in (_130_415, p))
in Some (_130_416))
end
| (Some (p), Some (sc, p')) -> begin
(match ((sc.FStar_Absyn_Syntax.n, p'.FStar_Absyn_Syntax.v)) with
| (FStar_Absyn_Syntax.Exp_bvar (_49_1263), _49_1266) -> begin
(
# 620 "FStar.Parser.Desugar.fst"
let tup = (FStar_Absyn_Util.mk_tuple_data_lid 2 top.FStar_Parser_AST.range)
in (
# 621 "FStar.Parser.Desugar.fst"
let sc = (let _130_423 = (let _130_422 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _130_421 = (let _130_420 = (FStar_Absyn_Syntax.varg sc)
in (let _130_419 = (let _130_418 = (let _130_417 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _130_417))
in (_130_418)::[])
in (_130_420)::_130_419))
in (_130_422, _130_421)))
in (FStar_Absyn_Syntax.mk_Exp_app _130_423 None top.FStar_Parser_AST.range))
in (
# 622 "FStar.Parser.Desugar.fst"
let p = (let _130_424 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv tup), Some (FStar_Absyn_Syntax.Data_ctor), ((p', false))::((p, false))::[]))) None _130_424))
in Some ((sc, p)))))
end
| (FStar_Absyn_Syntax.Exp_app (_49_1272, args), FStar_Absyn_Syntax.Pat_cons (_49_1277, _49_1279, pats)) -> begin
(
# 625 "FStar.Parser.Desugar.fst"
let tup = (FStar_Absyn_Util.mk_tuple_data_lid (1 + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (
# 626 "FStar.Parser.Desugar.fst"
let sc = (let _130_430 = (let _130_429 = (FStar_Absyn_Util.fvar (Some (FStar_Absyn_Syntax.Data_ctor)) tup top.FStar_Parser_AST.range)
in (let _130_428 = (let _130_427 = (let _130_426 = (let _130_425 = (FStar_Absyn_Util.bvar_to_exp b)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _130_425))
in (_130_426)::[])
in (FStar_List.append args _130_427))
in (_130_429, _130_428)))
in (FStar_Absyn_Syntax.mk_Exp_app _130_430 None top.FStar_Parser_AST.range))
in (
# 627 "FStar.Parser.Desugar.fst"
let p = (let _130_431 = (FStar_Range.union_ranges p'.FStar_Absyn_Syntax.p p.FStar_Absyn_Syntax.p)
in (FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv tup), Some (FStar_Absyn_Syntax.Data_ctor), (FStar_List.append pats (((p, false))::[]))))) None _130_431))
in Some ((sc, p)))))
end
| _49_1288 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((FStar_Util.Inr (b), aq), sc_pat_opt)))
end)
in (match (_49_1292) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = _49_1296; FStar_Parser_AST.level = _49_1294}, arg, _49_1302) when ((FStar_Ident.lid_equals a FStar_Absyn_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Absyn_Const.assume_lid)) -> begin
(
# 638 "FStar.Parser.Desugar.fst"
let phi = (desugar_formula env arg)
in (let _130_441 = (let _130_440 = (let _130_439 = (FStar_Absyn_Util.fvar None a (FStar_Ident.range_of_lid a))
in (let _130_438 = (let _130_437 = (FStar_All.pipe_left FStar_Absyn_Syntax.targ phi)
in (let _130_436 = (let _130_435 = (let _130_434 = (FStar_Absyn_Syntax.mk_Exp_constant FStar_Const.Const_unit None top.FStar_Parser_AST.range)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _130_434))
in (_130_435)::[])
in (_130_437)::_130_436))
in (_130_439, _130_438)))
in (FStar_Absyn_Syntax.mk_Exp_app _130_440))
in (FStar_All.pipe_left pos _130_441)))
end
| FStar_Parser_AST.App (_49_1307) -> begin
(
# 644 "FStar.Parser.Desugar.fst"
let rec aux = (fun args e -> (match ((let _130_446 = (unparen e)
in _130_446.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(
# 646 "FStar.Parser.Desugar.fst"
let arg = (let _130_447 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _130_447))
in (aux ((arg)::args) e))
end
| _49_1319 -> begin
(
# 649 "FStar.Parser.Desugar.fst"
let head = (desugar_exp env e)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_app (head, args))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _130_453 = (let _130_452 = (let _130_451 = (let _130_450 = (desugar_exp env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range), t1))::[], t2))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in (_130_450, FStar_Absyn_Syntax.Sequence))
in FStar_Absyn_Syntax.Meta_desugared (_130_451))
in (FStar_Absyn_Syntax.mk_Exp_meta _130_452))
in (FStar_All.pipe_left setpos _130_453))
end
| FStar_Parser_AST.Let (is_rec, (pat, _snd)::_tl, body) -> begin
(
# 658 "FStar.Parser.Desugar.fst"
let ds_let_rec = (fun _49_1335 -> (match (()) with
| () -> begin
(
# 659 "FStar.Parser.Desugar.fst"
let bindings = ((pat, _snd))::_tl
in (
# 660 "FStar.Parser.Desugar.fst"
let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _49_1339 -> (match (_49_1339) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _130_457 = (destruct_app_pattern env top_level p)
in (_130_457, def))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _130_458 = (destruct_app_pattern env top_level p)
in (_130_458, def))
end
| _49_1345 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _49_1350); FStar_Parser_AST.prange = _49_1347}, t) -> begin
if top_level then begin
(let _130_461 = (let _130_460 = (let _130_459 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_130_459))
in (_130_460, [], Some (t)))
in (_130_461, def))
end else begin
((FStar_Util.Inl (id), [], Some (t)), def)
end
end
| FStar_Parser_AST.PatVar (id, _49_1359) -> begin
if top_level then begin
(let _130_464 = (let _130_463 = (let _130_462 = (FStar_Parser_DesugarEnv.qualify env id)
in FStar_Util.Inr (_130_462))
in (_130_463, [], None))
in (_130_464, def))
end else begin
((FStar_Util.Inl (id), [], None), def)
end
end
| _49_1363 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected let binding", p.FStar_Parser_AST.prange))))
end)
end)
end
end))))
in (
# 676 "FStar.Parser.Desugar.fst"
let _49_1389 = (FStar_List.fold_left (fun _49_1367 _49_1376 -> (match ((_49_1367, _49_1376)) with
| ((env, fnames), ((f, _49_1370, _49_1372), _49_1375)) -> begin
(
# 678 "FStar.Parser.Desugar.fst"
let _49_1386 = (match (f) with
| FStar_Util.Inl (x) -> begin
(
# 680 "FStar.Parser.Desugar.fst"
let _49_1381 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_49_1381) with
| (env, xx) -> begin
(env, FStar_Util.Inl (xx))
end))
end
| FStar_Util.Inr (l) -> begin
(let _130_467 = (FStar_Parser_DesugarEnv.push_rec_binding env (FStar_Parser_DesugarEnv.Binding_let (l)))
in (_130_467, FStar_Util.Inr (l)))
end)
in (match (_49_1386) with
| (env, lbname) -> begin
(env, (lbname)::fnames)
end))
end)) (env, []) funs)
in (match (_49_1389) with
| (env', fnames) -> begin
(
# 685 "FStar.Parser.Desugar.fst"
let fnames = (FStar_List.rev fnames)
in (
# 686 "FStar.Parser.Desugar.fst"
let desugar_one_def = (fun env lbname _49_1400 -> (match (_49_1400) with
| ((_49_1395, args, result_t), def) -> begin
(
# 687 "FStar.Parser.Desugar.fst"
let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(let _130_474 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed ((def, t))) _130_474 FStar_Parser_AST.Expr))
end)
in (
# 690 "FStar.Parser.Desugar.fst"
let def = (match (args) with
| [] -> begin
def
end
| _49_1407 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.un_curry_abs args def) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
end)
in (
# 693 "FStar.Parser.Desugar.fst"
let body = (desugar_exp env def)
in (mk_lb (lbname, FStar_Absyn_Syntax.tun, body)))))
end))
in (
# 695 "FStar.Parser.Desugar.fst"
let lbs = (FStar_List.map2 (desugar_one_def (if is_rec then begin
env'
end else begin
env
end)) fnames funs)
in (
# 696 "FStar.Parser.Desugar.fst"
let body = (desugar_exp env' body)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((is_rec, lbs), body)))))))
end))))
end))
in (
# 699 "FStar.Parser.Desugar.fst"
let ds_non_rec = (fun pat t1 t2 -> (
# 700 "FStar.Parser.Desugar.fst"
let t1 = (desugar_exp env t1)
in (
# 701 "FStar.Parser.Desugar.fst"
let _49_1420 = (desugar_binding_pat_maybe_top top_level env pat)
in (match (_49_1420) with
| (env, binder, pat) -> begin
(match (binder) with
| TBinder (_49_1422) -> begin
(FStar_All.failwith "Unexpected type binder in let")
end
| LetBinder (l, t) -> begin
(
# 705 "FStar.Parser.Desugar.fst"
let body = (desugar_exp env t2)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Exp_let ((false, ({FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = t; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_ALL_lid; FStar_Absyn_Syntax.lbdef = t1})::[]), body))))
end
| VBinder (x, t, _49_1432) -> begin
(
# 708 "FStar.Parser.Desugar.fst"
let body = (desugar_exp env t2)
in (
# 709 "FStar.Parser.Desugar.fst"
let body = (match (pat) with
| (None) | (Some ({FStar_Absyn_Syntax.v = FStar_Absyn_Syntax.Pat_wild (_); FStar_Absyn_Syntax.sort = _; FStar_Absyn_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _130_486 = (let _130_485 = (FStar_Absyn_Util.bvd_to_exp x t)
in (_130_485, ((pat, None, body))::[]))
in (FStar_Absyn_Syntax.mk_Exp_match _130_486 None body.FStar_Absyn_Syntax.pos))
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
(let _130_499 = (let _130_498 = (let _130_497 = (desugar_exp env t1)
in (let _130_496 = (let _130_495 = (let _130_491 = (desugar_exp env t2)
in ((FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (true))) None t2.FStar_Parser_AST.range), None, _130_491))
in (let _130_494 = (let _130_493 = (let _130_492 = (desugar_exp env t3)
in ((FStar_Absyn_Util.withinfo (FStar_Absyn_Syntax.Pat_constant (FStar_Const.Const_bool (false))) None t3.FStar_Parser_AST.range), None, _130_492))
in (_130_493)::[])
in (_130_495)::_130_494))
in (_130_497, _130_496)))
in (FStar_Absyn_Syntax.mk_Exp_match _130_498))
in (FStar_All.pipe_left pos _130_499))
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(
# 726 "FStar.Parser.Desugar.fst"
let r = top.FStar_Parser_AST.range
in (
# 727 "FStar.Parser.Desugar.fst"
let handler = (FStar_Parser_AST.mk_function branches r r)
in (
# 728 "FStar.Parser.Desugar.fst"
let body = (FStar_Parser_AST.mk_function ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatConst (FStar_Const.Const_unit)) r), None, e))::[]) r r)
in (
# 729 "FStar.Parser.Desugar.fst"
let a1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (FStar_Absyn_Const.try_with_lid)) r top.FStar_Parser_AST.level), body, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (
# 730 "FStar.Parser.Desugar.fst"
let a2 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((a1, handler, FStar_Parser_AST.Nothing))) r top.FStar_Parser_AST.level)
in (desugar_exp env a2))))))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(
# 734 "FStar.Parser.Desugar.fst"
let desugar_branch = (fun _49_1471 -> (match (_49_1471) with
| (pat, wopt, b) -> begin
(
# 735 "FStar.Parser.Desugar.fst"
let _49_1474 = (desugar_match_pat env pat)
in (match (_49_1474) with
| (env, pat) -> begin
(
# 736 "FStar.Parser.Desugar.fst"
let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _130_502 = (desugar_exp env e)
in Some (_130_502))
end)
in (
# 739 "FStar.Parser.Desugar.fst"
let b = (desugar_exp env b)
in (pat, wopt, b)))
end))
end))
in (let _130_508 = (let _130_507 = (let _130_506 = (desugar_exp env e)
in (let _130_505 = (FStar_List.map desugar_branch branches)
in (_130_506, _130_505)))
in (FStar_Absyn_Syntax.mk_Exp_match _130_507))
in (FStar_All.pipe_left pos _130_508)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(let _130_514 = (let _130_513 = (let _130_512 = (desugar_exp env e)
in (let _130_511 = (desugar_typ env t)
in (_130_512, _130_511, None)))
in (FStar_Absyn_Syntax.mk_Exp_ascribed _130_513))
in (FStar_All.pipe_left pos _130_514))
end
| FStar_Parser_AST.Record (_49_1485, []) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected empty record", top.FStar_Parser_AST.range))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(
# 750 "FStar.Parser.Desugar.fst"
let _49_1496 = (FStar_List.hd fields)
in (match (_49_1496) with
| (f, _49_1495) -> begin
(
# 751 "FStar.Parser.Desugar.fst"
let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (
# 752 "FStar.Parser.Desugar.fst"
let _49_1502 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_record_by_field_name env) f)
in (match (_49_1502) with
| (record, _49_1501) -> begin
(
# 753 "FStar.Parser.Desugar.fst"
let get_field = (fun xopt f -> (
# 754 "FStar.Parser.Desugar.fst"
let fn = f.FStar_Ident.ident
in (
# 755 "FStar.Parser.Desugar.fst"
let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _49_1510 -> (match (_49_1510) with
| (g, _49_1509) -> begin
(
# 756 "FStar.Parser.Desugar.fst"
let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_49_1514, e) -> begin
(let _130_522 = (qfn fn)
in (_130_522, e))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _130_525 = (let _130_524 = (let _130_523 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in (_130_523, top.FStar_Parser_AST.range))
in FStar_Absyn_Syntax.Error (_130_524))
in (Prims.raise _130_525))
end
| Some (x) -> begin
(let _130_526 = (qfn fn)
in (_130_526, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Project ((x, f))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level)))
end)
end))))
in (
# 766 "FStar.Parser.Desugar.fst"
let recterm = (match (eopt) with
| None -> begin
(let _130_531 = (let _130_530 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _49_1526 -> (match (_49_1526) with
| (f, _49_1525) -> begin
(let _130_529 = (let _130_528 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _130_528))
in (_130_529, FStar_Parser_AST.Nothing))
end))))
in (record.FStar_Parser_DesugarEnv.constrname, _130_530))
in FStar_Parser_AST.Construct (_130_531))
end
| Some (e) -> begin
(
# 773 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.genident (Some (e.FStar_Parser_AST.range)))
in (
# 774 "FStar.Parser.Desugar.fst"
let xterm = (let _130_533 = (let _130_532 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_130_532))
in (FStar_Parser_AST.mk_term _130_533 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (
# 775 "FStar.Parser.Desugar.fst"
let record = (let _130_536 = (let _130_535 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map (fun _49_1534 -> (match (_49_1534) with
| (f, _49_1533) -> begin
(get_field (Some (xterm)) f)
end))))
in (None, _130_535))
in FStar_Parser_AST.Record (_130_536))
in FStar_Parser_AST.Let ((false, (((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar ((x, false))) x.FStar_Ident.idRange), e))::[], (FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level))))))
end)
in (
# 778 "FStar.Parser.Desugar.fst"
let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (
# 779 "FStar.Parser.Desugar.fst"
let e = (desugar_exp env recterm)
in (match (e.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Exp_meta (FStar_Absyn_Syntax.Meta_desugared ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Exp_fvar (fv, _49_1557); FStar_Absyn_Syntax.tk = _49_1554; FStar_Absyn_Syntax.pos = _49_1552; FStar_Absyn_Syntax.fvs = _49_1550; FStar_Absyn_Syntax.uvs = _49_1548}, args); FStar_Absyn_Syntax.tk = _49_1546; FStar_Absyn_Syntax.pos = _49_1544; FStar_Absyn_Syntax.fvs = _49_1542; FStar_Absyn_Syntax.uvs = _49_1540}, FStar_Absyn_Syntax.Data_app)) -> begin
(
# 782 "FStar.Parser.Desugar.fst"
let e = (let _130_546 = (let _130_545 = (let _130_544 = (let _130_543 = (let _130_542 = (let _130_541 = (let _130_540 = (let _130_539 = (FStar_All.pipe_right record.FStar_Parser_DesugarEnv.fields (FStar_List.map Prims.fst))
in (record.FStar_Parser_DesugarEnv.typename, _130_539))
in FStar_Absyn_Syntax.Record_ctor (_130_540))
in Some (_130_541))
in (fv, _130_542))
in (FStar_Absyn_Syntax.mk_Exp_fvar _130_543 None e.FStar_Absyn_Syntax.pos))
in (_130_544, args))
in (FStar_Absyn_Syntax.mk_Exp_app _130_545))
in (FStar_All.pipe_left pos _130_546))
in (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((e, FStar_Absyn_Syntax.Data_app)))))
end
| _49_1571 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(
# 790 "FStar.Parser.Desugar.fst"
let _49_1578 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_projector_by_field_name env) f)
in (match (_49_1578) with
| (fieldname, is_rec) -> begin
(
# 791 "FStar.Parser.Desugar.fst"
let e = (desugar_exp env e)
in (
# 792 "FStar.Parser.Desugar.fst"
let fn = (
# 793 "FStar.Parser.Desugar.fst"
let _49_1583 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_49_1583) with
| (ns, _49_1582) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (
# 795 "FStar.Parser.Desugar.fst"
let qual = if is_rec then begin
Some (FStar_Absyn_Syntax.Record_projector (fn))
end else begin
None
end
in (let _130_553 = (let _130_552 = (let _130_551 = (FStar_Absyn_Util.fvar qual fieldname (FStar_Ident.range_of_lid f))
in (let _130_550 = (let _130_549 = (FStar_Absyn_Syntax.varg e)
in (_130_549)::[])
in (_130_551, _130_550)))
in (FStar_Absyn_Syntax.mk_Exp_app _130_552))
in (FStar_All.pipe_left pos _130_553)))))
end))
end
| FStar_Parser_AST.Paren (e) -> begin
(desugar_exp env e)
end
| _49_1589 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end))))
and desugar_typ : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env top -> (
# 806 "FStar.Parser.Desugar.fst"
let wpos = (fun t -> (t None top.FStar_Parser_AST.range))
in (
# 807 "FStar.Parser.Desugar.fst"
let setpos = (fun t -> (
# 807 "FStar.Parser.Desugar.fst"
let _49_1596 = t
in {FStar_Absyn_Syntax.n = _49_1596.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _49_1596.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = top.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _49_1596.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _49_1596.FStar_Absyn_Syntax.uvs}))
in (
# 808 "FStar.Parser.Desugar.fst"
let top = (unparen top)
in (
# 809 "FStar.Parser.Desugar.fst"
let head_and_args = (fun t -> (
# 810 "FStar.Parser.Desugar.fst"
let rec aux = (fun args t -> (match ((let _130_576 = (unparen t)
in _130_576.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux (((arg, imp))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}, (FStar_List.append args' args))
end
| _49_1614 -> begin
(t, args)
end))
in (aux [] t)))
in (match (top.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Absyn_Syntax.tun)
end
| FStar_Parser_AST.Requires (t, lopt) -> begin
(
# 819 "FStar.Parser.Desugar.fst"
let t = (label_conjuncts "pre-condition" true lopt t)
in if (is_type env t) then begin
(desugar_typ env t)
end else begin
(let _130_577 = (desugar_exp env t)
in (FStar_All.pipe_right _130_577 FStar_Absyn_Util.b2t))
end)
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(
# 825 "FStar.Parser.Desugar.fst"
let t = (label_conjuncts "post-condition" false lopt t)
in if (is_type env t) then begin
(desugar_typ env t)
end else begin
(let _130_578 = (desugar_exp env t)
in (FStar_All.pipe_right _130_578 FStar_Absyn_Util.b2t))
end)
end
| FStar_Parser_AST.Op ("*", t1::_49_1628::[]) -> begin
if (is_type env t1) then begin
(
# 831 "FStar.Parser.Desugar.fst"
let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", t1::t2::[]) -> begin
(
# 833 "FStar.Parser.Desugar.fst"
let rest = (flatten t2)
in (t1)::rest)
end
| _49_1643 -> begin
(t)::[]
end))
in (
# 836 "FStar.Parser.Desugar.fst"
let targs = (let _130_583 = (flatten top)
in (FStar_All.pipe_right _130_583 (FStar_List.map (fun t -> (let _130_582 = (desugar_typ env t)
in (FStar_Absyn_Syntax.targ _130_582))))))
in (
# 837 "FStar.Parser.Desugar.fst"
let tup = (let _130_584 = (FStar_Absyn_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _130_584))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))))
end else begin
(let _130_590 = (let _130_589 = (let _130_588 = (let _130_587 = (FStar_Parser_AST.term_to_string t1)
in (FStar_Util.format1 "The operator \"*\" is resolved here as multiplication since \"%s\" is a term, although a type was expected" _130_587))
in (_130_588, top.FStar_Parser_AST.range))
in FStar_Absyn_Syntax.Error (_130_589))
in (Prims.raise _130_590))
end
end
| FStar_Parser_AST.Op ("=!=", args) -> begin
(desugar_typ env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Op (("~", ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Op (("==", args))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))::[]))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_tylid env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(let _130_591 = (desugar_exp env top)
in (FStar_All.pipe_right _130_591 FStar_Absyn_Util.b2t))
end
| Some (l) -> begin
(
# 848 "FStar.Parser.Desugar.fst"
let args = (FStar_List.map (fun t -> (let _130_593 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _130_593))) args)
in (let _130_594 = (FStar_Absyn_Util.ftv l FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _130_594 args)))
end)
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _130_595 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) a)
in (FStar_All.pipe_left setpos _130_595))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) when ((FStar_List.length l.FStar_Ident.ns) = 0) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_typ_var env l.FStar_Ident.ident)) with
| Some (t) -> begin
(setpos t)
end
| None -> begin
(let _130_596 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _130_596))
end)
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(
# 864 "FStar.Parser.Desugar.fst"
let l = (FStar_Absyn_Util.set_lid_range l top.FStar_Parser_AST.range)
in (let _130_597 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _130_597)))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(
# 868 "FStar.Parser.Desugar.fst"
let t = (let _130_598 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) l)
in (FStar_All.pipe_left setpos _130_598))
in (
# 869 "FStar.Parser.Desugar.fst"
let args = (FStar_List.map (fun _49_1679 -> (match (_49_1679) with
| (t, imp) -> begin
(let _130_600 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _130_600))
end)) args)
in (FStar_Absyn_Util.mk_typ_app t args)))
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(
# 873 "FStar.Parser.Desugar.fst"
let rec aux = (fun env bs _49_9 -> (match (_49_9) with
| [] -> begin
(
# 875 "FStar.Parser.Desugar.fst"
let body = (desugar_typ env body)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_lam ((FStar_List.rev bs), body))))
end
| hd::tl -> begin
(
# 878 "FStar.Parser.Desugar.fst"
let _49_1697 = (desugar_binding_pat env hd)
in (match (_49_1697) with
| (env, bnd, pat) -> begin
(match (pat) with
| Some (q) -> begin
(let _130_612 = (let _130_611 = (let _130_610 = (let _130_609 = (FStar_Absyn_Print.pat_to_string q)
in (FStar_Util.format1 "Pattern matching at the type level is not supported; got %s\n" _130_609))
in (_130_610, hd.FStar_Parser_AST.prange))
in FStar_Absyn_Syntax.Error (_130_611))
in (Prims.raise _130_612))
end
| None -> begin
(
# 882 "FStar.Parser.Desugar.fst"
let b = (binder_of_bnd bnd)
in (aux env ((b)::bs) tl))
end)
end))
end))
in (aux env [] binders))
end
| FStar_Parser_AST.App (_49_1703) -> begin
(
# 887 "FStar.Parser.Desugar.fst"
let rec aux = (fun args e -> (match ((let _130_617 = (unparen e)
in _130_617.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, arg, imp) -> begin
(
# 889 "FStar.Parser.Desugar.fst"
let arg = (let _130_618 = (desugar_typ_or_exp env arg)
in (FStar_All.pipe_left (arg_withimp_t imp) _130_618))
in (aux ((arg)::args) e))
end
| _49_1715 -> begin
(
# 892 "FStar.Parser.Desugar.fst"
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
# 900 "FStar.Parser.Desugar.fst"
let _49_1727 = (uncurry binders t)
in (match (_49_1727) with
| (bs, t) -> begin
(
# 901 "FStar.Parser.Desugar.fst"
let rec aux = (fun env bs _49_10 -> (match (_49_10) with
| [] -> begin
(
# 903 "FStar.Parser.Desugar.fst"
let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_fun ((FStar_List.rev bs), cod))))
end
| hd::tl -> begin
(
# 906 "FStar.Parser.Desugar.fst"
let mlenv = (FStar_Parser_DesugarEnv.default_ml env)
in (
# 907 "FStar.Parser.Desugar.fst"
let bb = (desugar_binder mlenv hd)
in (
# 908 "FStar.Parser.Desugar.fst"
let _49_1741 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_49_1741) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_exp_binder env b)) with
| (None, _49_1748) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(
# 916 "FStar.Parser.Desugar.fst"
let _49_1762 = (match ((as_binder env None (FStar_Util.Inr (b)))) with
| ((FStar_Util.Inr (x), _49_1754), env) -> begin
(x, env)
end
| _49_1759 -> begin
(FStar_All.failwith "impossible")
end)
in (match (_49_1762) with
| (b, env) -> begin
(
# 919 "FStar.Parser.Desugar.fst"
let f = if (is_type env f) then begin
(desugar_formula env f)
end else begin
(let _130_629 = (desugar_exp env f)
in (FStar_All.pipe_right _130_629 FStar_Absyn_Util.b2t))
end
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_refine (b, f))))
end))
end)
end
| (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) -> begin
(desugar_typ env t)
end
| FStar_Parser_AST.Ascribed (t, k) -> begin
(let _130_637 = (let _130_636 = (let _130_635 = (desugar_typ env t)
in (let _130_634 = (desugar_kind env k)
in (_130_635, _130_634)))
in (FStar_Absyn_Syntax.mk_Typ_ascribed' _130_636))
in (FStar_All.pipe_left wpos _130_637))
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(
# 931 "FStar.Parser.Desugar.fst"
let _49_1796 = (FStar_List.fold_left (fun _49_1781 b -> (match (_49_1781) with
| (env, tparams, typs) -> begin
(
# 932 "FStar.Parser.Desugar.fst"
let _49_1785 = (desugar_exp_binder env b)
in (match (_49_1785) with
| (xopt, t) -> begin
(
# 933 "FStar.Parser.Desugar.fst"
let _49_1791 = (match (xopt) with
| None -> begin
(let _130_640 = (FStar_Absyn_Util.new_bvd (Some (top.FStar_Parser_AST.range)))
in (env, _130_640))
end
| Some (x) -> begin
(FStar_Parser_DesugarEnv.push_local_vbinding env x)
end)
in (match (_49_1791) with
| (env, x) -> begin
(let _130_644 = (let _130_643 = (let _130_642 = (let _130_641 = (FStar_Absyn_Util.close_with_lam tparams t)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _130_641))
in (_130_642)::[])
in (FStar_List.append typs _130_643))
in (env, (FStar_List.append tparams (((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), None))::[])), _130_644))
end))
end))
end)) (env, [], []) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_49_1796) with
| (env, _49_1794, targs) -> begin
(
# 938 "FStar.Parser.Desugar.fst"
let tup = (let _130_645 = (FStar_Absyn_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) _130_645))
in (FStar_All.pipe_left wpos (FStar_Absyn_Syntax.mk_Typ_app (tup, targs))))
end))
end
| FStar_Parser_AST.Record (_49_1799) -> begin
(FStar_All.failwith "Unexpected record type")
end
| FStar_Parser_AST.Let (false, (x, v)::[], t) -> begin
(
# 945 "FStar.Parser.Desugar.fst"
let let_v = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.let_in_typ)) top.FStar_Parser_AST.range top.FStar_Parser_AST.level), v, FStar_Parser_AST.Nothing))) v.FStar_Parser_AST.range v.FStar_Parser_AST.level)
in (
# 946 "FStar.Parser.Desugar.fst"
let t' = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((let_v, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Abs (((x)::[], t))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level), FStar_Parser_AST.Nothing))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (desugar_typ env t')))
end
| (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.Labeled (_)) -> begin
(desugar_formula env top)
end
| _49_1818 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _49_1820 -> begin
(FStar_Parser_AST.error "Expected a type" top top.FStar_Parser_AST.range)
end))))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.comp = (fun r default_ok env t -> (
# 956 "FStar.Parser.Desugar.fst"
let fail = (fun msg -> (Prims.raise (FStar_Absyn_Syntax.Error ((msg, r)))))
in (
# 957 "FStar.Parser.Desugar.fst"
let pre_process_comp_typ = (fun t -> (
# 958 "FStar.Parser.Desugar.fst"
let _49_1831 = (head_and_args t)
in (match (_49_1831) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(
# 961 "FStar.Parser.Desugar.fst"
let unit = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type), FStar_Parser_AST.Nothing)
in (
# 962 "FStar.Parser.Desugar.fst"
let nil_pat = ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr), FStar_Parser_AST.Nothing)
in (
# 963 "FStar.Parser.Desugar.fst"
let _49_1857 = (FStar_All.pipe_right args (FStar_List.partition (fun _49_1839 -> (match (_49_1839) with
| (arg, _49_1838) -> begin
(match ((let _130_657 = (unparen arg)
in _130_657.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _49_1843; FStar_Parser_AST.level = _49_1841}, _49_1848, _49_1850) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = "decreases")
end
| _49_1854 -> begin
false
end)
end))))
in (match (_49_1857) with
| (decreases_clause, args) -> begin
(
# 967 "FStar.Parser.Desugar.fst"
let args = (match (args) with
| [] -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Not enough arguments to \'Lemma\'", t.FStar_Parser_AST.range))))
end
| ens::[] -> begin
(
# 970 "FStar.Parser.Desugar.fst"
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
# 974 "FStar.Parser.Desugar.fst"
let t = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Construct ((lemma, (FStar_List.append args decreases_clause)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in (desugar_typ env t)))
end))))
end
| FStar_Parser_AST.Name (tot) when (((tot.FStar_Ident.ident.FStar_Ident.idText = "Tot") && (not ((FStar_Parser_DesugarEnv.is_effect_name env FStar_Absyn_Const.effect_Tot_lid)))) && (let _130_658 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Ident.lid_equals _130_658 FStar_Absyn_Const.prims_lid))) -> begin
(
# 981 "FStar.Parser.Desugar.fst"
let args = (FStar_List.map (fun _49_1872 -> (match (_49_1872) with
| (t, imp) -> begin
(let _130_660 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t imp) _130_660))
end)) args)
in (let _130_661 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.effect_Tot_lid FStar_Absyn_Syntax.kun)
in (FStar_Absyn_Util.mk_typ_app _130_661 args)))
end
| _49_1875 -> begin
(desugar_typ env t)
end)
end)))
in (
# 986 "FStar.Parser.Desugar.fst"
let t = (pre_process_comp_typ t)
in (
# 987 "FStar.Parser.Desugar.fst"
let _49_1879 = (FStar_Absyn_Util.head_and_args t)
in (match (_49_1879) with
| (head, args) -> begin
(match ((let _130_663 = (let _130_662 = (FStar_Absyn_Util.compress_typ head)
in _130_662.FStar_Absyn_Syntax.n)
in (_130_663, args))) with
| (FStar_Absyn_Syntax.Typ_const (eff), (FStar_Util.Inl (result_typ), _49_1886)::rest) -> begin
(
# 990 "FStar.Parser.Desugar.fst"
let _49_1926 = (FStar_All.pipe_right rest (FStar_List.partition (fun _49_11 -> (match (_49_11) with
| (FStar_Util.Inr (_49_1892), _49_1895) -> begin
false
end
| (FStar_Util.Inl (t), _49_1900) -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app ({FStar_Absyn_Syntax.n = FStar_Absyn_Syntax.Typ_const (fv); FStar_Absyn_Syntax.tk = _49_1909; FStar_Absyn_Syntax.pos = _49_1907; FStar_Absyn_Syntax.fvs = _49_1905; FStar_Absyn_Syntax.uvs = _49_1903}, (FStar_Util.Inr (_49_1914), _49_1917)::[]) -> begin
(FStar_Ident.lid_equals fv.FStar_Absyn_Syntax.v FStar_Absyn_Const.decreases_lid)
end
| _49_1923 -> begin
false
end)
end))))
in (match (_49_1926) with
| (dec, rest) -> begin
(
# 998 "FStar.Parser.Desugar.fst"
let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _49_12 -> (match (_49_12) with
| (FStar_Util.Inl (t), _49_1931) -> begin
(match (t.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_app (_49_1934, (FStar_Util.Inr (arg), _49_1938)::[]) -> begin
FStar_Absyn_Syntax.DECREASES (arg)
end
| _49_1944 -> begin
(FStar_All.failwith "impos")
end)
end
| _49_1946 -> begin
(FStar_All.failwith "impos")
end))))
in if ((FStar_Parser_DesugarEnv.is_effect_name env eff.FStar_Absyn_Syntax.v) || (FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Tot_lid)) then begin
if ((FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Tot_lid) && ((FStar_List.length decreases_clause) = 0)) then begin
(FStar_Absyn_Syntax.mk_Total result_typ)
end else begin
(
# 1009 "FStar.Parser.Desugar.fst"
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
# 1014 "FStar.Parser.Desugar.fst"
let rest = if (FStar_Ident.lid_equals eff.FStar_Absyn_Syntax.v FStar_Absyn_Const.effect_Lemma_lid) then begin
(match (rest) with
| req::ens::(FStar_Util.Inr (pat), aq)::[] -> begin
(let _130_670 = (let _130_669 = (let _130_668 = (let _130_667 = (let _130_666 = (FStar_Absyn_Syntax.mk_Exp_meta (FStar_Absyn_Syntax.Meta_desugared ((pat, FStar_Absyn_Syntax.Meta_smt_pat))))
in FStar_Util.Inr (_130_666))
in (_130_667, aq))
in (_130_668)::[])
in (ens)::_130_669)
in (req)::_130_670)
end
| _49_1957 -> begin
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
(let _130_672 = (let _130_671 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _130_671))
in (fail _130_672))
end
end)
end))
end
| _49_1960 -> begin
if default_ok then begin
(env.FStar_Parser_DesugarEnv.default_result_effect t r)
end else begin
(let _130_674 = (let _130_673 = (FStar_Absyn_Print.typ_to_string t)
in (FStar_Util.format1 "%s is not an effect" _130_673))
in (fail _130_674))
end
end)
end))))))
and desugar_kind : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.knd = (fun env k -> (
# 1033 "FStar.Parser.Desugar.fst"
let pos = (fun f -> (f k.FStar_Parser_AST.range))
in (
# 1034 "FStar.Parser.Desugar.fst"
let setpos = (fun kk -> (
# 1034 "FStar.Parser.Desugar.fst"
let _49_1967 = kk
in {FStar_Absyn_Syntax.n = _49_1967.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _49_1967.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = k.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _49_1967.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _49_1967.FStar_Absyn_Syntax.uvs}))
in (
# 1035 "FStar.Parser.Desugar.fst"
let k = (unparen k)
in (match (k.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name ({FStar_Ident.ns = _49_1976; FStar_Ident.ident = _49_1974; FStar_Ident.nsstr = _49_1972; FStar_Ident.str = "Type"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_type)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _49_1985; FStar_Ident.ident = _49_1983; FStar_Ident.nsstr = _49_1981; FStar_Ident.str = "Effect"}) -> begin
(setpos FStar_Absyn_Syntax.mk_Kind_effect)
end
| FStar_Parser_AST.Name (l) -> begin
(match ((let _130_686 = (FStar_Parser_DesugarEnv.qualify_lid env l)
in (FStar_Parser_DesugarEnv.find_kind_abbrev env _130_686))) with
| Some (l) -> begin
(FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, []), FStar_Absyn_Syntax.mk_Kind_unknown)))
end
| _49_1993 -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end)
end
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Absyn_Syntax.kun)
end
| FStar_Parser_AST.Product (bs, k) -> begin
(
# 1046 "FStar.Parser.Desugar.fst"
let _49_2001 = (uncurry bs k)
in (match (_49_2001) with
| (bs, k) -> begin
(
# 1047 "FStar.Parser.Desugar.fst"
let rec aux = (fun env bs _49_13 -> (match (_49_13) with
| [] -> begin
(let _130_697 = (let _130_696 = (let _130_695 = (desugar_kind env k)
in ((FStar_List.rev bs), _130_695))
in (FStar_Absyn_Syntax.mk_Kind_arrow _130_696))
in (FStar_All.pipe_left pos _130_697))
end
| hd::tl -> begin
(
# 1051 "FStar.Parser.Desugar.fst"
let _49_2012 = (let _130_699 = (let _130_698 = (FStar_Parser_DesugarEnv.default_ml env)
in (desugar_binder _130_698 hd))
in (FStar_All.pipe_right _130_699 (as_binder env hd.FStar_Parser_AST.aqual)))
in (match (_49_2012) with
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
# 1059 "FStar.Parser.Desugar.fst"
let args = (FStar_List.map (fun _49_2022 -> (match (_49_2022) with
| (t, b) -> begin
(
# 1060 "FStar.Parser.Desugar.fst"
let qual = if (b = FStar_Parser_AST.Hash) then begin
Some (imp_tag)
end else begin
None
end
in (let _130_701 = (desugar_typ_or_exp env t)
in (_130_701, qual)))
end)) args)
in (FStar_All.pipe_left pos (FStar_Absyn_Syntax.mk_Kind_abbrev ((l, args), FStar_Absyn_Syntax.mk_Kind_unknown))))
end)
end
| _49_2026 -> begin
(FStar_Parser_AST.error "Unexpected term where kind was expected" k k.FStar_Parser_AST.range)
end)))))
and desugar_formula' : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env f -> (
# 1067 "FStar.Parser.Desugar.fst"
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
| _49_2037 -> begin
None
end))
in (
# 1074 "FStar.Parser.Desugar.fst"
let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (
# 1075 "FStar.Parser.Desugar.fst"
let setpos = (fun t -> (
# 1075 "FStar.Parser.Desugar.fst"
let _49_2042 = t
in {FStar_Absyn_Syntax.n = _49_2042.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _49_2042.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = f.FStar_Parser_AST.range; FStar_Absyn_Syntax.fvs = _49_2042.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _49_2042.FStar_Absyn_Syntax.uvs}))
in (
# 1076 "FStar.Parser.Desugar.fst"
let desugar_quant = (fun q qt b pats body -> (
# 1077 "FStar.Parser.Desugar.fst"
let tk = (desugar_binder env (
# 1077 "FStar.Parser.Desugar.fst"
let _49_2050 = b
in {FStar_Parser_AST.b = _49_2050.FStar_Parser_AST.b; FStar_Parser_AST.brange = _49_2050.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _49_2050.FStar_Parser_AST.aqual}))
in (
# 1078 "FStar.Parser.Desugar.fst"
let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _130_737 = (desugar_typ_or_exp env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _130_737)))))) pats))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(
# 1081 "FStar.Parser.Desugar.fst"
let _49_2065 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_49_2065) with
| (env, a) -> begin
(
# 1082 "FStar.Parser.Desugar.fst"
let pats = (desugar_pats env pats)
in (
# 1083 "FStar.Parser.Desugar.fst"
let body = (desugar_formula env body)
in (
# 1084 "FStar.Parser.Desugar.fst"
let body = (match (pats) with
| [] -> begin
body
end
| _49_2070 -> begin
(let _130_738 = (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
in (FStar_All.pipe_left setpos _130_738))
end)
in (
# 1087 "FStar.Parser.Desugar.fst"
let body = (let _130_744 = (let _130_743 = (let _130_742 = (let _130_741 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_130_741)::[])
in (_130_742, body))
in (FStar_Absyn_Syntax.mk_Typ_lam _130_743))
in (FStar_All.pipe_left pos _130_744))
in (let _130_749 = (let _130_748 = (let _130_745 = (FStar_Ident.set_lid_range qt b.FStar_Parser_AST.brange)
in (FStar_Absyn_Util.ftv _130_745 FStar_Absyn_Syntax.kun))
in (let _130_747 = (let _130_746 = (FStar_Absyn_Syntax.targ body)
in (_130_746)::[])
in (FStar_Absyn_Util.mk_typ_app _130_748 _130_747)))
in (FStar_All.pipe_left setpos _130_749))))))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(
# 1091 "FStar.Parser.Desugar.fst"
let _49_2080 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_49_2080) with
| (env, x) -> begin
(
# 1092 "FStar.Parser.Desugar.fst"
let pats = (desugar_pats env pats)
in (
# 1093 "FStar.Parser.Desugar.fst"
let body = (desugar_formula env body)
in (
# 1094 "FStar.Parser.Desugar.fst"
let body = (match (pats) with
| [] -> begin
body
end
| _49_2085 -> begin
(FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_pattern ((body, pats))))
end)
in (
# 1097 "FStar.Parser.Desugar.fst"
let body = (let _130_755 = (let _130_754 = (let _130_753 = (let _130_752 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_130_752)::[])
in (_130_753, body))
in (FStar_Absyn_Syntax.mk_Typ_lam _130_754))
in (FStar_All.pipe_left pos _130_755))
in (let _130_760 = (let _130_759 = (let _130_756 = (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange)
in (FStar_Absyn_Util.ftv _130_756 FStar_Absyn_Syntax.kun))
in (let _130_758 = (let _130_757 = (FStar_Absyn_Syntax.targ body)
in (_130_757)::[])
in (FStar_Absyn_Util.mk_typ_app _130_759 _130_758)))
in (FStar_All.pipe_left setpos _130_760))))))
end))
end
| _49_2089 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1102 "FStar.Parser.Desugar.fst"
let push_quant = (fun q binders pats body -> (match (binders) with
| b::b'::_rest -> begin
(
# 1104 "FStar.Parser.Desugar.fst"
let rest = (b')::_rest
in (
# 1105 "FStar.Parser.Desugar.fst"
let body = (let _130_775 = (q (rest, pats, body))
in (let _130_774 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _130_775 _130_774 FStar_Parser_AST.Formula)))
in (let _130_776 = (q ((b)::[], [], body))
in (FStar_Parser_AST.mk_term _130_776 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _49_2103 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _130_777 = (unparen f)
in _130_777.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(
# 1111 "FStar.Parser.Desugar.fst"
let f = (desugar_formula env f)
in (FStar_Absyn_Syntax.mk_Typ_meta (FStar_Absyn_Syntax.Meta_labeled ((f, l, FStar_Absyn_Syntax.dummyRange, p)))))
end
| FStar_Parser_AST.Op ("==", hd::_args) -> begin
(
# 1115 "FStar.Parser.Desugar.fst"
let args = (hd)::_args
in (
# 1116 "FStar.Parser.Desugar.fst"
let args = (FStar_List.map (fun t -> (let _130_779 = (desugar_typ_or_exp env t)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _130_779))) args)
in (
# 1117 "FStar.Parser.Desugar.fst"
let eq = if (is_type env hd) then begin
(let _130_780 = (FStar_Ident.set_lid_range FStar_Absyn_Const.eqT_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _130_780 FStar_Absyn_Syntax.kun))
end else begin
(let _130_781 = (FStar_Ident.set_lid_range FStar_Absyn_Const.eq2_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _130_781 FStar_Absyn_Syntax.kun))
end
in (FStar_Absyn_Util.mk_typ_app eq args))))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match (((connective s), args)) with
| (Some (conn), _49_2129::_49_2127::[]) -> begin
(let _130_786 = (let _130_782 = (FStar_Ident.set_lid_range conn f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _130_782 FStar_Absyn_Syntax.kun))
in (let _130_785 = (FStar_List.map (fun x -> (let _130_784 = (desugar_formula env x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _130_784))) args)
in (FStar_Absyn_Util.mk_typ_app _130_786 _130_785)))
end
| _49_2134 -> begin
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(let _130_787 = (desugar_exp env f)
in (FStar_All.pipe_right _130_787 FStar_Absyn_Util.b2t))
end
end)
end
| FStar_Parser_AST.If (f1, f2, f3) -> begin
(let _130_792 = (let _130_788 = (FStar_Ident.set_lid_range FStar_Absyn_Const.ite_lid f.FStar_Parser_AST.range)
in (FStar_Absyn_Util.ftv _130_788 FStar_Absyn_Syntax.kun))
in (let _130_791 = (FStar_List.map (fun x -> (match ((desugar_typ_or_exp env x)) with
| FStar_Util.Inl (t) -> begin
(FStar_Absyn_Syntax.targ t)
end
| FStar_Util.Inr (v) -> begin
(let _130_790 = (FStar_Absyn_Util.b2t v)
in (FStar_All.pipe_left FStar_Absyn_Syntax.targ _130_790))
end)) ((f1)::(f2)::(f3)::[]))
in (FStar_Absyn_Util.mk_typ_app _130_792 _130_791)))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall (_1::_2::_3, pats, body) -> begin
(
# 1145 "FStar.Parser.Desugar.fst"
let binders = (_1)::(_2)::_3
in (let _130_794 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _130_794)))
end
| FStar_Parser_AST.QExists (_1::_2::_3, pats, body) -> begin
(
# 1149 "FStar.Parser.Desugar.fst"
let binders = (_1)::(_2)::_3
in (let _130_796 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _130_796)))
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
| _49_2196 -> begin
if (is_type env f) then begin
(desugar_typ env f)
end else begin
(let _130_797 = (desugar_exp env f)
in (FStar_All.pipe_left FStar_Absyn_Util.b2t _130_797))
end
end)))))))
and desugar_formula : env_t  ->  FStar_Parser_AST.term  ->  FStar_Absyn_Syntax.typ = (fun env t -> (desugar_formula' (
# 1166 "FStar.Parser.Desugar.fst"
let _49_2199 = env
in {FStar_Parser_DesugarEnv.curmodule = _49_2199.FStar_Parser_DesugarEnv.curmodule; FStar_Parser_DesugarEnv.modules = _49_2199.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _49_2199.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.modul_abbrevs = _49_2199.FStar_Parser_DesugarEnv.modul_abbrevs; FStar_Parser_DesugarEnv.sigaccum = _49_2199.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _49_2199.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _49_2199.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = FStar_Parser_AST.Formula; FStar_Parser_DesugarEnv.sigmap = _49_2199.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _49_2199.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _49_2199.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _49_2199.FStar_Parser_DesugarEnv.admitted_iface}) t))
and desugar_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  ((FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd), (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ)) FStar_Util.either = (fun env b -> if (is_type_binder env b) then begin
(let _130_802 = (desugar_type_binder env b)
in FStar_Util.Inl (_130_802))
end else begin
(let _130_803 = (desugar_exp_binder env b)
in FStar_Util.Inr (_130_803))
end)
and typars_of_binders : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_DesugarEnv.env * ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.knd) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, FStar_Absyn_Syntax.typ) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (
# 1174 "FStar.Parser.Desugar.fst"
let _49_2232 = (FStar_List.fold_left (fun _49_2207 b -> (match (_49_2207) with
| (env, out) -> begin
(
# 1175 "FStar.Parser.Desugar.fst"
let tk = (desugar_binder env (
# 1175 "FStar.Parser.Desugar.fst"
let _49_2209 = b
in {FStar_Parser_AST.b = _49_2209.FStar_Parser_AST.b; FStar_Parser_AST.brange = _49_2209.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _49_2209.FStar_Parser_AST.aqual}))
in (match (tk) with
| FStar_Util.Inl (Some (a), k) -> begin
(
# 1178 "FStar.Parser.Desugar.fst"
let _49_2219 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_49_2219) with
| (env, a) -> begin
(env, ((FStar_Util.Inl ((FStar_Absyn_Util.bvd_to_bvar_s a k)), (trans_aqual b.FStar_Parser_AST.aqual)))::out)
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(
# 1181 "FStar.Parser.Desugar.fst"
let _49_2227 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_49_2227) with
| (env, x) -> begin
(env, ((FStar_Util.Inr ((FStar_Absyn_Util.bvd_to_bvar_s x t)), (trans_aqual b.FStar_Parser_AST.aqual)))::out)
end))
end
| _49_2229 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected binder", b.FStar_Parser_AST.brange))))
end))
end)) (env, []) bs)
in (match (_49_2232) with
| (env, tpars) -> begin
(env, (FStar_List.rev tpars))
end)))
and desugar_exp_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.typ) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (x, t) -> begin
(let _130_810 = (desugar_typ env t)
in (Some (x), _130_810))
end
| FStar_Parser_AST.TVariable (t) -> begin
(let _130_811 = (FStar_Parser_DesugarEnv.fail_or2 (FStar_Parser_DesugarEnv.try_lookup_typ_var env) t)
in (None, _130_811))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _130_812 = (desugar_typ env t)
in (None, _130_812))
end
| FStar_Parser_AST.Variable (x) -> begin
(Some (x), FStar_Absyn_Syntax.tun)
end
| _49_2246 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a type)", b.FStar_Parser_AST.brange))))
end))
and desugar_type_binder : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Absyn_Syntax.knd) = (fun env b -> (
# 1194 "FStar.Parser.Desugar.fst"
let fail = (fun _49_2250 -> (match (()) with
| () -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Unexpected domain of an arrow or sum (expected a kind)", b.FStar_Parser_AST.brange))))
end))
in (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, t)) | (FStar_Parser_AST.TAnnotated (x, t)) -> begin
(let _130_817 = (desugar_kind env t)
in (Some (x), _130_817))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _130_818 = (desugar_kind env t)
in (None, _130_818))
end
| FStar_Parser_AST.TVariable (x) -> begin
(Some (x), (
# 1199 "FStar.Parser.Desugar.fst"
let _49_2261 = FStar_Absyn_Syntax.mk_Kind_type
in {FStar_Absyn_Syntax.n = _49_2261.FStar_Absyn_Syntax.n; FStar_Absyn_Syntax.tk = _49_2261.FStar_Absyn_Syntax.tk; FStar_Absyn_Syntax.pos = b.FStar_Parser_AST.brange; FStar_Absyn_Syntax.fvs = _49_2261.FStar_Absyn_Syntax.fvs; FStar_Absyn_Syntax.uvs = _49_2261.FStar_Absyn_Syntax.uvs}))
end
| _49_2264 -> begin
(fail ())
end)))

# 1202 "FStar.Parser.Desugar.fst"
let gather_tc_binders : ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list = (fun tps k -> (
# 1203 "FStar.Parser.Desugar.fst"
let rec aux = (fun bs k -> (match (k.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Kind_arrow (binders, k) -> begin
(aux (FStar_List.append bs binders) k)
end
| FStar_Absyn_Syntax.Kind_abbrev (_49_2275, k) -> begin
(aux bs k)
end
| _49_2280 -> begin
bs
end))
in (let _130_827 = (aux tps k)
in (FStar_All.pipe_right _130_827 FStar_Absyn_Util.name_binders))))

# 1210 "FStar.Parser.Desugar.fst"
let mk_data_discriminators : FStar_Absyn_Syntax.qualifier Prims.list  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Ident.lid  ->  ((((FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t, ((FStar_Absyn_Syntax.exp', (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax FStar_Absyn_Syntax.bvdef, (FStar_Absyn_Syntax.typ', (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.syntax) FStar_Absyn_Syntax.withinfo_t) FStar_Util.either * FStar_Absyn_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Absyn_Syntax.knd', Prims.unit) FStar_Absyn_Syntax.syntax  ->  FStar_Ident.lident Prims.list  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun quals env t tps k datas -> (
# 1212 "FStar.Parser.Desugar.fst"
let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_DesugarEnv.iface) || env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(FStar_List.append ((FStar_Absyn_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (
# 1213 "FStar.Parser.Desugar.fst"
let binders = (gather_tc_binders tps k)
in (
# 1214 "FStar.Parser.Desugar.fst"
let p = (FStar_Ident.range_of_lid t)
in (
# 1215 "FStar.Parser.Desugar.fst"
let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _49_2294 -> (match (_49_2294) with
| (x, _49_2293) -> begin
(x, Some (imp_tag))
end))))
in (
# 1216 "FStar.Parser.Desugar.fst"
let binders = (let _130_848 = (let _130_847 = (let _130_846 = (let _130_845 = (let _130_844 = (FStar_Absyn_Util.ftv t FStar_Absyn_Syntax.kun)
in (let _130_843 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (_130_844, _130_843)))
in (FStar_Absyn_Syntax.mk_Typ_app' _130_845 None p))
in (FStar_All.pipe_left FStar_Absyn_Syntax.null_v_binder _130_846))
in (_130_847)::[])
in (FStar_List.append imp_binders _130_848))
in (
# 1217 "FStar.Parser.Desugar.fst"
let disc_type = (let _130_851 = (let _130_850 = (let _130_849 = (FStar_Absyn_Util.ftv FStar_Absyn_Const.bool_lid FStar_Absyn_Syntax.ktype)
in (FStar_Absyn_Util.total_comp _130_849 p))
in (binders, _130_850))
in (FStar_Absyn_Syntax.mk_Typ_fun _130_851 None p))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (
# 1219 "FStar.Parser.Desugar.fst"
let disc_name = (FStar_Absyn_Util.mk_discriminator d)
in (let _130_854 = (let _130_853 = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Discriminator (d))::[]))
in (disc_name, disc_type, _130_853, (FStar_Ident.range_of_lid disc_name)))
in FStar_Absyn_Syntax.Sig_val_decl (_130_854)))))))))))))

# 1223 "FStar.Parser.Desugar.fst"
let mk_indexed_projectors = (fun fvq refine_domain env _49_2306 lid formals t -> (match (_49_2306) with
| (tc, tps, k) -> begin
(
# 1224 "FStar.Parser.Desugar.fst"
let binders = (gather_tc_binders tps k)
in (
# 1225 "FStar.Parser.Desugar.fst"
let p = (FStar_Ident.range_of_lid lid)
in (
# 1226 "FStar.Parser.Desugar.fst"
let pos = (fun q -> (FStar_Absyn_Syntax.withinfo q None p))
in (
# 1227 "FStar.Parser.Desugar.fst"
let projectee = (let _130_865 = (FStar_Absyn_Syntax.mk_ident ("projectee", p))
in (let _130_864 = (FStar_Absyn_Util.genident (Some (p)))
in {FStar_Absyn_Syntax.ppname = _130_865; FStar_Absyn_Syntax.realname = _130_864}))
in (
# 1229 "FStar.Parser.Desugar.fst"
let arg_exp = (FStar_Absyn_Util.bvd_to_exp projectee FStar_Absyn_Syntax.tun)
in (
# 1230 "FStar.Parser.Desugar.fst"
let arg_binder = (
# 1231 "FStar.Parser.Desugar.fst"
let arg_typ = (let _130_868 = (let _130_867 = (FStar_Absyn_Util.ftv tc FStar_Absyn_Syntax.kun)
in (let _130_866 = (FStar_Absyn_Util.args_of_non_null_binders binders)
in (_130_867, _130_866)))
in (FStar_Absyn_Syntax.mk_Typ_app' _130_868 None p))
in if (not (refine_domain)) then begin
(FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s projectee arg_typ))
end else begin
(
# 1234 "FStar.Parser.Desugar.fst"
let disc_name = (FStar_Absyn_Util.mk_discriminator lid)
in (
# 1235 "FStar.Parser.Desugar.fst"
let x = (FStar_Absyn_Util.gen_bvar arg_typ)
in (let _130_878 = (let _130_877 = (let _130_876 = (let _130_875 = (let _130_874 = (let _130_873 = (let _130_872 = (FStar_Absyn_Util.fvar None disc_name p)
in (let _130_871 = (let _130_870 = (let _130_869 = (FStar_Absyn_Util.bvar_to_exp x)
in (FStar_All.pipe_left FStar_Absyn_Syntax.varg _130_869))
in (_130_870)::[])
in (_130_872, _130_871)))
in (FStar_Absyn_Syntax.mk_Exp_app _130_873 None p))
in (FStar_Absyn_Util.b2t _130_874))
in (x, _130_875))
in (FStar_Absyn_Syntax.mk_Typ_refine _130_876 None p))
in (FStar_All.pipe_left (FStar_Absyn_Util.bvd_to_bvar_s projectee) _130_877))
in (FStar_All.pipe_left FStar_Absyn_Syntax.v_binder _130_878))))
end)
in (
# 1237 "FStar.Parser.Desugar.fst"
let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _49_2323 -> (match (_49_2323) with
| (x, _49_2322) -> begin
(x, Some (imp_tag))
end))))
in (
# 1238 "FStar.Parser.Desugar.fst"
let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (
# 1239 "FStar.Parser.Desugar.fst"
let arg = (FStar_Absyn_Util.arg_of_non_null_binder arg_binder)
in (
# 1240 "FStar.Parser.Desugar.fst"
let subst = (let _130_886 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i f -> (match ((Prims.fst f)) with
| FStar_Util.Inl (a) -> begin
(
# 1242 "FStar.Parser.Desugar.fst"
let _49_2334 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_49_2334) with
| (field_name, _49_2333) -> begin
(
# 1243 "FStar.Parser.Desugar.fst"
let proj = (let _130_883 = (let _130_882 = (FStar_Absyn_Util.ftv field_name FStar_Absyn_Syntax.kun)
in (_130_882, (arg)::[]))
in (FStar_Absyn_Syntax.mk_Typ_app _130_883 None p))
in (FStar_Util.Inl ((a.FStar_Absyn_Syntax.v, proj)))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(
# 1247 "FStar.Parser.Desugar.fst"
let _49_2341 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_49_2341) with
| (field_name, _49_2340) -> begin
(
# 1248 "FStar.Parser.Desugar.fst"
let proj = (let _130_885 = (let _130_884 = (FStar_Absyn_Util.fvar None field_name p)
in (_130_884, (arg)::[]))
in (FStar_Absyn_Syntax.mk_Exp_app _130_885 None p))
in (FStar_Util.Inr ((x.FStar_Absyn_Syntax.v, proj)))::[])
end))
end))))
in (FStar_All.pipe_right _130_886 FStar_List.flatten))
in (
# 1251 "FStar.Parser.Desugar.fst"
let ntps = (FStar_List.length tps)
in (
# 1252 "FStar.Parser.Desugar.fst"
let all_params = (let _130_888 = (FStar_All.pipe_right tps (FStar_List.map (fun _49_2348 -> (match (_49_2348) with
| (b, _49_2347) -> begin
(b, Some (imp_tag))
end))))
in (FStar_List.append _130_888 formals))
in (let _130_918 = (FStar_All.pipe_right formals (FStar_List.mapi (fun i ax -> (match ((Prims.fst ax)) with
| FStar_Util.Inl (a) -> begin
(
# 1256 "FStar.Parser.Desugar.fst"
let _49_2357 = (FStar_Absyn_Util.mk_field_projector_name lid a i)
in (match (_49_2357) with
| (field_name, _49_2356) -> begin
(
# 1257 "FStar.Parser.Desugar.fst"
let kk = (let _130_892 = (let _130_891 = (FStar_Absyn_Util.subst_kind subst a.FStar_Absyn_Syntax.sort)
in (binders, _130_891))
in (FStar_Absyn_Syntax.mk_Kind_arrow _130_892 p))
in (FStar_Absyn_Syntax.Sig_tycon ((field_name, [], kk, [], [], (FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector ((lid, FStar_Util.Inl (a.FStar_Absyn_Syntax.v))))::[], (FStar_Ident.range_of_lid field_name))))::[])
end))
end
| FStar_Util.Inr (x) -> begin
(
# 1261 "FStar.Parser.Desugar.fst"
let _49_2364 = (FStar_Absyn_Util.mk_field_projector_name lid x i)
in (match (_49_2364) with
| (field_name, _49_2363) -> begin
(
# 1262 "FStar.Parser.Desugar.fst"
let t = (let _130_895 = (let _130_894 = (let _130_893 = (FStar_Absyn_Util.subst_typ subst x.FStar_Absyn_Syntax.sort)
in (FStar_Absyn_Util.total_comp _130_893 p))
in (binders, _130_894))
in (FStar_Absyn_Syntax.mk_Typ_fun _130_895 None p))
in (
# 1263 "FStar.Parser.Desugar.fst"
let quals = (fun q -> if ((not (env.FStar_Parser_DesugarEnv.iface)) || env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(FStar_Absyn_Syntax.Assumption)::q
end else begin
q
end)
in (
# 1264 "FStar.Parser.Desugar.fst"
let quals = (quals ((FStar_Absyn_Syntax.Logic)::(FStar_Absyn_Syntax.Projector ((lid, FStar_Util.Inr (x.FStar_Absyn_Syntax.v))))::[]))
in (
# 1265 "FStar.Parser.Desugar.fst"
let impl = if (((let _130_898 = (FStar_Parser_DesugarEnv.current_module env)
in (FStar_Ident.lid_equals FStar_Absyn_Const.prims_lid _130_898)) || (fvq <> FStar_Absyn_Syntax.Data_ctor)) || (let _130_900 = (let _130_899 = (FStar_Parser_DesugarEnv.current_module env)
in _130_899.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _130_900))) then begin
[]
end else begin
(
# 1270 "FStar.Parser.Desugar.fst"
let projection = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in (
# 1271 "FStar.Parser.Desugar.fst"
let as_imp = (fun _49_14 -> (match (_49_14) with
| Some (FStar_Absyn_Syntax.Implicit (_49_2372)) -> begin
true
end
| _49_2376 -> begin
false
end))
in (
# 1274 "FStar.Parser.Desugar.fst"
let arg_pats = (let _130_915 = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j by -> (match (by) with
| (FStar_Util.Inl (_49_2381), imp) -> begin
if (j < ntps) then begin
[]
end else begin
(let _130_908 = (let _130_907 = (let _130_906 = (let _130_905 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.kun)
in FStar_Absyn_Syntax.Pat_tvar (_130_905))
in (pos _130_906))
in (_130_907, (as_imp imp)))
in (_130_908)::[])
end
end
| (FStar_Util.Inr (_49_2386), imp) -> begin
if ((i + ntps) = j) then begin
(let _130_910 = (let _130_909 = (pos (FStar_Absyn_Syntax.Pat_var (projection)))
in (_130_909, (as_imp imp)))
in (_130_910)::[])
end else begin
if (j < ntps) then begin
[]
end else begin
(let _130_914 = (let _130_913 = (let _130_912 = (let _130_911 = (FStar_Absyn_Util.gen_bvar FStar_Absyn_Syntax.tun)
in FStar_Absyn_Syntax.Pat_wild (_130_911))
in (pos _130_912))
in (_130_913, (as_imp imp)))
in (_130_914)::[])
end
end
end))))
in (FStar_All.pipe_right _130_915 FStar_List.flatten))
in (
# 1283 "FStar.Parser.Desugar.fst"
let pat = (let _130_917 = (FStar_All.pipe_right (FStar_Absyn_Syntax.Pat_cons (((FStar_Absyn_Util.fv lid), Some (fvq), arg_pats))) pos)
in (let _130_916 = (FStar_Absyn_Util.bvar_to_exp projection)
in (_130_917, None, _130_916)))
in (
# 1284 "FStar.Parser.Desugar.fst"
let body = (FStar_Absyn_Syntax.mk_Exp_match (arg_exp, (pat)::[]) None p)
in (
# 1285 "FStar.Parser.Desugar.fst"
let imp = (FStar_Absyn_Syntax.mk_Exp_abs (binders, body) None (FStar_Ident.range_of_lid field_name))
in (
# 1286 "FStar.Parser.Desugar.fst"
let lb = {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (field_name); FStar_Absyn_Syntax.lbtyp = FStar_Absyn_Syntax.tun; FStar_Absyn_Syntax.lbeff = FStar_Absyn_Const.effect_Tot_lid; FStar_Absyn_Syntax.lbdef = imp}
in (FStar_Absyn_Syntax.Sig_let (((false, (lb)::[]), p, [], quals)))::[])))))))
end
in (FStar_Absyn_Syntax.Sig_val_decl ((field_name, t, quals, (FStar_Ident.range_of_lid field_name))))::impl))))
end))
end))))
in (FStar_All.pipe_right _130_918 FStar_List.flatten))))))))))))))
end))

# 1295 "FStar.Parser.Desugar.fst"
let mk_data_projectors : FStar_Parser_DesugarEnv.env  ->  FStar_Absyn_Syntax.sigelt  ->  FStar_Absyn_Syntax.sigelt Prims.list = (fun env _49_17 -> (match (_49_17) with
| FStar_Absyn_Syntax.Sig_datacon (lid, t, tycon, quals, _49_2403, _49_2405) when (not ((FStar_Ident.lid_equals lid FStar_Absyn_Const.lexcons_lid))) -> begin
(
# 1298 "FStar.Parser.Desugar.fst"
let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _49_15 -> (match (_49_15) with
| FStar_Absyn_Syntax.RecordConstructor (_49_2410) -> begin
true
end
| _49_2413 -> begin
false
end)))) then begin
false
end else begin
(
# 1301 "FStar.Parser.Desugar.fst"
let _49_2419 = tycon
in (match (_49_2419) with
| (l, _49_2416, _49_2418) -> begin
(match ((FStar_Parser_DesugarEnv.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > 1)
end
| _49_2423 -> begin
true
end)
end))
end
in (match ((FStar_Absyn_Util.function_formals t)) with
| Some (formals, cod) -> begin
(
# 1307 "FStar.Parser.Desugar.fst"
let cod = (FStar_Absyn_Util.comp_result cod)
in (
# 1308 "FStar.Parser.Desugar.fst"
let qual = (match ((FStar_Util.find_map quals (fun _49_16 -> (match (_49_16) with
| FStar_Absyn_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Absyn_Syntax.Record_ctor ((lid, fns)))
end
| _49_2434 -> begin
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
| _49_2440 -> begin
[]
end))
end
| _49_2442 -> begin
[]
end))

# 1318 "FStar.Parser.Desugar.fst"
let rec desugar_tycon : FStar_Parser_DesugarEnv.env  ->  FStar_Range.range  ->  FStar_Absyn_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Absyn_Syntax.sigelts) = (fun env rng quals tcs -> (
# 1319 "FStar.Parser.Desugar.fst"
let tycon_id = (fun _49_18 -> (match (_49_18) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (
# 1324 "FStar.Parser.Desugar.fst"
let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _130_938 = (let _130_937 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_130_937))
in (FStar_Parser_AST.mk_term _130_938 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| (FStar_Parser_AST.TAnnotated (a, _)) | (FStar_Parser_AST.TVariable (a)) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar (a)) a.FStar_Ident.idRange FStar_Parser_AST.Type)
end
| FStar_Parser_AST.NoName (t) -> begin
t
end))
in (
# 1330 "FStar.Parser.Desugar.fst"
let tot = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Absyn_Const.effect_Tot_lid)) rng FStar_Parser_AST.Expr)
in (
# 1331 "FStar.Parser.Desugar.fst"
let with_constructor_effect = (fun t -> (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((tot, t, FStar_Parser_AST.Nothing))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level))
in (
# 1332 "FStar.Parser.Desugar.fst"
let apply_binders = (fun t binders -> (
# 1333 "FStar.Parser.Desugar.fst"
let imp_of_aqual = (fun b -> (match (b.FStar_Parser_AST.aqual) with
| Some (FStar_Parser_AST.Implicit) -> begin
FStar_Parser_AST.Hash
end
| _49_2507 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _130_951 = (let _130_950 = (let _130_949 = (binder_to_term b)
in (out, _130_949, (imp_of_aqual b)))
in FStar_Parser_AST.App (_130_950))
in (FStar_Parser_AST.mk_term _130_951 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (
# 1338 "FStar.Parser.Desugar.fst"
let tycon_record_as_variant = (fun _49_19 -> (match (_49_19) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(
# 1340 "FStar.Parser.Desugar.fst"
let constrName = (FStar_Ident.mk_ident ((Prims.strcat "Mk" id.FStar_Ident.idText), id.FStar_Ident.idRange))
in (
# 1341 "FStar.Parser.Desugar.fst"
let mfields = (FStar_List.map (fun _49_2520 -> (match (_49_2520) with
| (x, t) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated (((FStar_Absyn_Util.mangle_field_name x), t))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (
# 1342 "FStar.Parser.Desugar.fst"
let result = (let _130_957 = (let _130_956 = (let _130_955 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_130_955))
in (FStar_Parser_AST.mk_term _130_956 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _130_957 parms))
in (
# 1343 "FStar.Parser.Desugar.fst"
let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product ((mfields, (with_constructor_effect result)))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _130_959 = (FStar_All.pipe_right fields (FStar_List.map (fun _49_2527 -> (match (_49_2527) with
| (x, _49_2526) -> begin
(FStar_Parser_DesugarEnv.qualify env x)
end))))
in (FStar_Parser_AST.TyconVariant ((id, parms, kopt, ((constrName, Some (constrTyp), false))::[])), _130_959))))))
end
| _49_2529 -> begin
(FStar_All.failwith "impossible")
end))
in (
# 1347 "FStar.Parser.Desugar.fst"
let desugar_abstract_tc = (fun quals _env mutuals _49_20 -> (match (_49_20) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(
# 1349 "FStar.Parser.Desugar.fst"
let _49_2543 = (typars_of_binders _env binders)
in (match (_49_2543) with
| (_env', typars) -> begin
(
# 1350 "FStar.Parser.Desugar.fst"
let k = (match (kopt) with
| None -> begin
FStar_Absyn_Syntax.kun
end
| Some (k) -> begin
(desugar_kind _env' k)
end)
in (
# 1353 "FStar.Parser.Desugar.fst"
let tconstr = (let _130_970 = (let _130_969 = (let _130_968 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_130_968))
in (FStar_Parser_AST.mk_term _130_969 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _130_970 binders))
in (
# 1354 "FStar.Parser.Desugar.fst"
let qlid = (FStar_Parser_DesugarEnv.qualify _env id)
in (
# 1355 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_tycon ((qlid, typars, k, mutuals, [], quals, rng))
in (
# 1356 "FStar.Parser.Desugar.fst"
let _env = (FStar_Parser_DesugarEnv.push_rec_binding _env (FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in (
# 1357 "FStar.Parser.Desugar.fst"
let _env2 = (FStar_Parser_DesugarEnv.push_rec_binding _env' (FStar_Parser_DesugarEnv.Binding_tycon (qlid)))
in (_env, _env2, se, tconstr)))))))
end))
end
| _49_2554 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (
# 1360 "FStar.Parser.Desugar.fst"
let push_tparam = (fun env _49_21 -> (match (_49_21) with
| (FStar_Util.Inr (x), _49_2561) -> begin
(FStar_Parser_DesugarEnv.push_bvvdef env x.FStar_Absyn_Syntax.v)
end
| (FStar_Util.Inl (a), _49_2566) -> begin
(FStar_Parser_DesugarEnv.push_btvdef env a.FStar_Absyn_Syntax.v)
end))
in (
# 1363 "FStar.Parser.Desugar.fst"
let push_tparams = (FStar_List.fold_left push_tparam)
in (match (tcs) with
| FStar_Parser_AST.TyconAbstract (_49_2570)::[] -> begin
(
# 1366 "FStar.Parser.Desugar.fst"
let tc = (FStar_List.hd tcs)
in (
# 1367 "FStar.Parser.Desugar.fst"
let _49_2581 = (desugar_abstract_tc quals env [] tc)
in (match (_49_2581) with
| (_49_2575, _49_2577, se, _49_2580) -> begin
(
# 1368 "FStar.Parser.Desugar.fst"
let quals = if ((FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Assumption)) || (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.New))) then begin
quals
end else begin
(
# 1371 "FStar.Parser.Desugar.fst"
let _49_2582 = (let _130_980 = (FStar_Range.string_of_range rng)
in (let _130_979 = (let _130_978 = (let _130_977 = (FStar_Absyn_Util.lids_of_sigelt se)
in (FStar_All.pipe_right _130_977 (FStar_List.map FStar_Absyn_Print.sli)))
in (FStar_All.pipe_right _130_978 (FStar_String.concat ", ")))
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'new\' qualifier on %s\n" _130_980 _130_979)))
in (FStar_Absyn_Syntax.New)::quals)
end
in (
# 1374 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[])))
end)))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t)::[] -> begin
(
# 1379 "FStar.Parser.Desugar.fst"
let _49_2595 = (typars_of_binders env binders)
in (match (_49_2595) with
| (env', typars) -> begin
(
# 1380 "FStar.Parser.Desugar.fst"
let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _49_22 -> (match (_49_22) with
| FStar_Absyn_Syntax.Effect -> begin
true
end
| _49_2600 -> begin
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
# 1386 "FStar.Parser.Desugar.fst"
let t0 = t
in (
# 1387 "FStar.Parser.Desugar.fst"
let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _49_23 -> (match (_49_23) with
| FStar_Absyn_Syntax.Logic -> begin
true
end
| _49_2608 -> begin
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
# 1392 "FStar.Parser.Desugar.fst"
let se = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Absyn_Syntax.Effect)) then begin
(
# 1394 "FStar.Parser.Desugar.fst"
let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (let _130_986 = (let _130_985 = (FStar_Parser_DesugarEnv.qualify env id)
in (let _130_984 = (FStar_All.pipe_right quals (FStar_List.filter (fun _49_24 -> (match (_49_24) with
| FStar_Absyn_Syntax.Effect -> begin
false
end
| _49_2614 -> begin
true
end))))
in (_130_985, typars, c, _130_984, rng)))
in FStar_Absyn_Syntax.Sig_effect_abbrev (_130_986)))
end else begin
(
# 1396 "FStar.Parser.Desugar.fst"
let t = (desugar_typ env' t)
in (let _130_988 = (let _130_987 = (FStar_Parser_DesugarEnv.qualify env id)
in (_130_987, typars, k, t, quals, rng))
in FStar_Absyn_Syntax.Sig_typ_abbrev (_130_988)))
end
in (
# 1398 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[]))))))
end))
end
| FStar_Parser_AST.TyconRecord (_49_2619)::[] -> begin
(
# 1402 "FStar.Parser.Desugar.fst"
let trec = (FStar_List.hd tcs)
in (
# 1403 "FStar.Parser.Desugar.fst"
let _49_2625 = (tycon_record_as_variant trec)
in (match (_49_2625) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Absyn_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| _49_2629::_49_2627 -> begin
(
# 1407 "FStar.Parser.Desugar.fst"
let env0 = env
in (
# 1408 "FStar.Parser.Desugar.fst"
let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_DesugarEnv.qualify env) (tycon_id x))) tcs)
in (
# 1409 "FStar.Parser.Desugar.fst"
let rec collect_tcs = (fun quals et tc -> (
# 1410 "FStar.Parser.Desugar.fst"
let _49_2640 = et
in (match (_49_2640) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_49_2642) -> begin
(
# 1413 "FStar.Parser.Desugar.fst"
let trec = tc
in (
# 1414 "FStar.Parser.Desugar.fst"
let _49_2647 = (tycon_record_as_variant trec)
in (match (_49_2647) with
| (t, fs) -> begin
(collect_tcs ((FStar_Absyn_Syntax.RecordType (fs))::quals) (env, tcs) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(
# 1417 "FStar.Parser.Desugar.fst"
let _49_2659 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_49_2659) with
| (env, _49_2656, se, tconstr) -> begin
(env, (FStar_Util.Inl ((se, constructors, tconstr, quals)))::tcs)
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(
# 1420 "FStar.Parser.Desugar.fst"
let _49_2671 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract ((id, binders, kopt))))
in (match (_49_2671) with
| (env, _49_2668, se, tconstr) -> begin
(env, (FStar_Util.Inr ((se, t, quals)))::tcs)
end))
end
| _49_2673 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (
# 1423 "FStar.Parser.Desugar.fst"
let _49_2676 = (FStar_List.fold_left (collect_tcs quals) (env, []) tcs)
in (match (_49_2676) with
| (env, tcs) -> begin
(
# 1424 "FStar.Parser.Desugar.fst"
let tcs = (FStar_List.rev tcs)
in (
# 1425 "FStar.Parser.Desugar.fst"
let sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _49_26 -> (match (_49_26) with
| FStar_Util.Inr (FStar_Absyn_Syntax.Sig_tycon (id, tpars, k, _49_2683, _49_2685, _49_2687, _49_2689), t, quals) -> begin
(
# 1427 "FStar.Parser.Desugar.fst"
let env_tps = (push_tparams env tpars)
in (
# 1428 "FStar.Parser.Desugar.fst"
let t = (desugar_typ env_tps t)
in (FStar_Absyn_Syntax.Sig_typ_abbrev ((id, tpars, k, t, [], rng)))::[]))
end
| FStar_Util.Inl (FStar_Absyn_Syntax.Sig_tycon (tname, tpars, k, mutuals, _49_2703, tags, _49_2706), constrs, tconstr, quals) -> begin
(
# 1432 "FStar.Parser.Desugar.fst"
let tycon = (tname, tpars, k)
in (
# 1433 "FStar.Parser.Desugar.fst"
let env_tps = (push_tparams env tpars)
in (
# 1434 "FStar.Parser.Desugar.fst"
let _49_2737 = (let _130_1004 = (FStar_All.pipe_right constrs (FStar_List.map (fun _49_2719 -> (match (_49_2719) with
| (id, topt, of_notation) -> begin
(
# 1436 "FStar.Parser.Desugar.fst"
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
# 1444 "FStar.Parser.Desugar.fst"
let t = (let _130_999 = (FStar_Parser_DesugarEnv.default_total env_tps)
in (let _130_998 = (close env_tps t)
in (desugar_typ _130_999 _130_998)))
in (
# 1445 "FStar.Parser.Desugar.fst"
let name = (FStar_Parser_DesugarEnv.qualify env id)
in (
# 1446 "FStar.Parser.Desugar.fst"
let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _49_25 -> (match (_49_25) with
| FStar_Absyn_Syntax.RecordType (fns) -> begin
(FStar_Absyn_Syntax.RecordConstructor (fns))::[]
end
| _49_2733 -> begin
[]
end))))
in (let _130_1003 = (let _130_1002 = (let _130_1001 = (FStar_All.pipe_right t FStar_Absyn_Util.name_function_binders)
in (name, _130_1001, tycon, quals, mutuals, rng))
in FStar_Absyn_Syntax.Sig_datacon (_130_1002))
in (name, _130_1003))))))
end))))
in (FStar_All.pipe_left FStar_List.split _130_1004))
in (match (_49_2737) with
| (constrNames, constrs) -> begin
(FStar_Absyn_Syntax.Sig_tycon ((tname, tpars, k, mutuals, constrNames, tags, rng)))::constrs
end))))
end
| _49_2739 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1452 "FStar.Parser.Desugar.fst"
let bundle = (let _130_1006 = (let _130_1005 = (FStar_List.collect FStar_Absyn_Util.lids_of_sigelt sigelts)
in (sigelts, quals, _130_1005, rng))
in FStar_Absyn_Syntax.Sig_bundle (_130_1006))
in (
# 1453 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env0 bundle)
in (
# 1454 "FStar.Parser.Desugar.fst"
let data_ops = (FStar_All.pipe_right sigelts (FStar_List.collect (mk_data_projectors env)))
in (
# 1455 "FStar.Parser.Desugar.fst"
let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _49_27 -> (match (_49_27) with
| FStar_Absyn_Syntax.Sig_tycon (tname, tps, k, _49_2749, constrs, quals, _49_2753) -> begin
(mk_data_discriminators quals env tname tps k constrs)
end
| _49_2757 -> begin
[]
end))))
in (
# 1459 "FStar.Parser.Desugar.fst"
let ops = (FStar_List.append discs data_ops)
in (
# 1460 "FStar.Parser.Desugar.fst"
let env = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt env ops)
in (env, (FStar_List.append ((bundle)::[]) ops))))))))))
end)))))
end
| [] -> begin
(FStar_All.failwith "impossible")
end)))))))))))

# 1465 "FStar.Parser.Desugar.fst"
let desugar_binders : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.binder Prims.list) = (fun env binders -> (
# 1466 "FStar.Parser.Desugar.fst"
let _49_2788 = (FStar_List.fold_left (fun _49_2766 b -> (match (_49_2766) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| FStar_Util.Inl (Some (a), k) -> begin
(
# 1469 "FStar.Parser.Desugar.fst"
let _49_2775 = (FStar_Parser_DesugarEnv.push_local_tbinding env a)
in (match (_49_2775) with
| (env, a) -> begin
(let _130_1015 = (let _130_1014 = (FStar_Absyn_Syntax.t_binder (FStar_Absyn_Util.bvd_to_bvar_s a k))
in (_130_1014)::binders)
in (env, _130_1015))
end))
end
| FStar_Util.Inr (Some (x), t) -> begin
(
# 1473 "FStar.Parser.Desugar.fst"
let _49_2783 = (FStar_Parser_DesugarEnv.push_local_vbinding env x)
in (match (_49_2783) with
| (env, x) -> begin
(let _130_1017 = (let _130_1016 = (FStar_Absyn_Syntax.v_binder (FStar_Absyn_Util.bvd_to_bvar_s x t))
in (_130_1016)::binders)
in (env, _130_1017))
end))
end
| _49_2785 -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Missing name in binder", b.FStar_Parser_AST.brange))))
end)
end)) (env, []) binders)
in (match (_49_2788) with
| (env, binders) -> begin
(env, (FStar_List.rev binders))
end)))

# 1479 "FStar.Parser.Desugar.fst"
let trans_qual : FStar_Range.range  ->  FStar_Parser_AST.qualifier  ->  FStar_Absyn_Syntax.qualifier = (fun r _49_28 -> (match (_49_28) with
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
let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Absyn_Syntax.pragma = (fun _49_29 -> (match (_49_29) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Absyn_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions -> begin
FStar_Absyn_Syntax.ResetOptions
end))

# 1497 "FStar.Parser.Desugar.fst"
let trans_quals : FStar_Range.range  ->  FStar_Parser_AST.qualifier Prims.list  ->  FStar_Absyn_Syntax.qualifier Prims.list = (fun r -> (FStar_List.map (trans_qual r)))

# 1499 "FStar.Parser.Desugar.fst"
let rec desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Absyn_Syntax.sigelts) = (fun env d -> (
# 1500 "FStar.Parser.Desugar.fst"
let trans_quals = (trans_quals d.FStar_Parser_AST.drange)
in (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(
# 1503 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_pragma (((trans_pragma p), d.FStar_Parser_AST.drange))
in (env, (se)::[]))
end
| FStar_Parser_AST.TopLevelModule (_49_2815) -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (("Multiple modules in a file are no longer supported", d.FStar_Parser_AST.drange))))
end
| FStar_Parser_AST.Open (lid) -> begin
(
# 1510 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_namespace env lid)
in (env, []))
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(let _130_1035 = (FStar_Parser_DesugarEnv.push_module_abbrev env x l)
in (_130_1035, []))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(let _130_1036 = (trans_quals qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _130_1036 tcs))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _130_1038 = (let _130_1037 = (desugar_exp_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let ((isrec, lets, (FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr)))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Absyn_Util.compress_exp _130_1037))
in _130_1038.FStar_Absyn_Syntax.n)) with
| FStar_Absyn_Syntax.Exp_let (lbs, _49_2835) -> begin
(
# 1522 "FStar.Parser.Desugar.fst"
let lids = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (match (lb.FStar_Absyn_Syntax.lbname) with
| FStar_Util.Inr (l) -> begin
l
end
| _49_2842 -> begin
(FStar_All.failwith "impossible")
end))))
in (
# 1525 "FStar.Parser.Desugar.fst"
let quals = (match (quals) with
| _49_2847::_49_2845 -> begin
(trans_quals quals)
end
| _49_2850 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _49_30 -> (match (_49_30) with
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inl (_49_2859); FStar_Absyn_Syntax.lbtyp = _49_2857; FStar_Absyn_Syntax.lbeff = _49_2855; FStar_Absyn_Syntax.lbdef = _49_2853} -> begin
[]
end
| {FStar_Absyn_Syntax.lbname = FStar_Util.Inr (l); FStar_Absyn_Syntax.lbtyp = _49_2867; FStar_Absyn_Syntax.lbeff = _49_2865; FStar_Absyn_Syntax.lbdef = _49_2863} -> begin
(FStar_Parser_DesugarEnv.lookup_letbinding_quals env l)
end))))
end)
in (
# 1530 "FStar.Parser.Desugar.fst"
let s = FStar_Absyn_Syntax.Sig_let ((lbs, d.FStar_Parser_AST.drange, lids, quals))
in (
# 1531 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env s)
in (env, (s)::[])))))
end
| _49_2875 -> begin
(FStar_All.failwith "Desugaring a let did not produce a let")
end)
end
| FStar_Parser_AST.Main (t) -> begin
(
# 1537 "FStar.Parser.Desugar.fst"
let e = (desugar_exp env t)
in (
# 1538 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_main ((e, d.FStar_Parser_AST.drange))
in (env, (se)::[])))
end
| FStar_Parser_AST.Assume (atag, id, t) -> begin
(
# 1542 "FStar.Parser.Desugar.fst"
let f = (desugar_formula env t)
in (let _130_1044 = (let _130_1043 = (let _130_1042 = (let _130_1041 = (FStar_Parser_DesugarEnv.qualify env id)
in (_130_1041, f, (FStar_Absyn_Syntax.Assumption)::[], d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Sig_assume (_130_1042))
in (_130_1043)::[])
in (env, _130_1044)))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(
# 1546 "FStar.Parser.Desugar.fst"
let t = (let _130_1045 = (close_fun env t)
in (desugar_typ env _130_1045))
in (
# 1547 "FStar.Parser.Desugar.fst"
let quals = if (env.FStar_Parser_DesugarEnv.iface && env.FStar_Parser_DesugarEnv.admitted_iface) then begin
(let _130_1046 = (trans_quals quals)
in (FStar_Absyn_Syntax.Assumption)::_130_1046)
end else begin
(trans_quals quals)
end
in (
# 1548 "FStar.Parser.Desugar.fst"
let se = (let _130_1048 = (let _130_1047 = (FStar_Parser_DesugarEnv.qualify env id)
in (_130_1047, t, quals, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Sig_val_decl (_130_1048))
in (
# 1549 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[])))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(
# 1553 "FStar.Parser.Desugar.fst"
let t = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) FStar_Absyn_Const.exn_lid)
in (
# 1554 "FStar.Parser.Desugar.fst"
let l = (FStar_Parser_DesugarEnv.qualify env id)
in (
# 1555 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_datacon ((l, t, (FStar_Absyn_Const.exn_lid, [], FStar_Absyn_Syntax.ktype), (FStar_Absyn_Syntax.ExceptionConstructor)::[], (FStar_Absyn_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (
# 1556 "FStar.Parser.Desugar.fst"
let se' = FStar_Absyn_Syntax.Sig_bundle (((se)::[], (FStar_Absyn_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (
# 1557 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env se')
in (
# 1558 "FStar.Parser.Desugar.fst"
let data_ops = (mk_data_projectors env se)
in (
# 1559 "FStar.Parser.Desugar.fst"
let discs = (mk_data_discriminators [] env FStar_Absyn_Const.exn_lid [] FStar_Absyn_Syntax.ktype ((l)::[]))
in (
# 1560 "FStar.Parser.Desugar.fst"
let env = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops))))))))))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(
# 1564 "FStar.Parser.Desugar.fst"
let t = (desugar_typ env term)
in (
# 1565 "FStar.Parser.Desugar.fst"
let t = (let _130_1053 = (let _130_1052 = (let _130_1049 = (FStar_Absyn_Syntax.null_v_binder t)
in (_130_1049)::[])
in (let _130_1051 = (let _130_1050 = (FStar_Parser_DesugarEnv.fail_or env (FStar_Parser_DesugarEnv.try_lookup_typ_name env) FStar_Absyn_Const.exn_lid)
in (FStar_Absyn_Syntax.mk_Total _130_1050))
in (_130_1052, _130_1051)))
in (FStar_Absyn_Syntax.mk_Typ_fun _130_1053 None d.FStar_Parser_AST.drange))
in (
# 1566 "FStar.Parser.Desugar.fst"
let l = (FStar_Parser_DesugarEnv.qualify env id)
in (
# 1567 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_datacon ((l, t, (FStar_Absyn_Const.exn_lid, [], FStar_Absyn_Syntax.ktype), (FStar_Absyn_Syntax.ExceptionConstructor)::[], (FStar_Absyn_Const.exn_lid)::[], d.FStar_Parser_AST.drange))
in (
# 1568 "FStar.Parser.Desugar.fst"
let se' = FStar_Absyn_Syntax.Sig_bundle (((se)::[], (FStar_Absyn_Syntax.ExceptionConstructor)::[], (l)::[], d.FStar_Parser_AST.drange))
in (
# 1569 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env se')
in (
# 1570 "FStar.Parser.Desugar.fst"
let data_ops = (mk_data_projectors env se)
in (
# 1571 "FStar.Parser.Desugar.fst"
let discs = (mk_data_discriminators [] env FStar_Absyn_Const.exn_lid [] FStar_Absyn_Syntax.ktype ((l)::[]))
in (
# 1572 "FStar.Parser.Desugar.fst"
let env = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt env (FStar_List.append discs data_ops))
in (env, (FStar_List.append ((se')::discs) data_ops)))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(
# 1576 "FStar.Parser.Desugar.fst"
let _49_2928 = (desugar_binders env binders)
in (match (_49_2928) with
| (env_k, binders) -> begin
(
# 1577 "FStar.Parser.Desugar.fst"
let k = (desugar_kind env_k k)
in (
# 1578 "FStar.Parser.Desugar.fst"
let name = (FStar_Parser_DesugarEnv.qualify env id)
in (
# 1579 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_kind_abbrev ((name, binders, k, d.FStar_Parser_AST.drange))
in (
# 1580 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env se)
in (env, (se)::[])))))
end))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(
# 1584 "FStar.Parser.Desugar.fst"
let env0 = env
in (
# 1585 "FStar.Parser.Desugar.fst"
let _49_2944 = (desugar_binders env eff_binders)
in (match (_49_2944) with
| (env, binders) -> begin
(
# 1586 "FStar.Parser.Desugar.fst"
let defn = (desugar_typ env defn)
in (
# 1587 "FStar.Parser.Desugar.fst"
let _49_2948 = (FStar_Absyn_Util.head_and_args defn)
in (match (_49_2948) with
| (head, args) -> begin
(match (head.FStar_Absyn_Syntax.n) with
| FStar_Absyn_Syntax.Typ_const (eff) -> begin
(match ((FStar_Parser_DesugarEnv.try_lookup_effect_defn env eff.FStar_Absyn_Syntax.v)) with
| None -> begin
(let _130_1058 = (let _130_1057 = (let _130_1056 = (let _130_1055 = (let _130_1054 = (FStar_Absyn_Print.sli eff.FStar_Absyn_Syntax.v)
in (Prims.strcat "Effect " _130_1054))
in (Prims.strcat _130_1055 " not found"))
in (_130_1056, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Error (_130_1057))
in (Prims.raise _130_1058))
end
| Some (ed) -> begin
(
# 1593 "FStar.Parser.Desugar.fst"
let subst = (FStar_Absyn_Util.subst_of_list ed.FStar_Absyn_Syntax.binders args)
in (
# 1594 "FStar.Parser.Desugar.fst"
let sub = (FStar_Absyn_Util.subst_typ subst)
in (
# 1595 "FStar.Parser.Desugar.fst"
let ed = (let _130_1076 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _130_1075 = (trans_quals quals)
in (let _130_1074 = (FStar_Absyn_Util.subst_kind subst ed.FStar_Absyn_Syntax.signature)
in (let _130_1073 = (sub ed.FStar_Absyn_Syntax.ret)
in (let _130_1072 = (sub ed.FStar_Absyn_Syntax.bind_wp)
in (let _130_1071 = (sub ed.FStar_Absyn_Syntax.bind_wlp)
in (let _130_1070 = (sub ed.FStar_Absyn_Syntax.if_then_else)
in (let _130_1069 = (sub ed.FStar_Absyn_Syntax.ite_wp)
in (let _130_1068 = (sub ed.FStar_Absyn_Syntax.ite_wlp)
in (let _130_1067 = (sub ed.FStar_Absyn_Syntax.wp_binop)
in (let _130_1066 = (sub ed.FStar_Absyn_Syntax.wp_as_type)
in (let _130_1065 = (sub ed.FStar_Absyn_Syntax.close_wp)
in (let _130_1064 = (sub ed.FStar_Absyn_Syntax.close_wp_t)
in (let _130_1063 = (sub ed.FStar_Absyn_Syntax.assert_p)
in (let _130_1062 = (sub ed.FStar_Absyn_Syntax.assume_p)
in (let _130_1061 = (sub ed.FStar_Absyn_Syntax.null_wp)
in (let _130_1060 = (sub ed.FStar_Absyn_Syntax.trivial)
in {FStar_Absyn_Syntax.mname = _130_1076; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = _130_1075; FStar_Absyn_Syntax.signature = _130_1074; FStar_Absyn_Syntax.ret = _130_1073; FStar_Absyn_Syntax.bind_wp = _130_1072; FStar_Absyn_Syntax.bind_wlp = _130_1071; FStar_Absyn_Syntax.if_then_else = _130_1070; FStar_Absyn_Syntax.ite_wp = _130_1069; FStar_Absyn_Syntax.ite_wlp = _130_1068; FStar_Absyn_Syntax.wp_binop = _130_1067; FStar_Absyn_Syntax.wp_as_type = _130_1066; FStar_Absyn_Syntax.close_wp = _130_1065; FStar_Absyn_Syntax.close_wp_t = _130_1064; FStar_Absyn_Syntax.assert_p = _130_1063; FStar_Absyn_Syntax.assume_p = _130_1062; FStar_Absyn_Syntax.null_wp = _130_1061; FStar_Absyn_Syntax.trivial = _130_1060})))))))))))))))))
in (
# 1615 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (
# 1616 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)
end
| _49_2960 -> begin
(let _130_1080 = (let _130_1079 = (let _130_1078 = (let _130_1077 = (FStar_Absyn_Print.typ_to_string head)
in (Prims.strcat _130_1077 " is not an effect"))
in (_130_1078, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Error (_130_1079))
in (Prims.raise _130_1080))
end)
end)))
end)))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls)) -> begin
(
# 1623 "FStar.Parser.Desugar.fst"
let env0 = env
in (
# 1624 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.enter_monad_scope env eff_name)
in (
# 1625 "FStar.Parser.Desugar.fst"
let _49_2974 = (desugar_binders env eff_binders)
in (match (_49_2974) with
| (env, binders) -> begin
(
# 1626 "FStar.Parser.Desugar.fst"
let eff_k = (desugar_kind env eff_kind)
in (
# 1627 "FStar.Parser.Desugar.fst"
let _49_2985 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _49_2978 decl -> (match (_49_2978) with
| (env, out) -> begin
(
# 1628 "FStar.Parser.Desugar.fst"
let _49_2982 = (desugar_decl env decl)
in (match (_49_2982) with
| (env, ses) -> begin
(let _130_1084 = (let _130_1083 = (FStar_List.hd ses)
in (_130_1083)::out)
in (env, _130_1084))
end))
end)) (env, [])))
in (match (_49_2985) with
| (env, decls) -> begin
(
# 1630 "FStar.Parser.Desugar.fst"
let decls = (FStar_List.rev decls)
in (
# 1631 "FStar.Parser.Desugar.fst"
let lookup = (fun s -> (match ((let _130_1088 = (let _130_1087 = (FStar_Absyn_Syntax.mk_ident (s, d.FStar_Parser_AST.drange))
in (FStar_Parser_DesugarEnv.qualify env _130_1087))
in (FStar_Parser_DesugarEnv.try_resolve_typ_abbrev env _130_1088))) with
| None -> begin
(Prims.raise (FStar_Absyn_Syntax.Error (((Prims.strcat (Prims.strcat (Prims.strcat "Monad " eff_name.FStar_Ident.idText) " expects definition of ") s), d.FStar_Parser_AST.drange))))
end
| Some (t) -> begin
t
end))
in (
# 1634 "FStar.Parser.Desugar.fst"
let ed = (let _130_1104 = (FStar_Parser_DesugarEnv.qualify env0 eff_name)
in (let _130_1103 = (trans_quals quals)
in (let _130_1102 = (lookup "return")
in (let _130_1101 = (lookup "bind_wp")
in (let _130_1100 = (lookup "bind_wlp")
in (let _130_1099 = (lookup "if_then_else")
in (let _130_1098 = (lookup "ite_wp")
in (let _130_1097 = (lookup "ite_wlp")
in (let _130_1096 = (lookup "wp_binop")
in (let _130_1095 = (lookup "wp_as_type")
in (let _130_1094 = (lookup "close_wp")
in (let _130_1093 = (lookup "close_wp_t")
in (let _130_1092 = (lookup "assert_p")
in (let _130_1091 = (lookup "assume_p")
in (let _130_1090 = (lookup "null_wp")
in (let _130_1089 = (lookup "trivial")
in {FStar_Absyn_Syntax.mname = _130_1104; FStar_Absyn_Syntax.binders = binders; FStar_Absyn_Syntax.qualifiers = _130_1103; FStar_Absyn_Syntax.signature = eff_k; FStar_Absyn_Syntax.ret = _130_1102; FStar_Absyn_Syntax.bind_wp = _130_1101; FStar_Absyn_Syntax.bind_wlp = _130_1100; FStar_Absyn_Syntax.if_then_else = _130_1099; FStar_Absyn_Syntax.ite_wp = _130_1098; FStar_Absyn_Syntax.ite_wlp = _130_1097; FStar_Absyn_Syntax.wp_binop = _130_1096; FStar_Absyn_Syntax.wp_as_type = _130_1095; FStar_Absyn_Syntax.close_wp = _130_1094; FStar_Absyn_Syntax.close_wp_t = _130_1093; FStar_Absyn_Syntax.assert_p = _130_1092; FStar_Absyn_Syntax.assume_p = _130_1091; FStar_Absyn_Syntax.null_wp = _130_1090; FStar_Absyn_Syntax.trivial = _130_1089}))))))))))))))))
in (
# 1654 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_new_effect ((ed, d.FStar_Parser_AST.drange))
in (
# 1655 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.push_sigelt env0 se)
in (env, (se)::[]))))))
end)))
end))))
end
| FStar_Parser_AST.SubEffect (l) -> begin
(
# 1659 "FStar.Parser.Desugar.fst"
let lookup = (fun l -> (match ((FStar_Parser_DesugarEnv.try_lookup_effect_name env l)) with
| None -> begin
(let _130_1111 = (let _130_1110 = (let _130_1109 = (let _130_1108 = (let _130_1107 = (FStar_Absyn_Print.sli l)
in (Prims.strcat "Effect name " _130_1107))
in (Prims.strcat _130_1108 " not found"))
in (_130_1109, d.FStar_Parser_AST.drange))
in FStar_Absyn_Syntax.Error (_130_1110))
in (Prims.raise _130_1111))
end
| Some (l) -> begin
l
end))
in (
# 1662 "FStar.Parser.Desugar.fst"
let src = (lookup l.FStar_Parser_AST.msource)
in (
# 1663 "FStar.Parser.Desugar.fst"
let dst = (lookup l.FStar_Parser_AST.mdest)
in (
# 1664 "FStar.Parser.Desugar.fst"
let lift = (desugar_typ env l.FStar_Parser_AST.lift_op)
in (
# 1665 "FStar.Parser.Desugar.fst"
let se = FStar_Absyn_Syntax.Sig_sub_effect (({FStar_Absyn_Syntax.source = src; FStar_Absyn_Syntax.target = dst; FStar_Absyn_Syntax.lift = lift}, d.FStar_Parser_AST.drange))
in (env, (se)::[]))))))
end)))

# 1668 "FStar.Parser.Desugar.fst"
let desugar_decls : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _49_3010 d -> (match (_49_3010) with
| (env, sigelts) -> begin
(
# 1670 "FStar.Parser.Desugar.fst"
let _49_3014 = (desugar_decl env d)
in (match (_49_3014) with
| (env, se) -> begin
(env, (FStar_List.append sigelts se))
end))
end)) (env, []) decls))

# 1673 "FStar.Parser.Desugar.fst"
let open_prims_all : FStar_Parser_AST.decl Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.prims_lid)) FStar_Absyn_Syntax.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Absyn_Const.all_lid)) FStar_Absyn_Syntax.dummyRange))::[]

# 1680 "FStar.Parser.Desugar.fst"
let desugar_modul_common : FStar_Absyn_Syntax.modul Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Absyn_Syntax.modul * Prims.bool) = (fun curmod env m -> (
# 1681 "FStar.Parser.Desugar.fst"
let open_ns = (fun mname d -> (
# 1682 "FStar.Parser.Desugar.fst"
let d = if ((FStar_List.length mname.FStar_Ident.ns) <> 0) then begin
(let _130_1131 = (let _130_1130 = (let _130_1128 = (FStar_Absyn_Syntax.lid_of_ids mname.FStar_Ident.ns)
in FStar_Parser_AST.Open (_130_1128))
in (let _130_1129 = (FStar_Absyn_Syntax.range_of_lid mname)
in (FStar_Parser_AST.mk_decl _130_1130 _130_1129)))
in (_130_1131)::d)
end else begin
d
end
in d))
in (
# 1686 "FStar.Parser.Desugar.fst"
let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod) -> begin
(FStar_Parser_DesugarEnv.finish_module_or_interface env prev_mod)
end)
in (
# 1689 "FStar.Parser.Desugar.fst"
let _49_3041 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _130_1133 = (FStar_Parser_DesugarEnv.prepare_module_or_interface true admitted env mname)
in (let _130_1132 = (open_ns mname decls)
in (_130_1133, mname, _130_1132, true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _130_1135 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false env mname)
in (let _130_1134 = (open_ns mname decls)
in (_130_1135, mname, _130_1134, false)))
end)
in (match (_49_3041) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(
# 1694 "FStar.Parser.Desugar.fst"
let _49_3044 = (desugar_decls env decls)
in (match (_49_3044) with
| (env, sigelts) -> begin
(
# 1695 "FStar.Parser.Desugar.fst"
let modul = {FStar_Absyn_Syntax.name = mname; FStar_Absyn_Syntax.declarations = sigelts; FStar_Absyn_Syntax.exports = []; FStar_Absyn_Syntax.is_interface = intf; FStar_Absyn_Syntax.is_deserialized = false}
in (env, modul, pop_when_done))
end))
end)))))

# 1704 "FStar.Parser.Desugar.fst"
let desugar_partial_modul : FStar_Absyn_Syntax.modul Prims.option  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul) = (fun curmod env m -> (
# 1705 "FStar.Parser.Desugar.fst"
let m = if (FStar_ST.read FStar_Options.interactive_fsi) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface ((mname, decls, true))
end
| FStar_Parser_AST.Interface (mname, _49_3055, _49_3057) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (
# 1712 "FStar.Parser.Desugar.fst"
let _49_3065 = (desugar_modul_common curmod env m)
in (match (_49_3065) with
| (x, y, _49_3064) -> begin
(x, y)
end))))

# 1715 "FStar.Parser.Desugar.fst"
let desugar_modul : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Absyn_Syntax.modul) = (fun env m -> (
# 1716 "FStar.Parser.Desugar.fst"
let _49_3071 = (desugar_modul_common None env m)
in (match (_49_3071) with
| (env, modul, pop_when_done) -> begin
(
# 1717 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.finish_module_or_interface env modul)
in (
# 1718 "FStar.Parser.Desugar.fst"
let _49_3073 = if (FStar_Options.should_dump modul.FStar_Absyn_Syntax.name.FStar_Ident.str) then begin
(let _130_1146 = (FStar_Absyn_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _130_1146))
end else begin
()
end
in (let _130_1147 = if pop_when_done then begin
(FStar_Parser_DesugarEnv.export_interface modul.FStar_Absyn_Syntax.name env)
end else begin
env
end
in (_130_1147, modul))))
end)))

# 1721 "FStar.Parser.Desugar.fst"
let desugar_file : FStar_Parser_DesugarEnv.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_DesugarEnv.env * FStar_Absyn_Syntax.modul Prims.list) = (fun env f -> (
# 1722 "FStar.Parser.Desugar.fst"
let _49_3086 = (FStar_List.fold_left (fun _49_3079 m -> (match (_49_3079) with
| (env, mods) -> begin
(
# 1723 "FStar.Parser.Desugar.fst"
let _49_3083 = (desugar_modul env m)
in (match (_49_3083) with
| (env, m) -> begin
(env, (m)::mods)
end))
end)) (env, []) f)
in (match (_49_3086) with
| (env, mods) -> begin
(env, (FStar_List.rev mods))
end)))

# 1727 "FStar.Parser.Desugar.fst"
let add_modul_to_env : FStar_Absyn_Syntax.modul  ->  FStar_Parser_DesugarEnv.env  ->  FStar_Parser_DesugarEnv.env = (fun m en -> (
# 1728 "FStar.Parser.Desugar.fst"
let _49_3091 = (FStar_Parser_DesugarEnv.prepare_module_or_interface false false en m.FStar_Absyn_Syntax.name)
in (match (_49_3091) with
| (en, pop_when_done) -> begin
(
# 1729 "FStar.Parser.Desugar.fst"
let en = (FStar_List.fold_left FStar_Parser_DesugarEnv.push_sigelt (
# 1729 "FStar.Parser.Desugar.fst"
let _49_3092 = en
in {FStar_Parser_DesugarEnv.curmodule = Some (m.FStar_Absyn_Syntax.name); FStar_Parser_DesugarEnv.modules = _49_3092.FStar_Parser_DesugarEnv.modules; FStar_Parser_DesugarEnv.open_namespaces = _49_3092.FStar_Parser_DesugarEnv.open_namespaces; FStar_Parser_DesugarEnv.modul_abbrevs = _49_3092.FStar_Parser_DesugarEnv.modul_abbrevs; FStar_Parser_DesugarEnv.sigaccum = _49_3092.FStar_Parser_DesugarEnv.sigaccum; FStar_Parser_DesugarEnv.localbindings = _49_3092.FStar_Parser_DesugarEnv.localbindings; FStar_Parser_DesugarEnv.recbindings = _49_3092.FStar_Parser_DesugarEnv.recbindings; FStar_Parser_DesugarEnv.phase = _49_3092.FStar_Parser_DesugarEnv.phase; FStar_Parser_DesugarEnv.sigmap = _49_3092.FStar_Parser_DesugarEnv.sigmap; FStar_Parser_DesugarEnv.default_result_effect = _49_3092.FStar_Parser_DesugarEnv.default_result_effect; FStar_Parser_DesugarEnv.iface = _49_3092.FStar_Parser_DesugarEnv.iface; FStar_Parser_DesugarEnv.admitted_iface = _49_3092.FStar_Parser_DesugarEnv.admitted_iface}) m.FStar_Absyn_Syntax.exports)
in (
# 1730 "FStar.Parser.Desugar.fst"
let env = (FStar_Parser_DesugarEnv.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_DesugarEnv.export_interface m.FStar_Absyn_Syntax.name env)
end else begin
env
end))
end)))




