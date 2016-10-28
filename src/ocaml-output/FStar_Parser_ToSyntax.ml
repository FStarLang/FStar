
open Prims

let trans_aqual : FStar_Parser_AST.arg_qualifier Prims.option  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _65_1 -> (match (_65_1) with
| Some (FStar_Parser_AST.Implicit) -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| Some (FStar_Parser_AST.Equality) -> begin
Some (FStar_Syntax_Syntax.Equality)
end
| _65_32 -> begin
None
end))


let trans_qual : FStar_Range.range  ->  FStar_Parser_AST.qualifier  ->  FStar_Syntax_Syntax.qualifier = (fun r _65_2 -> (match (_65_2) with
| FStar_Parser_AST.Private -> begin
FStar_Syntax_Syntax.Private
end
| FStar_Parser_AST.Assumption -> begin
FStar_Syntax_Syntax.Assumption
end
| FStar_Parser_AST.Unfold_for_unification_and_vcgen -> begin
FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen
end
| FStar_Parser_AST.Inline_for_extraction -> begin
FStar_Syntax_Syntax.Inline_for_extraction
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

let _65_46 = (FStar_TypeChecker_Errors.warn r "The \'opaque\' qualifier is deprecated since its use was strangely schizophrenic. There were two overloaded uses: (1) Given \'opaque val f : t\', the behavior was to exclude the definition of \'f\' to the SMT solver. This corresponds roughly to the new \'irreducible\' qualifier. (2) Given \'opaque type t = t\'\', the behavior was to provide the definition of \'t\' to the SMT solver, but not to inline it, unless absolutely required for unification. This corresponds roughly to the behavior of \'unfoldable\' (which is currently the default).")
in FStar_Syntax_Syntax.Visible_default)
end
| FStar_Parser_AST.Reflectable -> begin
FStar_Syntax_Syntax.Reflectable
end
| FStar_Parser_AST.Reifiable -> begin
FStar_Syntax_Syntax.Reifiable
end
| FStar_Parser_AST.Noeq -> begin
FStar_Syntax_Syntax.Noeq
end
| FStar_Parser_AST.Unopteq -> begin
FStar_Syntax_Syntax.Unopteq
end
| FStar_Parser_AST.DefaultEffect -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("The \'default\' qualifier on effects is no longer supported"), (r)))))
end
| (FStar_Parser_AST.Inline) | (FStar_Parser_AST.Visible) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unsupported qualifier"), (r)))))
end))


let trans_pragma : FStar_Parser_AST.pragma  ->  FStar_Syntax_Syntax.pragma = (fun _65_3 -> (match (_65_3) with
| FStar_Parser_AST.SetOptions (s) -> begin
FStar_Syntax_Syntax.SetOptions (s)
end
| FStar_Parser_AST.ResetOptions (sopt) -> begin
FStar_Syntax_Syntax.ResetOptions (sopt)
end))


let as_imp : FStar_Parser_AST.imp  ->  FStar_Syntax_Syntax.arg_qualifier Prims.option = (fun _65_4 -> (match (_65_4) with
| FStar_Parser_AST.Hash -> begin
Some (FStar_Syntax_Syntax.imp_tag)
end
| _65_63 -> begin
None
end))


let arg_withimp_e = (fun imp t -> ((t), ((as_imp imp))))


let arg_withimp_t = (fun imp t -> (match (imp) with
| FStar_Parser_AST.Hash -> begin
((t), (Some (FStar_Syntax_Syntax.imp_tag)))
end
| _65_70 -> begin
((t), (None))
end))


let contains_binder : FStar_Parser_AST.binder Prims.list  ->  Prims.bool = (fun binders -> (FStar_All.pipe_right binders (FStar_Util.for_some (fun b -> (match (b.FStar_Parser_AST.b) with
| FStar_Parser_AST.Annotated (_65_74) -> begin
true
end
| _65_77 -> begin
false
end)))))


let rec unparen : FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Paren (t) -> begin
(unparen t)
end
| _65_82 -> begin
t
end))


let tm_type_z : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _160_23 = (let _160_22 = (FStar_Ident.lid_of_path (("Type0")::[]) r)
in FStar_Parser_AST.Name (_160_22))
in (FStar_Parser_AST.mk_term _160_23 r FStar_Parser_AST.Kind)))


let tm_type : FStar_Range.range  ->  FStar_Parser_AST.term = (fun r -> (let _160_27 = (let _160_26 = (FStar_Ident.lid_of_path (("Type")::[]) r)
in FStar_Parser_AST.Name (_160_26))
in (FStar_Parser_AST.mk_term _160_27 r FStar_Parser_AST.Kind)))


let rec is_comp_type : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  Prims.bool = (fun env t -> (match (t.FStar_Parser_AST.tm) with
| (FStar_Parser_AST.Name (l)) | (FStar_Parser_AST.Construct (l, _)) -> begin
(let _160_32 = (FStar_Parser_Env.try_lookup_effect_name env l)
in (FStar_All.pipe_right _160_32 FStar_Option.isSome))
end
| FStar_Parser_AST.App (head, _65_95, _65_97) -> begin
(is_comp_type env head)
end
| (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) | (FStar_Parser_AST.LetOpen (_, t)) -> begin
(is_comp_type env t)
end
| _65_111 -> begin
false
end))


let unit_ty : FStar_Parser_AST.term = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.unit_lid)) FStar_Range.dummyRange FStar_Parser_AST.Type)


let compile_op : Prims.int  ->  Prims.string  ->  Prims.string = (fun arity s -> (

let name_of_char = (fun _65_5 -> (match (_65_5) with
| '&' -> begin
"Amp"
end
| '@' -> begin
"At"
end
| '+' -> begin
"Plus"
end
| '-' when (arity = (Prims.parse_int "1")) -> begin
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
| _65_133 -> begin
"UNKNOWN"
end))
in (

let rec aux = (fun i -> if (i = (FStar_String.length s)) then begin
[]
end else begin
(let _160_43 = (let _160_41 = (FStar_Util.char_at s i)
in (name_of_char _160_41))
in (let _160_42 = (aux (i + (Prims.parse_int "1")))
in (_160_43)::_160_42))
end)
in (match (s) with
| ".[]<-" -> begin
"op_String_Assignment"
end
| ".()<-" -> begin
"op_Array_Assignment"
end
| ".[]" -> begin
"op_String_Access"
end
| ".()" -> begin
"op_Array_Access"
end
| _65_142 -> begin
(let _160_45 = (let _160_44 = (aux (Prims.parse_int "0"))
in (FStar_String.concat "_" _160_44))
in (Prims.strcat "op_" _160_45))
end))))


let compile_op_lid : Prims.int  ->  Prims.string  ->  FStar_Range.range  ->  FStar_Ident.lident = (fun n s r -> (let _160_55 = (let _160_54 = (let _160_53 = (let _160_52 = (compile_op n s)
in ((_160_52), (r)))
in (FStar_Ident.mk_ident _160_53))
in (_160_54)::[])
in (FStar_All.pipe_right _160_55 FStar_Ident.lid_of_ids)))


let op_as_term : FStar_Parser_Env.env  ->  Prims.int  ->  FStar_Range.range  ->  Prims.string  ->  FStar_Syntax_Syntax.term Prims.option = (fun env arity rng s -> (

let r = (fun l dd -> (let _160_69 = (let _160_68 = (FStar_Syntax_Syntax.lid_as_fv (FStar_Ident.set_lid_range l rng) dd None)
in (FStar_All.pipe_right _160_68 FStar_Syntax_Syntax.fv_to_tm))
in Some (_160_69)))
in (

let fallback = (fun _65_154 -> (match (()) with
| () -> begin
(match (s) with
| "=" -> begin
(r FStar_Syntax_Const.op_Eq FStar_Syntax_Syntax.Delta_equational)
end
| ":=" -> begin
(r FStar_Syntax_Const.write_lid FStar_Syntax_Syntax.Delta_equational)
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
| "-" when (arity = (Prims.parse_int "1")) -> begin
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
(r FStar_Syntax_Const.not_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "2"))))
end
| "==" -> begin
(r FStar_Syntax_Const.eq2_lid FStar_Syntax_Syntax.Delta_constant)
end
| "<<" -> begin
(r FStar_Syntax_Const.precedes_lid FStar_Syntax_Syntax.Delta_constant)
end
| "/\\" -> begin
(r FStar_Syntax_Const.and_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))))
end
| "\\/" -> begin
(r FStar_Syntax_Const.or_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))))
end
| "==>" -> begin
(r FStar_Syntax_Const.imp_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))))
end
| "<==>" -> begin
(r FStar_Syntax_Const.iff_lid (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "2"))))
end
| _65_182 -> begin
None
end)
end))
in (match ((let _160_72 = (compile_op_lid arity s rng)
in (FStar_Parser_Env.try_lookup_lid env _160_72))) with
| Some (t) -> begin
Some ((Prims.fst t))
end
| _65_186 -> begin
(fallback ())
end))))


let sort_ftv : FStar_Ident.ident Prims.list  ->  FStar_Ident.ident Prims.list = (fun ftv -> (let _160_79 = (FStar_Util.remove_dups (fun x y -> (x.FStar_Ident.idText = y.FStar_Ident.idText)) ftv)
in (FStar_All.pipe_left (FStar_Util.sort_with (fun x y -> (FStar_String.compare x.FStar_Ident.idText y.FStar_Ident.idText))) _160_79)))


let rec free_type_vars_b : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Parser_Env.env * FStar_Ident.ident Prims.list) = (fun env binder -> (match (binder.FStar_Parser_AST.b) with
| FStar_Parser_AST.Variable (_65_195) -> begin
((env), ([]))
end
| FStar_Parser_AST.TVariable (x) -> begin
(

let _65_202 = (FStar_Parser_Env.push_bv env x)
in (match (_65_202) with
| (env, _65_201) -> begin
((env), ((x)::[]))
end))
end
| FStar_Parser_AST.Annotated (_65_204, term) -> begin
(let _160_86 = (free_type_vars env term)
in ((env), (_160_86)))
end
| FStar_Parser_AST.TAnnotated (id, _65_210) -> begin
(

let _65_216 = (FStar_Parser_Env.push_bv env id)
in (match (_65_216) with
| (env, _65_215) -> begin
((env), ([]))
end))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _160_87 = (free_type_vars env t)
in ((env), (_160_87)))
end))
and free_type_vars : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Ident.ident Prims.list = (fun env t -> (match ((let _160_90 = (unparen t)
in _160_90.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (_65_222) -> begin
(FStar_All.failwith "Impossible --- labeled source term")
end
| FStar_Parser_AST.Tvar (a) -> begin
(match ((FStar_Parser_Env.try_lookup_id env a)) with
| None -> begin
(a)::[]
end
| _65_228 -> begin
[]
end)
end
| (FStar_Parser_AST.Wild) | (FStar_Parser_AST.Const (_)) | (FStar_Parser_AST.Var (_)) | (FStar_Parser_AST.Name (_)) -> begin
[]
end
| (FStar_Parser_AST.Assign (_, t)) | (FStar_Parser_AST.Requires (t, _)) | (FStar_Parser_AST.Ensures (t, _)) | (FStar_Parser_AST.NamedTyp (_, t)) | (FStar_Parser_AST.Paren (t)) | (FStar_Parser_AST.Ascribed (t, _)) -> begin
(free_type_vars env t)
end
| FStar_Parser_AST.Construct (_65_262, ts) -> begin
(FStar_List.collect (fun _65_269 -> (match (_65_269) with
| (t, _65_268) -> begin
(free_type_vars env t)
end)) ts)
end
| FStar_Parser_AST.Op (_65_271, ts) -> begin
(FStar_List.collect (free_type_vars env) ts)
end
| FStar_Parser_AST.App (t1, t2, _65_278) -> begin
(let _160_93 = (free_type_vars env t1)
in (let _160_92 = (free_type_vars env t2)
in (FStar_List.append _160_93 _160_92)))
end
| FStar_Parser_AST.Refine (b, t) -> begin
(

let _65_287 = (free_type_vars_b env b)
in (match (_65_287) with
| (env, f) -> begin
(let _160_94 = (free_type_vars env t)
in (FStar_List.append f _160_94))
end))
end
| (FStar_Parser_AST.Product (binders, body)) | (FStar_Parser_AST.Sum (binders, body)) -> begin
(

let _65_303 = (FStar_List.fold_left (fun _65_296 binder -> (match (_65_296) with
| (env, free) -> begin
(

let _65_300 = (free_type_vars_b env binder)
in (match (_65_300) with
| (env, f) -> begin
((env), ((FStar_List.append f free)))
end))
end)) ((env), ([])) binders)
in (match (_65_303) with
| (env, free) -> begin
(let _160_97 = (free_type_vars env body)
in (FStar_List.append free _160_97))
end))
end
| FStar_Parser_AST.Project (t, _65_306) -> begin
(free_type_vars env t)
end
| (FStar_Parser_AST.Abs (_)) | (FStar_Parser_AST.Let (_)) | (FStar_Parser_AST.LetOpen (_)) | (FStar_Parser_AST.If (_)) | (FStar_Parser_AST.QForall (_)) | (FStar_Parser_AST.QExists (_)) | (FStar_Parser_AST.Record (_)) | (FStar_Parser_AST.Match (_)) | (FStar_Parser_AST.TryWith (_)) | (FStar_Parser_AST.Seq (_)) -> begin
[]
end))


let head_and_args : FStar_Parser_AST.term  ->  (FStar_Parser_AST.term * (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list) = (fun t -> (

let rec aux = (fun args t -> (match ((let _160_104 = (unparen t)
in _160_104.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (t, arg, imp) -> begin
(aux ((((arg), (imp)))::args) t)
end
| FStar_Parser_AST.Construct (l, args') -> begin
(({FStar_Parser_AST.tm = FStar_Parser_AST.Name (l); FStar_Parser_AST.range = t.FStar_Parser_AST.range; FStar_Parser_AST.level = t.FStar_Parser_AST.level}), ((FStar_List.append args' args)))
end
| _65_353 -> begin
((t), (args))
end))
in (aux [] t)))


let close : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _160_109 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _160_109))
in if ((FStar_List.length ftv) = (Prims.parse_int "0")) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _160_113 = (let _160_112 = (let _160_111 = (tm_type x.FStar_Ident.idRange)
in ((x), (_160_111)))
in FStar_Parser_AST.TAnnotated (_160_112))
in (FStar_Parser_AST.mk_binder _160_113 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result))
end))


let close_fun : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.term = (fun env t -> (

let ftv = (let _160_118 = (free_type_vars env t)
in (FStar_All.pipe_left sort_ftv _160_118))
in if ((FStar_List.length ftv) = (Prims.parse_int "0")) then begin
t
end else begin
(

let binders = (FStar_All.pipe_right ftv (FStar_List.map (fun x -> (let _160_122 = (let _160_121 = (let _160_120 = (tm_type x.FStar_Ident.idRange)
in ((x), (_160_120)))
in FStar_Parser_AST.TAnnotated (_160_121))
in (FStar_Parser_AST.mk_binder _160_122 x.FStar_Ident.idRange FStar_Parser_AST.Type (Some (FStar_Parser_AST.Implicit)))))))
in (

let t = (match ((let _160_123 = (unparen t)
in _160_123.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Product (_65_366) -> begin
t
end
| _65_369 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
end)
in (

let result = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((binders), (t)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
in result)))
end))


let rec uncurry : FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  (FStar_Parser_AST.binder Prims.list * FStar_Parser_AST.term) = (fun bs t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Product (binders, t) -> begin
(uncurry (FStar_List.append bs binders) t)
end
| _65_379 -> begin
((bs), (t))
end))


let rec is_var_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| (FStar_Parser_AST.PatWild) | (FStar_Parser_AST.PatTvar (_, _)) | (FStar_Parser_AST.PatVar (_, _)) -> begin
true
end
| FStar_Parser_AST.PatAscribed (p, _65_396) -> begin
(is_var_pattern p)
end
| _65_400 -> begin
false
end))


let rec is_app_pattern : FStar_Parser_AST.pattern  ->  Prims.bool = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, _65_404) -> begin
(is_app_pattern p)
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (_65_410); FStar_Parser_AST.prange = _65_408}, _65_414) -> begin
true
end
| _65_418 -> begin
false
end))


let replace_unit_pattern : FStar_Parser_AST.pattern  ->  FStar_Parser_AST.pattern = (fun p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatConst (FStar_Const.Const_unit) -> begin
(FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatAscribed ((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)), (unit_ty)))) p.FStar_Parser_AST.prange)
end
| _65_423 -> begin
p
end))


let rec destruct_app_pattern : FStar_Parser_Env.env  ->  Prims.bool  ->  FStar_Parser_AST.pattern  ->  ((FStar_Ident.ident, FStar_Ident.lident) FStar_Util.either * FStar_Parser_AST.pattern Prims.list * FStar_Parser_AST.term Prims.option) = (fun env is_top_level p -> (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _65_435 = (destruct_app_pattern env is_top_level p)
in (match (_65_435) with
| (name, args, _65_434) -> begin
((name), (args), (Some (t)))
end))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _65_440); FStar_Parser_AST.prange = _65_437}, args) when is_top_level -> begin
(let _160_141 = (let _160_140 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_160_140))
in ((_160_141), (args), (None)))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _65_451); FStar_Parser_AST.prange = _65_448}, args) -> begin
((FStar_Util.Inl (id)), (args), (None))
end
| _65_459 -> begin
(FStar_All.failwith "Not an app pattern")
end))


type bnd =
| LocalBinder of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual)
| LetBinder of (FStar_Ident.lident * FStar_Syntax_Syntax.term)


let is_LocalBinder = (fun _discr_ -> (match (_discr_) with
| LocalBinder (_) -> begin
true
end
| _ -> begin
false
end))


let is_LetBinder = (fun _discr_ -> (match (_discr_) with
| LetBinder (_) -> begin
true
end
| _ -> begin
false
end))


let ___LocalBinder____0 = (fun projectee -> (match (projectee) with
| LocalBinder (_65_462) -> begin
_65_462
end))


let ___LetBinder____0 = (fun projectee -> (match (projectee) with
| LetBinder (_65_465) -> begin
_65_465
end))


let binder_of_bnd : bnd  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.aqual) = (fun _65_6 -> (match (_65_6) with
| LocalBinder (a, aq) -> begin
((a), (aq))
end
| _65_472 -> begin
(FStar_All.failwith "Impossible")
end))


let as_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.arg_qualifier Prims.option  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term)  ->  (FStar_Syntax_Syntax.binder * FStar_Parser_Env.env) = (fun env imp _65_7 -> (match (_65_7) with
| (None, k) -> begin
(let _160_178 = (FStar_Syntax_Syntax.null_binder k)
in ((_160_178), (env)))
end
| (Some (a), k) -> begin
(

let _65_485 = (FStar_Parser_Env.push_bv env a)
in (match (_65_485) with
| (env, a) -> begin
(((((

let _65_486 = a
in {FStar_Syntax_Syntax.ppname = _65_486.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_486.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})), ((trans_aqual imp)))), (env))
end))
end))


type env_t =
FStar_Parser_Env.env


type lenv_t =
FStar_Syntax_Syntax.bv Prims.list


let mk_lb : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.term)  ->  FStar_Syntax_Syntax.letbinding = (fun _65_491 -> (match (_65_491) with
| (n, t, e) -> begin
{FStar_Syntax_Syntax.lbname = n; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = e}
end))


let no_annot_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun bs t -> (FStar_Syntax_Util.abs bs t None))


let mk_ref_read = (fun tm -> (

let tm' = (let _160_191 = (let _160_190 = (let _160_186 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.sread_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _160_186))
in (let _160_189 = (let _160_188 = (let _160_187 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (_160_187)))
in (_160_188)::[])
in ((_160_190), (_160_189))))
in FStar_Syntax_Syntax.Tm_app (_160_191))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_alloc = (fun tm -> (

let tm' = (let _160_198 = (let _160_197 = (let _160_193 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.salloc_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _160_193))
in (let _160_196 = (let _160_195 = (let _160_194 = (FStar_Syntax_Syntax.as_implicit false)
in ((tm), (_160_194)))
in (_160_195)::[])
in ((_160_197), (_160_196))))
in FStar_Syntax_Syntax.Tm_app (_160_198))
in (FStar_Syntax_Syntax.mk tm' None tm.FStar_Syntax_Syntax.pos)))


let mk_ref_assign = (fun t1 t2 pos -> (

let tm = (let _160_210 = (let _160_209 = (let _160_202 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.swrite_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _160_202))
in (let _160_208 = (let _160_207 = (let _160_203 = (FStar_Syntax_Syntax.as_implicit false)
in ((t1), (_160_203)))
in (let _160_206 = (let _160_205 = (let _160_204 = (FStar_Syntax_Syntax.as_implicit false)
in ((t2), (_160_204)))
in (_160_205)::[])
in (_160_207)::_160_206))
in ((_160_209), (_160_208))))
in FStar_Syntax_Syntax.Tm_app (_160_210))
in (FStar_Syntax_Syntax.mk tm None pos)))


let is_special_effect_combinator : Prims.string  ->  Prims.bool = (fun _65_8 -> (match (_65_8) with
| ("repr") | ("post") | ("pre") | ("wp") -> begin
true
end
| _65_508 -> begin
false
end))


let rec desugar_data_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat) = (fun env p is_mut -> (

let check_linear_pattern_variables = (fun p -> (

let rec pat_vars = (fun p -> (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_dot_term (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) | (FStar_Syntax_Syntax.Pat_constant (_)) -> begin
FStar_Syntax_Syntax.no_names
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(FStar_Util.set_add x FStar_Syntax_Syntax.no_names)
end
| FStar_Syntax_Syntax.Pat_cons (_65_528, pats) -> begin
(FStar_All.pipe_right pats (FStar_List.fold_left (fun out _65_536 -> (match (_65_536) with
| (p, _65_535) -> begin
(let _160_259 = (pat_vars p)
in (FStar_Util.set_union out _160_259))
end)) FStar_Syntax_Syntax.no_names))
end
| FStar_Syntax_Syntax.Pat_disj ([]) -> begin
(FStar_All.failwith "Impossible")
end
| FStar_Syntax_Syntax.Pat_disj ((hd)::tl) -> begin
(

let xs = (pat_vars hd)
in if (not ((FStar_Util.for_all (fun p -> (

let ys = (pat_vars p)
in ((FStar_Util.set_is_subset_of xs ys) && (FStar_Util.set_is_subset_of ys xs)))) tl))) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Disjunctive pattern binds different variables in each case"), (p.FStar_Syntax_Syntax.p)))))
end else begin
xs
end)
end))
in (pat_vars p)))
in (

let _65_559 = (match (((is_mut), (p.FStar_Parser_AST.pat))) with
| ((false, _)) | ((true, FStar_Parser_AST.PatVar (_))) -> begin
()
end
| (true, _65_557) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("let-mutable is for variables only"), (p.FStar_Parser_AST.prange)))))
end)
in (

let push_bv_maybe_mut = if is_mut then begin
FStar_Parser_Env.push_bv_mutable
end else begin
FStar_Parser_Env.push_bv
end
in (

let resolvex = (fun l e x -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun y -> (y.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = x.FStar_Ident.idText))))) with
| Some (y) -> begin
((l), (e), (y))
end
| _65_570 -> begin
(

let _65_573 = (push_bv_maybe_mut e x)
in (match (_65_573) with
| (e, x) -> begin
(((x)::l), (e), (x))
end))
end))
in (

let resolvea = (fun l e a -> (match ((FStar_All.pipe_right l (FStar_Util.find_opt (fun b -> (b.FStar_Syntax_Syntax.ppname.FStar_Ident.idText = a.FStar_Ident.idText))))) with
| Some (b) -> begin
((l), (e), (b))
end
| _65_582 -> begin
(

let _65_585 = (push_bv_maybe_mut e a)
in (match (_65_585) with
| (e, a) -> begin
(((a)::l), (e), (a))
end))
end))
in (

let rec aux = (fun loc env p -> (

let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p.FStar_Parser_AST.prange))
in (

let pos_r = (fun r q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n r))
in (match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (op) -> begin
(let _160_295 = (let _160_294 = (let _160_293 = (let _160_292 = (let _160_291 = (compile_op (Prims.parse_int "0") op)
in (FStar_Ident.id_of_text _160_291))
in ((_160_292), (None)))
in FStar_Parser_AST.PatVar (_160_293))
in {FStar_Parser_AST.pat = _160_294; FStar_Parser_AST.prange = p.FStar_Parser_AST.prange})
in (aux loc env _160_295))
end
| FStar_Parser_AST.PatOr ([]) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.PatOr ((p)::ps) -> begin
(

let _65_609 = (aux loc env p)
in (match (_65_609) with
| (loc, env, var, p, _65_608) -> begin
(

let _65_626 = (FStar_List.fold_left (fun _65_613 p -> (match (_65_613) with
| (loc, env, ps) -> begin
(

let _65_622 = (aux loc env p)
in (match (_65_622) with
| (loc, env, _65_618, p, _65_621) -> begin
((loc), (env), ((p)::ps))
end))
end)) ((loc), (env), ([])) ps)
in (match (_65_626) with
| (loc, env, ps) -> begin
(

let pat = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_disj ((p)::(FStar_List.rev ps))))
in ((loc), (env), (var), (pat), (false)))
end))
end))
end
| FStar_Parser_AST.PatAscribed (p, t) -> begin
(

let _65_637 = (aux loc env p)
in (match (_65_637) with
| (loc, env', binder, p, imp) -> begin
(

let binder = (match (binder) with
| LetBinder (_65_639) -> begin
(FStar_All.failwith "impossible")
end
| LocalBinder (x, aq) -> begin
(

let t = (let _160_298 = (close_fun env t)
in (desugar_term env _160_298))
in LocalBinder ((((

let _65_646 = x
in {FStar_Syntax_Syntax.ppname = _65_646.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_646.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (aq))))
end)
in ((loc), (env'), (binder), (p), (imp)))
end))
end
| FStar_Parser_AST.PatWild -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _160_299 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_wild (x)))
in ((loc), (env), (LocalBinder (((x), (None)))), (_160_299), (false))))
end
| FStar_Parser_AST.PatConst (c) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _160_300 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_constant (c)))
in ((loc), (env), (LocalBinder (((x), (None)))), (_160_300), (false))))
end
| (FStar_Parser_AST.PatTvar (x, aq)) | (FStar_Parser_AST.PatVar (x, aq)) -> begin
(

let imp = (aq = Some (FStar_Parser_AST.Implicit))
in (

let aq = (trans_aqual aq)
in (

let _65_665 = (resolvex loc env x)
in (match (_65_665) with
| (loc, env, xbv) -> begin
(let _160_301 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_var (xbv)))
in ((loc), (env), (LocalBinder (((xbv), (aq)))), (_160_301), (imp)))
end))))
end
| FStar_Parser_AST.PatName (l) -> begin
(

let l = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _160_302 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), ([])))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_160_302), (false)))))
end
| FStar_Parser_AST.PatApp ({FStar_Parser_AST.pat = FStar_Parser_AST.PatName (l); FStar_Parser_AST.prange = _65_671}, args) -> begin
(

let _65_693 = (FStar_List.fold_right (fun arg _65_682 -> (match (_65_682) with
| (loc, env, args) -> begin
(

let _65_689 = (aux loc env arg)
in (match (_65_689) with
| (loc, env, _65_686, arg, imp) -> begin
((loc), (env), ((((arg), (imp)))::args))
end))
end)) args ((loc), (env), ([])))
in (match (_65_693) with
| (loc, env, args) -> begin
(

let l = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_datacon env) l)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _160_305 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_160_305), (false)))))
end))
end
| FStar_Parser_AST.PatApp (_65_697) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatList (pats) -> begin
(

let _65_717 = (FStar_List.fold_right (fun pat _65_705 -> (match (_65_705) with
| (loc, env, pats) -> begin
(

let _65_713 = (aux loc env pat)
in (match (_65_713) with
| (loc, env, _65_709, pat, _65_712) -> begin
((loc), (env), ((pat)::pats))
end))
end)) pats ((loc), (env), ([])))
in (match (_65_717) with
| (loc, env, pats) -> begin
(

let pat = (let _160_318 = (let _160_317 = (let _160_313 = (FStar_Range.end_range p.FStar_Parser_AST.prange)
in (pos_r _160_313))
in (let _160_316 = (let _160_315 = (let _160_314 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.nil_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_160_314), ([])))
in FStar_Syntax_Syntax.Pat_cons (_160_315))
in (FStar_All.pipe_left _160_317 _160_316)))
in (FStar_List.fold_right (fun hd tl -> (

let r = (FStar_Range.union_ranges hd.FStar_Syntax_Syntax.p tl.FStar_Syntax_Syntax.p)
in (let _160_312 = (let _160_311 = (let _160_310 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.cons_lid FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor)))
in ((_160_310), ((((hd), (false)))::(((tl), (false)))::[])))
in FStar_Syntax_Syntax.Pat_cons (_160_311))
in (FStar_All.pipe_left (pos_r r) _160_312)))) pats _160_318))
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in ((loc), (env), (LocalBinder (((x), (None)))), (pat), (false))))
end))
end
| FStar_Parser_AST.PatTuple (args, dep) -> begin
(

let _65_743 = (FStar_List.fold_left (fun _65_730 p -> (match (_65_730) with
| (loc, env, pats) -> begin
(

let _65_739 = (aux loc env p)
in (match (_65_739) with
| (loc, env, _65_735, pat, _65_738) -> begin
((loc), (env), ((((pat), (false)))::pats))
end))
end)) ((loc), (env), ([])) args)
in (match (_65_743) with
| (loc, env, args) -> begin
(

let args = (FStar_List.rev args)
in (

let l = if dep then begin
(FStar_Syntax_Util.mk_dtuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end else begin
(FStar_Syntax_Util.mk_tuple_data_lid (FStar_List.length args) p.FStar_Parser_AST.prange)
end
in (

let _65_749 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) l)
in (match (_65_749) with
| (constr, _65_748) -> begin
(

let l = (match (constr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| _65_753 -> begin
(FStar_All.failwith "impossible")
end)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p.FStar_Parser_AST.prange)) FStar_Syntax_Syntax.tun)
in (let _160_321 = (FStar_All.pipe_left pos (FStar_Syntax_Syntax.Pat_cons (((l), (args)))))
in ((loc), (env), (LocalBinder (((x), (None)))), (_160_321), (false)))))
end))))
end))
end
| FStar_Parser_AST.PatRecord ([]) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected pattern"), (p.FStar_Parser_AST.prange)))))
end
| FStar_Parser_AST.PatRecord (fields) -> begin
(

let _65_763 = (FStar_List.hd fields)
in (match (_65_763) with
| (f, _65_762) -> begin
(

let _65_767 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_65_767) with
| (record, _65_766) -> begin
(

let fields = (FStar_All.pipe_right fields (FStar_List.map (fun _65_770 -> (match (_65_770) with
| (f, p) -> begin
(let _160_323 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.qualify_field_to_record env record) f)
in ((_160_323), (p)))
end))))
in (

let args = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _65_775 -> (match (_65_775) with
| (f, _65_774) -> begin
(match ((FStar_All.pipe_right fields (FStar_List.tryFind (fun _65_779 -> (match (_65_779) with
| (g, _65_778) -> begin
(FStar_Ident.lid_equals f g)
end))))) with
| None -> begin
(FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild p.FStar_Parser_AST.prange)
end
| Some (_65_782, p) -> begin
p
end)
end))))
in (

let app = (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatApp ((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatName (record.FStar_Parser_Env.constrname)) p.FStar_Parser_AST.prange)), (args)))) p.FStar_Parser_AST.prange)
in (

let _65_794 = (aux loc env app)
in (match (_65_794) with
| (env, e, b, p, _65_793) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_cons (fv, args) -> begin
(let _160_332 = (let _160_331 = (let _160_330 = (

let _65_799 = fv
in (let _160_329 = (let _160_328 = (let _160_327 = (let _160_326 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_Env.typename), (_160_326)))
in FStar_Syntax_Syntax.Record_ctor (_160_327))
in Some (_160_328))
in {FStar_Syntax_Syntax.fv_name = _65_799.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = _65_799.FStar_Syntax_Syntax.fv_delta; FStar_Syntax_Syntax.fv_qual = _160_329}))
in ((_160_330), (args)))
in FStar_Syntax_Syntax.Pat_cons (_160_331))
in (FStar_All.pipe_left pos _160_332))
end
| _65_802 -> begin
p
end)
in ((env), (e), (b), (p), (false)))
end)))))
end))
end))
end))))
in (

let _65_811 = (aux [] env p)
in (match (_65_811) with
| (_65_805, env, b, p, _65_810) -> begin
(

let _65_812 = (let _160_333 = (check_linear_pattern_variables p)
in (FStar_All.pipe_left Prims.ignore _160_333))
in ((env), (b), (p)))
end)))))))))
and desugar_binding_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  Prims.bool  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun top env p is_mut -> (

let mklet = (fun x -> (let _160_342 = (let _160_341 = (let _160_340 = (FStar_Parser_Env.qualify env x)
in ((_160_340), (FStar_Syntax_Syntax.tun)))
in LetBinder (_160_341))
in ((env), (_160_342), (None))))
in if top then begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatOp (x) -> begin
(let _160_344 = (let _160_343 = (compile_op (Prims.parse_int "0") x)
in (FStar_Ident.id_of_text _160_343))
in (mklet _160_344))
end
| FStar_Parser_AST.PatVar (x, _65_824) -> begin
(mklet x)
end
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (x, _65_831); FStar_Parser_AST.prange = _65_828}, t) -> begin
(let _160_348 = (let _160_347 = (let _160_346 = (FStar_Parser_Env.qualify env x)
in (let _160_345 = (desugar_term env t)
in ((_160_346), (_160_345))))
in LetBinder (_160_347))
in ((env), (_160_348), (None)))
end
| _65_839 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected pattern at the top-level"), (p.FStar_Parser_AST.prange)))))
end)
end else begin
(

let _65_843 = (desugar_data_pat env p is_mut)
in (match (_65_843) with
| (env, binder, p) -> begin
(

let p = (match (p.FStar_Syntax_Syntax.v) with
| (FStar_Syntax_Syntax.Pat_var (_)) | (FStar_Syntax_Syntax.Pat_wild (_)) -> begin
None
end
| _65_851 -> begin
Some (p)
end)
in ((env), (binder), (p)))
end))
end))
and desugar_binding_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * bnd * FStar_Syntax_Syntax.pat Prims.option) = (fun env p -> (desugar_binding_pat_maybe_top false env p false))
and desugar_match_pat_maybe_top : Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun _65_855 env pat -> (

let _65_863 = (desugar_data_pat env pat false)
in (match (_65_863) with
| (env, _65_861, pat) -> begin
((env), (pat))
end)))
and desugar_match_pat : FStar_Parser_Env.env  ->  FStar_Parser_AST.pattern  ->  (env_t * FStar_Syntax_Syntax.pat) = (fun env p -> (desugar_match_pat_maybe_top false env p))
and desugar_term : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let _65_868 = env
in {FStar_Parser_Env.curmodule = _65_868.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _65_868.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _65_868.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _65_868.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _65_868.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _65_868.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _65_868.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _65_868.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _65_868.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _65_868.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _65_868.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = false})
in (desugar_term_maybe_top false env e)))
and desugar_typ : FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env e -> (

let env = (

let _65_873 = env
in {FStar_Parser_Env.curmodule = _65_873.FStar_Parser_Env.curmodule; FStar_Parser_Env.modules = _65_873.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _65_873.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _65_873.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _65_873.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _65_873.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _65_873.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _65_873.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _65_873.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _65_873.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _65_873.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = true})
in (desugar_term_maybe_top false env e)))
and desugar_machine_integer : FStar_Parser_Env.env  ->  Prims.string  ->  (FStar_Const.signedness * FStar_Const.width)  ->  FStar_Range.range  ->  (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax = (fun env repr _65_880 range -> (match (_65_880) with
| (signedness, width) -> begin
(

let lid = (Prims.strcat "FStar." (Prims.strcat (match (signedness) with
| FStar_Const.Unsigned -> begin
"U"
end
| FStar_Const.Signed -> begin
""
end) (Prims.strcat "Int" (Prims.strcat (match (width) with
| FStar_Const.Int8 -> begin
"8"
end
| FStar_Const.Int16 -> begin
"16"
end
| FStar_Const.Int32 -> begin
"32"
end
| FStar_Const.Int64 -> begin
"64"
end) (Prims.strcat "." (Prims.strcat (match (signedness) with
| FStar_Const.Unsigned -> begin
"u"
end
| FStar_Const.Signed -> begin
""
end) "int_to_t"))))))
in (

let lid = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text lid) range)
in (

let lid = (match ((FStar_Parser_Env.try_lookup_lid env lid)) with
| Some (lid) -> begin
(Prims.fst lid)
end
| None -> begin
(let _160_364 = (FStar_Util.format1 "%s not in scope\n" (FStar_Ident.text_of_lid lid))
in (FStar_All.failwith _160_364))
end)
in (

let repr = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (((repr), (None))))) None range)
in (let _160_369 = (let _160_368 = (let _160_367 = (let _160_366 = (let _160_365 = (FStar_Syntax_Syntax.as_implicit false)
in ((repr), (_160_365)))
in (_160_366)::[])
in ((lid), (_160_367)))
in FStar_Syntax_Syntax.Tm_app (_160_368))
in (FStar_Syntax_Syntax.mk _160_369 None range))))))
end))
and desugar_term_maybe_top : Prims.bool  ->  env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun top_level env top -> (

let mk = (fun e -> (FStar_Syntax_Syntax.mk e None top.FStar_Parser_AST.range))
in (

let setpos = (fun e -> (

let _65_904 = e
in {FStar_Syntax_Syntax.n = _65_904.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _65_904.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = top.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _65_904.FStar_Syntax_Syntax.vars}))
in (match ((let _160_377 = (unparen top)
in _160_377.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Wild -> begin
(setpos FStar_Syntax_Syntax.tun)
end
| FStar_Parser_AST.Labeled (_65_908) -> begin
(desugar_formula env top)
end
| FStar_Parser_AST.Requires (t, lopt) -> begin
(desugar_formula env t)
end
| FStar_Parser_AST.Ensures (t, lopt) -> begin
(desugar_formula env t)
end
| FStar_Parser_AST.Const (FStar_Const.Const_int (i, Some (size))) -> begin
(desugar_machine_integer env i size top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Const (c) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (c)))
end
| FStar_Parser_AST.Op ("=!=", args) -> begin
(desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Op ((("~"), (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Op ((("=="), (args)))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))::[])))) top.FStar_Parser_AST.range top.FStar_Parser_AST.level))
end
| FStar_Parser_AST.Op ("*", (_65_934)::(_65_932)::[]) when (let _160_378 = (op_as_term env (Prims.parse_int "2") top.FStar_Parser_AST.range "*")
in (FStar_All.pipe_right _160_378 FStar_Option.isNone)) -> begin
(

let rec flatten = (fun t -> (match (t.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Op ("*", (t1)::(t2)::[]) -> begin
(let _160_381 = (flatten t1)
in (FStar_List.append _160_381 ((t2)::[])))
end
| _65_947 -> begin
(t)::[]
end))
in (

let targs = (let _160_385 = (let _160_382 = (unparen top)
in (flatten _160_382))
in (FStar_All.pipe_right _160_385 (FStar_List.map (fun t -> (let _160_384 = (desugar_typ env t)
in (FStar_Syntax_Syntax.as_arg _160_384))))))
in (

let _65_953 = (let _160_386 = (FStar_Syntax_Util.mk_tuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) _160_386))
in (match (_65_953) with
| (tup, _65_952) -> begin
(mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))))
end
| FStar_Parser_AST.Tvar (a) -> begin
(let _160_388 = (let _160_387 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) a)
in (Prims.fst _160_387))
in (FStar_All.pipe_left setpos _160_388))
end
| FStar_Parser_AST.Op (s, args) -> begin
(match ((op_as_term env (FStar_List.length args) top.FStar_Parser_AST.range s)) with
| None -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((((Prims.strcat "Unexpected or unbound operator: " s)), (top.FStar_Parser_AST.range)))))
end
| Some (op) -> begin
if ((FStar_List.length args) > (Prims.parse_int "0")) then begin
(

let args = (FStar_All.pipe_right args (FStar_List.map (fun t -> (let _160_390 = (desugar_term env t)
in ((_160_390), (None))))))
in (mk (FStar_Syntax_Syntax.Tm_app (((op), (args))))))
end else begin
op
end
end)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _65_971; FStar_Ident.ident = _65_969; FStar_Ident.nsstr = _65_967; FStar_Ident.str = "Type0"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_zero)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _65_980; FStar_Ident.ident = _65_978; FStar_Ident.nsstr = _65_976; FStar_Ident.str = "Type"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _65_989; FStar_Ident.ident = _65_987; FStar_Ident.nsstr = _65_985; FStar_Ident.str = "Effect"}) -> begin
(mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_effect)))
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _65_998; FStar_Ident.ident = _65_996; FStar_Ident.nsstr = _65_994; FStar_Ident.str = "True"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.true_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant None)
end
| FStar_Parser_AST.Name ({FStar_Ident.ns = _65_1007; FStar_Ident.ident = _65_1005; FStar_Ident.nsstr = _65_1003; FStar_Ident.str = "False"}) -> begin
(FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.false_lid top.FStar_Parser_AST.range) FStar_Syntax_Syntax.Delta_constant None)
end
| FStar_Parser_AST.Var ({FStar_Ident.ns = (eff)::rest; FStar_Ident.ident = {FStar_Ident.idText = txt; FStar_Ident.idRange = _65_1015}; FStar_Ident.nsstr = _65_1013; FStar_Ident.str = _65_1011}) when ((is_special_effect_combinator txt) && (let _160_391 = (FStar_Ident.lid_of_ids ((eff)::rest))
in (FStar_Parser_Env.is_effect_name env _160_391))) -> begin
(match ((let _160_392 = (FStar_Ident.lid_of_ids ((eff)::rest))
in (FStar_Parser_Env.try_lookup_effect_defn env _160_392))) with
| Some (ed) -> begin
(let _160_393 = (FStar_Ident.lid_of_path (FStar_Ident.path_of_text (Prims.strcat (FStar_Ident.text_of_lid ed.FStar_Syntax_Syntax.mname) (Prims.strcat "_" txt))) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.fvar _160_393 (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None))
end
| None -> begin
(FStar_All.failwith "immpossible special_effect_combinator")
end)
end
| FStar_Parser_AST.Assign (ident, t2) -> begin
(

let t2 = (desugar_term env t2)
in (

let _65_1033 = (FStar_Parser_Env.fail_or2 (FStar_Parser_Env.try_lookup_id env) ident)
in (match (_65_1033) with
| (t1, mut) -> begin
(

let _65_1034 = if (not (mut)) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Can only assign to mutable values"), (top.FStar_Parser_AST.range)))))
end else begin
()
end
in (mk_ref_assign t1 t2 top.FStar_Parser_AST.range))
end)))
end
| (FStar_Parser_AST.Var (l)) | (FStar_Parser_AST.Name (l)) -> begin
(

let _65_1041 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) l)
in (match (_65_1041) with
| (tm, mut) -> begin
(

let tm = (setpos tm)
in if mut then begin
(let _160_396 = (let _160_395 = (let _160_394 = (mk_ref_read tm)
in ((_160_394), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_rval))))
in FStar_Syntax_Syntax.Tm_meta (_160_395))
in (FStar_All.pipe_left mk _160_396))
end else begin
tm
end)
end))
end
| FStar_Parser_AST.Construct (l, args) -> begin
(match ((FStar_Parser_Env.try_lookup_datacon env l)) with
| Some (head) -> begin
(

let _65_1051 = (let _160_397 = (mk (FStar_Syntax_Syntax.Tm_fvar (head)))
in ((_160_397), (true)))
in (match (_65_1051) with
| (head, is_data) -> begin
(match (args) with
| [] -> begin
head
end
| _65_1054 -> begin
(

let args = (FStar_List.map (fun _65_1057 -> (match (_65_1057) with
| (t, imp) -> begin
(

let te = (desugar_term env t)
in (arg_withimp_e imp te))
end)) args)
in (

let app = (mk (FStar_Syntax_Syntax.Tm_app (((head), (args)))))
in if is_data then begin
(mk (FStar_Syntax_Syntax.Tm_meta (((app), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app))))))
end else begin
app
end))
end)
end))
end
| None -> begin
(

let l = (FStar_Parser_Env.expand_module_abbrev env l)
in (

let env = (FStar_Parser_Env.push_namespace env l)
in (match (args) with
| ((e, _65_1066))::[] -> begin
(desugar_term_maybe_top top_level env e)
end
| _65_1070 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("The Foo.Bar (...) local open takes exactly one argument"), (top.FStar_Parser_AST.range)))))
end)))
end)
end
| FStar_Parser_AST.Sum (binders, t) -> begin
(

let _65_1095 = (FStar_List.fold_left (fun _65_1078 b -> (match (_65_1078) with
| (env, tparams, typs) -> begin
(

let _65_1082 = (desugar_binder env b)
in (match (_65_1082) with
| (xopt, t) -> begin
(

let _65_1088 = (match (xopt) with
| None -> begin
(let _160_401 = (FStar_Syntax_Syntax.new_bv (Some (top.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in ((env), (_160_401)))
end
| Some (x) -> begin
(FStar_Parser_Env.push_bv env x)
end)
in (match (_65_1088) with
| (env, x) -> begin
(let _160_405 = (let _160_404 = (let _160_403 = (let _160_402 = (no_annot_abs tparams t)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _160_402))
in (_160_403)::[])
in (FStar_List.append typs _160_404))
in ((env), ((FStar_List.append tparams (((((

let _65_1089 = x
in {FStar_Syntax_Syntax.ppname = _65_1089.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_1089.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t})), (None)))::[]))), (_160_405)))
end))
end))
end)) ((env), ([]), ([])) (FStar_List.append binders (((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range FStar_Parser_AST.Type None))::[])))
in (match (_65_1095) with
| (env, _65_1093, targs) -> begin
(

let _65_1099 = (let _160_406 = (FStar_Syntax_Util.mk_dtuple_lid (FStar_List.length targs) top.FStar_Parser_AST.range)
in (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) _160_406))
in (match (_65_1099) with
| (tup, _65_1098) -> begin
(FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_app (((tup), (targs)))))
end))
end))
end
| FStar_Parser_AST.Product (binders, t) -> begin
(

let _65_1106 = (uncurry binders t)
in (match (_65_1106) with
| (bs, t) -> begin
(

let rec aux = (fun env bs _65_9 -> (match (_65_9) with
| [] -> begin
(

let cod = (desugar_comp top.FStar_Parser_AST.range true env t)
in (let _160_413 = (FStar_Syntax_Util.arrow (FStar_List.rev bs) cod)
in (FStar_All.pipe_left setpos _160_413)))
end
| (hd)::tl -> begin
(

let mlenv = (FStar_Parser_Env.default_ml env)
in (

let bb = (desugar_binder mlenv hd)
in (

let _65_1120 = (as_binder env hd.FStar_Parser_AST.aqual bb)
in (match (_65_1120) with
| (b, env) -> begin
(aux env ((b)::bs) tl)
end))))
end))
in (aux env [] bs))
end))
end
| FStar_Parser_AST.Refine (b, f) -> begin
(match ((desugar_binder env b)) with
| (None, _65_1127) -> begin
(FStar_All.failwith "Missing binder in refinement")
end
| b -> begin
(

let _65_1135 = (as_binder env None b)
in (match (_65_1135) with
| ((x, _65_1132), env) -> begin
(

let f = (desugar_formula env f)
in (let _160_414 = (FStar_Syntax_Util.refine x f)
in (FStar_All.pipe_left setpos _160_414)))
end))
end)
end
| FStar_Parser_AST.Abs (binders, body) -> begin
(

let binders = (FStar_All.pipe_right binders (FStar_List.map replace_unit_pattern))
in (

let _65_1156 = (FStar_List.fold_left (fun _65_1144 pat -> (match (_65_1144) with
| (env, ftvs) -> begin
(match (pat.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed (_65_1147, t) -> begin
(let _160_418 = (let _160_417 = (free_type_vars env t)
in (FStar_List.append _160_417 ftvs))
in ((env), (_160_418)))
end
| _65_1152 -> begin
((env), (ftvs))
end)
end)) ((env), ([])) binders)
in (match (_65_1156) with
| (_65_1154, ftv) -> begin
(

let ftv = (sort_ftv ftv)
in (

let binders = (let _160_420 = (FStar_All.pipe_right ftv (FStar_List.map (fun a -> (FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatTvar (((a), (Some (FStar_Parser_AST.Implicit))))) top.FStar_Parser_AST.range))))
in (FStar_List.append _160_420 binders))
in (

let rec aux = (fun env bs sc_pat_opt _65_10 -> (match (_65_10) with
| [] -> begin
(

let body = (desugar_term env body)
in (

let body = (match (sc_pat_opt) with
| Some (sc, pat) -> begin
(

let body = (let _160_430 = (let _160_429 = (FStar_Syntax_Syntax.pat_bvs pat)
in (FStar_All.pipe_right _160_429 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_Syntax_Subst.close _160_430 body))
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_match (((sc), ((((pat), (None), (body)))::[])))) None body.FStar_Syntax_Syntax.pos))
end
| None -> begin
body
end)
in (let _160_431 = (no_annot_abs (FStar_List.rev bs) body)
in (setpos _160_431))))
end
| (p)::rest -> begin
(

let _65_1180 = (desugar_binding_pat env p)
in (match (_65_1180) with
| (env, b, pat) -> begin
(

let _65_1231 = (match (b) with
| LetBinder (_65_1182) -> begin
(FStar_All.failwith "Impossible")
end
| LocalBinder (x, aq) -> begin
(

let sc_pat_opt = (match (((pat), (sc_pat_opt))) with
| (None, _65_1190) -> begin
sc_pat_opt
end
| (Some (p), None) -> begin
(let _160_433 = (let _160_432 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_160_432), (p)))
in Some (_160_433))
end
| (Some (p), Some (sc, p')) -> begin
(match (((sc.FStar_Syntax_Syntax.n), (p'.FStar_Syntax_Syntax.v))) with
| (FStar_Syntax_Syntax.Tm_name (_65_1204), _65_1207) -> begin
(

let tup2 = (let _160_434 = (FStar_Syntax_Util.mk_tuple_data_lid (Prims.parse_int "2") top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _160_434 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (let _160_442 = (let _160_441 = (let _160_440 = (mk (FStar_Syntax_Syntax.Tm_fvar (tup2)))
in (let _160_439 = (let _160_438 = (FStar_Syntax_Syntax.as_arg sc)
in (let _160_437 = (let _160_436 = (let _160_435 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _160_435))
in (_160_436)::[])
in (_160_438)::_160_437))
in ((_160_440), (_160_439))))
in FStar_Syntax_Syntax.Tm_app (_160_441))
in (FStar_Syntax_Syntax.mk _160_442 None top.FStar_Parser_AST.range))
in (

let p = (let _160_443 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tup2), ((((p'), (false)))::(((p), (false)))::[])))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _160_443))
in Some (((sc), (p))))))
end
| (FStar_Syntax_Syntax.Tm_app (_65_1213, args), FStar_Syntax_Syntax.Pat_cons (_65_1218, pats)) -> begin
(

let tupn = (let _160_444 = (FStar_Syntax_Util.mk_tuple_data_lid ((Prims.parse_int "1") + (FStar_List.length args)) top.FStar_Parser_AST.range)
in (FStar_Syntax_Syntax.lid_as_fv _160_444 FStar_Syntax_Syntax.Delta_constant (Some (FStar_Syntax_Syntax.Data_ctor))))
in (

let sc = (let _160_451 = (let _160_450 = (let _160_449 = (mk (FStar_Syntax_Syntax.Tm_fvar (tupn)))
in (let _160_448 = (let _160_447 = (let _160_446 = (let _160_445 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _160_445))
in (_160_446)::[])
in (FStar_List.append args _160_447))
in ((_160_449), (_160_448))))
in FStar_Syntax_Syntax.Tm_app (_160_450))
in (mk _160_451))
in (

let p = (let _160_452 = (FStar_Range.union_ranges p'.FStar_Syntax_Syntax.p p.FStar_Syntax_Syntax.p)
in (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_cons (((tupn), ((FStar_List.append pats ((((p), (false)))::[])))))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n _160_452))
in Some (((sc), (p))))))
end
| _65_1227 -> begin
(FStar_All.failwith "Impossible")
end)
end)
in ((((x), (aq))), (sc_pat_opt)))
end)
in (match (_65_1231) with
| (b, sc_pat_opt) -> begin
(aux env ((b)::bs) sc_pat_opt rest)
end))
end))
end))
in (aux env [] None binders))))
end)))
end
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (a); FStar_Parser_AST.range = rng; FStar_Parser_AST.level = _65_1233}, phi, _65_1240) when ((FStar_Ident.lid_equals a FStar_Syntax_Const.assert_lid) || (FStar_Ident.lid_equals a FStar_Syntax_Const.assume_lid)) -> begin
(

let phi = (desugar_formula env phi)
in (

let a = (FStar_Ident.set_lid_range a rng)
in (let _160_460 = (let _160_459 = (let _160_458 = (FStar_Syntax_Syntax.fvar a FStar_Syntax_Syntax.Delta_equational None)
in (let _160_457 = (let _160_456 = (FStar_Syntax_Syntax.as_arg phi)
in (let _160_455 = (let _160_454 = (let _160_453 = (mk (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_unit)))
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _160_453))
in (_160_454)::[])
in (_160_456)::_160_455))
in ((_160_458), (_160_457))))
in FStar_Syntax_Syntax.Tm_app (_160_459))
in (mk _160_460))))
end
| FStar_Parser_AST.App (_65_1246) -> begin
(

let rec aux = (fun args e -> (match ((let _160_465 = (unparen e)
in _160_465.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App (e, t, imp) -> begin
(

let arg = (let _160_466 = (desugar_term env t)
in (FStar_All.pipe_left (arg_withimp_e imp) _160_466))
in (aux ((arg)::args) e))
end
| _65_1258 -> begin
(

let head = (desugar_term env e)
in (mk (FStar_Syntax_Syntax.Tm_app (((head), (args))))))
end))
in (aux [] top))
end
| FStar_Parser_AST.Seq (t1, t2) -> begin
(let _160_469 = (let _160_468 = (let _160_467 = (desugar_term env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern FStar_Parser_AST.PatWild t1.FStar_Parser_AST.range)), (t1)))::[]), (t2)))) top.FStar_Parser_AST.range FStar_Parser_AST.Expr))
in ((_160_467), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Sequence))))
in FStar_Syntax_Syntax.Tm_meta (_160_468))
in (mk _160_469))
end
| FStar_Parser_AST.LetOpen (lid, e) -> begin
(

let lid = (FStar_Parser_Env.expand_module_abbrev env lid)
in (

let env = (FStar_Parser_Env.push_namespace env lid)
in (desugar_term_maybe_top top_level env e)))
end
| FStar_Parser_AST.Let (qual, ((pat, _snd))::_tl, body) -> begin
(

let is_rec = (qual = FStar_Parser_AST.Rec)
in (

let ds_let_rec_or_app = (fun _65_1281 -> (match (()) with
| () -> begin
(

let bindings = (((pat), (_snd)))::_tl
in (

let funs = (FStar_All.pipe_right bindings (FStar_List.map (fun _65_1285 -> (match (_65_1285) with
| (p, def) -> begin
if (is_app_pattern p) then begin
(let _160_473 = (destruct_app_pattern env top_level p)
in ((_160_473), (def)))
end else begin
(match ((FStar_Parser_AST.un_function p def)) with
| Some (p, def) -> begin
(let _160_474 = (destruct_app_pattern env top_level p)
in ((_160_474), (def)))
end
| _65_1291 -> begin
(match (p.FStar_Parser_AST.pat) with
| FStar_Parser_AST.PatAscribed ({FStar_Parser_AST.pat = FStar_Parser_AST.PatVar (id, _65_1296); FStar_Parser_AST.prange = _65_1293}, t) -> begin
if top_level then begin
(let _160_477 = (let _160_476 = (let _160_475 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_160_475))
in ((_160_476), ([]), (Some (t))))
in ((_160_477), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (Some (t)))), (def))
end
end
| FStar_Parser_AST.PatVar (id, _65_1305) -> begin
if top_level then begin
(let _160_480 = (let _160_479 = (let _160_478 = (FStar_Parser_Env.qualify env id)
in FStar_Util.Inr (_160_478))
in ((_160_479), ([]), (None)))
in ((_160_480), (def)))
end else begin
((((FStar_Util.Inl (id)), ([]), (None))), (def))
end
end
| _65_1309 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected let binding"), (p.FStar_Parser_AST.prange)))))
end)
end)
end
end))))
in (

let _65_1338 = (FStar_List.fold_left (fun _65_1314 _65_1323 -> (match (((_65_1314), (_65_1323))) with
| ((env, fnames, rec_bindings), ((f, _65_1317, _65_1319), _65_1322)) -> begin
(

let _65_1334 = (match (f) with
| FStar_Util.Inl (x) -> begin
(

let _65_1328 = (FStar_Parser_Env.push_bv env x)
in (match (_65_1328) with
| (env, xx) -> begin
(let _160_484 = (let _160_483 = (FStar_Syntax_Syntax.mk_binder xx)
in (_160_483)::rec_bindings)
in ((env), (FStar_Util.Inl (xx)), (_160_484)))
end))
end
| FStar_Util.Inr (l) -> begin
(let _160_485 = (FStar_Parser_Env.push_top_level_rec_binding env l.FStar_Ident.ident FStar_Syntax_Syntax.Delta_equational)
in ((_160_485), (FStar_Util.Inr (l)), (rec_bindings)))
end)
in (match (_65_1334) with
| (env, lbname, rec_bindings) -> begin
((env), ((lbname)::fnames), (rec_bindings))
end))
end)) ((env), ([]), ([])) funs)
in (match (_65_1338) with
| (env', fnames, rec_bindings) -> begin
(

let fnames = (FStar_List.rev fnames)
in (

let desugar_one_def = (fun env lbname _65_1349 -> (match (_65_1349) with
| ((_65_1344, args, result_t), def) -> begin
(

let args = (FStar_All.pipe_right args (FStar_List.map replace_unit_pattern))
in (

let def = (match (result_t) with
| None -> begin
def
end
| Some (t) -> begin
(

let _65_1358 = if (is_comp_type env t) then begin
(match ((FStar_All.pipe_right args (FStar_List.tryFind (fun x -> (not ((is_var_pattern x))))))) with
| None -> begin
()
end
| Some (p) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Computation type annotations are only permitted on let-bindings without inlined patterns; replace this pattern with a variable"), (p.FStar_Parser_AST.prange)))))
end)
end else begin
()
end
in (let _160_493 = (FStar_Range.union_ranges t.FStar_Parser_AST.range def.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term (FStar_Parser_AST.Ascribed (((def), (t)))) _160_493 FStar_Parser_AST.Expr)))
end)
in (

let def = (match (args) with
| [] -> begin
def
end
| _65_1363 -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.un_curry_abs args def) top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
end)
in (

let body = (desugar_term env def)
in (

let lbname = (match (lbname) with
| FStar_Util.Inl (x) -> begin
FStar_Util.Inl (x)
end
| FStar_Util.Inr (l) -> begin
(let _160_495 = (let _160_494 = (FStar_Syntax_Util.incr_delta_qualifier body)
in (FStar_Syntax_Syntax.lid_as_fv l _160_494 None))
in FStar_Util.Inr (_160_495))
end)
in (

let body = if is_rec then begin
(FStar_Syntax_Subst.close rec_bindings body)
end else begin
body
end
in (mk_lb ((lbname), (FStar_Syntax_Syntax.tun), (body)))))))))
end))
in (

let lbs = (FStar_List.map2 (desugar_one_def (if is_rec then begin
env'
end else begin
env
end)) fnames funs)
in (

let body = (desugar_term env' body)
in (let _160_498 = (let _160_497 = (let _160_496 = (FStar_Syntax_Subst.close rec_bindings body)
in ((((is_rec), (lbs))), (_160_496)))
in FStar_Syntax_Syntax.Tm_let (_160_497))
in (FStar_All.pipe_left mk _160_498))))))
end))))
end))
in (

let ds_non_rec = (fun pat t1 t2 -> (

let t1 = (desugar_term env t1)
in (

let is_mutable = (qual = FStar_Parser_AST.Mutable)
in (

let t1 = if is_mutable then begin
(mk_ref_alloc t1)
end else begin
t1
end
in (

let _65_1384 = (desugar_binding_pat_maybe_top top_level env pat is_mutable)
in (match (_65_1384) with
| (env, binder, pat) -> begin
(

let tm = (match (binder) with
| LetBinder (l, t) -> begin
(

let body = (desugar_term env t2)
in (

let fv = (let _160_505 = (FStar_Syntax_Util.incr_delta_qualifier t1)
in (FStar_Syntax_Syntax.lid_as_fv l _160_505 None))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_let (((((false), (({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = t; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_ALL_lid; FStar_Syntax_Syntax.lbdef = t1})::[]))), (body)))))))
end
| LocalBinder (x, _65_1393) -> begin
(

let body = (desugar_term env t2)
in (

let body = (match (pat) with
| (None) | (Some ({FStar_Syntax_Syntax.v = FStar_Syntax_Syntax.Pat_wild (_); FStar_Syntax_Syntax.ty = _; FStar_Syntax_Syntax.p = _})) -> begin
body
end
| Some (pat) -> begin
(let _160_510 = (let _160_509 = (let _160_508 = (FStar_Syntax_Syntax.bv_to_name x)
in (let _160_507 = (let _160_506 = (FStar_Syntax_Util.branch ((pat), (None), (body)))
in (_160_506)::[])
in ((_160_508), (_160_507))))
in FStar_Syntax_Syntax.Tm_match (_160_509))
in (FStar_Syntax_Syntax.mk _160_510 None body.FStar_Syntax_Syntax.pos))
end)
in (let _160_515 = (let _160_514 = (let _160_513 = (let _160_512 = (let _160_511 = (FStar_Syntax_Syntax.mk_binder x)
in (_160_511)::[])
in (FStar_Syntax_Subst.close _160_512 body))
in ((((false), (((mk_lb ((FStar_Util.Inl (x)), (x.FStar_Syntax_Syntax.sort), (t1))))::[]))), (_160_513)))
in FStar_Syntax_Syntax.Tm_let (_160_514))
in (FStar_All.pipe_left mk _160_515))))
end)
in if is_mutable then begin
(FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((tm), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Mutable_alloc))))))
end else begin
tm
end)
end))))))
in if (is_rec || (is_app_pattern pat)) then begin
(ds_let_rec_or_app ())
end else begin
(ds_non_rec pat _snd body)
end)))
end
| FStar_Parser_AST.If (t1, t2, t3) -> begin
(

let x = (FStar_Syntax_Syntax.new_bv (Some (t3.FStar_Parser_AST.range)) FStar_Syntax_Syntax.tun)
in (let _160_526 = (let _160_525 = (let _160_524 = (desugar_term env t1)
in (let _160_523 = (let _160_522 = (let _160_517 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool (true))) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t2.FStar_Parser_AST.range)
in (let _160_516 = (desugar_term env t2)
in ((_160_517), (None), (_160_516))))
in (let _160_521 = (let _160_520 = (let _160_519 = (FStar_Syntax_Syntax.withinfo (FStar_Syntax_Syntax.Pat_wild (x)) FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n t3.FStar_Parser_AST.range)
in (let _160_518 = (desugar_term env t3)
in ((_160_519), (None), (_160_518))))
in (_160_520)::[])
in (_160_522)::_160_521))
in ((_160_524), (_160_523))))
in FStar_Syntax_Syntax.Tm_match (_160_525))
in (mk _160_526)))
end
| FStar_Parser_AST.TryWith (e, branches) -> begin
(

let r = top.FStar_Parser_AST.range
in (

let handler = (FStar_Parser_AST.mk_function branches r r)
in (

let body = (FStar_Parser_AST.mk_function (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatConst (FStar_Const.Const_unit)) r)), (None), (e)))::[]) r r)
in (

let a1 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Var (FStar_Syntax_Const.try_with_lid)) r top.FStar_Parser_AST.level)), (body), (FStar_Parser_AST.Nothing)))) r top.FStar_Parser_AST.level)
in (

let a2 = (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((a1), (handler), (FStar_Parser_AST.Nothing)))) r top.FStar_Parser_AST.level)
in (desugar_term env a2))))))
end
| FStar_Parser_AST.Match (e, branches) -> begin
(

let desugar_branch = (fun _65_1434 -> (match (_65_1434) with
| (pat, wopt, b) -> begin
(

let _65_1437 = (desugar_match_pat env pat)
in (match (_65_1437) with
| (env, pat) -> begin
(

let wopt = (match (wopt) with
| None -> begin
None
end
| Some (e) -> begin
(let _160_529 = (desugar_term env e)
in Some (_160_529))
end)
in (

let b = (desugar_term env b)
in (FStar_Syntax_Util.branch ((pat), (wopt), (b)))))
end))
end))
in (let _160_533 = (let _160_532 = (let _160_531 = (desugar_term env e)
in (let _160_530 = (FStar_List.map desugar_branch branches)
in ((_160_531), (_160_530))))
in FStar_Syntax_Syntax.Tm_match (_160_532))
in (FStar_All.pipe_left mk _160_533)))
end
| FStar_Parser_AST.Ascribed (e, t) -> begin
(

let env = (FStar_Parser_Env.default_ml env)
in (

let c = (desugar_comp t.FStar_Parser_AST.range true env t)
in (

let annot = if (FStar_Syntax_Util.is_ml_comp c) then begin
FStar_Util.Inl ((FStar_Syntax_Util.comp_result c))
end else begin
FStar_Util.Inr (c)
end
in (let _160_536 = (let _160_535 = (let _160_534 = (desugar_term env e)
in ((_160_534), (annot), (None)))
in FStar_Syntax_Syntax.Tm_ascribed (_160_535))
in (FStar_All.pipe_left mk _160_536)))))
end
| FStar_Parser_AST.Record (_65_1451, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected empty record"), (top.FStar_Parser_AST.range)))))
end
| FStar_Parser_AST.Record (eopt, fields) -> begin
(

let _65_1462 = (FStar_List.hd fields)
in (match (_65_1462) with
| (f, _65_1461) -> begin
(

let qfn = (fun g -> (FStar_Ident.lid_of_ids (FStar_List.append f.FStar_Ident.ns ((g)::[]))))
in (

let _65_1468 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_record_by_field_name env) f)
in (match (_65_1468) with
| (record, _65_1467) -> begin
(

let get_field = (fun xopt f -> (

let fn = f.FStar_Ident.ident
in (

let found = (FStar_All.pipe_right fields (FStar_Util.find_opt (fun _65_1476 -> (match (_65_1476) with
| (g, _65_1475) -> begin
(

let gn = g.FStar_Ident.ident
in (fn.FStar_Ident.idText = gn.FStar_Ident.idText))
end))))
in (match (found) with
| Some (_65_1480, e) -> begin
(let _160_544 = (qfn fn)
in ((_160_544), (e)))
end
| None -> begin
(match (xopt) with
| None -> begin
(let _160_547 = (let _160_546 = (let _160_545 = (FStar_Util.format1 "Field %s is missing" (FStar_Ident.text_of_lid f))
in ((_160_545), (top.FStar_Parser_AST.range)))
in FStar_Syntax_Syntax.Error (_160_546))
in (Prims.raise _160_547))
end
| Some (x) -> begin
(let _160_548 = (qfn fn)
in ((_160_548), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Project (((x), (f)))) x.FStar_Parser_AST.range x.FStar_Parser_AST.level))))
end)
end))))
in (

let recterm = (match (eopt) with
| None -> begin
(let _160_553 = (let _160_552 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _65_1492 -> (match (_65_1492) with
| (f, _65_1491) -> begin
(let _160_551 = (let _160_550 = (get_field None f)
in (FStar_All.pipe_left Prims.snd _160_550))
in ((_160_551), (FStar_Parser_AST.Nothing)))
end))))
in ((record.FStar_Parser_Env.constrname), (_160_552)))
in FStar_Parser_AST.Construct (_160_553))
end
| Some (e) -> begin
(

let x = (FStar_Ident.gen e.FStar_Parser_AST.range)
in (

let xterm = (let _160_555 = (let _160_554 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_160_554))
in (FStar_Parser_AST.mk_term _160_555 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
in (

let record = (let _160_558 = (let _160_557 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map (fun _65_1500 -> (match (_65_1500) with
| (f, _65_1499) -> begin
(get_field (Some (xterm)) f)
end))))
in ((None), (_160_557)))
in FStar_Parser_AST.Record (_160_558))
in FStar_Parser_AST.Let (((FStar_Parser_AST.NoLetQualifier), (((((FStar_Parser_AST.mk_pattern (FStar_Parser_AST.PatVar (((x), (None)))) x.FStar_Ident.idRange)), (e)))::[]), ((FStar_Parser_AST.mk_term record top.FStar_Parser_AST.range top.FStar_Parser_AST.level)))))))
end)
in (

let recterm = (FStar_Parser_AST.mk_term recterm top.FStar_Parser_AST.range top.FStar_Parser_AST.level)
in (

let e = (desugar_term env recterm)
in (match (e.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _65_1516; FStar_Syntax_Syntax.pos = _65_1514; FStar_Syntax_Syntax.vars = _65_1512}, args); FStar_Syntax_Syntax.tk = _65_1510; FStar_Syntax_Syntax.pos = _65_1508; FStar_Syntax_Syntax.vars = _65_1506}, FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)) -> begin
(

let e = (let _160_565 = (let _160_564 = (let _160_563 = (let _160_562 = (let _160_561 = (let _160_560 = (let _160_559 = (FStar_All.pipe_right record.FStar_Parser_Env.fields (FStar_List.map Prims.fst))
in ((record.FStar_Parser_Env.typename), (_160_559)))
in FStar_Syntax_Syntax.Record_ctor (_160_560))
in Some (_160_561))
in (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v e.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant _160_562))
in ((_160_563), (args)))
in FStar_Syntax_Syntax.Tm_app (_160_564))
in (FStar_All.pipe_left mk _160_565))
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((e), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Data_app)))))))
end
| _65_1530 -> begin
e
end)))))
end)))
end))
end
| FStar_Parser_AST.Project (e, f) -> begin
(

let _65_1537 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_projector_by_field_name env) f)
in (match (_65_1537) with
| (fieldname, is_rec) -> begin
(

let e = (desugar_term env e)
in (

let fn = (

let _65_1542 = (FStar_Util.prefix fieldname.FStar_Ident.ns)
in (match (_65_1542) with
| (ns, _65_1541) -> begin
(FStar_Ident.lid_of_ids (FStar_List.append ns ((f.FStar_Ident.ident)::[])))
end))
in (

let qual = if is_rec then begin
Some (FStar_Syntax_Syntax.Record_projector (fn))
end else begin
None
end
in (let _160_570 = (let _160_569 = (let _160_568 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range fieldname (FStar_Ident.range_of_lid f)) FStar_Syntax_Syntax.Delta_equational qual)
in (let _160_567 = (let _160_566 = (FStar_Syntax_Syntax.as_arg e)
in (_160_566)::[])
in ((_160_568), (_160_567))))
in FStar_Syntax_Syntax.Tm_app (_160_569))
in (FStar_All.pipe_left mk _160_570)))))
end))
end
| (FStar_Parser_AST.NamedTyp (_, e)) | (FStar_Parser_AST.Paren (e)) -> begin
(desugar_term env e)
end
| _65_1552 when (top.FStar_Parser_AST.level = FStar_Parser_AST.Formula) -> begin
(desugar_formula env top)
end
| _65_1554 -> begin
(FStar_Parser_AST.error "Unexpected term" top top.FStar_Parser_AST.range)
end
| FStar_Parser_AST.Let (_65_1556, _65_1558, _65_1560) -> begin
(FStar_All.failwith "Not implemented yet")
end
| FStar_Parser_AST.QForall (_65_1564, _65_1566, _65_1568) -> begin
(FStar_All.failwith "Not implemented yet")
end
| FStar_Parser_AST.QExists (_65_1572, _65_1574, _65_1576) -> begin
(FStar_All.failwith "Not implemented yet")
end))))
and desugar_args : FStar_Parser_Env.env  ->  (FStar_Parser_AST.term * FStar_Parser_AST.imp) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env args -> (FStar_All.pipe_right args (FStar_List.map (fun _65_1583 -> (match (_65_1583) with
| (a, imp) -> begin
(let _160_574 = (desugar_term env a)
in (arg_withimp_e imp _160_574))
end)))))
and desugar_comp : FStar_Range.range  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.term  ->  (FStar_Syntax_Syntax.comp', Prims.unit) FStar_Syntax_Syntax.syntax = (fun r default_ok env t -> (

let fail = (fun msg -> (Prims.raise (FStar_Syntax_Syntax.Error (((msg), (r))))))
in (

let is_requires = (fun _65_1595 -> (match (_65_1595) with
| (t, _65_1594) -> begin
(match ((let _160_582 = (unparen t)
in _160_582.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Requires (_65_1597) -> begin
true
end
| _65_1600 -> begin
false
end)
end))
in (

let is_ensures = (fun _65_1605 -> (match (_65_1605) with
| (t, _65_1604) -> begin
(match ((let _160_585 = (unparen t)
in _160_585.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Ensures (_65_1607) -> begin
true
end
| _65_1610 -> begin
false
end)
end))
in (

let is_app = (fun head _65_1616 -> (match (_65_1616) with
| (t, _65_1615) -> begin
(match ((let _160_590 = (unparen t)
in _160_590.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.App ({FStar_Parser_AST.tm = FStar_Parser_AST.Var (d); FStar_Parser_AST.range = _65_1620; FStar_Parser_AST.level = _65_1618}, _65_1625, _65_1627) -> begin
(d.FStar_Ident.ident.FStar_Ident.idText = head)
end
| _65_1631 -> begin
false
end)
end))
in (

let is_decreases = (is_app "decreases")
in (

let pre_process_comp_typ = (fun t -> (

let _65_1637 = (head_and_args t)
in (match (_65_1637) with
| (head, args) -> begin
(match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (lemma) when (lemma.FStar_Ident.ident.FStar_Ident.idText = "Lemma") -> begin
(

let unit_tm = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.unit_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Type)), (FStar_Parser_AST.Nothing))
in (

let nil_pat = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.nil_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Expr)), (FStar_Parser_AST.Nothing))
in (

let req_true = (((FStar_Parser_AST.mk_term (FStar_Parser_AST.Requires ((((FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.true_lid)) t.FStar_Parser_AST.range FStar_Parser_AST.Formula)), (None)))) t.FStar_Parser_AST.range FStar_Parser_AST.Type)), (FStar_Parser_AST.Nothing))
in (

let args = (match (args) with
| [] -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Not enough arguments to \'Lemma\'"), (t.FStar_Parser_AST.range)))))
end
| (ens)::[] -> begin
(unit_tm)::(req_true)::(ens)::(nil_pat)::[]
end
| (req)::(ens)::[] when ((is_requires req) && (is_ensures ens)) -> begin
(unit_tm)::(req)::(ens)::(nil_pat)::[]
end
| (ens)::(dec)::[] when ((is_ensures ens) && (is_decreases dec)) -> begin
(unit_tm)::(req_true)::(ens)::(nil_pat)::(dec)::[]
end
| (req)::(ens)::(dec)::[] when (((is_requires req) && (is_ensures ens)) && (is_app "decreases" dec)) -> begin
(unit_tm)::(req)::(ens)::(nil_pat)::(dec)::[]
end
| more -> begin
(unit_tm)::more
end)
in (

let head = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_name env) lemma)
in ((head), (args)))))))
end
| FStar_Parser_AST.Name (l) when (FStar_Parser_Env.is_effect_name env l) -> begin
(let _160_594 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_name env) l)
in ((_160_594), (args)))
end
| FStar_Parser_AST.Name (l) when ((let _160_595 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _160_595 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "Tot")) -> begin
(((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)), (args))
end
| FStar_Parser_AST.Name (l) when ((let _160_596 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals _160_596 FStar_Syntax_Const.prims_lid)) && (l.FStar_Ident.ident.FStar_Ident.idText = "GTot")) -> begin
(((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_GTot_lid head.FStar_Parser_AST.range)), (args))
end
| FStar_Parser_AST.Name (l) when ((((l.FStar_Ident.ident.FStar_Ident.idText = "Type") || (l.FStar_Ident.ident.FStar_Ident.idText = "Type0")) || (l.FStar_Ident.ident.FStar_Ident.idText = "Effect")) && default_ok) -> begin
(((FStar_Ident.set_lid_range FStar_Syntax_Const.effect_Tot_lid head.FStar_Parser_AST.range)), ((((t), (FStar_Parser_AST.Nothing)))::[]))
end
| _65_1668 when default_ok -> begin
(((FStar_Ident.set_lid_range env.FStar_Parser_Env.default_result_effect head.FStar_Parser_AST.range)), ((((t), (FStar_Parser_AST.Nothing)))::[]))
end
| _65_1670 -> begin
(let _160_598 = (let _160_597 = (FStar_Parser_AST.term_to_string t)
in (FStar_Util.format1 "%s is not an effect" _160_597))
in (fail _160_598))
end)
end)))
in (

let _65_1673 = (pre_process_comp_typ t)
in (match (_65_1673) with
| (eff, args) -> begin
(

let _65_1674 = if ((FStar_List.length args) = (Prims.parse_int "0")) then begin
(let _160_600 = (let _160_599 = (FStar_Syntax_Print.lid_to_string eff)
in (FStar_Util.format1 "Not enough args to effect %s" _160_599))
in (fail _160_600))
end else begin
()
end
in (

let _65_1678 = (let _160_602 = (FStar_List.hd args)
in (let _160_601 = (FStar_List.tl args)
in ((_160_602), (_160_601))))
in (match (_65_1678) with
| (result_arg, rest) -> begin
(

let result_typ = (desugar_typ env (Prims.fst result_arg))
in (

let rest = (desugar_args env rest)
in (

let _65_1703 = (FStar_All.pipe_right rest (FStar_List.partition (fun _65_1684 -> (match (_65_1684) with
| (t, _65_1683) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.tk = _65_1690; FStar_Syntax_Syntax.pos = _65_1688; FStar_Syntax_Syntax.vars = _65_1686}, (_65_1695)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.decreases_lid)
end
| _65_1700 -> begin
false
end)
end))))
in (match (_65_1703) with
| (dec, rest) -> begin
(

let decreases_clause = (FStar_All.pipe_right dec (FStar_List.map (fun _65_1707 -> (match (_65_1707) with
| (t, _65_1706) -> begin
(match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (_65_1709, ((arg, _65_1712))::[]) -> begin
FStar_Syntax_Syntax.DECREASES (arg)
end
| _65_1718 -> begin
(FStar_All.failwith "impos")
end)
end))))
in (

let no_additional_args = (((FStar_List.length decreases_clause) = (Prims.parse_int "0")) && ((FStar_List.length rest) = (Prims.parse_int "0")))
in if (no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Tot_lid)) then begin
(FStar_Syntax_Syntax.mk_Total result_typ)
end else begin
if (no_additional_args && (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_GTot_lid)) then begin
(FStar_Syntax_Syntax.mk_GTotal result_typ)
end else begin
(

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

let rest = if (FStar_Ident.lid_equals eff FStar_Syntax_Const.effect_Lemma_lid) then begin
(match (rest) with
| (req)::(ens)::((pat, aq))::[] -> begin
(

let pat = (match (pat.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.nil_lid) -> begin
(

let nil = (FStar_Syntax_Syntax.mk_Tm_uinst pat ((FStar_Syntax_Syntax.U_succ (FStar_Syntax_Syntax.U_zero))::[]))
in (

let pattern = (let _160_605 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range FStar_Syntax_Const.pattern_lid pat.FStar_Syntax_Syntax.pos) FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.mk_Tm_uinst _160_605 ((FStar_Syntax_Syntax.U_zero)::[])))
in (FStar_Syntax_Syntax.mk_Tm_app nil ((((pattern), (Some (FStar_Syntax_Syntax.imp_tag))))::[]) None pat.FStar_Syntax_Syntax.pos)))
end
| _65_1733 -> begin
pat
end)
in (let _160_609 = (let _160_608 = (let _160_607 = (let _160_606 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((pat), (FStar_Syntax_Syntax.Meta_desugared (FStar_Syntax_Syntax.Meta_smt_pat))))) None pat.FStar_Syntax_Syntax.pos)
in ((_160_606), (aq)))
in (_160_607)::[])
in (ens)::_160_608)
in (req)::_160_609))
end
| _65_1736 -> begin
rest
end)
end else begin
rest
end
in (FStar_Syntax_Syntax.mk_Comp {FStar_Syntax_Syntax.comp_univs = []; FStar_Syntax_Syntax.effect_name = eff; FStar_Syntax_Syntax.result_typ = result_typ; FStar_Syntax_Syntax.effect_args = rest; FStar_Syntax_Syntax.flags = (FStar_List.append flags decreases_clause)})))
end
end))
end))))
end)))
end)))))))))
and desugar_formula : env_t  ->  FStar_Parser_AST.term  ->  FStar_Syntax_Syntax.term = (fun env f -> (

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
| _65_1748 -> begin
None
end))
in (

let mk = (fun t -> (FStar_Syntax_Syntax.mk t None f.FStar_Parser_AST.range))
in (

let pos = (fun t -> (t None f.FStar_Parser_AST.range))
in (

let setpos = (fun t -> (

let _65_1755 = t
in {FStar_Syntax_Syntax.n = _65_1755.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.tk = _65_1755.FStar_Syntax_Syntax.tk; FStar_Syntax_Syntax.pos = f.FStar_Parser_AST.range; FStar_Syntax_Syntax.vars = _65_1755.FStar_Syntax_Syntax.vars}))
in (

let desugar_quant = (fun q b pats body -> (

let tk = (desugar_binder env (

let _65_1762 = b
in {FStar_Parser_AST.b = _65_1762.FStar_Parser_AST.b; FStar_Parser_AST.brange = _65_1762.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _65_1762.FStar_Parser_AST.aqual}))
in (

let desugar_pats = (fun env pats -> (FStar_List.map (fun es -> (FStar_All.pipe_right es (FStar_List.map (fun e -> (let _160_644 = (desugar_term env e)
in (FStar_All.pipe_left (arg_withimp_t FStar_Parser_AST.Nothing) _160_644)))))) pats))
in (match (tk) with
| (Some (a), k) -> begin
(

let _65_1776 = (FStar_Parser_Env.push_bv env a)
in (match (_65_1776) with
| (env, a) -> begin
(

let a = (

let _65_1777 = a
in {FStar_Syntax_Syntax.ppname = _65_1777.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_1777.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in (

let pats = (desugar_pats env pats)
in (

let body = (desugar_formula env body)
in (

let body = (match (pats) with
| [] -> begin
body
end
| _65_1784 -> begin
(mk (FStar_Syntax_Syntax.Tm_meta (((body), (FStar_Syntax_Syntax.Meta_pattern (pats))))))
end)
in (

let body = (let _160_647 = (let _160_646 = (let _160_645 = (FStar_Syntax_Syntax.mk_binder a)
in (_160_645)::[])
in (no_annot_abs _160_646 body))
in (FStar_All.pipe_left setpos _160_647))
in (let _160_652 = (let _160_651 = (let _160_650 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range q b.FStar_Parser_AST.brange) (FStar_Syntax_Syntax.Delta_defined_at_level ((Prims.parse_int "1"))) None)
in (let _160_649 = (let _160_648 = (FStar_Syntax_Syntax.as_arg body)
in (_160_648)::[])
in ((_160_650), (_160_649))))
in FStar_Syntax_Syntax.Tm_app (_160_651))
in (FStar_All.pipe_left mk _160_652)))))))
end))
end
| _65_1788 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let push_quant = (fun q binders pats body -> (match (binders) with
| (b)::(b')::_rest -> begin
(

let rest = (b')::_rest
in (

let body = (let _160_667 = (q ((rest), (pats), (body)))
in (let _160_666 = (FStar_Range.union_ranges b'.FStar_Parser_AST.brange body.FStar_Parser_AST.range)
in (FStar_Parser_AST.mk_term _160_667 _160_666 FStar_Parser_AST.Formula)))
in (let _160_668 = (q (((b)::[]), ([]), (body)))
in (FStar_Parser_AST.mk_term _160_668 f.FStar_Parser_AST.range FStar_Parser_AST.Formula))))
end
| _65_1802 -> begin
(FStar_All.failwith "impossible")
end))
in (match ((let _160_669 = (unparen f)
in _160_669.FStar_Parser_AST.tm)) with
| FStar_Parser_AST.Labeled (f, l, p) -> begin
(

let f = (desugar_formula env f)
in (FStar_All.pipe_left mk (FStar_Syntax_Syntax.Tm_meta (((f), (FStar_Syntax_Syntax.Meta_labeled (((l), (f.FStar_Syntax_Syntax.pos), (p)))))))))
end
| (FStar_Parser_AST.QForall ([], _, _)) | (FStar_Parser_AST.QExists ([], _, _)) -> begin
(FStar_All.failwith "Impossible: Quantifier without binders")
end
| FStar_Parser_AST.QForall ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _160_671 = (push_quant (fun x -> FStar_Parser_AST.QForall (x)) binders pats body)
in (desugar_formula env _160_671)))
end
| FStar_Parser_AST.QExists ((_1)::(_2)::_3, pats, body) -> begin
(

let binders = (_1)::(_2)::_3
in (let _160_673 = (push_quant (fun x -> FStar_Parser_AST.QExists (x)) binders pats body)
in (desugar_formula env _160_673)))
end
| FStar_Parser_AST.QForall ((b)::[], pats, body) -> begin
(desugar_quant FStar_Syntax_Const.forall_lid b pats body)
end
| FStar_Parser_AST.QExists ((b)::[], pats, body) -> begin
(desugar_quant FStar_Syntax_Const.exists_lid b pats body)
end
| FStar_Parser_AST.Paren (f) -> begin
(desugar_formula env f)
end
| _65_1860 -> begin
(desugar_term env f)
end))))))))
and typars_of_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list) = (fun env bs -> (

let _65_1884 = (FStar_List.fold_left (fun _65_1865 b -> (match (_65_1865) with
| (env, out) -> begin
(

let tk = (desugar_binder env (

let _65_1867 = b
in {FStar_Parser_AST.b = _65_1867.FStar_Parser_AST.b; FStar_Parser_AST.brange = _65_1867.FStar_Parser_AST.brange; FStar_Parser_AST.blevel = FStar_Parser_AST.Formula; FStar_Parser_AST.aqual = _65_1867.FStar_Parser_AST.aqual}))
in (match (tk) with
| (Some (a), k) -> begin
(

let _65_1876 = (FStar_Parser_Env.push_bv env a)
in (match (_65_1876) with
| (env, a) -> begin
(

let a = (

let _65_1877 = a
in {FStar_Syntax_Syntax.ppname = _65_1877.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_1877.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k})
in ((env), ((((a), ((trans_aqual b.FStar_Parser_AST.aqual))))::out)))
end))
end
| _65_1881 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected binder"), (b.FStar_Parser_AST.brange)))))
end))
end)) ((env), ([])) bs)
in (match (_65_1884) with
| (env, tpars) -> begin
((env), ((FStar_List.rev tpars)))
end)))
and desugar_binder : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder  ->  (FStar_Ident.ident Prims.option * FStar_Syntax_Syntax.term) = (fun env b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.TAnnotated (x, t)) | (FStar_Parser_AST.Annotated (x, t)) -> begin
(let _160_680 = (desugar_typ env t)
in ((Some (x)), (_160_680)))
end
| FStar_Parser_AST.TVariable (x) -> begin
(let _160_681 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type (FStar_Syntax_Syntax.U_unknown)) None x.FStar_Ident.idRange)
in ((Some (x)), (_160_681)))
end
| FStar_Parser_AST.NoName (t) -> begin
(let _160_682 = (desugar_typ env t)
in ((None), (_160_682)))
end
| FStar_Parser_AST.Variable (x) -> begin
((Some (x)), (FStar_Syntax_Syntax.tun))
end))


let mk_data_discriminators : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  FStar_Ident.lid  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun quals env t tps k datas -> (

let quals = (FStar_All.pipe_right quals (FStar_List.filter (fun _65_11 -> (match (_65_11) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| _65_1909 -> begin
false
end))))
in (

let quals = (fun q -> if ((FStar_All.pipe_left Prims.op_Negation env.FStar_Parser_Env.iface) || env.FStar_Parser_Env.admitted_iface) then begin
(FStar_List.append ((FStar_Syntax_Syntax.Assumption)::q) quals)
end else begin
(FStar_List.append q quals)
end)
in (

let binders = (let _160_699 = (let _160_698 = (FStar_Syntax_Util.arrow_formals k)
in (Prims.fst _160_698))
in (FStar_List.append tps _160_699))
in (

let p = (FStar_Ident.range_of_lid t)
in (

let _65_1917 = (FStar_Syntax_Util.args_of_binders binders)
in (match (_65_1917) with
| (binders, args) -> begin
(

let imp_binders = (FStar_All.pipe_right binders (FStar_List.map (fun _65_1921 -> (match (_65_1921) with
| (x, _65_1920) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (

let binders = (let _160_705 = (let _160_704 = (let _160_703 = (let _160_702 = (let _160_701 = (FStar_Syntax_Syntax.lid_as_fv t FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _160_701))
in (FStar_Syntax_Syntax.mk_Tm_app _160_702 args None p))
in (FStar_All.pipe_left FStar_Syntax_Syntax.null_binder _160_703))
in (_160_704)::[])
in (FStar_List.append imp_binders _160_705))
in (

let disc_type = (let _160_708 = (let _160_707 = (let _160_706 = (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.bool_lid FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _160_706))
in (FStar_Syntax_Syntax.mk_Total _160_707))
in (FStar_Syntax_Util.arrow binders _160_708))
in (FStar_All.pipe_right datas (FStar_List.map (fun d -> (

let disc_name = (FStar_Syntax_Util.mk_discriminator d)
in (let _160_711 = (let _160_710 = (quals ((FStar_Syntax_Syntax.Logic)::(FStar_Syntax_Syntax.Discriminator (d))::[]))
in ((disc_name), ([]), (disc_type), (_160_710), ((FStar_Ident.range_of_lid disc_name))))
in FStar_Syntax_Syntax.Sig_declare_typ (_160_711)))))))))
end)))))))


let mk_indexed_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Syntax_Syntax.fv_qual  ->  Prims.bool  ->  FStar_Parser_Env.env  ->  FStar_Ident.lident  ->  FStar_Ident.lid  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binder Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals fvq refine_domain env tc lid inductive_tps imp_tps fields t -> (

let p = (FStar_Ident.range_of_lid lid)
in (

let pos = (fun q -> (FStar_Syntax_Syntax.withinfo q FStar_Syntax_Syntax.tun.FStar_Syntax_Syntax.n p))
in (

let projectee = (fun ptyp -> (FStar_Syntax_Syntax.gen_bv "projectee" (Some (p)) ptyp))
in (

let tps = (FStar_List.map2 (fun _65_1945 _65_1949 -> (match (((_65_1945), (_65_1949))) with
| ((_65_1943, imp), (x, _65_1948)) -> begin
((x), (imp))
end)) inductive_tps imp_tps)
in (

let _65_2050 = (

let _65_1953 = (FStar_Syntax_Util.head_and_args t)
in (match (_65_1953) with
| (head, args0) -> begin
(

let args = (

let rec arguments = (fun tps args -> (match (((tps), (args))) with
| ([], _65_1959) -> begin
args
end
| (_65_1962, []) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Not enough arguments to type"), ((FStar_Ident.range_of_lid lid))))))
end
| (((_65_1967, Some (FStar_Syntax_Syntax.Implicit (_65_1969))))::tps', ((_65_1976, Some (FStar_Syntax_Syntax.Implicit (_65_1978))))::args') -> begin
(arguments tps' args')
end
| (((_65_1986, Some (FStar_Syntax_Syntax.Implicit (_65_1988))))::tps', ((_65_1996, _65_1998))::_65_1994) -> begin
(arguments tps' args)
end
| (((_65_2005, _65_2007))::_65_2003, ((a, Some (FStar_Syntax_Syntax.Implicit (_65_2014))))::_65_2011) -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected implicit annotation on argument"), (a.FStar_Syntax_Syntax.pos)))))
end
| (((_65_2022, _65_2024))::tps', ((_65_2029, _65_2031))::args') -> begin
(arguments tps' args')
end))
in (arguments inductive_tps args0))
in (

let indices = (FStar_All.pipe_right args (FStar_List.map (fun _65_2036 -> (let _160_743 = (FStar_Syntax_Syntax.new_bv (Some (p)) FStar_Syntax_Syntax.tun)
in (FStar_All.pipe_right _160_743 FStar_Syntax_Syntax.mk_binder)))))
in (

let arg_typ = (let _160_748 = (let _160_744 = (FStar_Syntax_Syntax.lid_as_fv tc FStar_Syntax_Syntax.Delta_constant None)
in (FStar_Syntax_Syntax.fv_to_tm _160_744))
in (let _160_747 = (FStar_All.pipe_right (FStar_List.append tps indices) (FStar_List.map (fun _65_2041 -> (match (_65_2041) with
| (x, imp) -> begin
(let _160_746 = (FStar_Syntax_Syntax.bv_to_name x)
in ((_160_746), (imp)))
end))))
in (FStar_Syntax_Syntax.mk_Tm_app _160_748 _160_747 None p)))
in (

let arg_binder = if (not (refine_domain)) then begin
(let _160_749 = (projectee arg_typ)
in (FStar_Syntax_Syntax.mk_binder _160_749))
end else begin
(

let disc_name = (FStar_Syntax_Util.mk_discriminator lid)
in (

let x = (FStar_Syntax_Syntax.new_bv (Some (p)) arg_typ)
in (let _160_757 = (

let _65_2045 = (projectee arg_typ)
in (let _160_756 = (let _160_755 = (let _160_754 = (let _160_753 = (FStar_Syntax_Syntax.fvar (FStar_Ident.set_lid_range disc_name p) FStar_Syntax_Syntax.Delta_equational None)
in (let _160_752 = (let _160_751 = (let _160_750 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _160_750))
in (_160_751)::[])
in (FStar_Syntax_Syntax.mk_Tm_app _160_753 _160_752 None p)))
in (FStar_Syntax_Util.b2t _160_754))
in (FStar_Syntax_Util.refine x _160_755))
in {FStar_Syntax_Syntax.ppname = _65_2045.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_2045.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _160_756}))
in (FStar_Syntax_Syntax.mk_binder _160_757))))
end
in ((arg_binder), (indices))))))
end))
in (match (_65_2050) with
| (arg_binder, indices) -> begin
(

let arg_exp = (FStar_Syntax_Syntax.bv_to_name (Prims.fst arg_binder))
in (

let imp_binders = (let _160_759 = (FStar_All.pipe_right indices (FStar_List.map (fun _65_2055 -> (match (_65_2055) with
| (x, _65_2054) -> begin
((x), (Some (FStar_Syntax_Syntax.imp_tag)))
end))))
in (FStar_List.append imp_tps _160_759))
in (

let binders = (FStar_List.append imp_binders ((arg_binder)::[]))
in (

let arg = (FStar_Syntax_Util.arg_of_non_null_binder arg_binder)
in (

let subst = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _65_2063 -> (match (_65_2063) with
| (a, _65_2062) -> begin
(

let _65_2067 = (FStar_Syntax_Util.mk_field_projector_name lid a i)
in (match (_65_2067) with
| (field_name, _65_2066) -> begin
(

let proj = (let _160_763 = (let _160_762 = (FStar_Syntax_Syntax.lid_as_fv field_name FStar_Syntax_Syntax.Delta_equational None)
in (FStar_Syntax_Syntax.fv_to_tm _160_762))
in (FStar_Syntax_Syntax.mk_Tm_app _160_763 ((arg)::[]) None p))
in FStar_Syntax_Syntax.NT (((a), (proj))))
end))
end))))
in (

let ntps = (FStar_List.length tps)
in (

let all_params = (FStar_List.append imp_tps fields)
in (let _160_802 = (FStar_All.pipe_right fields (FStar_List.mapi (fun i _65_2076 -> (match (_65_2076) with
| (x, _65_2075) -> begin
(

let _65_2080 = (FStar_Syntax_Util.mk_field_projector_name lid x i)
in (match (_65_2080) with
| (field_name, _65_2079) -> begin
(

let t = (let _160_767 = (let _160_766 = (FStar_Syntax_Subst.subst subst x.FStar_Syntax_Syntax.sort)
in (FStar_Syntax_Syntax.mk_Total _160_766))
in (FStar_Syntax_Util.arrow binders _160_767))
in (

let only_decl = (((let _160_768 = (FStar_Parser_Env.current_module env)
in (FStar_Ident.lid_equals FStar_Syntax_Const.prims_lid _160_768)) || (fvq <> FStar_Syntax_Syntax.Data_ctor)) || (let _160_770 = (let _160_769 = (FStar_Parser_Env.current_module env)
in _160_769.FStar_Ident.str)
in (FStar_Options.dont_gen_projectors _160_770)))
in (

let no_decl = (FStar_Syntax_Syntax.is_type x.FStar_Syntax_Syntax.sort)
in (

let quals = (fun q -> if only_decl then begin
(let _160_774 = (FStar_List.filter (fun _65_12 -> (match (_65_12) with
| FStar_Syntax_Syntax.Abstract -> begin
false
end
| _65_2089 -> begin
true
end)) q)
in (FStar_Syntax_Syntax.Assumption)::_160_774)
end else begin
q
end)
in (

let quals = (

let iquals = (FStar_All.pipe_right iquals (FStar_List.filter (fun _65_13 -> (match (_65_13) with
| (FStar_Syntax_Syntax.Abstract) | (FStar_Syntax_Syntax.Private) -> begin
true
end
| _65_2094 -> begin
false
end))))
in (quals ((FStar_Syntax_Syntax.Projector (((lid), (x.FStar_Syntax_Syntax.ppname))))::iquals)))
in (

let decl = FStar_Syntax_Syntax.Sig_declare_typ (((field_name), ([]), (t), (quals), ((FStar_Ident.range_of_lid field_name))))
in if only_decl then begin
(decl)::[]
end else begin
(

let projection = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in (

let arg_pats = (FStar_All.pipe_right all_params (FStar_List.mapi (fun j _65_2102 -> (match (_65_2102) with
| (x, imp) -> begin
(

let b = (FStar_Syntax_Syntax.is_implicit imp)
in if ((i + ntps) = j) then begin
(let _160_778 = (pos (FStar_Syntax_Syntax.Pat_var (projection)))
in ((_160_778), (b)))
end else begin
if (b && (j < ntps)) then begin
(let _160_782 = (let _160_781 = (let _160_780 = (let _160_779 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in ((_160_779), (FStar_Syntax_Syntax.tun)))
in FStar_Syntax_Syntax.Pat_dot_term (_160_780))
in (pos _160_781))
in ((_160_782), (b)))
end else begin
(let _160_785 = (let _160_784 = (let _160_783 = (FStar_Syntax_Syntax.gen_bv x.FStar_Syntax_Syntax.ppname.FStar_Ident.idText None FStar_Syntax_Syntax.tun)
in FStar_Syntax_Syntax.Pat_wild (_160_783))
in (pos _160_784))
in ((_160_785), (b)))
end
end)
end))))
in (

let pat = (let _160_790 = (let _160_788 = (let _160_787 = (let _160_786 = (FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.Delta_constant (Some (fvq)))
in ((_160_786), (arg_pats)))
in FStar_Syntax_Syntax.Pat_cons (_160_787))
in (FStar_All.pipe_right _160_788 pos))
in (let _160_789 = (FStar_Syntax_Syntax.bv_to_name projection)
in ((_160_790), (None), (_160_789))))
in (

let body = (let _160_794 = (let _160_793 = (let _160_792 = (let _160_791 = (FStar_Syntax_Util.branch pat)
in (_160_791)::[])
in ((arg_exp), (_160_792)))
in FStar_Syntax_Syntax.Tm_match (_160_793))
in (FStar_Syntax_Syntax.mk _160_794 None p))
in (

let imp = (no_annot_abs binders body)
in (

let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
FStar_Syntax_Syntax.Delta_abstract (FStar_Syntax_Syntax.Delta_equational)
end else begin
FStar_Syntax_Syntax.Delta_equational
end
in (

let lb = (let _160_796 = (let _160_795 = (FStar_Syntax_Syntax.lid_as_fv field_name dd None)
in FStar_Util.Inr (_160_795))
in {FStar_Syntax_Syntax.lbname = _160_796; FStar_Syntax_Syntax.lbunivs = []; FStar_Syntax_Syntax.lbtyp = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = imp})
in (

let impl = (let _160_801 = (let _160_800 = (let _160_799 = (let _160_798 = (FStar_All.pipe_right lb.FStar_Syntax_Syntax.lbname FStar_Util.right)
in (FStar_All.pipe_right _160_798 (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in (_160_799)::[])
in ((((false), ((lb)::[]))), (p), (_160_800), (quals)))
in FStar_Syntax_Syntax.Sig_let (_160_801))
in if no_decl then begin
(impl)::[]
end else begin
(decl)::(impl)::[]
end))))))))
end))))))
end))
end))))
in (FStar_All.pipe_right _160_802 FStar_List.flatten)))))))))
end)))))))


let mk_data_projectors : FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_Env.env  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.sigelt)  ->  FStar_Syntax_Syntax.sigelt Prims.list = (fun iquals env _65_2116 -> (match (_65_2116) with
| (inductive_tps, se) -> begin
(match (se) with
| FStar_Syntax_Syntax.Sig_datacon (lid, _65_2119, t, l, n, quals, _65_2125, _65_2127) when (not ((FStar_Ident.lid_equals lid FStar_Syntax_Const.lexcons_lid))) -> begin
(

let refine_domain = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _65_14 -> (match (_65_14) with
| FStar_Syntax_Syntax.RecordConstructor (_65_2132) -> begin
true
end
| _65_2135 -> begin
false
end)))) then begin
false
end else begin
(match ((FStar_Parser_Env.find_all_datacons env l)) with
| Some (l) -> begin
((FStar_List.length l) > (Prims.parse_int "1"))
end
| _65_2139 -> begin
true
end)
end
in (

let _65_2143 = (FStar_Syntax_Util.arrow_formals t)
in (match (_65_2143) with
| (formals, cod) -> begin
(match (formals) with
| [] -> begin
[]
end
| _65_2146 -> begin
(

let fv_qual = (match ((FStar_Util.find_map quals (fun _65_15 -> (match (_65_15) with
| FStar_Syntax_Syntax.RecordConstructor (fns) -> begin
Some (FStar_Syntax_Syntax.Record_ctor (((lid), (fns))))
end
| _65_2151 -> begin
None
end)))) with
| None -> begin
FStar_Syntax_Syntax.Data_ctor
end
| Some (q) -> begin
q
end)
in (

let iquals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract iquals) then begin
(FStar_Syntax_Syntax.Private)::iquals
end else begin
iquals
end
in (

let _65_2159 = (FStar_Util.first_N n formals)
in (match (_65_2159) with
| (tps, rest) -> begin
(mk_indexed_projectors iquals fv_qual refine_domain env l lid inductive_tps tps rest cod)
end))))
end)
end)))
end
| _65_2161 -> begin
[]
end)
end))


let mk_typ_abbrev : FStar_Ident.lident  ->  FStar_Syntax_Syntax.univ_name Prims.list  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Ident.lident Prims.list  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.sigelt = (fun lid uvs typars k t lids quals rng -> (

let dd = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _160_827 = (FStar_Syntax_Util.incr_delta_qualifier t)
in FStar_Syntax_Syntax.Delta_abstract (_160_827))
end else begin
(FStar_Syntax_Util.incr_delta_qualifier t)
end
in (

let lb = (let _160_832 = (let _160_828 = (FStar_Syntax_Syntax.lid_as_fv lid dd None)
in FStar_Util.Inr (_160_828))
in (let _160_831 = (let _160_829 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow typars _160_829))
in (let _160_830 = (no_annot_abs typars t)
in {FStar_Syntax_Syntax.lbname = _160_832; FStar_Syntax_Syntax.lbunivs = uvs; FStar_Syntax_Syntax.lbtyp = _160_831; FStar_Syntax_Syntax.lbeff = FStar_Syntax_Const.effect_Tot_lid; FStar_Syntax_Syntax.lbdef = _160_830})))
in FStar_Syntax_Syntax.Sig_let (((((false), ((lb)::[]))), (rng), (lids), (quals))))))


let rec desugar_tycon : FStar_Parser_Env.env  ->  FStar_Range.range  ->  FStar_Syntax_Syntax.qualifier Prims.list  ->  FStar_Parser_AST.tycon Prims.list  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env rng quals tcs -> (

let tycon_id = (fun _65_16 -> (match (_65_16) with
| (FStar_Parser_AST.TyconAbstract (id, _, _)) | (FStar_Parser_AST.TyconAbbrev (id, _, _, _)) | (FStar_Parser_AST.TyconRecord (id, _, _, _)) | (FStar_Parser_AST.TyconVariant (id, _, _, _)) -> begin
id
end))
in (

let binder_to_term = (fun b -> (match (b.FStar_Parser_AST.b) with
| (FStar_Parser_AST.Annotated (x, _)) | (FStar_Parser_AST.Variable (x)) -> begin
(let _160_846 = (let _160_845 = (FStar_Ident.lid_of_ids ((x)::[]))
in FStar_Parser_AST.Var (_160_845))
in (FStar_Parser_AST.mk_term _160_846 x.FStar_Ident.idRange FStar_Parser_AST.Expr))
end
| (FStar_Parser_AST.TAnnotated (a, _)) | (FStar_Parser_AST.TVariable (a)) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Tvar (a)) a.FStar_Ident.idRange FStar_Parser_AST.Type)
end
| FStar_Parser_AST.NoName (t) -> begin
t
end))
in (

let tot = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Name (FStar_Syntax_Const.effect_Tot_lid)) rng FStar_Parser_AST.Expr)
in (

let with_constructor_effect = (fun t -> (FStar_Parser_AST.mk_term (FStar_Parser_AST.App (((tot), (t), (FStar_Parser_AST.Nothing)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level))
in (

let apply_binders = (fun t binders -> (

let imp_of_aqual = (fun b -> (match (b.FStar_Parser_AST.aqual) with
| Some (FStar_Parser_AST.Implicit) -> begin
FStar_Parser_AST.Hash
end
| _65_2236 -> begin
FStar_Parser_AST.Nothing
end))
in (FStar_List.fold_left (fun out b -> (let _160_859 = (let _160_858 = (let _160_857 = (binder_to_term b)
in ((out), (_160_857), ((imp_of_aqual b))))
in FStar_Parser_AST.App (_160_858))
in (FStar_Parser_AST.mk_term _160_859 out.FStar_Parser_AST.range out.FStar_Parser_AST.level))) t binders)))
in (

let tycon_record_as_variant = (fun _65_17 -> (match (_65_17) with
| FStar_Parser_AST.TyconRecord (id, parms, kopt, fields) -> begin
(

let constrName = (FStar_Ident.mk_ident (((Prims.strcat "Mk" id.FStar_Ident.idText)), (id.FStar_Ident.idRange)))
in (

let mfields = (FStar_List.map (fun _65_2251 -> (match (_65_2251) with
| (x, t, _65_2250) -> begin
(FStar_Parser_AST.mk_binder (FStar_Parser_AST.Annotated ((((FStar_Syntax_Util.mangle_field_name x)), (t)))) x.FStar_Ident.idRange FStar_Parser_AST.Expr None)
end)) fields)
in (

let result = (let _160_865 = (let _160_864 = (let _160_863 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_160_863))
in (FStar_Parser_AST.mk_term _160_864 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _160_865 parms))
in (

let constrTyp = (FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((mfields), ((with_constructor_effect result))))) id.FStar_Ident.idRange FStar_Parser_AST.Type)
in (let _160_867 = (FStar_All.pipe_right fields (FStar_List.map (fun _65_2260 -> (match (_65_2260) with
| (x, _65_2257, _65_2259) -> begin
(FStar_Parser_Env.qualify env x)
end))))
in ((FStar_Parser_AST.TyconVariant (((id), (parms), (kopt), ((((constrName), (Some (constrTyp)), (None), (false)))::[])))), (_160_867)))))))
end
| _65_2262 -> begin
(FStar_All.failwith "impossible")
end))
in (

let desugar_abstract_tc = (fun quals _env mutuals _65_18 -> (match (_65_18) with
| FStar_Parser_AST.TyconAbstract (id, binders, kopt) -> begin
(

let _65_2276 = (typars_of_binders _env binders)
in (match (_65_2276) with
| (_env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
FStar_Syntax_Util.ktype
end
| Some (k) -> begin
(desugar_term _env' k)
end)
in (

let tconstr = (let _160_878 = (let _160_877 = (let _160_876 = (FStar_Ident.lid_of_ids ((id)::[]))
in FStar_Parser_AST.Var (_160_876))
in (FStar_Parser_AST.mk_term _160_877 id.FStar_Ident.idRange FStar_Parser_AST.Type))
in (apply_binders _160_878 binders))
in (

let qlid = (FStar_Parser_Env.qualify _env id)
in (

let typars = (FStar_Syntax_Subst.close_binders typars)
in (

let k = (FStar_Syntax_Subst.close typars k)
in (

let se = FStar_Syntax_Syntax.Sig_inductive_typ (((qlid), ([]), (typars), (k), (mutuals), ([]), (quals), (rng)))
in (

let _env = (FStar_Parser_Env.push_top_level_rec_binding _env id FStar_Syntax_Syntax.Delta_constant)
in (

let _env2 = (FStar_Parser_Env.push_top_level_rec_binding _env' id FStar_Syntax_Syntax.Delta_constant)
in ((_env), (_env2), (se), (tconstr))))))))))
end))
end
| _65_2289 -> begin
(FStar_All.failwith "Unexpected tycon")
end))
in (

let push_tparams = (fun env bs -> (

let _65_2304 = (FStar_List.fold_left (fun _65_2295 _65_2298 -> (match (((_65_2295), (_65_2298))) with
| ((env, tps), (x, imp)) -> begin
(

let _65_2301 = (FStar_Parser_Env.push_bv env x.FStar_Syntax_Syntax.ppname)
in (match (_65_2301) with
| (env, y) -> begin
((env), ((((y), (imp)))::tps))
end))
end)) ((env), ([])) bs)
in (match (_65_2304) with
| (env, bs) -> begin
((env), ((FStar_List.rev bs)))
end)))
in (match (tcs) with
| (FStar_Parser_AST.TyconAbstract (id, bs, kopt))::[] -> begin
(

let kopt = (match (kopt) with
| None -> begin
(let _160_885 = (tm_type_z id.FStar_Ident.idRange)
in Some (_160_885))
end
| _65_2313 -> begin
kopt
end)
in (

let tc = FStar_Parser_AST.TyconAbstract (((id), (bs), (kopt)))
in (

let _65_2323 = (desugar_abstract_tc quals env [] tc)
in (match (_65_2323) with
| (_65_2317, _65_2319, se, _65_2322) -> begin
(

let se = (match (se) with
| FStar_Syntax_Syntax.Sig_inductive_typ (l, _65_2326, typars, k, [], [], quals, rng) -> begin
(

let quals = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Assumption)) then begin
quals
end else begin
(

let _65_2335 = (let _160_887 = (FStar_Range.string_of_range rng)
in (let _160_886 = (FStar_Syntax_Print.lid_to_string l)
in (FStar_Util.print2 "%s (Warning): Adding an implicit \'assume new\' qualifier on %s\n" _160_887 _160_886)))
in (FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.New)::quals)
end
in (

let t = (match (typars) with
| [] -> begin
k
end
| _65_2340 -> begin
(let _160_890 = (let _160_889 = (let _160_888 = (FStar_Syntax_Syntax.mk_Total k)
in ((typars), (_160_888)))
in FStar_Syntax_Syntax.Tm_arrow (_160_889))
in (FStar_Syntax_Syntax.mk _160_890 None rng))
end)
in FStar_Syntax_Syntax.Sig_declare_typ (((l), ([]), (t), (quals), (rng)))))
end
| _65_2343 -> begin
se
end)
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in ((env), ((se)::[]))))
end))))
end
| (FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t))::[] -> begin
(

let _65_2355 = (typars_of_binders env binders)
in (match (_65_2355) with
| (env', typars) -> begin
(

let k = (match (kopt) with
| None -> begin
if (FStar_Util.for_some (fun _65_19 -> (match (_65_19) with
| FStar_Syntax_Syntax.Effect -> begin
true
end
| _65_2360 -> begin
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

let t0 = t
in (

let quals = if (FStar_All.pipe_right quals (FStar_Util.for_some (fun _65_20 -> (match (_65_20) with
| FStar_Syntax_Syntax.Logic -> begin
true
end
| _65_2368 -> begin
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

let se = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Effect)) then begin
(

let c = (desugar_comp t.FStar_Parser_AST.range false env' t)
in (

let typars = (FStar_Syntax_Subst.close_binders typars)
in (

let c = (FStar_Syntax_Subst.close_comp typars c)
in (let _160_896 = (let _160_895 = (FStar_Parser_Env.qualify env id)
in (let _160_894 = (FStar_All.pipe_right quals (FStar_List.filter (fun _65_21 -> (match (_65_21) with
| FStar_Syntax_Syntax.Effect -> begin
false
end
| _65_2376 -> begin
true
end))))
in ((_160_895), ([]), (typars), (c), (_160_894), (rng))))
in FStar_Syntax_Syntax.Sig_effect_abbrev (_160_896)))))
end else begin
(

let t = (desugar_typ env' t)
in (

let nm = (FStar_Parser_Env.qualify env id)
in (mk_typ_abbrev nm [] typars k t ((nm)::[]) quals rng)))
end
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in ((env), ((se)::[])))))))
end))
end
| (FStar_Parser_AST.TyconRecord (_65_2382))::[] -> begin
(

let trec = (FStar_List.hd tcs)
in (

let _65_2388 = (tycon_record_as_variant trec)
in (match (_65_2388) with
| (t, fs) -> begin
(desugar_tycon env rng ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((t)::[]))
end)))
end
| (_65_2392)::_65_2390 -> begin
(

let env0 = env
in (

let mutuals = (FStar_List.map (fun x -> (FStar_All.pipe_left (FStar_Parser_Env.qualify env) (tycon_id x))) tcs)
in (

let rec collect_tcs = (fun quals et tc -> (

let _65_2403 = et
in (match (_65_2403) with
| (env, tcs) -> begin
(match (tc) with
| FStar_Parser_AST.TyconRecord (_65_2405) -> begin
(

let trec = tc
in (

let _65_2410 = (tycon_record_as_variant trec)
in (match (_65_2410) with
| (t, fs) -> begin
(collect_tcs ((FStar_Syntax_Syntax.RecordType (fs))::quals) ((env), (tcs)) t)
end)))
end
| FStar_Parser_AST.TyconVariant (id, binders, kopt, constructors) -> begin
(

let _65_2422 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_65_2422) with
| (env, _65_2419, se, tconstr) -> begin
((env), ((FStar_Util.Inl (((se), (constructors), (tconstr), (quals))))::tcs))
end))
end
| FStar_Parser_AST.TyconAbbrev (id, binders, kopt, t) -> begin
(

let _65_2434 = (desugar_abstract_tc quals env mutuals (FStar_Parser_AST.TyconAbstract (((id), (binders), (kopt)))))
in (match (_65_2434) with
| (env, _65_2431, se, tconstr) -> begin
((env), ((FStar_Util.Inr (((se), (t), (quals))))::tcs))
end))
end
| _65_2436 -> begin
(FStar_All.failwith "Unrecognized mutual type definition")
end)
end)))
in (

let _65_2439 = (FStar_List.fold_left (collect_tcs quals) ((env), ([])) tcs)
in (match (_65_2439) with
| (env, tcs) -> begin
(

let tcs = (FStar_List.rev tcs)
in (

let tps_sigelts = (FStar_All.pipe_right tcs (FStar_List.collect (fun _65_23 -> (match (_65_23) with
| FStar_Util.Inr (FStar_Syntax_Syntax.Sig_inductive_typ (id, uvs, tpars, k, _65_2447, _65_2449, _65_2451, _65_2453), t, quals) -> begin
(

let _65_2463 = (push_tparams env tpars)
in (match (_65_2463) with
| (env_tps, _65_2462) -> begin
(

let t = (desugar_term env_tps t)
in (let _160_906 = (let _160_905 = (mk_typ_abbrev id uvs tpars k t ((id)::[]) quals rng)
in (([]), (_160_905)))
in (_160_906)::[]))
end))
end
| FStar_Util.Inl (FStar_Syntax_Syntax.Sig_inductive_typ (tname, univs, tpars, k, mutuals, _65_2471, tags, _65_2474), constrs, tconstr, quals) -> begin
(

let tycon = ((tname), (tpars), (k))
in (

let _65_2485 = (push_tparams env tpars)
in (match (_65_2485) with
| (env_tps, tps) -> begin
(

let data_tpars = (FStar_List.map (fun _65_2489 -> (match (_65_2489) with
| (x, _65_2488) -> begin
((x), (Some (FStar_Syntax_Syntax.Implicit (true))))
end)) tps)
in (

let _65_2515 = (let _160_918 = (FStar_All.pipe_right constrs (FStar_List.map (fun _65_2496 -> (match (_65_2496) with
| (id, topt, _65_2494, of_notation) -> begin
(

let t = if of_notation then begin
(match (topt) with
| Some (t) -> begin
(FStar_Parser_AST.mk_term (FStar_Parser_AST.Product (((((FStar_Parser_AST.mk_binder (FStar_Parser_AST.NoName (t)) t.FStar_Parser_AST.range t.FStar_Parser_AST.level None))::[]), (tconstr)))) t.FStar_Parser_AST.range t.FStar_Parser_AST.level)
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

let t = (let _160_910 = (FStar_Parser_Env.default_total env_tps)
in (let _160_909 = (close env_tps t)
in (desugar_term _160_910 _160_909)))
in (

let name = (FStar_Parser_Env.qualify env id)
in (

let quals = (FStar_All.pipe_right tags (FStar_List.collect (fun _65_22 -> (match (_65_22) with
| FStar_Syntax_Syntax.RecordType (fns) -> begin
(FStar_Syntax_Syntax.RecordConstructor (fns))::[]
end
| _65_2510 -> begin
[]
end))))
in (

let ntps = (FStar_List.length data_tpars)
in (let _160_917 = (let _160_916 = (let _160_915 = (let _160_914 = (let _160_913 = (let _160_912 = (FStar_All.pipe_right t FStar_Syntax_Util.name_function_binders)
in (FStar_Syntax_Syntax.mk_Total _160_912))
in (FStar_Syntax_Util.arrow data_tpars _160_913))
in ((name), (univs), (_160_914), (tname), (ntps), (quals), (mutuals), (rng)))
in FStar_Syntax_Syntax.Sig_datacon (_160_915))
in ((tps), (_160_916)))
in ((name), (_160_917))))))))
end))))
in (FStar_All.pipe_left FStar_List.split _160_918))
in (match (_65_2515) with
| (constrNames, constrs) -> begin
((([]), (FStar_Syntax_Syntax.Sig_inductive_typ (((tname), (univs), (tpars), (k), (mutuals), (constrNames), (tags), (rng))))))::constrs
end)))
end)))
end
| _65_2517 -> begin
(FStar_All.failwith "impossible")
end))))
in (

let sigelts = (FStar_All.pipe_right tps_sigelts (FStar_List.map Prims.snd))
in (

let bundle = (let _160_920 = (let _160_919 = (FStar_List.collect FStar_Syntax_Util.lids_of_sigelt sigelts)
in ((sigelts), (quals), (_160_919), (rng)))
in FStar_Syntax_Syntax.Sig_bundle (_160_920))
in (

let env = (FStar_Parser_Env.push_sigelt env0 bundle)
in (

let data_ops = (FStar_All.pipe_right tps_sigelts (FStar_List.collect (mk_data_projectors quals env)))
in (

let discs = (FStar_All.pipe_right sigelts (FStar_List.collect (fun _65_24 -> (match (_65_24) with
| FStar_Syntax_Syntax.Sig_inductive_typ (tname, _65_2526, tps, k, _65_2530, constrs, quals, _65_2534) when ((FStar_List.length constrs) > (Prims.parse_int "1")) -> begin
(

let quals = if (FStar_List.contains FStar_Syntax_Syntax.Abstract quals) then begin
(FStar_Syntax_Syntax.Private)::quals
end else begin
quals
end
in (mk_data_discriminators quals env tname tps k constrs))
end
| _65_2539 -> begin
[]
end))))
in (

let ops = (FStar_List.append discs data_ops)
in (

let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env ops)
in ((env), ((FStar_List.append ((bundle)::[]) ops))))))))))))
end)))))
end
| [] -> begin
(FStar_All.failwith "impossible")
end))))))))))


let desugar_binders : FStar_Parser_Env.env  ->  FStar_Parser_AST.binder Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.binder Prims.list) = (fun env binders -> (

let _65_2563 = (FStar_List.fold_left (fun _65_2548 b -> (match (_65_2548) with
| (env, binders) -> begin
(match ((desugar_binder env b)) with
| (Some (a), k) -> begin
(

let _65_2556 = (FStar_Parser_Env.push_bv env a)
in (match (_65_2556) with
| (env, a) -> begin
(let _160_929 = (let _160_928 = (FStar_Syntax_Syntax.mk_binder (

let _65_2557 = a
in {FStar_Syntax_Syntax.ppname = _65_2557.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _65_2557.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = k}))
in (_160_928)::binders)
in ((env), (_160_929)))
end))
end
| _65_2560 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Missing name in binder"), (b.FStar_Parser_AST.brange)))))
end)
end)) ((env), ([])) binders)
in (match (_65_2563) with
| (env, binders) -> begin
((env), ((FStar_List.rev binders)))
end)))


let rec desugar_effect : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl  ->  FStar_Parser_AST.qualifiers  ->  FStar_Ident.ident  ->  FStar_Parser_AST.binder Prims.list  ->  FStar_Parser_AST.term  ->  FStar_Parser_AST.decl Prims.list  ->  FStar_Parser_AST.decl Prims.list  ->  Prims.bool  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelt Prims.list) = (fun env d quals eff_name eff_binders eff_kind eff_decls actions for_free -> (

let env0 = env
in (

let monad_env = (FStar_Parser_Env.enter_monad_scope env eff_name)
in (

let _65_2577 = (desugar_binders monad_env eff_binders)
in (match (_65_2577) with
| (env, binders) -> begin
(

let eff_k = (let _160_950 = (FStar_Parser_Env.default_total env)
in (desugar_term _160_950 eff_kind))
in (

let _65_2588 = (FStar_All.pipe_right eff_decls (FStar_List.fold_left (fun _65_2581 decl -> (match (_65_2581) with
| (env, out) -> begin
(

let _65_2585 = (desugar_decl env decl)
in (match (_65_2585) with
| (env, ses) -> begin
(let _160_954 = (let _160_953 = (FStar_List.hd ses)
in (_160_953)::out)
in ((env), (_160_954)))
end))
end)) ((env), ([]))))
in (match (_65_2588) with
| (env, decls) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let actions = (FStar_All.pipe_right actions (FStar_List.map (fun d -> (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Tycon (_65_2592, ((FStar_Parser_AST.TyconAbbrev (name, _65_2595, _65_2597, {FStar_Parser_AST.tm = FStar_Parser_AST.Construct (_65_2603, ((def, _65_2610))::((cps_type, _65_2606))::[]); FStar_Parser_AST.range = _65_2601; FStar_Parser_AST.level = _65_2599}), _65_2619))::[]) when (not (for_free)) -> begin
(let _160_960 = (FStar_Parser_Env.qualify env name)
in (let _160_959 = (let _160_956 = (desugar_term env def)
in (FStar_Syntax_Subst.close binders _160_956))
in (let _160_958 = (let _160_957 = (desugar_typ env cps_type)
in (FStar_Syntax_Subst.close binders _160_957))
in {FStar_Syntax_Syntax.action_name = _160_960; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = _160_959; FStar_Syntax_Syntax.action_typ = _160_958})))
end
| FStar_Parser_AST.Tycon (_65_2625, ((FStar_Parser_AST.TyconAbbrev (name, _65_2628, _65_2630, defn), _65_2635))::[]) when for_free -> begin
(let _160_963 = (FStar_Parser_Env.qualify env name)
in (let _160_962 = (let _160_961 = (desugar_term env defn)
in (FStar_Syntax_Subst.close binders _160_961))
in {FStar_Syntax_Syntax.action_name = _160_963; FStar_Syntax_Syntax.action_univs = []; FStar_Syntax_Syntax.action_defn = _160_962; FStar_Syntax_Syntax.action_typ = FStar_Syntax_Syntax.tun}))
end
| _65_2641 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Malformed action declaration; if this is an \"effect for free\", just provide the direct-style declaration. If this is not an \"effect for free\", please provide a pair of the definition and its cps-type with arrows inserted in the right place (see examples)."), (d.FStar_Parser_AST.drange)))))
end))))
in (

let eff_k = (FStar_Syntax_Subst.close binders eff_k)
in (

let lookup = (fun s -> (

let l = (FStar_Parser_Env.qualify env (FStar_Ident.mk_ident ((s), (d.FStar_Parser_AST.drange))))
in (let _160_967 = (let _160_966 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_definition env) l)
in (FStar_All.pipe_left (FStar_Syntax_Subst.close binders) _160_966))
in (([]), (_160_967)))))
in (

let mname = (FStar_Parser_Env.qualify env0 eff_name)
in (

let qualifiers = (FStar_List.map (trans_qual d.FStar_Parser_AST.drange) quals)
in (

let se = if for_free then begin
(

let dummy_tscheme = (let _160_968 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None FStar_Range.dummyRange)
in (([]), (_160_968)))
in (let _160_974 = (let _160_973 = (let _160_972 = (let _160_969 = (lookup "repr")
in (Prims.snd _160_969))
in (let _160_971 = (lookup "return")
in (let _160_970 = (lookup "bind")
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = dummy_tscheme; FStar_Syntax_Syntax.bind_wp = dummy_tscheme; FStar_Syntax_Syntax.if_then_else = dummy_tscheme; FStar_Syntax_Syntax.ite_wp = dummy_tscheme; FStar_Syntax_Syntax.stronger = dummy_tscheme; FStar_Syntax_Syntax.close_wp = dummy_tscheme; FStar_Syntax_Syntax.assert_p = dummy_tscheme; FStar_Syntax_Syntax.assume_p = dummy_tscheme; FStar_Syntax_Syntax.null_wp = dummy_tscheme; FStar_Syntax_Syntax.trivial = dummy_tscheme; FStar_Syntax_Syntax.repr = _160_972; FStar_Syntax_Syntax.return_repr = _160_971; FStar_Syntax_Syntax.bind_repr = _160_970; FStar_Syntax_Syntax.actions = actions})))
in ((_160_973), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_new_effect_for_free (_160_974)))
end else begin
(

let rr = ((FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable)) || (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reflectable)))
in (

let un_ts = (([]), (FStar_Syntax_Syntax.tun))
in (let _160_990 = (let _160_989 = (let _160_988 = (lookup "return_wp")
in (let _160_987 = (lookup "bind_wp")
in (let _160_986 = (lookup "if_then_else")
in (let _160_985 = (lookup "ite_wp")
in (let _160_984 = (lookup "stronger")
in (let _160_983 = (lookup "close_wp")
in (let _160_982 = (lookup "assert_p")
in (let _160_981 = (lookup "assume_p")
in (let _160_980 = (lookup "null_wp")
in (let _160_979 = (lookup "trivial")
in (let _160_978 = if rr then begin
(let _160_975 = (lookup "repr")
in (FStar_All.pipe_left Prims.snd _160_975))
end else begin
FStar_Syntax_Syntax.tun
end
in (let _160_977 = if rr then begin
(lookup "return")
end else begin
un_ts
end
in (let _160_976 = if rr then begin
(lookup "bind")
end else begin
un_ts
end
in {FStar_Syntax_Syntax.qualifiers = qualifiers; FStar_Syntax_Syntax.mname = mname; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = eff_k; FStar_Syntax_Syntax.ret_wp = _160_988; FStar_Syntax_Syntax.bind_wp = _160_987; FStar_Syntax_Syntax.if_then_else = _160_986; FStar_Syntax_Syntax.ite_wp = _160_985; FStar_Syntax_Syntax.stronger = _160_984; FStar_Syntax_Syntax.close_wp = _160_983; FStar_Syntax_Syntax.assert_p = _160_982; FStar_Syntax_Syntax.assume_p = _160_981; FStar_Syntax_Syntax.null_wp = _160_980; FStar_Syntax_Syntax.trivial = _160_979; FStar_Syntax_Syntax.repr = _160_978; FStar_Syntax_Syntax.return_repr = _160_977; FStar_Syntax_Syntax.bind_repr = _160_976; FStar_Syntax_Syntax.actions = actions})))))))))))))
in ((_160_989), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_new_effect (_160_990))))
end
in (

let env = (FStar_Parser_Env.push_sigelt env0 se)
in (

let env = (FStar_All.pipe_right actions (FStar_List.fold_left (fun env a -> (let _160_993 = (FStar_Syntax_Util.action_as_lb a)
in (FStar_Parser_Env.push_sigelt env _160_993))) env))
in (

let env = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Parser_AST.Reflectable)) then begin
(

let reflect_lid = (FStar_All.pipe_right (FStar_Ident.id_of_text "reflect") (FStar_Parser_Env.qualify monad_env))
in (

let refl_decl = FStar_Syntax_Syntax.Sig_declare_typ (((reflect_lid), ([]), (FStar_Syntax_Syntax.tun), ((FStar_Syntax_Syntax.Assumption)::(FStar_Syntax_Syntax.Reflectable)::[]), (d.FStar_Parser_AST.drange)))
in (FStar_Parser_Env.push_sigelt env refl_decl)))
end else begin
env
end
in ((env), ((se)::[]))))))))))))
end)))
end)))))
and desugar_decl : env_t  ->  FStar_Parser_AST.decl  ->  (env_t * FStar_Syntax_Syntax.sigelts) = (fun env d -> (

let trans_qual = (trans_qual d.FStar_Parser_AST.drange)
in (match (d.FStar_Parser_AST.d) with
| FStar_Parser_AST.Pragma (p) -> begin
(

let se = FStar_Syntax_Syntax.Sig_pragma ((((trans_pragma p)), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[])))
end
| FStar_Parser_AST.Fsdoc (_65_2667) -> begin
((env), ([]))
end
| FStar_Parser_AST.TopLevelModule (id) -> begin
((env), ([]))
end
| FStar_Parser_AST.Open (lid) -> begin
(

let env = (FStar_Parser_Env.push_namespace env lid)
in ((env), ([])))
end
| FStar_Parser_AST.ModuleAbbrev (x, l) -> begin
(let _160_997 = (FStar_Parser_Env.push_module_abbrev env x l)
in ((_160_997), ([])))
end
| FStar_Parser_AST.Tycon (qual, tcs) -> begin
(

let tcs = (FStar_List.map (fun _65_2685 -> (match (_65_2685) with
| (x, _65_2684) -> begin
x
end)) tcs)
in (let _160_999 = (FStar_List.map trans_qual qual)
in (desugar_tycon env d.FStar_Parser_AST.drange _160_999 tcs)))
end
| FStar_Parser_AST.ToplevelLet (quals, isrec, lets) -> begin
(match ((let _160_1001 = (let _160_1000 = (desugar_term_maybe_top true env (FStar_Parser_AST.mk_term (FStar_Parser_AST.Let (((isrec), (lets), ((FStar_Parser_AST.mk_term (FStar_Parser_AST.Const (FStar_Const.Const_unit)) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))))) d.FStar_Parser_AST.drange FStar_Parser_AST.Expr))
in (FStar_All.pipe_left FStar_Syntax_Subst.compress _160_1000))
in _160_1001.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_let (lbs, _65_2694) -> begin
(

let fvs = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (FStar_Util.right lb.FStar_Syntax_Syntax.lbname))))
in (

let quals = (match (quals) with
| (_65_2702)::_65_2700 -> begin
(FStar_List.map trans_qual quals)
end
| _65_2705 -> begin
(FStar_All.pipe_right (Prims.snd lbs) (FStar_List.collect (fun _65_25 -> (match (_65_25) with
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inl (_65_2716); FStar_Syntax_Syntax.lbunivs = _65_2714; FStar_Syntax_Syntax.lbtyp = _65_2712; FStar_Syntax_Syntax.lbeff = _65_2710; FStar_Syntax_Syntax.lbdef = _65_2708} -> begin
[]
end
| {FStar_Syntax_Syntax.lbname = FStar_Util.Inr (fv); FStar_Syntax_Syntax.lbunivs = _65_2726; FStar_Syntax_Syntax.lbtyp = _65_2724; FStar_Syntax_Syntax.lbeff = _65_2722; FStar_Syntax_Syntax.lbdef = _65_2720} -> begin
(FStar_Parser_Env.lookup_letbinding_quals env fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
end))))
end)
in (

let quals = if (FStar_All.pipe_right lets (FStar_Util.for_some (fun _65_2734 -> (match (_65_2734) with
| (_65_2732, t) -> begin
(t.FStar_Parser_AST.level = FStar_Parser_AST.Formula)
end)))) then begin
(FStar_Syntax_Syntax.Logic)::quals
end else begin
quals
end
in (

let lbs = if (FStar_All.pipe_right quals (FStar_List.contains FStar_Syntax_Syntax.Abstract)) then begin
(let _160_1006 = (FStar_All.pipe_right (Prims.snd lbs) (FStar_List.map (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let _65_2738 = lb
in {FStar_Syntax_Syntax.lbname = FStar_Util.Inr ((

let _65_2740 = fv
in {FStar_Syntax_Syntax.fv_name = _65_2740.FStar_Syntax_Syntax.fv_name; FStar_Syntax_Syntax.fv_delta = FStar_Syntax_Syntax.Delta_abstract (fv.FStar_Syntax_Syntax.fv_delta); FStar_Syntax_Syntax.fv_qual = _65_2740.FStar_Syntax_Syntax.fv_qual})); FStar_Syntax_Syntax.lbunivs = _65_2738.FStar_Syntax_Syntax.lbunivs; FStar_Syntax_Syntax.lbtyp = _65_2738.FStar_Syntax_Syntax.lbtyp; FStar_Syntax_Syntax.lbeff = _65_2738.FStar_Syntax_Syntax.lbeff; FStar_Syntax_Syntax.lbdef = _65_2738.FStar_Syntax_Syntax.lbdef})))))
in (((Prims.fst lbs)), (_160_1006)))
end else begin
lbs
end
in (

let s = (let _160_1009 = (let _160_1008 = (FStar_All.pipe_right fvs (FStar_List.map (fun fv -> fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)))
in ((lbs), (d.FStar_Parser_AST.drange), (_160_1008), (quals)))
in FStar_Syntax_Syntax.Sig_let (_160_1009))
in (

let env = (FStar_Parser_Env.push_sigelt env s)
in ((env), ((s)::[]))))))))
end
| _65_2747 -> begin
(FStar_All.failwith "Desugaring a let did not produce a let")
end)
end
| FStar_Parser_AST.Main (t) -> begin
(

let e = (desugar_term env t)
in (

let se = FStar_Syntax_Syntax.Sig_main (((e), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[]))))
end
| FStar_Parser_AST.Assume (atag, id, t) -> begin
(

let f = (desugar_formula env t)
in (let _160_1013 = (let _160_1012 = (let _160_1011 = (let _160_1010 = (FStar_Parser_Env.qualify env id)
in ((_160_1010), (f), ((FStar_Syntax_Syntax.Assumption)::[]), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Sig_assume (_160_1011))
in (_160_1012)::[])
in ((env), (_160_1013))))
end
| FStar_Parser_AST.Val (quals, id, t) -> begin
(

let t = (let _160_1014 = (close_fun env t)
in (desugar_term env _160_1014))
in (

let quals = if (env.FStar_Parser_Env.iface && env.FStar_Parser_Env.admitted_iface) then begin
(FStar_Parser_AST.Assumption)::quals
end else begin
quals
end
in (

let se = (let _160_1017 = (let _160_1016 = (FStar_Parser_Env.qualify env id)
in (let _160_1015 = (FStar_List.map trans_qual quals)
in ((_160_1016), ([]), (t), (_160_1015), (d.FStar_Parser_AST.drange))))
in FStar_Syntax_Syntax.Sig_declare_typ (_160_1017))
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in ((env), ((se)::[]))))))
end
| FStar_Parser_AST.Exception (id, None) -> begin
(

let _65_2774 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (match (_65_2774) with
| (t, _65_2773) -> begin
(

let l = (FStar_Parser_Env.qualify env id)
in (

let se = FStar_Syntax_Syntax.Sig_datacon (((l), ([]), (t), (FStar_Syntax_Const.exn_lid), ((Prims.parse_int "0")), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((FStar_Syntax_Const.exn_lid)::[]), (d.FStar_Parser_AST.drange)))
in (

let se' = FStar_Syntax_Syntax.Sig_bundle ((((se)::[]), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((l)::[]), (d.FStar_Parser_AST.drange)))
in (

let env = (FStar_Parser_Env.push_sigelt env se')
in (

let data_ops = (mk_data_projectors [] env (([]), (se)))
in (

let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (

let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in ((env), ((FStar_List.append ((se')::discs) data_ops))))))))))
end))
end
| FStar_Parser_AST.Exception (id, Some (term)) -> begin
(

let t = (desugar_term env term)
in (

let t = (let _160_1022 = (let _160_1018 = (FStar_Syntax_Syntax.null_binder t)
in (_160_1018)::[])
in (let _160_1021 = (let _160_1020 = (let _160_1019 = (FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_lid env) FStar_Syntax_Const.exn_lid)
in (Prims.fst _160_1019))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Total _160_1020))
in (FStar_Syntax_Util.arrow _160_1022 _160_1021)))
in (

let l = (FStar_Parser_Env.qualify env id)
in (

let se = FStar_Syntax_Syntax.Sig_datacon (((l), ([]), (t), (FStar_Syntax_Const.exn_lid), ((Prims.parse_int "0")), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((FStar_Syntax_Const.exn_lid)::[]), (d.FStar_Parser_AST.drange)))
in (

let se' = FStar_Syntax_Syntax.Sig_bundle ((((se)::[]), ((FStar_Syntax_Syntax.ExceptionConstructor)::[]), ((l)::[]), (d.FStar_Parser_AST.drange)))
in (

let env = (FStar_Parser_Env.push_sigelt env se')
in (

let data_ops = (mk_data_projectors [] env (([]), (se)))
in (

let discs = (mk_data_discriminators [] env FStar_Syntax_Const.exn_lid [] FStar_Syntax_Syntax.tun ((l)::[]))
in (

let env = (FStar_List.fold_left FStar_Parser_Env.push_sigelt env (FStar_List.append discs data_ops))
in ((env), ((FStar_List.append ((se')::discs) data_ops))))))))))))
end
| FStar_Parser_AST.KindAbbrev (id, binders, k) -> begin
(

let _65_2803 = (desugar_binders env binders)
in (match (_65_2803) with
| (env_k, binders) -> begin
(

let k = (desugar_term env_k k)
in (

let name = (FStar_Parser_Env.qualify env id)
in (

let se = (mk_typ_abbrev name [] binders FStar_Syntax_Syntax.tun k ((name)::[]) [] d.FStar_Parser_AST.drange)
in (

let env = (FStar_Parser_Env.push_sigelt env se)
in ((env), ((se)::[]))))))
end))
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.RedefineEffect (eff_name, eff_binders, defn)) -> begin
(

let env0 = env
in (

let _65_2819 = (desugar_binders env eff_binders)
in (match (_65_2819) with
| (env, binders) -> begin
(

let _65_2830 = (

let _65_2822 = (head_and_args defn)
in (match (_65_2822) with
| (head, args) -> begin
(

let ed = (match (head.FStar_Parser_AST.tm) with
| FStar_Parser_AST.Name (l) -> begin
(FStar_Parser_Env.fail_or env (FStar_Parser_Env.try_lookup_effect_defn env) l)
end
| _65_2826 -> begin
(let _160_1027 = (let _160_1026 = (let _160_1025 = (let _160_1024 = (let _160_1023 = (FStar_Parser_AST.term_to_string head)
in (Prims.strcat _160_1023 " not found"))
in (Prims.strcat "Effect " _160_1024))
in ((_160_1025), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_160_1026))
in (Prims.raise _160_1027))
end)
in (let _160_1028 = (desugar_args env args)
in ((ed), (_160_1028))))
end))
in (match (_65_2830) with
| (ed, args) -> begin
(

let binders = (FStar_Syntax_Subst.close_binders binders)
in (

let sub = (fun _65_2836 -> (match (_65_2836) with
| (_65_2834, x) -> begin
(

let _65_2839 = (FStar_Syntax_Subst.open_term ed.FStar_Syntax_Syntax.binders x)
in (match (_65_2839) with
| (edb, x) -> begin
(

let _65_2840 = if ((FStar_List.length args) <> (FStar_List.length edb)) then begin
(Prims.raise (FStar_Syntax_Syntax.Error ((("Unexpected number of arguments to effect constructor"), (defn.FStar_Parser_AST.range)))))
end else begin
()
end
in (

let s = (FStar_Syntax_Util.subst_of_list edb args)
in (let _160_1032 = (let _160_1031 = (FStar_Syntax_Subst.subst s x)
in (FStar_Syntax_Subst.close binders _160_1031))
in (([]), (_160_1032)))))
end))
end))
in (

let ed = (let _160_1046 = (FStar_List.map trans_qual quals)
in (let _160_1045 = (FStar_Parser_Env.qualify env0 eff_name)
in (let _160_1044 = (let _160_1033 = (sub (([]), (ed.FStar_Syntax_Syntax.signature)))
in (Prims.snd _160_1033))
in (let _160_1043 = (sub ed.FStar_Syntax_Syntax.ret_wp)
in (let _160_1042 = (sub ed.FStar_Syntax_Syntax.bind_wp)
in (let _160_1041 = (sub ed.FStar_Syntax_Syntax.if_then_else)
in (let _160_1040 = (sub ed.FStar_Syntax_Syntax.ite_wp)
in (let _160_1039 = (sub ed.FStar_Syntax_Syntax.stronger)
in (let _160_1038 = (sub ed.FStar_Syntax_Syntax.close_wp)
in (let _160_1037 = (sub ed.FStar_Syntax_Syntax.assert_p)
in (let _160_1036 = (sub ed.FStar_Syntax_Syntax.assume_p)
in (let _160_1035 = (sub ed.FStar_Syntax_Syntax.null_wp)
in (let _160_1034 = (sub ed.FStar_Syntax_Syntax.trivial)
in {FStar_Syntax_Syntax.qualifiers = _160_1046; FStar_Syntax_Syntax.mname = _160_1045; FStar_Syntax_Syntax.univs = []; FStar_Syntax_Syntax.binders = binders; FStar_Syntax_Syntax.signature = _160_1044; FStar_Syntax_Syntax.ret_wp = _160_1043; FStar_Syntax_Syntax.bind_wp = _160_1042; FStar_Syntax_Syntax.if_then_else = _160_1041; FStar_Syntax_Syntax.ite_wp = _160_1040; FStar_Syntax_Syntax.stronger = _160_1039; FStar_Syntax_Syntax.close_wp = _160_1038; FStar_Syntax_Syntax.assert_p = _160_1037; FStar_Syntax_Syntax.assume_p = _160_1036; FStar_Syntax_Syntax.null_wp = _160_1035; FStar_Syntax_Syntax.trivial = _160_1034; FStar_Syntax_Syntax.repr = FStar_Syntax_Syntax.tun; FStar_Syntax_Syntax.return_repr = (([]), (FStar_Syntax_Syntax.tun)); FStar_Syntax_Syntax.bind_repr = (([]), (FStar_Syntax_Syntax.tun)); FStar_Syntax_Syntax.actions = []})))))))))))))
in (

let se = FStar_Syntax_Syntax.Sig_new_effect (((ed), (d.FStar_Parser_AST.drange)))
in (

let env = (FStar_Parser_Env.push_sigelt env0 se)
in ((env), ((se)::[])))))))
end))
end)))
end
| FStar_Parser_AST.NewEffectForFree (_65_2847, FStar_Parser_AST.RedefineEffect (_65_2849)) -> begin
(FStar_All.failwith "impossible")
end
| FStar_Parser_AST.NewEffectForFree (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls, actions)) -> begin
(desugar_effect env d quals eff_name eff_binders eff_kind eff_decls actions true)
end
| FStar_Parser_AST.NewEffect (quals, FStar_Parser_AST.DefineEffect (eff_name, eff_binders, eff_kind, eff_decls, actions)) -> begin
(desugar_effect env d quals eff_name eff_binders eff_kind eff_decls actions false)
end
| FStar_Parser_AST.SubEffect (l) -> begin
(

let lookup = (fun l -> (match ((FStar_Parser_Env.try_lookup_effect_name env l)) with
| None -> begin
(let _160_1053 = (let _160_1052 = (let _160_1051 = (let _160_1050 = (let _160_1049 = (FStar_Syntax_Print.lid_to_string l)
in (Prims.strcat _160_1049 " not found"))
in (Prims.strcat "Effect name " _160_1050))
in ((_160_1051), (d.FStar_Parser_AST.drange)))
in FStar_Syntax_Syntax.Error (_160_1052))
in (Prims.raise _160_1053))
end
| Some (l) -> begin
l
end))
in (

let src = (lookup l.FStar_Parser_AST.msource)
in (

let dst = (lookup l.FStar_Parser_AST.mdest)
in (

let _65_2892 = (match (l.FStar_Parser_AST.lift_op) with
| FStar_Parser_AST.NonReifiableLift (t) -> begin
(let _160_1056 = (let _160_1055 = (let _160_1054 = (desugar_term env t)
in (([]), (_160_1054)))
in Some (_160_1055))
in ((_160_1056), (None)))
end
| FStar_Parser_AST.ReifiableLift (wp, t) -> begin
(let _160_1062 = (let _160_1058 = (let _160_1057 = (desugar_term env wp)
in (([]), (_160_1057)))
in Some (_160_1058))
in (let _160_1061 = (let _160_1060 = (let _160_1059 = (desugar_term env t)
in (([]), (_160_1059)))
in Some (_160_1060))
in ((_160_1062), (_160_1061))))
end
| FStar_Parser_AST.LiftForFree (t) -> begin
(let _160_1065 = (let _160_1064 = (let _160_1063 = (desugar_term env t)
in (([]), (_160_1063)))
in Some (_160_1064))
in ((None), (_160_1065)))
end)
in (match (_65_2892) with
| (lift_wp, lift) -> begin
(

let se = FStar_Syntax_Syntax.Sig_sub_effect ((({FStar_Syntax_Syntax.source = src; FStar_Syntax_Syntax.target = dst; FStar_Syntax_Syntax.lift_wp = lift_wp; FStar_Syntax_Syntax.lift = lift}), (d.FStar_Parser_AST.drange)))
in ((env), ((se)::[])))
end)))))
end)))


let desugar_decls : FStar_Parser_Env.env  ->  FStar_Parser_AST.decl Prims.list  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.sigelts) = (fun env decls -> (FStar_List.fold_left (fun _65_2898 d -> (match (_65_2898) with
| (env, sigelts) -> begin
(

let _65_2902 = (desugar_decl env d)
in (match (_65_2902) with
| (env, se) -> begin
((env), ((FStar_List.append sigelts se)))
end))
end)) ((env), ([])) decls))


let open_prims_all : (FStar_Parser_AST.fsdoc Prims.option  ->  FStar_Parser_AST.decl) Prims.list = ((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.prims_lid)) FStar_Range.dummyRange))::((FStar_Parser_AST.mk_decl (FStar_Parser_AST.Open (FStar_Syntax_Const.all_lid)) FStar_Range.dummyRange))::[]


let desugar_modul_common : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul * Prims.bool) = (fun curmod env m -> (

let env = (match (curmod) with
| None -> begin
env
end
| Some (prev_mod) -> begin
(FStar_Parser_Env.finish_module_or_interface env prev_mod)
end)
in (

let _65_2925 = (match (m) with
| FStar_Parser_AST.Interface (mname, decls, admitted) -> begin
(let _160_1083 = (FStar_Parser_Env.prepare_module_or_interface true admitted env mname)
in ((_160_1083), (mname), (decls), (true)))
end
| FStar_Parser_AST.Module (mname, decls) -> begin
(let _160_1084 = (FStar_Parser_Env.prepare_module_or_interface false false env mname)
in ((_160_1084), (mname), (decls), (false)))
end)
in (match (_65_2925) with
| ((env, pop_when_done), mname, decls, intf) -> begin
(

let _65_2928 = (desugar_decls env decls)
in (match (_65_2928) with
| (env, sigelts) -> begin
(

let modul = {FStar_Syntax_Syntax.name = mname; FStar_Syntax_Syntax.declarations = sigelts; FStar_Syntax_Syntax.exports = []; FStar_Syntax_Syntax.is_interface = intf}
in ((env), (modul), (pop_when_done)))
end))
end))))


let desugar_partial_modul : FStar_Syntax_Syntax.modul Prims.option  ->  FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul) = (fun curmod env m -> (

let m = if (FStar_Options.interactive_fsi ()) then begin
(match (m) with
| FStar_Parser_AST.Module (mname, decls) -> begin
FStar_Parser_AST.Interface (((mname), (decls), (true)))
end
| FStar_Parser_AST.Interface (mname, _65_2939, _65_2941) -> begin
(FStar_All.failwith (Prims.strcat "Impossible: " mname.FStar_Ident.ident.FStar_Ident.idText))
end)
end else begin
m
end
in (

let _65_2949 = (desugar_modul_common curmod env m)
in (match (_65_2949) with
| (x, y, _65_2948) -> begin
((x), (y))
end))))


let desugar_modul : FStar_Parser_Env.env  ->  FStar_Parser_AST.modul  ->  (env_t * FStar_Syntax_Syntax.modul) = (fun env m -> (

let _65_2955 = (desugar_modul_common None env m)
in (match (_65_2955) with
| (env, modul, pop_when_done) -> begin
(

let env = (FStar_Parser_Env.finish_module_or_interface env modul)
in (

let _65_2957 = if (FStar_Options.dump_module modul.FStar_Syntax_Syntax.name.FStar_Ident.str) then begin
(let _160_1095 = (FStar_Syntax_Print.modul_to_string modul)
in (FStar_Util.print1 "%s\n" _160_1095))
end else begin
()
end
in (let _160_1096 = if pop_when_done then begin
(FStar_Parser_Env.export_interface modul.FStar_Syntax_Syntax.name env)
end else begin
env
end
in ((_160_1096), (modul)))))
end)))


let desugar_file : FStar_Parser_Env.env  ->  FStar_Parser_AST.file  ->  (FStar_Parser_Env.env * FStar_Syntax_Syntax.modul Prims.list) = (fun env f -> (

let _65_2970 = (FStar_List.fold_left (fun _65_2963 m -> (match (_65_2963) with
| (env, mods) -> begin
(

let _65_2967 = (desugar_modul env m)
in (match (_65_2967) with
| (env, m) -> begin
((env), ((m)::mods))
end))
end)) ((env), ([])) f)
in (match (_65_2970) with
| (env, mods) -> begin
((env), ((FStar_List.rev mods)))
end)))


let add_modul_to_env : FStar_Syntax_Syntax.modul  ->  FStar_Parser_Env.env  ->  FStar_Parser_Env.env = (fun m en -> (

let _65_2975 = (FStar_Parser_Env.prepare_module_or_interface false false en m.FStar_Syntax_Syntax.name)
in (match (_65_2975) with
| (en, pop_when_done) -> begin
(

let en = (FStar_List.fold_left FStar_Parser_Env.push_sigelt (

let _65_2976 = en
in {FStar_Parser_Env.curmodule = Some (m.FStar_Syntax_Syntax.name); FStar_Parser_Env.modules = _65_2976.FStar_Parser_Env.modules; FStar_Parser_Env.open_namespaces = _65_2976.FStar_Parser_Env.open_namespaces; FStar_Parser_Env.modul_abbrevs = _65_2976.FStar_Parser_Env.modul_abbrevs; FStar_Parser_Env.sigaccum = _65_2976.FStar_Parser_Env.sigaccum; FStar_Parser_Env.localbindings = _65_2976.FStar_Parser_Env.localbindings; FStar_Parser_Env.recbindings = _65_2976.FStar_Parser_Env.recbindings; FStar_Parser_Env.sigmap = _65_2976.FStar_Parser_Env.sigmap; FStar_Parser_Env.default_result_effect = _65_2976.FStar_Parser_Env.default_result_effect; FStar_Parser_Env.iface = _65_2976.FStar_Parser_Env.iface; FStar_Parser_Env.admitted_iface = _65_2976.FStar_Parser_Env.admitted_iface; FStar_Parser_Env.expect_typ = _65_2976.FStar_Parser_Env.expect_typ}) m.FStar_Syntax_Syntax.exports)
in (

let env = (FStar_Parser_Env.finish_module_or_interface en m)
in if pop_when_done then begin
(FStar_Parser_Env.export_interface m.FStar_Syntax_Syntax.name env)
end else begin
env
end))
end)))




