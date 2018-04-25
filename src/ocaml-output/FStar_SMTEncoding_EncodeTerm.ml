
open Prims
open FStar_Pervasives

let mkForall_fuel' : 'Auu____7 . 'Auu____7  ->  (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (fun n1 uu____27 -> (match (uu____27) with
| (pats, vars, body) -> begin
(

let fallback = (fun uu____54 -> (FStar_SMTEncoding_Util.mkForall ((pats), (vars), (body))))
in (

let uu____59 = (FStar_Options.unthrottle_inductives ())
in (match (uu____59) with
| true -> begin
(fallback ())
end
| uu____60 -> begin
(

let uu____61 = (FStar_SMTEncoding_Env.fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____61) with
| (fsym, fterm) -> begin
(

let add_fuel1 = (fun tms -> (FStar_All.pipe_right tms (FStar_List.map (fun p -> (match (p.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("HasType"), args) -> begin
(FStar_SMTEncoding_Util.mkApp (("HasTypeFuel"), ((fterm)::args)))
end
| uu____94 -> begin
p
end)))))
in (

let pats1 = (FStar_List.map add_fuel1 pats)
in (

let body1 = (match (body.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (guard)::(body')::[]) -> begin
(

let guard1 = (match (guard.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, guards) -> begin
(

let uu____115 = (add_fuel1 guards)
in (FStar_SMTEncoding_Util.mk_and_l uu____115))
end
| uu____118 -> begin
(

let uu____119 = (add_fuel1 ((guard)::[]))
in (FStar_All.pipe_right uu____119 FStar_List.hd))
end)
in (FStar_SMTEncoding_Util.mkImp ((guard1), (body'))))
end
| uu____124 -> begin
body
end)
in (

let vars1 = (((fsym), (FStar_SMTEncoding_Term.Fuel_sort)))::vars
in (FStar_SMTEncoding_Util.mkForall ((pats1), (vars1), (body1)))))))
end))
end)))
end))


let mkForall_fuel : (FStar_SMTEncoding_Term.pat Prims.list Prims.list * FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term = (mkForall_fuel' (Prims.parse_int "1"))


let head_normal : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let t1 = (FStar_Syntax_Util.unmeta t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____171) -> begin
true
end
| FStar_Syntax_Syntax.Tm_refine (uu____184) -> begin
true
end
| FStar_Syntax_Syntax.Tm_bvar (uu____191) -> begin
true
end
| FStar_Syntax_Syntax.Tm_uvar (uu____192) -> begin
true
end
| FStar_Syntax_Syntax.Tm_abs (uu____209) -> begin
true
end
| FStar_Syntax_Syntax.Tm_constant (uu____226) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____228 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.FStar_SMTEncoding_Env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____228 FStar_Option.isNone))
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____246; FStar_Syntax_Syntax.vars = uu____247}, uu____248) -> begin
(

let uu____269 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.FStar_SMTEncoding_Env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____269 FStar_Option.isNone))
end
| uu____286 -> begin
false
end)))


let head_redex : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____297 = (

let uu____298 = (FStar_Syntax_Util.un_uinst t)
in uu____298.FStar_Syntax_Syntax.n)
in (match (uu____297) with
| FStar_Syntax_Syntax.Tm_abs (uu____301, uu____302, FStar_Pervasives_Native.Some (rc)) -> begin
(((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid) || (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_GTot_lid)) || (FStar_List.existsb (fun uu___68_323 -> (match (uu___68_323) with
| FStar_Syntax_Syntax.TOTAL -> begin
true
end
| uu____324 -> begin
false
end)) rc.FStar_Syntax_Syntax.residual_flags))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____326 = (FStar_TypeChecker_Env.lookup_definition ((FStar_TypeChecker_Env.Eager_unfolding_only)::[]) env.FStar_SMTEncoding_Env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____326 FStar_Option.isSome))
end
| uu____343 -> begin
false
end)))


let whnf : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (

let uu____354 = (head_normal env t)
in (match (uu____354) with
| true -> begin
t
end
| uu____355 -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.FStar_SMTEncoding_Env.tcenv t)
end)))


let norm : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Exclude (FStar_TypeChecker_Normalize.Zeta))::(FStar_TypeChecker_Normalize.Eager_unfolding)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.FStar_SMTEncoding_Env.tcenv t))


let trivial_post : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun t -> (

let uu____371 = (

let uu____372 = (FStar_Syntax_Syntax.null_binder t)
in (uu____372)::[])
in (

let uu____373 = (FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None)
in (FStar_Syntax_Util.abs uu____371 uu____373 FStar_Pervasives_Native.None))))


let mk_Apply : FStar_SMTEncoding_Term.term  ->  (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e vars -> (FStar_All.pipe_right vars (FStar_List.fold_left (fun out var -> (match ((FStar_Pervasives_Native.snd var)) with
| FStar_SMTEncoding_Term.Fuel_sort -> begin
(

let uu____415 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Term.mk_ApplyTF out uu____415))
end
| s -> begin
(

let uu____418 = (FStar_SMTEncoding_Util.mkFreeV var)
in (FStar_SMTEncoding_Util.mk_ApplyTT out uu____418))
end)) e)))


let mk_Apply_args : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun e args -> (FStar_All.pipe_right args (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)))


let raise_arity_mismatch : 'a . Prims.string  ->  Prims.int  ->  Prims.int  ->  FStar_Range.range  ->  'a = (fun head1 arity n_args rng -> (

let uu____466 = (

let uu____471 = (

let uu____472 = (FStar_Util.string_of_int arity)
in (

let uu____473 = (FStar_Util.string_of_int n_args)
in (FStar_Util.format3 "Head symbol %s expects at least %s arguments; got only %s" head1 uu____472 uu____473)))
in ((FStar_Errors.Fatal_SMTEncodingArityMismatch), (uu____471)))
in (FStar_Errors.raise_error uu____466 rng)))


let maybe_curry_app : FStar_Range.range  ->  FStar_SMTEncoding_Term.op  ->  Prims.int  ->  FStar_SMTEncoding_Term.term Prims.list  ->  FStar_SMTEncoding_Term.term = (fun rng head1 arity args -> (

let n_args = (FStar_List.length args)
in (match ((Prims.op_Equality n_args arity)) with
| true -> begin
(FStar_SMTEncoding_Util.mkApp' ((head1), (args)))
end
| uu____505 -> begin
(match ((n_args > arity)) with
| true -> begin
(

let uu____512 = (FStar_Util.first_N arity args)
in (match (uu____512) with
| (args1, rest) -> begin
(

let head2 = (FStar_SMTEncoding_Util.mkApp' ((head1), (args1)))
in (mk_Apply_args head2 rest))
end))
end
| uu____534 -> begin
(

let uu____535 = (FStar_SMTEncoding_Term.op_to_string head1)
in (raise_arity_mismatch uu____535 arity n_args rng))
end)
end)))


let is_app : FStar_SMTEncoding_Term.op  ->  Prims.bool = (fun uu___69_544 -> (match (uu___69_544) with
| FStar_SMTEncoding_Term.Var ("ApplyTT") -> begin
true
end
| FStar_SMTEncoding_Term.Var ("ApplyTF") -> begin
true
end
| uu____545 -> begin
false
end))


let is_an_eta_expansion : FStar_SMTEncoding_Env.env_t  ->  FStar_SMTEncoding_Term.fv Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option = (fun env vars body -> (

let rec check_partial_applications = (fun t xs -> (match (((t.FStar_SMTEncoding_Term.tm), (xs))) with
| (FStar_SMTEncoding_Term.App (app, (f)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (y); FStar_SMTEncoding_Term.freevars = uu____591; FStar_SMTEncoding_Term.rng = uu____592})::[]), (x)::xs1) when ((is_app app) && (FStar_SMTEncoding_Term.fv_eq x y)) -> begin
(check_partial_applications f xs1)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (f), args), uu____615) -> begin
(

let uu____624 = ((Prims.op_Equality (FStar_List.length args) (FStar_List.length xs)) && (FStar_List.forall2 (fun a v1 -> (match (a.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (fv) -> begin
(FStar_SMTEncoding_Term.fv_eq fv v1)
end
| uu____635 -> begin
false
end)) args (FStar_List.rev xs)))
in (match (uu____624) with
| true -> begin
(FStar_SMTEncoding_Env.tok_of_name env f)
end
| uu____638 -> begin
FStar_Pervasives_Native.None
end))
end
| (uu____639, []) -> begin
(

let fvs = (FStar_SMTEncoding_Term.free_variables t)
in (

let uu____643 = (FStar_All.pipe_right fvs (FStar_List.for_all (fun fv -> (

let uu____647 = (FStar_Util.for_some (FStar_SMTEncoding_Term.fv_eq fv) vars)
in (not (uu____647))))))
in (match (uu____643) with
| true -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____650 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____651 -> begin
FStar_Pervasives_Native.None
end))
in (check_partial_applications body (FStar_List.rev vars))))


let check_pattern_vars : 'Auu____668 'Auu____669 . FStar_SMTEncoding_Env.env_t  ->  (FStar_Syntax_Syntax.bv * 'Auu____668) Prims.list  ->  (FStar_Syntax_Syntax.term * 'Auu____669) Prims.list  ->  unit = (fun env vars pats -> (

let pats1 = (FStar_All.pipe_right pats (FStar_List.map (fun uu____727 -> (match (uu____727) with
| (x, uu____733) -> begin
(FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.AllowUnboundUniverses)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.FStar_SMTEncoding_Env.tcenv x)
end))))
in (match (pats1) with
| [] -> begin
()
end
| (hd1)::tl1 -> begin
(

let pat_vars = (

let uu____741 = (FStar_Syntax_Free.names hd1)
in (FStar_List.fold_left (fun out x -> (

let uu____753 = (FStar_Syntax_Free.names x)
in (FStar_Util.set_union out uu____753))) uu____741 tl1))
in (

let uu____756 = (FStar_All.pipe_right vars (FStar_Util.find_opt (fun uu____783 -> (match (uu____783) with
| (b, uu____789) -> begin
(

let uu____790 = (FStar_Util.set_mem b pat_vars)
in (not (uu____790)))
end))))
in (match (uu____756) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (x, uu____796) -> begin
(

let pos = (FStar_List.fold_left (fun out t -> (FStar_Range.union_ranges out t.FStar_Syntax_Syntax.pos)) hd1.FStar_Syntax_Syntax.pos tl1)
in (

let uu____810 = (

let uu____815 = (

let uu____816 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "SMT pattern misses at least one bound variable: %s" uu____816))
in ((FStar_Errors.Warning_SMTPatternMissingBoundVar), (uu____815)))
in (FStar_Errors.log_issue pos uu____810)))
end)))
end)))


type label =
(FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range)


type labels =
label Prims.list

type pattern =
{pat_vars : (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list; pat_term : unit  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t); guard : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term; projections : FStar_SMTEncoding_Term.term  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list}


let __proj__Mkpattern__item__pat_vars : pattern  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list = (fun projectee -> (match (projectee) with
| {pat_vars = __fname__pat_vars; pat_term = __fname__pat_term; guard = __fname__guard; projections = __fname__projections} -> begin
__fname__pat_vars
end))


let __proj__Mkpattern__item__pat_term : pattern  ->  unit  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun projectee -> (match (projectee) with
| {pat_vars = __fname__pat_vars; pat_term = __fname__pat_term; guard = __fname__guard; projections = __fname__projections} -> begin
__fname__pat_term
end))


let __proj__Mkpattern__item__guard : pattern  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun projectee -> (match (projectee) with
| {pat_vars = __fname__pat_vars; pat_term = __fname__pat_term; guard = __fname__guard; projections = __fname__projections} -> begin
__fname__guard
end))


let __proj__Mkpattern__item__projections : pattern  ->  FStar_SMTEncoding_Term.term  ->  (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list = (fun projectee -> (match (projectee) with
| {pat_vars = __fname__pat_vars; pat_term = __fname__pat_term; guard = __fname__guard; projections = __fname__projections} -> begin
__fname__projections
end))


let as_function_typ : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.term = (fun env t0 -> (

let rec aux = (fun norm1 t -> (

let t1 = (FStar_Syntax_Subst.compress t)
in (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (uu____1091) -> begin
t1
end
| FStar_Syntax_Syntax.Tm_refine (uu____1104) -> begin
(

let uu____1111 = (FStar_Syntax_Util.unrefine t1)
in (aux true uu____1111))
end
| uu____1112 -> begin
(match (norm1) with
| true -> begin
(

let uu____1113 = (whnf env t1)
in (aux false uu____1113))
end
| uu____1114 -> begin
(

let uu____1115 = (

let uu____1116 = (FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos)
in (

let uu____1117 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format2 "(%s) Expected a function typ; got %s" uu____1116 uu____1117)))
in (failwith uu____1115))
end)
end)))
in (aux true t0)))


let rec curried_arrow_formals_comp : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) = (fun k -> (

let k1 = (FStar_Syntax_Subst.compress k)
in (match (k1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(FStar_Syntax_Subst.open_comp bs c)
end
| FStar_Syntax_Syntax.Tm_refine (bv, uu____1151) -> begin
(curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort)
end
| uu____1156 -> begin
(

let uu____1157 = (FStar_Syntax_Syntax.mk_Total k1)
in (([]), (uu____1157)))
end)))


let is_arithmetic_primitive : 'Auu____1174 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  'Auu____1174 Prims.list  ->  Prims.bool = (fun head1 args -> (match (((head1.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____1196)::(uu____1197)::[]) -> begin
(((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Subtraction)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Multiply)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____1201)::[]) -> begin
(FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus)
end
| uu____1204 -> begin
false
end))


let isInteger : FStar_Syntax_Syntax.term'  ->  Prims.bool = (fun tm -> (match (tm) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (n1, FStar_Pervasives_Native.None)) -> begin
true
end
| uu____1227 -> begin
false
end))


let getInteger : FStar_Syntax_Syntax.term'  ->  Prims.int = (fun tm -> (match (tm) with
| FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int (n1, FStar_Pervasives_Native.None)) -> begin
(FStar_Util.int_of_string n1)
end
| uu____1244 -> begin
(failwith "Expected an Integer term")
end))


let is_BitVector_primitive : 'Auu____1251 . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax * 'Auu____1251) Prims.list  ->  Prims.bool = (fun head1 args -> (match (((head1.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((sz_arg, uu____1292))::(uu____1293)::(uu____1294)::[]) -> begin
((((((((((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_and_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_xor_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_or_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_add_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_sub_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_shift_left_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_shift_right_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_udiv_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mod_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid)) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mul_lid)) && (isInteger sz_arg.FStar_Syntax_Syntax.n))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((sz_arg, uu____1345))::(uu____1346)::[]) -> begin
(((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_to_nat_lid)) && (isInteger sz_arg.FStar_Syntax_Syntax.n))
end
| uu____1383 -> begin
false
end))


let rec encode_const : FStar_Const.sconst  ->  FStar_SMTEncoding_Env.env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list) = (fun c env -> (match (c) with
| FStar_Const.Const_unit -> begin
((FStar_SMTEncoding_Term.mk_Term_unit), ([]))
end
| FStar_Const.Const_bool (true) -> begin
(

let uu____1704 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((uu____1704), ([])))
end
| FStar_Const.Const_bool (false) -> begin
(

let uu____1707 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse)
in ((uu____1707), ([])))
end
| FStar_Const.Const_char (c1) -> begin
(

let uu____1711 = (

let uu____1712 = (

let uu____1719 = (

let uu____1722 = (

let uu____1723 = (FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c1))
in (FStar_SMTEncoding_Term.boxInt uu____1723))
in (uu____1722)::[])
in (("FStar.Char.__char_of_int"), (uu____1719)))
in (FStar_SMTEncoding_Util.mkApp uu____1712))
in ((uu____1711), ([])))
end
| FStar_Const.Const_int (i, FStar_Pervasives_Native.None) -> begin
(

let uu____1739 = (

let uu____1740 = (FStar_SMTEncoding_Util.mkInteger i)
in (FStar_SMTEncoding_Term.boxInt uu____1740))
in ((uu____1739), ([])))
end
| FStar_Const.Const_int (repr, FStar_Pervasives_Native.Some (sw)) -> begin
(

let syntax_term = (FStar_ToSyntax_ToSyntax.desugar_machine_integer env.FStar_SMTEncoding_Env.tcenv.FStar_TypeChecker_Env.dsenv repr sw FStar_Range.dummyRange)
in (encode_term syntax_term env))
end
| FStar_Const.Const_string (s, uu____1761) -> begin
(

let uu____1762 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.string_const s)
in ((uu____1762), ([])))
end
| FStar_Const.Const_range (uu____1765) -> begin
(

let uu____1766 = (FStar_SMTEncoding_Term.mk_Range_const ())
in ((uu____1766), ([])))
end
| FStar_Const.Const_effect -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| c1 -> begin
(

let uu____1772 = (

let uu____1773 = (FStar_Syntax_Print.const_to_string c1)
in (FStar_Util.format1 "Unhandled constant: %s" uu____1773))
in (failwith uu____1772))
end))
and encode_binders : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.binders  ->  FStar_SMTEncoding_Env.env_t  ->  (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Env.env_t * FStar_SMTEncoding_Term.decls_t * FStar_Syntax_Syntax.bv Prims.list) = (fun fuel_opt bs env -> ((

let uu____1802 = (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv FStar_Options.Low)
in (match (uu____1802) with
| true -> begin
(

let uu____1803 = (FStar_Syntax_Print.binders_to_string ", " bs)
in (FStar_Util.print1 "Encoding binders %s\n" uu____1803))
end
| uu____1804 -> begin
()
end));
(

let uu____1805 = (FStar_All.pipe_right bs (FStar_List.fold_left (fun uu____1889 b -> (match (uu____1889) with
| (vars, guards, env1, decls, names1) -> begin
(

let uu____1968 = (

let x = (FStar_SMTEncoding_Env.unmangle (FStar_Pervasives_Native.fst b))
in (

let uu____1984 = (FStar_SMTEncoding_Env.gen_term_var env1 x)
in (match (uu____1984) with
| (xxsym, xx, env') -> begin
(

let uu____2008 = (

let uu____2013 = (norm env1 x.FStar_Syntax_Syntax.sort)
in (encode_term_pred fuel_opt uu____2013 env1 xx))
in (match (uu____2008) with
| (guard_x_t, decls') -> begin
((((xxsym), (FStar_SMTEncoding_Term.Term_sort))), (guard_x_t), (env'), (decls'), (x))
end))
end)))
in (match (uu____1968) with
| (v1, g, env2, decls', n1) -> begin
(((v1)::vars), ((g)::guards), (env2), ((FStar_List.append decls decls')), ((n1)::names1))
end))
end)) (([]), ([]), (env), ([]), ([]))))
in (match (uu____1805) with
| (vars, guards, env1, decls, names1) -> begin
(((FStar_List.rev vars)), ((FStar_List.rev guards)), (env1), (decls), ((FStar_List.rev names1)))
end));
))
and encode_term_pred : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Env.env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____2172 = (encode_term t env)
in (match (uu____2172) with
| (t1, decls) -> begin
(

let uu____2183 = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1)
in ((uu____2183), (decls)))
end)))
and encode_term_pred' : FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option  ->  FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Env.env_t  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun fuel_opt t env e -> (

let uu____2194 = (encode_term t env)
in (match (uu____2194) with
| (t1, decls) -> begin
(match (fuel_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____2209 = (FStar_SMTEncoding_Term.mk_HasTypeZ e t1)
in ((uu____2209), (decls)))
end
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____2211 = (FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1)
in ((uu____2211), (decls)))
end)
end)))
and encode_arith_term : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.args  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun env head1 args_e -> (

let uu____2217 = (encode_args args_e env)
in (match (uu____2217) with
| (arg_tms, decls) -> begin
(

let head_fv = (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____2236 -> begin
(failwith "Impossible")
end)
in (

let unary = (fun arg_tms1 -> (

let uu____2247 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxInt uu____2247)))
in (

let binary = (fun arg_tms1 -> (

let uu____2262 = (

let uu____2263 = (FStar_List.hd arg_tms1)
in (FStar_SMTEncoding_Term.unboxInt uu____2263))
in (

let uu____2264 = (

let uu____2265 = (

let uu____2266 = (FStar_List.tl arg_tms1)
in (FStar_List.hd uu____2266))
in (FStar_SMTEncoding_Term.unboxInt uu____2265))
in ((uu____2262), (uu____2264)))))
in (

let mk_default = (fun uu____2274 -> (

let uu____2275 = (FStar_SMTEncoding_Env.lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name)
in (match (uu____2275) with
| (fname, fuel_args, arity) -> begin
(

let args = (FStar_List.append fuel_args arg_tms)
in (maybe_curry_app head1.FStar_Syntax_Syntax.pos fname arity args))
end)))
in (

let mk_l = (fun op mk_args ts -> (

let uu____2337 = (FStar_Options.smtencoding_l_arith_native ())
in (match (uu____2337) with
| true -> begin
(

let uu____2338 = (

let uu____2339 = (mk_args ts)
in (op uu____2339))
in (FStar_All.pipe_right uu____2338 FStar_SMTEncoding_Term.boxInt))
end
| uu____2340 -> begin
(mk_default ())
end)))
in (

let mk_nl = (fun nm op ts -> (

let uu____2374 = (FStar_Options.smtencoding_nl_arith_wrapped ())
in (match (uu____2374) with
| true -> begin
(

let uu____2375 = (binary ts)
in (match (uu____2375) with
| (t1, t2) -> begin
(

let uu____2382 = (FStar_SMTEncoding_Util.mkApp ((nm), ((t1)::(t2)::[])))
in (FStar_All.pipe_right uu____2382 FStar_SMTEncoding_Term.boxInt))
end))
end
| uu____2385 -> begin
(

let uu____2386 = (FStar_Options.smtencoding_nl_arith_native ())
in (match (uu____2386) with
| true -> begin
(

let uu____2387 = (

let uu____2388 = (binary ts)
in (op uu____2388))
in (FStar_All.pipe_right uu____2387 FStar_SMTEncoding_Term.boxInt))
end
| uu____2393 -> begin
(mk_default ())
end))
end)))
in (

let add1 = (mk_l FStar_SMTEncoding_Util.mkAdd binary)
in (

let sub1 = (mk_l FStar_SMTEncoding_Util.mkSub binary)
in (

let minus = (mk_l FStar_SMTEncoding_Util.mkMinus unary)
in (

let mul1 = (mk_nl "_mul" FStar_SMTEncoding_Util.mkMul)
in (

let div1 = (mk_nl "_div" FStar_SMTEncoding_Util.mkDiv)
in (

let modulus = (mk_nl "_mod" FStar_SMTEncoding_Util.mkMod)
in (

let ops = (((FStar_Parser_Const.op_Addition), (add1)))::(((FStar_Parser_Const.op_Subtraction), (sub1)))::(((FStar_Parser_Const.op_Multiply), (mul1)))::(((FStar_Parser_Const.op_Division), (div1)))::(((FStar_Parser_Const.op_Modulus), (modulus)))::(((FStar_Parser_Const.op_Minus), (minus)))::[]
in (

let uu____2549 = (

let uu____2559 = (FStar_List.tryFind (fun uu____2583 -> (match (uu____2583) with
| (l, uu____2593) -> begin
(FStar_Syntax_Syntax.fv_eq_lid head_fv l)
end)) ops)
in (FStar_All.pipe_right uu____2559 FStar_Util.must))
in (match (uu____2549) with
| (uu____2637, op) -> begin
(

let uu____2649 = (op arg_tms)
in ((uu____2649), (decls)))
end)))))))))))))))
end)))
and encode_BitVector_term : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.arg Prims.list  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl Prims.list) = (fun env head1 args_e -> (

let uu____2657 = (FStar_List.hd args_e)
in (match (uu____2657) with
| (tm_sz, uu____2665) -> begin
(

let sz = (getInteger tm_sz.FStar_Syntax_Syntax.n)
in (

let sz_key = (FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz))
in (

let sz_decls = (

let uu____2675 = (FStar_Util.smap_try_find env.FStar_SMTEncoding_Env.cache sz_key)
in (match (uu____2675) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
[]
end
| FStar_Pervasives_Native.None -> begin
(

let t_decls1 = (FStar_SMTEncoding_Term.mkBvConstructor sz)
in ((

let uu____2683 = (FStar_SMTEncoding_Env.mk_cache_entry env "" [] [])
in (FStar_Util.smap_add env.FStar_SMTEncoding_Env.cache sz_key uu____2683));
t_decls1;
))
end))
in (

let uu____2684 = (match (((head1.FStar_Syntax_Syntax.n), (args_e))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____2704)::((sz_arg, uu____2706))::(uu____2707)::[]) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid) && (isInteger sz_arg.FStar_Syntax_Syntax.n)) -> begin
(

let uu____2756 = (

let uu____2759 = (FStar_List.tail args_e)
in (FStar_List.tail uu____2759))
in (

let uu____2762 = (

let uu____2765 = (getInteger sz_arg.FStar_Syntax_Syntax.n)
in FStar_Pervasives_Native.Some (uu____2765))
in ((uu____2756), (uu____2762))))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____2771)::((sz_arg, uu____2773))::(uu____2774)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid) -> begin
(

let uu____2823 = (

let uu____2824 = (FStar_Syntax_Print.term_to_string sz_arg)
in (FStar_Util.format1 "Not a constant bitvector extend size: %s" uu____2824))
in (failwith uu____2823))
end
| uu____2833 -> begin
(

let uu____2840 = (FStar_List.tail args_e)
in ((uu____2840), (FStar_Pervasives_Native.None)))
end)
in (match (uu____2684) with
| (arg_tms, ext_sz) -> begin
(

let uu____2863 = (encode_args arg_tms env)
in (match (uu____2863) with
| (arg_tms1, decls) -> begin
(

let head_fv = (match (head1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
fv
end
| uu____2884 -> begin
(failwith "Impossible")
end)
in (

let unary = (fun arg_tms2 -> (

let uu____2895 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____2895)))
in (

let unary_arith = (fun arg_tms2 -> (

let uu____2906 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxInt uu____2906)))
in (

let binary = (fun arg_tms2 -> (

let uu____2921 = (

let uu____2922 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____2922))
in (

let uu____2923 = (

let uu____2924 = (

let uu____2925 = (FStar_List.tl arg_tms2)
in (FStar_List.hd uu____2925))
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____2924))
in ((uu____2921), (uu____2923)))))
in (

let binary_arith = (fun arg_tms2 -> (

let uu____2942 = (

let uu____2943 = (FStar_List.hd arg_tms2)
in (FStar_SMTEncoding_Term.unboxBitVec sz uu____2943))
in (

let uu____2944 = (

let uu____2945 = (

let uu____2946 = (FStar_List.tl arg_tms2)
in (FStar_List.hd uu____2946))
in (FStar_SMTEncoding_Term.unboxInt uu____2945))
in ((uu____2942), (uu____2944)))))
in (

let mk_bv = (fun op mk_args resBox ts -> (

let uu____3004 = (

let uu____3005 = (mk_args ts)
in (op uu____3005))
in (FStar_All.pipe_right uu____3004 resBox)))
in (

let bv_and = (mk_bv FStar_SMTEncoding_Util.mkBvAnd binary (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_xor = (mk_bv FStar_SMTEncoding_Util.mkBvXor binary (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_or = (mk_bv FStar_SMTEncoding_Util.mkBvOr binary (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_add = (mk_bv FStar_SMTEncoding_Util.mkBvAdd binary (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_sub = (mk_bv FStar_SMTEncoding_Util.mkBvSub binary (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_shl = (mk_bv (FStar_SMTEncoding_Util.mkBvShl sz) binary_arith (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_shr = (mk_bv (FStar_SMTEncoding_Util.mkBvShr sz) binary_arith (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_udiv = (mk_bv (FStar_SMTEncoding_Util.mkBvUdiv sz) binary_arith (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_mod = (mk_bv (FStar_SMTEncoding_Util.mkBvMod sz) binary_arith (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_mul = (mk_bv (FStar_SMTEncoding_Util.mkBvMul sz) binary_arith (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let bv_ult = (mk_bv FStar_SMTEncoding_Util.mkBvUlt binary FStar_SMTEncoding_Term.boxBool)
in (

let bv_uext = (fun arg_tms2 -> (

let uu____3137 = (

let uu____3142 = (match (ext_sz) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(failwith "impossible")
end)
in (FStar_SMTEncoding_Util.mkBvUext uu____3142))
in (

let uu____3144 = (

let uu____3149 = (

let uu____3150 = (match (ext_sz) with
| FStar_Pervasives_Native.Some (x) -> begin
x
end
| FStar_Pervasives_Native.None -> begin
(failwith "impossible")
end)
in (sz + uu____3150))
in (FStar_SMTEncoding_Term.boxBitVec uu____3149))
in (mk_bv uu____3137 unary uu____3144 arg_tms2))))
in (

let to_int1 = (mk_bv FStar_SMTEncoding_Util.mkBvToNat unary FStar_SMTEncoding_Term.boxInt)
in (

let bv_to = (mk_bv (FStar_SMTEncoding_Util.mkNatToBv sz) unary_arith (FStar_SMTEncoding_Term.boxBitVec sz))
in (

let ops = (((FStar_Parser_Const.bv_and_lid), (bv_and)))::(((FStar_Parser_Const.bv_xor_lid), (bv_xor)))::(((FStar_Parser_Const.bv_or_lid), (bv_or)))::(((FStar_Parser_Const.bv_add_lid), (bv_add)))::(((FStar_Parser_Const.bv_sub_lid), (bv_sub)))::(((FStar_Parser_Const.bv_shift_left_lid), (bv_shl)))::(((FStar_Parser_Const.bv_shift_right_lid), (bv_shr)))::(((FStar_Parser_Const.bv_udiv_lid), (bv_udiv)))::(((FStar_Parser_Const.bv_mod_lid), (bv_mod)))::(((FStar_Parser_Const.bv_mul_lid), (bv_mul)))::(((FStar_Parser_Const.bv_ult_lid), (bv_ult)))::(((FStar_Parser_Const.bv_uext_lid), (bv_uext)))::(((FStar_Parser_Const.bv_to_nat_lid), (to_int1)))::(((FStar_Parser_Const.nat_to_bv_lid), (bv_to)))::[]
in (

let uu____3383 = (

let uu____3393 = (FStar_List.tryFind (fun uu____3417 -> (match (uu____3417) with
| (l, uu____3427) -> begin
(FStar_Syntax_Syntax.fv_eq_lid head_fv l)
end)) ops)
in (FStar_All.pipe_right uu____3393 FStar_Util.must))
in (match (uu____3383) with
| (uu____3473, op) -> begin
(

let uu____3485 = (op arg_tms1)
in ((uu____3485), ((FStar_List.append sz_decls decls))))
end)))))))))))))))))))))))
end))
end)))))
end)))
and encode_deeply_embedded_quantifier : FStar_Syntax_Syntax.term  ->  FStar_SMTEncoding_Env.env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let env1 = (

let uu___73_3495 = env
in {FStar_SMTEncoding_Env.bvar_bindings = uu___73_3495.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___73_3495.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___73_3495.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = uu___73_3495.FStar_SMTEncoding_Env.tcenv; FStar_SMTEncoding_Env.warn = uu___73_3495.FStar_SMTEncoding_Env.warn; FStar_SMTEncoding_Env.cache = uu___73_3495.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = uu___73_3495.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___73_3495.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___73_3495.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___73_3495.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = true})
in (

let uu____3496 = (encode_term t env1)
in (match (uu____3496) with
| (tm, decls) -> begin
(

let vars = (FStar_SMTEncoding_Term.free_variables tm)
in (

let valid_tm = (FStar_SMTEncoding_Term.mk_Valid tm)
in (

let key = (FStar_SMTEncoding_Util.mkForall (([]), (vars), (valid_tm)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term key)
in (

let uu____3517 = (FStar_Util.smap_try_find env1.FStar_SMTEncoding_Env.cache tkey_hash)
in (match (uu____3517) with
| FStar_Pervasives_Native.Some (uu____3524) -> begin
((tm), (decls))
end
| uu____3525 -> begin
(match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (uu____3532, ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (uu____3533); FStar_SMTEncoding_Term.freevars = uu____3534; FStar_SMTEncoding_Term.rng = uu____3535})::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV (uu____3536); FStar_SMTEncoding_Term.freevars = uu____3537; FStar_SMTEncoding_Term.rng = uu____3538})::[]) -> begin
((FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_QuantifierWithoutPattern), ("Not encoding deeply embedded, unguarded quantifier to SMT")));
((tm), (decls));
)
end
| uu____3566 -> begin
(

let uu____3567 = (encode_formula t env1)
in (match (uu____3567) with
| (phi, decls') -> begin
(

let interp = (match (vars) with
| [] -> begin
(

let uu____3583 = (

let uu____3588 = (FStar_SMTEncoding_Term.mk_Valid tm)
in ((uu____3588), (phi)))
in (FStar_SMTEncoding_Util.mkIff uu____3583))
end
| uu____3589 -> begin
(

let uu____3590 = (

let uu____3601 = (

let uu____3602 = (

let uu____3607 = (FStar_SMTEncoding_Term.mk_Valid tm)
in ((uu____3607), (phi)))
in (FStar_SMTEncoding_Util.mkIff uu____3602))
in ((((valid_tm)::[])::[]), (vars), (uu____3601)))
in (FStar_SMTEncoding_Util.mkForall uu____3590))
end)
in (

let ax = (

let uu____3617 = (

let uu____3624 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique "l_quant_interp")
in ((interp), (FStar_Pervasives_Native.Some ("Interpretation of deeply embedded quantifier")), (uu____3624)))
in (FStar_SMTEncoding_Util.mkAssume uu____3617))
in ((

let uu____3628 = (FStar_SMTEncoding_Env.mk_cache_entry env1 "" [] ((ax)::[]))
in (FStar_Util.smap_add env1.FStar_SMTEncoding_Env.cache tkey_hash uu____3628));
((tm), ((FStar_List.append decls (FStar_List.append decls' ((ax)::[])))));
)))
end))
end)
end))))))
end))))
and encode_term : FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Env.env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let t0 = (FStar_Syntax_Subst.compress t)
in ((

let uu____3639 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____3639) with
| true -> begin
(

let uu____3640 = (FStar_Syntax_Print.tag_of_term t)
in (

let uu____3641 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____3642 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.print3 "(%s) (%s)   %s\n" uu____3640 uu____3641 uu____3642))))
end
| uu____3643 -> begin
()
end));
(match (t0.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_delayed (uu____3648) -> begin
(

let uu____3673 = (

let uu____3674 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____3675 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____3676 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____3677 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3674 uu____3675 uu____3676 uu____3677)))))
in (failwith uu____3673))
end
| FStar_Syntax_Syntax.Tm_unknown -> begin
(

let uu____3682 = (

let uu____3683 = (FStar_All.pipe_left FStar_Range.string_of_range t.FStar_Syntax_Syntax.pos)
in (

let uu____3684 = (FStar_Syntax_Print.tag_of_term t0)
in (

let uu____3685 = (FStar_Syntax_Print.term_to_string t0)
in (

let uu____3686 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3683 uu____3684 uu____3685 uu____3686)))))
in (failwith uu____3682))
end
| FStar_Syntax_Syntax.Tm_lazy (i) -> begin
(

let uu____3692 = (FStar_Syntax_Util.unfold_lazy i)
in (encode_term uu____3692 env))
end
| FStar_Syntax_Syntax.Tm_bvar (x) -> begin
(

let uu____3694 = (

let uu____3695 = (FStar_Syntax_Print.bv_to_string x)
in (FStar_Util.format1 "Impossible: locally nameless; got %s" uu____3695))
in (failwith uu____3694))
end
| FStar_Syntax_Syntax.Tm_ascribed (t1, (k, uu____3702), uu____3703) -> begin
(

let uu____3752 = (match (k) with
| FStar_Util.Inl (t2) -> begin
(FStar_Syntax_Util.is_unit t2)
end
| uu____3760 -> begin
false
end)
in (match (uu____3752) with
| true -> begin
((FStar_SMTEncoding_Term.mk_Term_unit), ([]))
end
| uu____3775 -> begin
(encode_term t1 env)
end))
end
| FStar_Syntax_Syntax.Tm_quoted (qt, uu____3777) -> begin
(

let tv = (

let uu____3783 = (FStar_Reflection_Basic.inspect_ln qt)
in (FStar_Syntax_Embeddings.embed FStar_Reflection_Embeddings.e_term_view t.FStar_Syntax_Syntax.pos uu____3783))
in (

let t1 = (

let uu____3787 = (

let uu____3796 = (FStar_Syntax_Syntax.as_arg tv)
in (uu____3796)::[])
in (FStar_Syntax_Util.mk_app (FStar_Reflection_Data.refl_constant_term FStar_Reflection_Data.fstar_refl_pack_ln) uu____3787))
in (encode_term t1 env)))
end
| FStar_Syntax_Syntax.Tm_meta (t1, FStar_Syntax_Syntax.Meta_pattern (uu____3798)) -> begin
(encode_term t1 (

let uu___74_3814 = env
in {FStar_SMTEncoding_Env.bvar_bindings = uu___74_3814.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___74_3814.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___74_3814.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = uu___74_3814.FStar_SMTEncoding_Env.tcenv; FStar_SMTEncoding_Env.warn = uu___74_3814.FStar_SMTEncoding_Env.warn; FStar_SMTEncoding_Env.cache = uu___74_3814.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = uu___74_3814.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = uu___74_3814.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___74_3814.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___74_3814.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = false}))
end
| FStar_Syntax_Syntax.Tm_meta (t1, uu____3816) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
(

let t1 = (FStar_SMTEncoding_Env.lookup_term_var env x)
in ((t1), ([])))
end
| FStar_Syntax_Syntax.Tm_fvar (v1) -> begin
(

let uu____3826 = (head_redex env t)
in (match (uu____3826) with
| true -> begin
(

let uu____3831 = (whnf env t)
in (encode_term uu____3831 env))
end
| uu____3832 -> begin
(

let uu____3833 = (FStar_SMTEncoding_Env.lookup_free_var_name env v1.FStar_Syntax_Syntax.fv_name)
in (match (uu____3833) with
| (uu____3842, arity) -> begin
(

let tok = (FStar_SMTEncoding_Env.lookup_free_var env v1.FStar_Syntax_Syntax.fv_name)
in (

let aux_decls = (match ((arity > (Prims.parse_int "0"))) with
| true -> begin
(match (tok.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (uu____3852) -> begin
(

let uu____3857 = (

let uu____3858 = (

let uu____3865 = (FStar_SMTEncoding_Term.kick_partial_app tok)
in (

let uu____3866 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique "@kick_partial_app")
in ((uu____3865), (FStar_Pervasives_Native.Some ("kick_partial_app")), (uu____3866))))
in (FStar_SMTEncoding_Util.mkAssume uu____3858))
in (uu____3857)::[])
end
| FStar_SMTEncoding_Term.App (uu____3869, []) -> begin
(

let uu____3872 = (

let uu____3873 = (

let uu____3880 = (FStar_SMTEncoding_Term.kick_partial_app tok)
in (

let uu____3881 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique "@kick_partial_app")
in ((uu____3880), (FStar_Pervasives_Native.Some ("kick_partial_app")), (uu____3881))))
in (FStar_SMTEncoding_Util.mkAssume uu____3873))
in (uu____3872)::[])
end
| uu____3884 -> begin
[]
end)
end
| uu____3885 -> begin
[]
end)
in ((tok), (aux_decls))))
end))
end))
end
| FStar_Syntax_Syntax.Tm_type (uu____3888) -> begin
((FStar_SMTEncoding_Term.mk_Term_type), ([]))
end
| FStar_Syntax_Syntax.Tm_uinst (t1, uu____3892) -> begin
(encode_term t1 env)
end
| FStar_Syntax_Syntax.Tm_constant (c) -> begin
(encode_const c env)
end
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let module_name = env.FStar_SMTEncoding_Env.current_module_name
in (

let uu____3917 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____3917) with
| (binders1, res) -> begin
(

let uu____3928 = ((env.FStar_SMTEncoding_Env.encode_non_total_function_typ && (FStar_Syntax_Util.is_pure_or_ghost_comp res)) || (FStar_Syntax_Util.is_tot_or_gtot_comp res))
in (match (uu____3928) with
| true -> begin
(

let uu____3933 = (encode_binders FStar_Pervasives_Native.None binders1 env)
in (match (uu____3933) with
| (vars, guards, env', decls, uu____3958) -> begin
(

let fsym = (

let uu____3976 = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh "f")
in ((uu____3976), (FStar_SMTEncoding_Term.Term_sort)))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let app = (mk_Apply f vars)
in (

let uu____3979 = (FStar_TypeChecker_Util.pure_or_ghost_pre_and_post (

let uu___75_3988 = env.FStar_SMTEncoding_Env.tcenv
in {FStar_TypeChecker_Env.solver = uu___75_3988.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = uu___75_3988.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = uu___75_3988.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = uu___75_3988.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = uu___75_3988.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = uu___75_3988.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = uu___75_3988.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = uu___75_3988.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = uu___75_3988.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = uu___75_3988.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = uu___75_3988.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = uu___75_3988.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = uu___75_3988.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = uu___75_3988.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = uu___75_3988.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = uu___75_3988.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = uu___75_3988.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = uu___75_3988.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.lax = true; FStar_TypeChecker_Env.lax_universes = uu___75_3988.FStar_TypeChecker_Env.lax_universes; FStar_TypeChecker_Env.failhard = uu___75_3988.FStar_TypeChecker_Env.failhard; FStar_TypeChecker_Env.nosynth = uu___75_3988.FStar_TypeChecker_Env.nosynth; FStar_TypeChecker_Env.tc_term = uu___75_3988.FStar_TypeChecker_Env.tc_term; FStar_TypeChecker_Env.type_of = uu___75_3988.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.universe_of = uu___75_3988.FStar_TypeChecker_Env.universe_of; FStar_TypeChecker_Env.check_type_of = uu___75_3988.FStar_TypeChecker_Env.check_type_of; FStar_TypeChecker_Env.use_bv_sorts = uu___75_3988.FStar_TypeChecker_Env.use_bv_sorts; FStar_TypeChecker_Env.qtbl_name_and_index = uu___75_3988.FStar_TypeChecker_Env.qtbl_name_and_index; FStar_TypeChecker_Env.normalized_eff_names = uu___75_3988.FStar_TypeChecker_Env.normalized_eff_names; FStar_TypeChecker_Env.proof_ns = uu___75_3988.FStar_TypeChecker_Env.proof_ns; FStar_TypeChecker_Env.synth_hook = uu___75_3988.FStar_TypeChecker_Env.synth_hook; FStar_TypeChecker_Env.splice = uu___75_3988.FStar_TypeChecker_Env.splice; FStar_TypeChecker_Env.is_native_tactic = uu___75_3988.FStar_TypeChecker_Env.is_native_tactic; FStar_TypeChecker_Env.identifier_info = uu___75_3988.FStar_TypeChecker_Env.identifier_info; FStar_TypeChecker_Env.tc_hooks = uu___75_3988.FStar_TypeChecker_Env.tc_hooks; FStar_TypeChecker_Env.dsenv = uu___75_3988.FStar_TypeChecker_Env.dsenv; FStar_TypeChecker_Env.dep_graph = uu___75_3988.FStar_TypeChecker_Env.dep_graph}) res)
in (match (uu____3979) with
| (pre_opt, res_t) -> begin
(

let uu____3999 = (encode_term_pred FStar_Pervasives_Native.None res_t env' app)
in (match (uu____3999) with
| (res_pred, decls') -> begin
(

let uu____4010 = (match (pre_opt) with
| FStar_Pervasives_Native.None -> begin
(

let uu____4023 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____4023), ([])))
end
| FStar_Pervasives_Native.Some (pre) -> begin
(

let uu____4027 = (encode_formula pre env')
in (match (uu____4027) with
| (guard, decls0) -> begin
(

let uu____4040 = (FStar_SMTEncoding_Util.mk_and_l ((guard)::guards))
in ((uu____4040), (decls0)))
end))
end)
in (match (uu____4010) with
| (guards1, guard_decls) -> begin
(

let t_interp = (

let uu____4052 = (

let uu____4063 = (FStar_SMTEncoding_Util.mkImp ((guards1), (res_pred)))
in ((((app)::[])::[]), (vars), (uu____4063)))
in (FStar_SMTEncoding_Util.mkForall uu____4052))
in (

let cvars = (

let uu____4081 = (FStar_SMTEncoding_Term.free_variables t_interp)
in (FStar_All.pipe_right uu____4081 (FStar_List.filter (fun uu____4095 -> (match (uu____4095) with
| (x, uu____4101) -> begin
(Prims.op_disEquality x (FStar_Pervasives_Native.fst fsym))
end)))))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((fsym)::cvars), (t_interp)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____4120 = (FStar_Util.smap_try_find env.FStar_SMTEncoding_Env.cache tkey_hash)
in (match (uu____4120) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____4128 = (

let uu____4129 = (

let uu____4136 = (FStar_All.pipe_right cvars (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name), (uu____4136)))
in (FStar_SMTEncoding_Util.mkApp uu____4129))
in ((uu____4128), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append guard_decls (FStar_SMTEncoding_Env.use_cache_entry cache_entry)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let tsym = (

let uu____4156 = (

let uu____4157 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_arrow_" uu____4157))
in (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique uu____4156))
in (

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars)
in (

let caption = (

let uu____4168 = (FStar_Options.log_queries ())
in (match (uu____4168) with
| true -> begin
(

let uu____4171 = (

let uu____4172 = (FStar_TypeChecker_Normalize.term_to_string env.FStar_SMTEncoding_Env.tcenv t0)
in (FStar_Util.replace_char uu____4172 10 32 (* *)))
in FStar_Pervasives_Native.Some (uu____4171))
end
| uu____4175 -> begin
FStar_Pervasives_Native.None
end))
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (caption)))
in (

let t1 = (

let uu____4182 = (

let uu____4189 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars)
in ((tsym), (uu____4189)))
in (FStar_SMTEncoding_Util.mkApp uu____4182))
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in (

let k_assumption = (

let a_name = (Prims.strcat "kinding_" tsym)
in (

let uu____4201 = (

let uu____4208 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars), (t_has_kind)))
in ((uu____4208), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____4201)))
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t1)
in (

let f_has_t_z = (FStar_SMTEncoding_Term.mk_HasTypeZ f t1)
in (

let pre_typing = (

let a_name = (Prims.strcat "pre_typing_" tsym)
in (

let uu____4229 = (

let uu____4236 = (

let uu____4237 = (

let uu____4248 = (

let uu____4249 = (

let uu____4254 = (

let uu____4255 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____4255))
in ((f_has_t), (uu____4254)))
in (FStar_SMTEncoding_Util.mkImp uu____4249))
in ((((f_has_t)::[])::[]), ((fsym)::cvars), (uu____4248)))
in (mkForall_fuel uu____4237))
in ((uu____4236), (FStar_Pervasives_Native.Some ("pre-typing for functions")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____4229)))
in (

let t_interp1 = (

let a_name = (Prims.strcat "interpretation_" tsym)
in (

let uu____4278 = (

let uu____4285 = (

let uu____4286 = (

let uu____4297 = (FStar_SMTEncoding_Util.mkIff ((f_has_t_z), (t_interp)))
in ((((f_has_t_z)::[])::[]), ((fsym)::cvars), (uu____4297)))
in (FStar_SMTEncoding_Util.mkForall uu____4286))
in ((uu____4285), (FStar_Pervasives_Native.Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____4278)))
in (

let t_decls1 = (FStar_List.append ((tdecl)::decls) (FStar_List.append decls' (FStar_List.append guard_decls ((k_assumption)::(pre_typing)::(t_interp1)::[]))))
in ((

let uu____4322 = (FStar_SMTEncoding_Env.mk_cache_entry env tsym cvar_sorts t_decls1)
in (FStar_Util.smap_add env.FStar_SMTEncoding_Env.cache tkey_hash uu____4322));
((t1), (t_decls1));
)))))))))))))
end))))))
end))
end))
end)))))
end))
end
| uu____4325 -> begin
(

let tsym = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh "Non_total_Tm_arrow")
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let t1 = (FStar_SMTEncoding_Util.mkApp ((tsym), ([])))
in (

let t_kinding = (

let a_name = (Prims.strcat "non_total_function_typing_" tsym)
in (

let uu____4337 = (

let uu____4344 = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in ((uu____4344), (FStar_Pervasives_Native.Some ("Typing for non-total arrows")), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____4337)))
in (

let fsym = (("f"), (FStar_SMTEncoding_Term.Term_sort))
in (

let f = (FStar_SMTEncoding_Util.mkFreeV fsym)
in (

let f_has_t = (FStar_SMTEncoding_Term.mk_HasType f t1)
in (

let t_interp = (

let a_name = (Prims.strcat "pre_typing_" tsym)
in (

let uu____4356 = (

let uu____4363 = (

let uu____4364 = (

let uu____4375 = (

let uu____4376 = (

let uu____4381 = (

let uu____4382 = (FStar_SMTEncoding_Term.mk_PreType f)
in (FStar_SMTEncoding_Term.mk_tester "Tm_arrow" uu____4382))
in ((f_has_t), (uu____4381)))
in (FStar_SMTEncoding_Util.mkImp uu____4376))
in ((((f_has_t)::[])::[]), ((fsym)::[]), (uu____4375)))
in (mkForall_fuel uu____4364))
in ((uu____4363), (FStar_Pervasives_Native.Some (a_name)), ((Prims.strcat module_name (Prims.strcat "_" a_name)))))
in (FStar_SMTEncoding_Util.mkAssume uu____4356)))
in ((t1), ((tdecl)::(t_kinding)::(t_interp)::[]))))))))))
end))
end)))
end
| FStar_Syntax_Syntax.Tm_refine (uu____4409) -> begin
(

let uu____4416 = (

let uu____4421 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.FStar_SMTEncoding_Env.tcenv t0)
in (match (uu____4421) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, f); FStar_Syntax_Syntax.pos = uu____4428; FStar_Syntax_Syntax.vars = uu____4429} -> begin
(

let uu____4436 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) f)
in (match (uu____4436) with
| (b, f1) -> begin
(

let uu____4461 = (

let uu____4462 = (FStar_List.hd b)
in (FStar_Pervasives_Native.fst uu____4462))
in ((uu____4461), (f1)))
end))
end
| uu____4471 -> begin
(failwith "impossible")
end))
in (match (uu____4416) with
| (x, f) -> begin
(

let bt = x.FStar_Syntax_Syntax.sort
in (

let uu____4485 = (encode_term x.FStar_Syntax_Syntax.sort env)
in (match (uu____4485) with
| (base_t, decls) -> begin
(

let uu____4496 = (FStar_SMTEncoding_Env.gen_term_var env x)
in (match (uu____4496) with
| (x1, xtm, env') -> begin
(

let uu____4510 = (encode_formula f env')
in (match (uu____4510) with
| (refinement, decls') -> begin
(

let uu____4521 = (FStar_SMTEncoding_Env.fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort)
in (match (uu____4521) with
| (fsym, fterm) -> begin
(

let tm_has_type_with_fuel = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (FStar_Pervasives_Native.Some (fterm)) xtm base_t)
in (

let encoding = (FStar_SMTEncoding_Util.mkAnd ((tm_has_type_with_fuel), (refinement)))
in (

let cvars = (

let uu____4537 = (

let uu____4540 = (FStar_SMTEncoding_Term.free_variables refinement)
in (

let uu____4547 = (FStar_SMTEncoding_Term.free_variables tm_has_type_with_fuel)
in (FStar_List.append uu____4540 uu____4547)))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____4537))
in (

let cvars1 = (FStar_All.pipe_right cvars (FStar_List.filter (fun uu____4580 -> (match (uu____4580) with
| (y, uu____4586) -> begin
((Prims.op_disEquality y x1) && (Prims.op_disEquality y fsym))
end))))
in (

let xfv = ((x1), (FStar_SMTEncoding_Term.Term_sort))
in (

let ffv = ((fsym), (FStar_SMTEncoding_Term.Fuel_sort))
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), ((ffv)::(xfv)::cvars1), (encoding)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____4619 = (FStar_Util.smap_try_find env.FStar_SMTEncoding_Env.cache tkey_hash)
in (match (uu____4619) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____4627 = (

let uu____4628 = (

let uu____4635 = (FStar_All.pipe_right cvars1 (FStar_List.map FStar_SMTEncoding_Util.mkFreeV))
in ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name), (uu____4635)))
in (FStar_SMTEncoding_Util.mkApp uu____4628))
in ((uu____4627), ((FStar_List.append decls (FStar_List.append decls' (FStar_SMTEncoding_Env.use_cache_entry cache_entry))))))
end
| FStar_Pervasives_Native.None -> begin
(

let module_name = env.FStar_SMTEncoding_Env.current_module_name
in (

let tsym = (

let uu____4656 = (

let uu____4657 = (

let uu____4658 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "_Tm_refine_" uu____4658))
in (Prims.strcat module_name uu____4657))
in (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique uu____4656))
in (

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars1)
in (

let tdecl = FStar_SMTEncoding_Term.DeclFun (((tsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let t1 = (

let uu____4672 = (

let uu____4679 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((tsym), (uu____4679)))
in (FStar_SMTEncoding_Util.mkApp uu____4672))
in (

let x_has_base_t = (FStar_SMTEncoding_Term.mk_HasType xtm base_t)
in (

let x_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel (FStar_Pervasives_Native.Some (fterm)) xtm t1)
in (

let t_has_kind = (FStar_SMTEncoding_Term.mk_HasType t1 FStar_SMTEncoding_Term.mk_Term_type)
in (

let t_haseq_base = (FStar_SMTEncoding_Term.mk_haseq base_t)
in (

let t_haseq_ref = (FStar_SMTEncoding_Term.mk_haseq t1)
in (

let t_haseq1 = (

let uu____4694 = (

let uu____4701 = (

let uu____4702 = (

let uu____4713 = (FStar_SMTEncoding_Util.mkIff ((t_haseq_ref), (t_haseq_base)))
in ((((t_haseq_ref)::[])::[]), (cvars1), (uu____4713)))
in (FStar_SMTEncoding_Util.mkForall uu____4702))
in ((uu____4701), (FStar_Pervasives_Native.Some ((Prims.strcat "haseq for " tsym))), ((Prims.strcat "haseq" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____4694))
in (

let t_kinding = (

let uu____4731 = (

let uu____4738 = (FStar_SMTEncoding_Util.mkForall ((((t_has_kind)::[])::[]), (cvars1), (t_has_kind)))
in ((uu____4738), (FStar_Pervasives_Native.Some ("refinement kinding")), ((Prims.strcat "refinement_kinding_" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____4731))
in (

let t_interp = (

let uu____4756 = (

let uu____4763 = (

let uu____4764 = (

let uu____4775 = (FStar_SMTEncoding_Util.mkIff ((x_has_t), (encoding)))
in ((((x_has_t)::[])::[]), ((ffv)::(xfv)::cvars1), (uu____4775)))
in (FStar_SMTEncoding_Util.mkForall uu____4764))
in ((uu____4763), (FStar_Pervasives_Native.Some ("refinement_interpretation")), ((Prims.strcat "refinement_interpretation_" tsym))))
in (FStar_SMTEncoding_Util.mkAssume uu____4756))
in (

let t_decls1 = (

let uu____4803 = (

let uu____4806 = (

let uu____4809 = (

let uu____4812 = (FStar_Syntax_Syntax.is_type bt)
in (match (uu____4812) with
| true -> begin
[]
end
| uu____4815 -> begin
(t_haseq1)::[]
end))
in (FStar_List.append ((tdecl)::(t_kinding)::(t_interp)::[]) uu____4809))
in (FStar_List.append decls' uu____4806))
in (FStar_List.append decls uu____4803))
in ((

let uu____4817 = (FStar_SMTEncoding_Env.mk_cache_entry env tsym cvar_sorts t_decls1)
in (FStar_Util.smap_add env.FStar_SMTEncoding_Env.cache tkey_hash uu____4817));
((t1), (t_decls1));
)))))))))))))))
end))))))))))
end))
end))
end))
end)))
end))
end
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(

let ttm = (

let uu____4847 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_SMTEncoding_Util.mk_Term_uvar uu____4847))
in (

let uu____4848 = (encode_term_pred FStar_Pervasives_Native.None k env ttm)
in (match (uu____4848) with
| (t_has_k, decls) -> begin
(

let d = (

let uu____4860 = (

let uu____4867 = (

let uu____4868 = (

let uu____4869 = (

let uu____4870 = (FStar_Syntax_Unionfind.uvar_id uv)
in (FStar_All.pipe_left FStar_Util.string_of_int uu____4870))
in (FStar_Util.format1 "uvar_typing_%s" uu____4869))
in (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique uu____4868))
in ((t_has_k), (FStar_Pervasives_Native.Some ("Uvar typing")), (uu____4867)))
in (FStar_SMTEncoding_Util.mkAssume uu____4860))
in ((ttm), ((FStar_List.append decls ((d)::[])))))
end)))
end
| FStar_Syntax_Syntax.Tm_app (uu____4875) -> begin
(

let uu____4890 = (FStar_Syntax_Util.head_and_args t0)
in (match (uu____4890) with
| (head1, args_e) -> begin
(

let uu____4931 = (

let uu____4944 = (

let uu____4945 = (FStar_Syntax_Subst.compress head1)
in uu____4945.FStar_Syntax_Syntax.n)
in ((uu____4944), (args_e)))
in (match (uu____4931) with
| uu____4960 when (head_redex env head1) -> begin
(

let uu____4973 = (whnf env t)
in (encode_term uu____4973 env))
end
| uu____4974 when (is_arithmetic_primitive head1 args_e) -> begin
(encode_arith_term env head1 args_e)
end
| uu____4993 when (is_BitVector_primitive head1 args_e) -> begin
(encode_BitVector_term env head1 args_e)
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), uu____5007) when ((not (env.FStar_SMTEncoding_Env.encoding_quantifier)) && ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid))) -> begin
(encode_deeply_embedded_quantifier t0 env)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____5025; FStar_Syntax_Syntax.vars = uu____5026}, uu____5027), uu____5028) when ((not (env.FStar_SMTEncoding_Env.encoding_quantifier)) && ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.forall_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.exists_lid))) -> begin
(encode_deeply_embedded_quantifier t0 env)
end
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____5050; FStar_Syntax_Syntax.vars = uu____5051}, uu____5052), (uu____5053)::((v1, uu____5055))::((v2, uu____5057))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
(

let uu____5108 = (encode_term v1 env)
in (match (uu____5108) with
| (v11, decls1) -> begin
(

let uu____5119 = (encode_term v2 env)
in (match (uu____5119) with
| (v21, decls2) -> begin
(

let uu____5130 = (FStar_SMTEncoding_Util.mk_LexCons v11 v21)
in ((uu____5130), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____5134)::((v1, uu____5136))::((v2, uu____5138))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.lexcons_lid) -> begin
(

let uu____5185 = (encode_term v1 env)
in (match (uu____5185) with
| (v11, decls1) -> begin
(

let uu____5196 = (encode_term v2 env)
in (match (uu____5196) with
| (v21, decls2) -> begin
(

let uu____5207 = (FStar_SMTEncoding_Util.mk_LexCons v11 v21)
in ((uu____5207), ((FStar_List.append decls1 decls2))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range_of), ((arg, uu____5211))::[]) -> begin
(encode_const (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos)) env)
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_set_range_of), ((arg, uu____5237))::((rng, uu____5239))::[]) -> begin
(encode_term arg env)
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify), uu____5274) -> begin
(

let e0 = (

let uu____5292 = (FStar_List.hd args_e)
in (FStar_TypeChecker_Util.reify_body_with_arg env.FStar_SMTEncoding_Env.tcenv head1 uu____5292))
in ((

let uu____5300 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv) (FStar_Options.Other ("SMTEncodingReify")))
in (match (uu____5300) with
| true -> begin
(

let uu____5301 = (FStar_Syntax_Print.term_to_string e0)
in (FStar_Util.print1 "Result of normalization %s\n" uu____5301))
end
| uu____5302 -> begin
()
end));
(

let e = (

let uu____5306 = (

let uu____5311 = (FStar_TypeChecker_Util.remove_reify e0)
in (

let uu____5312 = (FStar_List.tl args_e)
in (FStar_Syntax_Syntax.mk_Tm_app uu____5311 uu____5312)))
in (uu____5306 FStar_Pervasives_Native.None t0.FStar_Syntax_Syntax.pos))
in (encode_term e env));
))
end
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reflect (uu____5321)), ((arg, uu____5323))::[]) -> begin
(encode_term arg env)
end
| uu____5348 -> begin
(

let uu____5361 = (encode_args args_e env)
in (match (uu____5361) with
| (args, decls) -> begin
(

let encode_partial_app = (fun ht_opt -> (

let uu____5418 = (encode_term head1 env)
in (match (uu____5418) with
| (head2, decls') -> begin
(

let app_tm = (mk_Apply_args head2 args)
in (match (ht_opt) with
| FStar_Pervasives_Native.None -> begin
((app_tm), ((FStar_List.append decls decls')))
end
| FStar_Pervasives_Native.Some (formals, c) -> begin
(

let uu____5482 = (FStar_Util.first_N (FStar_List.length args_e) formals)
in (match (uu____5482) with
| (formals1, rest) -> begin
(

let subst1 = (FStar_List.map2 (fun uu____5560 uu____5561 -> (match (((uu____5560), (uu____5561))) with
| ((bv, uu____5583), (a, uu____5585)) -> begin
FStar_Syntax_Syntax.NT (((bv), (a)))
end)) formals1 args_e)
in (

let ty = (

let uu____5603 = (FStar_Syntax_Util.arrow rest c)
in (FStar_All.pipe_right uu____5603 (FStar_Syntax_Subst.subst subst1)))
in (

let uu____5608 = (encode_term_pred FStar_Pervasives_Native.None ty env app_tm)
in (match (uu____5608) with
| (has_type, decls'') -> begin
(

let cvars = (FStar_SMTEncoding_Term.free_variables has_type)
in (

let e_typing = (

let uu____5623 = (

let uu____5630 = (FStar_SMTEncoding_Util.mkForall ((((has_type)::[])::[]), (cvars), (has_type)))
in (

let uu____5639 = (

let uu____5640 = (

let uu____5641 = (

let uu____5642 = (FStar_SMTEncoding_Term.hash_of_term app_tm)
in (FStar_Util.digest_of_string uu____5642))
in (Prims.strcat "partial_app_typing_" uu____5641))
in (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique uu____5640))
in ((uu____5630), (FStar_Pervasives_Native.Some ("Partial app typing")), (uu____5639))))
in (FStar_SMTEncoding_Util.mkAssume uu____5623))
in ((app_tm), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' ((e_typing)::[]))))))))
end))))
end))
end))
end)))
in (

let encode_full_app = (fun fv -> (

let uu____5661 = (FStar_SMTEncoding_Env.lookup_free_var_sym env fv)
in (match (uu____5661) with
| (fname, fuel_args, arity) -> begin
(

let tm = (maybe_curry_app t0.FStar_Syntax_Syntax.pos fname arity (FStar_List.append fuel_args args))
in ((tm), (decls)))
end)))
in (

let head2 = (FStar_Syntax_Subst.compress head1)
in (

let head_type = (match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_name (x); FStar_Syntax_Syntax.pos = uu____5693; FStar_Syntax_Syntax.vars = uu____5694}, uu____5695) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_name (x) -> begin
FStar_Pervasives_Native.Some (x.FStar_Syntax_Syntax.sort)
end
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____5706; FStar_Syntax_Syntax.vars = uu____5707}, uu____5708) -> begin
(

let uu____5713 = (

let uu____5714 = (

let uu____5719 = (FStar_TypeChecker_Env.lookup_lid env.FStar_SMTEncoding_Env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____5719 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____5714 FStar_Pervasives_Native.snd))
in FStar_Pervasives_Native.Some (uu____5713))
end
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(

let uu____5749 = (

let uu____5750 = (

let uu____5755 = (FStar_TypeChecker_Env.lookup_lid env.FStar_SMTEncoding_Env.tcenv fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (FStar_All.pipe_right uu____5755 FStar_Pervasives_Native.fst))
in (FStar_All.pipe_right uu____5750 FStar_Pervasives_Native.snd))
in FStar_Pervasives_Native.Some (uu____5749))
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____5784, (FStar_Util.Inl (t1), uu____5786), uu____5787) -> begin
FStar_Pervasives_Native.Some (t1)
end
| FStar_Syntax_Syntax.Tm_ascribed (uu____5836, (FStar_Util.Inr (c), uu____5838), uu____5839) -> begin
FStar_Pervasives_Native.Some ((FStar_Syntax_Util.comp_result c))
end
| uu____5888 -> begin
FStar_Pervasives_Native.None
end)
in (match (head_type) with
| FStar_Pervasives_Native.None -> begin
(encode_partial_app FStar_Pervasives_Native.None)
end
| FStar_Pervasives_Native.Some (head_type1) -> begin
(

let head_type2 = (

let uu____5915 = (FStar_TypeChecker_Normalize.normalize_refinement ((FStar_TypeChecker_Normalize.Weak)::(FStar_TypeChecker_Normalize.HNF)::(FStar_TypeChecker_Normalize.EraseUniverses)::[]) env.FStar_SMTEncoding_Env.tcenv head_type1)
in (FStar_All.pipe_left FStar_Syntax_Util.unrefine uu____5915))
in (

let uu____5916 = (curried_arrow_formals_comp head_type2)
in (match (uu____5916) with
| (formals, c) -> begin
(match (head2.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (fv); FStar_Syntax_Syntax.pos = uu____5932; FStar_Syntax_Syntax.vars = uu____5933}, uu____5934) when (Prims.op_Equality (FStar_List.length formals) (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| FStar_Syntax_Syntax.Tm_fvar (fv) when (Prims.op_Equality (FStar_List.length formals) (FStar_List.length args)) -> begin
(encode_full_app fv.FStar_Syntax_Syntax.fv_name)
end
| uu____5948 -> begin
(match (((FStar_List.length formals) > (FStar_List.length args))) with
| true -> begin
(encode_partial_app (FStar_Pervasives_Native.Some (((formals), (c)))))
end
| uu____5961 -> begin
(encode_partial_app FStar_Pervasives_Native.None)
end)
end)
end)))
end)))))
end))
end))
end))
end
| FStar_Syntax_Syntax.Tm_abs (bs, body, lopt) -> begin
(

let uu____5997 = (FStar_Syntax_Subst.open_term' bs body)
in (match (uu____5997) with
| (bs1, body1, opening) -> begin
(

let fallback = (fun uu____6022 -> (

let f = (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.fresh "Tm_abs")
in (

let decl = FStar_SMTEncoding_Term.DeclFun (((f), ([]), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.Some ("Imprecise function encoding"))))
in (

let uu____6029 = (FStar_SMTEncoding_Util.mkFreeV ((f), (FStar_SMTEncoding_Term.Term_sort)))
in ((uu____6029), ((decl)::[]))))))
in (

let is_impure = (fun rc -> (

let uu____6038 = (FStar_TypeChecker_Util.is_pure_or_ghost_effect env.FStar_SMTEncoding_Env.tcenv rc.FStar_Syntax_Syntax.residual_effect)
in (FStar_All.pipe_right uu____6038 Prims.op_Negation)))
in (

let codomain_eff = (fun rc -> (

let res_typ = (match (rc.FStar_Syntax_Syntax.residual_typ) with
| FStar_Pervasives_Native.None -> begin
(

let uu____6050 = (FStar_TypeChecker_Rel.new_uvar FStar_Range.dummyRange [] FStar_Syntax_Util.ktype0)
in (FStar_All.pipe_right uu____6050 FStar_Pervasives_Native.fst))
end
| FStar_Pervasives_Native.Some (t1) -> begin
t1
end)
in (

let uu____6068 = (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_Tot_lid)
in (match (uu____6068) with
| true -> begin
(

let uu____6071 = (FStar_Syntax_Syntax.mk_Total res_typ)
in FStar_Pervasives_Native.Some (uu____6071))
end
| uu____6072 -> begin
(

let uu____6073 = (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect FStar_Parser_Const.effect_GTot_lid)
in (match (uu____6073) with
| true -> begin
(

let uu____6076 = (FStar_Syntax_Syntax.mk_GTotal res_typ)
in FStar_Pervasives_Native.Some (uu____6076))
end
| uu____6077 -> begin
FStar_Pervasives_Native.None
end))
end))))
in (match (lopt) with
| FStar_Pervasives_Native.None -> begin
((

let uu____6083 = (

let uu____6088 = (

let uu____6089 = (FStar_Syntax_Print.term_to_string t0)
in (FStar_Util.format1 "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)" uu____6089))
in ((FStar_Errors.Warning_FunctionLiteralPrecisionLoss), (uu____6088)))
in (FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos uu____6083));
(fallback ());
)
end
| FStar_Pervasives_Native.Some (rc) -> begin
(

let uu____6091 = ((is_impure rc) && (

let uu____6093 = (FStar_TypeChecker_Env.is_reifiable env.FStar_SMTEncoding_Env.tcenv rc)
in (not (uu____6093))))
in (match (uu____6091) with
| true -> begin
(fallback ())
end
| uu____6098 -> begin
(

let cache_size = (FStar_Util.smap_size env.FStar_SMTEncoding_Env.cache)
in (

let uu____6100 = (encode_binders FStar_Pervasives_Native.None bs1 env)
in (match (uu____6100) with
| (vars, guards, envbody, decls, uu____6125) -> begin
(

let body2 = (

let uu____6139 = (FStar_TypeChecker_Env.is_reifiable env.FStar_SMTEncoding_Env.tcenv rc)
in (match (uu____6139) with
| true -> begin
(FStar_TypeChecker_Util.reify_body env.FStar_SMTEncoding_Env.tcenv body1)
end
| uu____6140 -> begin
body1
end))
in (

let uu____6141 = (encode_term body2 envbody)
in (match (uu____6141) with
| (body3, decls') -> begin
(

let uu____6152 = (

let uu____6161 = (codomain_eff rc)
in (match (uu____6161) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), ([]))
end
| FStar_Pervasives_Native.Some (c) -> begin
(

let tfun = (FStar_Syntax_Util.arrow bs1 c)
in (

let uu____6180 = (encode_term tfun env)
in (match (uu____6180) with
| (t1, decls1) -> begin
((FStar_Pervasives_Native.Some (t1)), (decls1))
end)))
end))
in (match (uu____6152) with
| (arrow_t_opt, decls'') -> begin
(

let key_body = (

let uu____6212 = (

let uu____6223 = (

let uu____6224 = (

let uu____6229 = (FStar_SMTEncoding_Util.mk_and_l guards)
in ((uu____6229), (body3)))
in (FStar_SMTEncoding_Util.mkImp uu____6224))
in (([]), (vars), (uu____6223)))
in (FStar_SMTEncoding_Util.mkForall uu____6212))
in (

let cvars = (FStar_SMTEncoding_Term.free_variables key_body)
in (

let cvars1 = (match (arrow_t_opt) with
| FStar_Pervasives_Native.None -> begin
cvars
end
| FStar_Pervasives_Native.Some (t1) -> begin
(

let uu____6241 = (

let uu____6244 = (FStar_SMTEncoding_Term.free_variables t1)
in (FStar_List.append uu____6244 cvars))
in (FStar_Util.remove_dups FStar_SMTEncoding_Term.fv_eq uu____6241))
end)
in (

let tkey = (FStar_SMTEncoding_Util.mkForall (([]), (cvars1), (key_body)))
in (

let tkey_hash = (FStar_SMTEncoding_Term.hash_of_term tkey)
in (

let uu____6263 = (FStar_Util.smap_try_find env.FStar_SMTEncoding_Env.cache tkey_hash)
in (match (uu____6263) with
| FStar_Pervasives_Native.Some (cache_entry) -> begin
(

let uu____6271 = (

let uu____6272 = (

let uu____6279 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((cache_entry.FStar_SMTEncoding_Env.cache_symbol_name), (uu____6279)))
in (FStar_SMTEncoding_Util.mkApp uu____6272))
in ((uu____6271), ((FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' (FStar_SMTEncoding_Env.use_cache_entry cache_entry)))))))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____6290 = (is_an_eta_expansion env vars body3)
in (match (uu____6290) with
| FStar_Pervasives_Native.Some (t1) -> begin
(

let decls1 = (

let uu____6301 = (

let uu____6302 = (FStar_Util.smap_size env.FStar_SMTEncoding_Env.cache)
in (Prims.op_Equality uu____6302 cache_size))
in (match (uu____6301) with
| true -> begin
[]
end
| uu____6305 -> begin
(FStar_List.append decls (FStar_List.append decls' decls''))
end))
in ((t1), (decls1)))
end
| FStar_Pervasives_Native.None -> begin
(

let cvar_sorts = (FStar_List.map FStar_Pervasives_Native.snd cvars1)
in (

let fsym = (

let module_name = env.FStar_SMTEncoding_Env.current_module_name
in (

let fsym = (

let uu____6318 = (

let uu____6319 = (FStar_Util.digest_of_string tkey_hash)
in (Prims.strcat "Tm_abs_" uu____6319))
in (FStar_SMTEncoding_Env.varops.FStar_SMTEncoding_Env.mk_unique uu____6318))
in (Prims.strcat module_name (Prims.strcat "_" fsym))))
in (

let fdecl = FStar_SMTEncoding_Term.DeclFun (((fsym), (cvar_sorts), (FStar_SMTEncoding_Term.Term_sort), (FStar_Pervasives_Native.None)))
in (

let f = (

let uu____6326 = (

let uu____6333 = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV cvars1)
in ((fsym), (uu____6333)))
in (FStar_SMTEncoding_Util.mkApp uu____6326))
in (

let app = (mk_Apply f vars)
in (

let typing_f = (match (arrow_t_opt) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (t1) -> begin
(

let f_has_t = (FStar_SMTEncoding_Term.mk_HasTypeWithFuel FStar_Pervasives_Native.None f t1)
in (

let a_name = (Prims.strcat "typing_" fsym)
in (

let uu____6351 = (

let uu____6352 = (

let uu____6359 = (FStar_SMTEncoding_Util.mkForall ((((f)::[])::[]), (cvars1), (f_has_t)))
in ((uu____6359), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____6352))
in (uu____6351)::[])))
end)
in (

let interp_f = (

let a_name = (Prims.strcat "interpretation_" fsym)
in (

let uu____6372 = (

let uu____6379 = (

let uu____6380 = (

let uu____6391 = (FStar_SMTEncoding_Util.mkEq ((app), (body3)))
in ((((app)::[])::[]), ((FStar_List.append vars cvars1)), (uu____6391)))
in (FStar_SMTEncoding_Util.mkForall uu____6380))
in ((uu____6379), (FStar_Pervasives_Native.Some (a_name)), (a_name)))
in (FStar_SMTEncoding_Util.mkAssume uu____6372)))
in (

let f_decls = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' (FStar_List.append ((fdecl)::typing_f) ((interp_f)::[])))))
in ((

let uu____6408 = (FStar_SMTEncoding_Env.mk_cache_entry env fsym cvar_sorts f_decls)
in (FStar_Util.smap_add env.FStar_SMTEncoding_Env.cache tkey_hash uu____6408));
((f), (f_decls));
)))))))))
end))
end)))))))
end))
end)))
end)))
end))
end))))
end))
end
| FStar_Syntax_Syntax.Tm_let ((uu____6411, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inr (uu____6412); FStar_Syntax_Syntax.lbunivs = uu____6413; FStar_Syntax_Syntax.lbtyp = uu____6414; FStar_Syntax_Syntax.lbeff = uu____6415; FStar_Syntax_Syntax.lbdef = uu____6416; FStar_Syntax_Syntax.lbattrs = uu____6417; FStar_Syntax_Syntax.lbpos = uu____6418})::uu____6419), uu____6420) -> begin
(failwith "Impossible: already handled by encoding of Sig_let")
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____6450; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____6452; FStar_Syntax_Syntax.lbdef = e1; FStar_Syntax_Syntax.lbattrs = uu____6454; FStar_Syntax_Syntax.lbpos = uu____6455})::[]), e2) -> begin
(encode_let x t1 e1 e2 env encode_term)
end
| FStar_Syntax_Syntax.Tm_let (uu____6479) -> begin
((FStar_Errors.diag t0.FStar_Syntax_Syntax.pos "Non-top-level recursive functions, and their enclosings let bindings (including the top-level let) are not yet fully encoded to the SMT solver; you may not be able to prove some facts");
(FStar_Exn.raise FStar_SMTEncoding_Env.Inner_let_rec);
)
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env encode_term)
end);
)))
and encode_let : FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  FStar_SMTEncoding_Env.env_t  ->  (FStar_Syntax_Syntax.term  ->  FStar_SMTEncoding_Env.env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun x t1 e1 e2 env encode_body -> (

let uu____6549 = (

let uu____6554 = (FStar_Syntax_Util.ascribe e1 ((FStar_Util.Inl (t1)), (FStar_Pervasives_Native.None)))
in (encode_term uu____6554 env))
in (match (uu____6549) with
| (ee1, decls1) -> begin
(

let uu____6575 = (FStar_Syntax_Subst.open_term ((((x), (FStar_Pervasives_Native.None)))::[]) e2)
in (match (uu____6575) with
| (xs, e21) -> begin
(

let uu____6600 = (FStar_List.hd xs)
in (match (uu____6600) with
| (x1, uu____6614) -> begin
(

let env' = (FStar_SMTEncoding_Env.push_term_var env x1 ee1)
in (

let uu____6616 = (encode_body e21 env')
in (match (uu____6616) with
| (ee2, decls2) -> begin
((ee2), ((FStar_List.append decls1 decls2)))
end)))
end))
end))
end)))
and encode_match : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.branch Prims.list  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Env.env_t  ->  (FStar_Syntax_Syntax.term  ->  FStar_SMTEncoding_Env.env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun e pats default_case env encode_br -> (

let uu____6648 = (

let uu____6655 = (

let uu____6656 = (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown FStar_Pervasives_Native.None FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.null_bv uu____6656))
in (FStar_SMTEncoding_Env.gen_term_var env uu____6655))
in (match (uu____6648) with
| (scrsym, scr', env1) -> begin
(

let uu____6664 = (encode_term e env1)
in (match (uu____6664) with
| (scr, decls) -> begin
(

let uu____6675 = (

let encode_branch = (fun b uu____6704 -> (match (uu____6704) with
| (else_case, decls1) -> begin
(

let uu____6723 = (FStar_Syntax_Subst.open_branch b)
in (match (uu____6723) with
| (p, w, br) -> begin
(

let uu____6749 = (encode_pat env1 p)
in (match (uu____6749) with
| (env0, pattern) -> begin
(

let guard = (pattern.guard scr')
in (

let projections = (pattern.projections scr')
in (

let env2 = (FStar_All.pipe_right projections (FStar_List.fold_left (fun env2 uu____6786 -> (match (uu____6786) with
| (x, t) -> begin
(FStar_SMTEncoding_Env.push_term_var env2 x t)
end)) env1))
in (

let uu____6793 = (match (w) with
| FStar_Pervasives_Native.None -> begin
((guard), ([]))
end
| FStar_Pervasives_Native.Some (w1) -> begin
(

let uu____6815 = (encode_term w1 env2)
in (match (uu____6815) with
| (w2, decls2) -> begin
(

let uu____6828 = (

let uu____6829 = (

let uu____6834 = (

let uu____6835 = (

let uu____6840 = (FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue)
in ((w2), (uu____6840)))
in (FStar_SMTEncoding_Util.mkEq uu____6835))
in ((guard), (uu____6834)))
in (FStar_SMTEncoding_Util.mkAnd uu____6829))
in ((uu____6828), (decls2)))
end))
end)
in (match (uu____6793) with
| (guard1, decls2) -> begin
(

let uu____6853 = (encode_br br env2)
in (match (uu____6853) with
| (br1, decls3) -> begin
(

let uu____6866 = (FStar_SMTEncoding_Util.mkITE ((guard1), (br1), (else_case)))
in ((uu____6866), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end)))))
end))
end))
end))
in (FStar_List.fold_right encode_branch pats ((default_case), (decls))))
in (match (uu____6675) with
| (match_tm, decls1) -> begin
(

let uu____6885 = (FStar_SMTEncoding_Term.mkLet' (((((((scrsym), (FStar_SMTEncoding_Term.Term_sort))), (scr)))::[]), (match_tm)) FStar_Range.dummyRange)
in ((uu____6885), (decls1)))
end))
end))
end)))
and encode_pat : FStar_SMTEncoding_Env.env_t  ->  FStar_Syntax_Syntax.pat  ->  (FStar_SMTEncoding_Env.env_t * pattern) = (fun env pat -> ((

let uu____6925 = (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv FStar_Options.Low)
in (match (uu____6925) with
| true -> begin
(

let uu____6926 = (FStar_Syntax_Print.pat_to_string pat)
in (FStar_Util.print1 "Encoding pattern %s\n" uu____6926))
end
| uu____6927 -> begin
()
end));
(

let uu____6928 = (FStar_TypeChecker_Util.decorated_pattern_as_term pat)
in (match (uu____6928) with
| (vars, pat_term) -> begin
(

let uu____6945 = (FStar_All.pipe_right vars (FStar_List.fold_left (fun uu____6998 v1 -> (match (uu____6998) with
| (env1, vars1) -> begin
(

let uu____7050 = (FStar_SMTEncoding_Env.gen_term_var env1 v1)
in (match (uu____7050) with
| (xx, uu____7072, env2) -> begin
((env2), ((((v1), (((xx), (FStar_SMTEncoding_Term.Term_sort)))))::vars1))
end))
end)) ((env), ([]))))
in (match (uu____6945) with
| (env1, vars1) -> begin
(

let rec mk_guard = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_var (uu____7155) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_wild (uu____7156) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_dot_term (uu____7157) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| FStar_Syntax_Syntax.Pat_constant (c) -> begin
(

let uu____7165 = (encode_const c env1)
in (match (uu____7165) with
| (tm, decls) -> begin
((match (decls) with
| (uu____7179)::uu____7180 -> begin
(failwith "Unexpected encoding of constant pattern")
end
| uu____7183 -> begin
()
end);
(FStar_SMTEncoding_Util.mkEq ((scrutinee), (tm)));
)
end))
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let is_f = (

let tc_name = (FStar_TypeChecker_Env.typ_of_datacon env1.FStar_SMTEncoding_Env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v)
in (

let uu____7206 = (FStar_TypeChecker_Env.datacons_of_typ env1.FStar_SMTEncoding_Env.tcenv tc_name)
in (match (uu____7206) with
| (uu____7213, (uu____7214)::[]) -> begin
FStar_SMTEncoding_Util.mkTrue
end
| uu____7217 -> begin
(FStar_SMTEncoding_Env.mk_data_tester env1 f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v scrutinee)
end)))
in (

let sub_term_guards = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____7250 -> (match (uu____7250) with
| (arg, uu____7258) -> begin
(

let proj = (FStar_SMTEncoding_Env.primitive_projector_by_pos env1.FStar_SMTEncoding_Env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____7264 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_guard arg uu____7264)))
end))))
in (FStar_SMTEncoding_Util.mk_and_l ((is_f)::sub_term_guards))))
end))
in (

let rec mk_projections = (fun pat1 scrutinee -> (match (pat1.FStar_Syntax_Syntax.v) with
| FStar_Syntax_Syntax.Pat_dot_term (x, uu____7295) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_var (x) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_wild (x) -> begin
(((x), (scrutinee)))::[]
end
| FStar_Syntax_Syntax.Pat_constant (uu____7326) -> begin
[]
end
| FStar_Syntax_Syntax.Pat_cons (f, args) -> begin
(

let uu____7349 = (FStar_All.pipe_right args (FStar_List.mapi (fun i uu____7393 -> (match (uu____7393) with
| (arg, uu____7407) -> begin
(

let proj = (FStar_SMTEncoding_Env.primitive_projector_by_pos env1.FStar_SMTEncoding_Env.tcenv f.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v i)
in (

let uu____7413 = (FStar_SMTEncoding_Util.mkApp ((proj), ((scrutinee)::[])))
in (mk_projections arg uu____7413)))
end))))
in (FStar_All.pipe_right uu____7349 FStar_List.flatten))
end))
in (

let pat_term1 = (fun uu____7443 -> (encode_term pat_term env1))
in (

let pattern = {pat_vars = vars1; pat_term = pat_term1; guard = (mk_guard pat); projections = (mk_projections pat)}
in ((env1), (pattern))))))
end))
end));
))
and encode_args : FStar_Syntax_Syntax.args  ->  FStar_SMTEncoding_Env.env_t  ->  (FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.decls_t) = (fun l env -> (

let uu____7453 = (FStar_All.pipe_right l (FStar_List.fold_left (fun uu____7491 uu____7492 -> (match (((uu____7491), (uu____7492))) with
| ((tms, decls), (t, uu____7528)) -> begin
(

let uu____7549 = (encode_term t env)
in (match (uu____7549) with
| (t1, decls') -> begin
(((t1)::tms), ((FStar_List.append decls decls')))
end))
end)) (([]), ([]))))
in (match (uu____7453) with
| (l1, decls) -> begin
(((FStar_List.rev l1)), (decls))
end)))
and encode_function_type_as_formula : FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Env.env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun t env -> (

let list_elements1 = (fun e -> (

let uu____7608 = (FStar_Syntax_Util.list_elements e)
in (match (uu____7608) with
| FStar_Pervasives_Native.Some (l) -> begin
l
end
| FStar_Pervasives_Native.None -> begin
((FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos ((FStar_Errors.Warning_NonListLiteralSMTPattern), ("SMT pattern is not a list literal; ignoring the pattern")));
[];
)
end)))
in (

let one_pat = (fun p -> (

let uu____7635 = (

let uu____7650 = (FStar_Syntax_Util.unmeta p)
in (FStar_All.pipe_right uu____7650 FStar_Syntax_Util.head_and_args))
in (match (uu____7635) with
| (head1, args) -> begin
(

let uu____7693 = (

let uu____7706 = (

let uu____7707 = (FStar_Syntax_Util.un_uinst head1)
in uu____7707.FStar_Syntax_Syntax.n)
in ((uu____7706), (args)))
in (match (uu____7693) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((uu____7725, uu____7726))::(arg)::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpat_lid) -> begin
arg
end
| uu____7764 -> begin
(failwith "Unexpected pattern term")
end))
end)))
in (

let lemma_pats = (fun p -> (

let elts = (list_elements1 p)
in (

let smt_pat_or = (fun t1 -> (

let uu____7812 = (

let uu____7827 = (FStar_Syntax_Util.unmeta t1)
in (FStar_All.pipe_right uu____7827 FStar_Syntax_Util.head_and_args))
in (match (uu____7812) with
| (head1, args) -> begin
(

let uu____7868 = (

let uu____7881 = (

let uu____7882 = (FStar_Syntax_Util.un_uinst head1)
in uu____7882.FStar_Syntax_Syntax.n)
in ((uu____7881), (args)))
in (match (uu____7868) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((e, uu____7899))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.smtpatOr_lid) -> begin
FStar_Pervasives_Native.Some (e)
end
| uu____7926 -> begin
FStar_Pervasives_Native.None
end))
end)))
in (match (elts) with
| (t1)::[] -> begin
(

let uu____7952 = (smt_pat_or t1)
in (match (uu____7952) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____7972 = (list_elements1 e)
in (FStar_All.pipe_right uu____7972 (FStar_List.map (fun branch1 -> (

let uu____7998 = (list_elements1 branch1)
in (FStar_All.pipe_right uu____7998 (FStar_List.map one_pat)))))))
end
| uu____8017 -> begin
(

let uu____8022 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____8022)::[])
end))
end
| uu____8063 -> begin
(

let uu____8066 = (FStar_All.pipe_right elts (FStar_List.map one_pat))
in (uu____8066)::[])
end))))
in (

let uu____8107 = (

let uu____8130 = (

let uu____8131 = (FStar_Syntax_Subst.compress t)
in uu____8131.FStar_Syntax_Syntax.n)
in (match (uu____8130) with
| FStar_Syntax_Syntax.Tm_arrow (binders, c) -> begin
(

let uu____8174 = (FStar_Syntax_Subst.open_comp binders c)
in (match (uu____8174) with
| (binders1, c1) -> begin
(match (c1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp ({FStar_Syntax_Syntax.comp_univs = uu____8225; FStar_Syntax_Syntax.effect_name = uu____8226; FStar_Syntax_Syntax.result_typ = uu____8227; FStar_Syntax_Syntax.effect_args = ((pre, uu____8229))::((post, uu____8231))::((pats, uu____8233))::[]; FStar_Syntax_Syntax.flags = uu____8234}) -> begin
(

let uu____8275 = (lemma_pats pats)
in ((binders1), (pre), (post), (uu____8275)))
end
| uu____8300 -> begin
(failwith "impos")
end)
end))
end
| uu____8323 -> begin
(failwith "Impos")
end))
in (match (uu____8107) with
| (binders, pre, post, patterns) -> begin
(

let env1 = (

let uu___76_8383 = env
in {FStar_SMTEncoding_Env.bvar_bindings = uu___76_8383.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___76_8383.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___76_8383.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = uu___76_8383.FStar_SMTEncoding_Env.tcenv; FStar_SMTEncoding_Env.warn = uu___76_8383.FStar_SMTEncoding_Env.warn; FStar_SMTEncoding_Env.cache = uu___76_8383.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = uu___76_8383.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = true; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___76_8383.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___76_8383.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = uu___76_8383.FStar_SMTEncoding_Env.encoding_quantifier})
in (

let uu____8384 = (encode_binders FStar_Pervasives_Native.None binders env1)
in (match (uu____8384) with
| (vars, guards, env2, decls, uu____8409) -> begin
(

let uu____8422 = (encode_smt_patterns patterns env2)
in (match (uu____8422) with
| (pats, decls') -> begin
(

let post1 = (FStar_Syntax_Util.unthunk_lemma_post post)
in (

let env3 = (

let uu___77_8455 = env2
in {FStar_SMTEncoding_Env.bvar_bindings = uu___77_8455.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___77_8455.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___77_8455.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = uu___77_8455.FStar_SMTEncoding_Env.tcenv; FStar_SMTEncoding_Env.warn = uu___77_8455.FStar_SMTEncoding_Env.warn; FStar_SMTEncoding_Env.cache = uu___77_8455.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = true; FStar_SMTEncoding_Env.use_zfuel_name = uu___77_8455.FStar_SMTEncoding_Env.use_zfuel_name; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___77_8455.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___77_8455.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = uu___77_8455.FStar_SMTEncoding_Env.encoding_quantifier})
in (

let uu____8456 = (

let uu____8461 = (FStar_Syntax_Util.unmeta pre)
in (encode_formula uu____8461 env3))
in (match (uu____8456) with
| (pre1, decls'') -> begin
(

let uu____8468 = (

let uu____8473 = (FStar_Syntax_Util.unmeta post1)
in (encode_formula uu____8473 env3))
in (match (uu____8468) with
| (post2, decls''') -> begin
(

let decls1 = (FStar_List.append decls (FStar_List.append decls' (FStar_List.append decls'' decls''')))
in (

let uu____8483 = (

let uu____8484 = (

let uu____8495 = (

let uu____8496 = (

let uu____8501 = (FStar_SMTEncoding_Util.mk_and_l ((pre1)::guards))
in ((uu____8501), (post2)))
in (FStar_SMTEncoding_Util.mkImp uu____8496))
in ((pats), (vars), (uu____8495)))
in (FStar_SMTEncoding_Util.mkForall uu____8484))
in ((uu____8483), (decls1))))
end))
end))))
end))
end)))
end))))))
and encode_smt_patterns : FStar_Syntax_Syntax.arg Prims.list Prims.list  ->  FStar_SMTEncoding_Env.env_t  ->  (FStar_SMTEncoding_Term.term Prims.list Prims.list * FStar_SMTEncoding_Term.decl Prims.list) = (fun pats_l env -> (

let env1 = (

let uu___78_8527 = env
in {FStar_SMTEncoding_Env.bvar_bindings = uu___78_8527.FStar_SMTEncoding_Env.bvar_bindings; FStar_SMTEncoding_Env.fvar_bindings = uu___78_8527.FStar_SMTEncoding_Env.fvar_bindings; FStar_SMTEncoding_Env.depth = uu___78_8527.FStar_SMTEncoding_Env.depth; FStar_SMTEncoding_Env.tcenv = uu___78_8527.FStar_SMTEncoding_Env.tcenv; FStar_SMTEncoding_Env.warn = uu___78_8527.FStar_SMTEncoding_Env.warn; FStar_SMTEncoding_Env.cache = uu___78_8527.FStar_SMTEncoding_Env.cache; FStar_SMTEncoding_Env.nolabels = uu___78_8527.FStar_SMTEncoding_Env.nolabels; FStar_SMTEncoding_Env.use_zfuel_name = true; FStar_SMTEncoding_Env.encode_non_total_function_typ = uu___78_8527.FStar_SMTEncoding_Env.encode_non_total_function_typ; FStar_SMTEncoding_Env.current_module_name = uu___78_8527.FStar_SMTEncoding_Env.current_module_name; FStar_SMTEncoding_Env.encoding_quantifier = uu___78_8527.FStar_SMTEncoding_Env.encoding_quantifier})
in (

let encode_smt_pattern = (fun t -> (

let uu____8540 = (FStar_Syntax_Util.head_and_args t)
in (match (uu____8540) with
| (head1, args) -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (((head2.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____8599)::((x, uu____8601))::((t1, uu____8603))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.has_type_lid) -> begin
(

let uu____8650 = (encode_term x env1)
in (match (uu____8650) with
| (x1, decls) -> begin
(

let uu____8663 = (encode_term t1 env1)
in (match (uu____8663) with
| (t2, decls') -> begin
(

let uu____8676 = (FStar_SMTEncoding_Term.mk_HasType x1 t2)
in ((uu____8676), ((FStar_List.append decls decls'))))
end))
end))
end
| uu____8679 -> begin
(encode_term t env1)
end))
end)))
in (FStar_List.fold_right (fun pats uu____8716 -> (match (uu____8716) with
| (pats_l1, decls) -> begin
(

let uu____8757 = (FStar_List.fold_right (fun uu____8787 uu____8788 -> (match (((uu____8787), (uu____8788))) with
| ((p, uu____8822), (pats1, decls1)) -> begin
(

let uu____8845 = (encode_smt_pattern p)
in (match (uu____8845) with
| (t, d) -> begin
(((t)::pats1), ((FStar_List.append d decls1)))
end))
end)) pats (([]), (decls)))
in (match (uu____8757) with
| (pats1, decls1) -> begin
(((pats1)::pats_l1), (decls1))
end))
end)) pats_l (([]), ([]))))))
and encode_formula : FStar_Syntax_Syntax.typ  ->  FStar_SMTEncoding_Env.env_t  ->  (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t) = (fun phi env -> (

let debug1 = (fun phi1 -> (

let uu____8922 = (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.FStar_SMTEncoding_Env.tcenv) (FStar_Options.Other ("SMTEncoding")))
in (match (uu____8922) with
| true -> begin
(

let uu____8923 = (FStar_Syntax_Print.tag_of_term phi1)
in (

let uu____8924 = (FStar_Syntax_Print.term_to_string phi1)
in (FStar_Util.print2 "Formula (%s)  %s\n" uu____8923 uu____8924)))
end
| uu____8925 -> begin
()
end)))
in (

let enc = (fun f r l -> (

let uu____8963 = (FStar_Util.fold_map (fun decls x -> (

let uu____8991 = (encode_term (FStar_Pervasives_Native.fst x) env)
in (match (uu____8991) with
| (t, decls') -> begin
(((FStar_List.append decls decls')), (t))
end))) [] l)
in (match (uu____8963) with
| (decls, args) -> begin
(

let uu____9020 = (

let uu___79_9021 = (f args)
in {FStar_SMTEncoding_Term.tm = uu___79_9021.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___79_9021.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____9020), (decls)))
end)))
in (

let const_op = (fun f r uu____9058 -> (

let uu____9071 = (f r)
in ((uu____9071), ([]))))
in (

let un_op = (fun f l -> (

let uu____9094 = (FStar_List.hd l)
in (FStar_All.pipe_left f uu____9094)))
in (

let bin_op = (fun f uu___70_9114 -> (match (uu___70_9114) with
| (t1)::(t2)::[] -> begin
(f ((t1), (t2)))
end
| uu____9125 -> begin
(failwith "Impossible")
end))
in (

let enc_prop_c = (fun f r l -> (

let uu____9165 = (FStar_Util.fold_map (fun decls uu____9188 -> (match (uu____9188) with
| (t, uu____9202) -> begin
(

let uu____9203 = (encode_formula t env)
in (match (uu____9203) with
| (phi1, decls') -> begin
(((FStar_List.append decls decls')), (phi1))
end))
end)) [] l)
in (match (uu____9165) with
| (decls, phis) -> begin
(

let uu____9232 = (

let uu___80_9233 = (f phis)
in {FStar_SMTEncoding_Term.tm = uu___80_9233.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___80_9233.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = r})
in ((uu____9232), (decls)))
end)))
in (

let eq_op = (fun r args -> (

let rf = (FStar_List.filter (fun uu____9298 -> (match (uu____9298) with
| (a, q) -> begin
(match (q) with
| FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Implicit (uu____9317)) -> begin
false
end
| uu____9318 -> begin
true
end)
end)) args)
in (match ((Prims.op_disEquality (FStar_List.length rf) (Prims.parse_int "2"))) with
| true -> begin
(

let uu____9333 = (FStar_Util.format1 "eq_op: got %s non-implicit arguments instead of 2?" (Prims.string_of_int (FStar_List.length rf)))
in (failwith uu____9333))
end
| uu____9346 -> begin
(

let uu____9347 = (enc (bin_op FStar_SMTEncoding_Util.mkEq))
in (uu____9347 r rf))
end)))
in (

let mk_imp1 = (fun r uu___71_9382 -> (match (uu___71_9382) with
| ((lhs, uu____9388))::((rhs, uu____9390))::[] -> begin
(

let uu____9417 = (encode_formula rhs env)
in (match (uu____9417) with
| (l1, decls1) -> begin
(match (l1.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu____9432) -> begin
((l1), (decls1))
end
| uu____9437 -> begin
(

let uu____9438 = (encode_formula lhs env)
in (match (uu____9438) with
| (l2, decls2) -> begin
(

let uu____9449 = (FStar_SMTEncoding_Term.mkImp ((l2), (l1)) r)
in ((uu____9449), ((FStar_List.append decls1 decls2))))
end))
end)
end))
end
| uu____9452 -> begin
(failwith "impossible")
end))
in (

let mk_ite = (fun r uu___72_9479 -> (match (uu___72_9479) with
| ((guard, uu____9485))::((_then, uu____9487))::((_else, uu____9489))::[] -> begin
(

let uu____9526 = (encode_formula guard env)
in (match (uu____9526) with
| (g, decls1) -> begin
(

let uu____9537 = (encode_formula _then env)
in (match (uu____9537) with
| (t, decls2) -> begin
(

let uu____9548 = (encode_formula _else env)
in (match (uu____9548) with
| (e, decls3) -> begin
(

let res = (FStar_SMTEncoding_Term.mkITE ((g), (t), (e)) r)
in ((res), ((FStar_List.append decls1 (FStar_List.append decls2 decls3)))))
end))
end))
end))
end
| uu____9562 -> begin
(failwith "impossible")
end))
in (

let unboxInt_l = (fun f l -> (

let uu____9591 = (FStar_List.map FStar_SMTEncoding_Term.unboxInt l)
in (f uu____9591)))
in (

let connectives = (

let uu____9611 = (

let uu____9626 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd))
in ((FStar_Parser_Const.and_lid), (uu____9626)))
in (

let uu____9649 = (

let uu____9666 = (

let uu____9681 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr))
in ((FStar_Parser_Const.or_lid), (uu____9681)))
in (

let uu____9704 = (

let uu____9721 = (

let uu____9739 = (

let uu____9754 = (enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff))
in ((FStar_Parser_Const.iff_lid), (uu____9754)))
in (

let uu____9777 = (

let uu____9794 = (

let uu____9812 = (

let uu____9827 = (enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot))
in ((FStar_Parser_Const.not_lid), (uu____9827)))
in (uu____9812)::(((FStar_Parser_Const.eq2_lid), (eq_op)))::(((FStar_Parser_Const.eq3_lid), (eq_op)))::(((FStar_Parser_Const.true_lid), ((const_op FStar_SMTEncoding_Term.mkTrue))))::(((FStar_Parser_Const.false_lid), ((const_op FStar_SMTEncoding_Term.mkFalse))))::[])
in (((FStar_Parser_Const.ite_lid), (mk_ite)))::uu____9794)
in (uu____9739)::uu____9777))
in (((FStar_Parser_Const.imp_lid), (mk_imp1)))::uu____9721)
in (uu____9666)::uu____9704))
in (uu____9611)::uu____9649))
in (

let rec fallback = (fun phi1 -> (match (phi1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_meta (phi', FStar_Syntax_Syntax.Meta_labeled (msg, r, b)) -> begin
(

let uu____10194 = (encode_formula phi' env)
in (match (uu____10194) with
| (phi2, decls) -> begin
(

let uu____10205 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Labeled (((phi2), (msg), (r)))) r)
in ((uu____10205), (decls)))
end))
end
| FStar_Syntax_Syntax.Tm_meta (uu____10206) -> begin
(

let uu____10213 = (FStar_Syntax_Util.unmeta phi1)
in (encode_formula uu____10213 env))
end
| FStar_Syntax_Syntax.Tm_match (e, pats) -> begin
(

let uu____10252 = (encode_match e pats FStar_SMTEncoding_Util.mkFalse env encode_formula)
in (match (uu____10252) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_let ((false, ({FStar_Syntax_Syntax.lbname = FStar_Util.Inl (x); FStar_Syntax_Syntax.lbunivs = uu____10264; FStar_Syntax_Syntax.lbtyp = t1; FStar_Syntax_Syntax.lbeff = uu____10266; FStar_Syntax_Syntax.lbdef = e1; FStar_Syntax_Syntax.lbattrs = uu____10268; FStar_Syntax_Syntax.lbpos = uu____10269})::[]), e2) -> begin
(

let uu____10293 = (encode_let x t1 e1 e2 env encode_formula)
in (match (uu____10293) with
| (t, decls) -> begin
((t), (decls))
end))
end
| FStar_Syntax_Syntax.Tm_app (head1, args) -> begin
(

let head2 = (FStar_Syntax_Util.un_uinst head1)
in (match (((head2.FStar_Syntax_Syntax.n), (args))) with
| (FStar_Syntax_Syntax.Tm_fvar (fv), (uu____10340)::((x, uu____10342))::((t, uu____10344))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.has_type_lid) -> begin
(

let uu____10391 = (encode_term x env)
in (match (uu____10391) with
| (x1, decls) -> begin
(

let uu____10402 = (encode_term t env)
in (match (uu____10402) with
| (t1, decls') -> begin
(

let uu____10413 = (FStar_SMTEncoding_Term.mk_HasType x1 t1)
in ((uu____10413), ((FStar_List.append decls decls'))))
end))
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((r, uu____10418))::((msg, uu____10420))::((phi2, uu____10422))::[]) when (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.labeled_lid) -> begin
(

let uu____10467 = (

let uu____10472 = (

let uu____10473 = (FStar_Syntax_Subst.compress r)
in uu____10473.FStar_Syntax_Syntax.n)
in (

let uu____10476 = (

let uu____10477 = (FStar_Syntax_Subst.compress msg)
in uu____10477.FStar_Syntax_Syntax.n)
in ((uu____10472), (uu____10476))))
in (match (uu____10467) with
| (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range (r1)), FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string (s, uu____10486))) -> begin
(

let phi3 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_meta (((phi2), (FStar_Syntax_Syntax.Meta_labeled (((s), (r1), (false))))))) FStar_Pervasives_Native.None r1)
in (fallback phi3))
end
| uu____10492 -> begin
(fallback phi2)
end))
end
| (FStar_Syntax_Syntax.Tm_fvar (fv), ((t, uu____10499))::[]) when ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.squash_lid) || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.auto_squash_lid)) -> begin
(encode_formula t env)
end
| uu____10524 when (head_redex env head2) -> begin
(

let uu____10537 = (whnf env phi1)
in (encode_formula uu____10537 env))
end
| uu____10538 -> begin
(

let uu____10551 = (encode_term phi1 env)
in (match (uu____10551) with
| (tt, decls) -> begin
(

let uu____10562 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___81_10565 = tt
in {FStar_SMTEncoding_Term.tm = uu___81_10565.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___81_10565.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____10562), (decls)))
end))
end))
end
| uu____10566 -> begin
(

let uu____10567 = (encode_term phi1 env)
in (match (uu____10567) with
| (tt, decls) -> begin
(

let uu____10578 = (FStar_SMTEncoding_Term.mk_Valid (

let uu___82_10581 = tt
in {FStar_SMTEncoding_Term.tm = uu___82_10581.FStar_SMTEncoding_Term.tm; FStar_SMTEncoding_Term.freevars = uu___82_10581.FStar_SMTEncoding_Term.freevars; FStar_SMTEncoding_Term.rng = phi1.FStar_Syntax_Syntax.pos}))
in ((uu____10578), (decls)))
end))
end))
in (

let encode_q_body = (fun env1 bs ps body -> (

let uu____10625 = (encode_binders FStar_Pervasives_Native.None bs env1)
in (match (uu____10625) with
| (vars, guards, env2, decls, uu____10664) -> begin
(

let uu____10677 = (encode_smt_patterns ps env2)
in (match (uu____10677) with
| (pats, decls') -> begin
(

let uu____10720 = (encode_formula body env2)
in (match (uu____10720) with
| (body1, decls'') -> begin
(

let guards1 = (match (pats) with
| (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (gf), (p)::[]); FStar_SMTEncoding_Term.freevars = uu____10752; FStar_SMTEncoding_Term.rng = uu____10753})::[])::[] when (

let uu____10768 = (FStar_Ident.text_of_lid FStar_Parser_Const.guard_free)
in (Prims.op_Equality uu____10768 gf)) -> begin
[]
end
| uu____10769 -> begin
guards
end)
in (

let uu____10774 = (FStar_SMTEncoding_Util.mk_and_l guards1)
in ((vars), (pats), (uu____10774), (body1), ((FStar_List.append decls (FStar_List.append decls' decls''))))))
end))
end))
end)))
in ((debug1 phi);
(

let phi1 = (FStar_Syntax_Util.unascribe phi)
in (

let uu____10785 = (FStar_Syntax_Util.destruct_typ_as_formula phi1)
in (match (uu____10785) with
| FStar_Pervasives_Native.None -> begin
(fallback phi1)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op, arms)) -> begin
(

let uu____10794 = (FStar_All.pipe_right connectives (FStar_List.tryFind (fun uu____10860 -> (match (uu____10860) with
| (l, uu____10874) -> begin
(FStar_Ident.lid_equals op l)
end))))
in (match (uu____10794) with
| FStar_Pervasives_Native.None -> begin
(fallback phi1)
end
| FStar_Pervasives_Native.Some (uu____10913, f) -> begin
(f phi1.FStar_Syntax_Syntax.pos arms)
end))
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars env vars)));
(

let uu____10959 = (encode_q_body env vars pats body)
in (match (uu____10959) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let tm = (

let uu____11004 = (

let uu____11015 = (FStar_SMTEncoding_Util.mkImp ((guard), (body1)))
in ((pats1), (vars1), (uu____11015)))
in (FStar_SMTEncoding_Term.mkForall uu____11004 phi1.FStar_Syntax_Syntax.pos))
in ((tm), (decls)))
end));
)
end
| FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx (vars, pats, body)) -> begin
((FStar_All.pipe_right pats (FStar_List.iter (check_pattern_vars env vars)));
(

let uu____11034 = (encode_q_body env vars pats body)
in (match (uu____11034) with
| (vars1, pats1, guard, body1, decls) -> begin
(

let uu____11078 = (

let uu____11079 = (

let uu____11090 = (FStar_SMTEncoding_Util.mkAnd ((guard), (body1)))
in ((pats1), (vars1), (uu____11090)))
in (FStar_SMTEncoding_Term.mkExists uu____11079 phi1.FStar_Syntax_Syntax.pos))
in ((uu____11078), (decls)))
end));
)
end)));
)))))))))))))))




