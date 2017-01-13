
open Prims

exception Not_a_wp_implication of (Prims.string)


let is_Not_a_wp_implication = (fun _discr_ -> (match (_discr_) with
| Not_a_wp_implication (_) -> begin
true
end
| _ -> begin
false
end))


let ___Not_a_wp_implication____0 = (fun projectee -> (match (projectee) with
| Not_a_wp_implication (_92_2) -> begin
_92_2
end))


type label =
FStar_SMTEncoding_Term.error_label


type labels =
FStar_SMTEncoding_Term.error_labels


let sort_labels : (FStar_SMTEncoding_Term.error_label * Prims.bool) Prims.list  ->  (((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) * Prims.bool) Prims.list = (fun l -> (FStar_List.sortWith (fun _92_12 _92_21 -> (match (((_92_12), (_92_21))) with
| (((_92_5, _92_7, r1), _92_11), ((_92_14, _92_16, r2), _92_20)) -> begin
(FStar_Range.compare r1 r2)
end)) l))


let remove_dups : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun l -> (FStar_Util.remove_dups (fun _92_27 _92_32 -> (match (((_92_27), (_92_32))) with
| ((_92_24, m1, r1), (_92_29, m2, r2)) -> begin
((r1 = r2) && (m1 = m2))
end)) l))


type msg =
(Prims.string * FStar_Range.range)


type ranges =
(Prims.string Prims.option * FStar_Range.range) Prims.list


let fresh_label : Prims.string  ->  FStar_Range.range  ->  FStar_SMTEncoding_Term.term  ->  (label * FStar_SMTEncoding_Term.term) = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun message range t -> (

let l = (

let _92_37 = (FStar_Util.incr ctr)
in (let _193_21 = (let _193_20 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _193_20))
in (FStar_Util.format1 "label_%s" _193_21)))
in (

let lvar = ((l), (FStar_SMTEncoding_Term.Bool_sort))
in (

let label = ((lvar), (message), (range))
in (

let lterm = (FStar_SMTEncoding_Util.mkFreeV lvar)
in (

let lt = (FStar_SMTEncoding_Term.mkOr ((lterm), (t)) range)
in ((label), (lt)))))))))


let label_goals = (fun use_env_msg r q -> (

let rec is_a_post_condition = (fun post_name_opt tm -> (match (((post_name_opt), (tm.FStar_SMTEncoding_Term.tm))) with
| (None, _92_52) -> begin
false
end
| (Some (nm), FStar_SMTEncoding_Term.FreeV (nm', _92_58)) -> begin
(nm = nm')
end
| ((_, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Valid"), (tm)::[]))) | ((_, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("ApplyTT"), (tm)::_))) -> begin
(is_a_post_condition post_name_opt tm)
end
| _92_82 -> begin
false
end))
in (

let conjuncts = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, cs) -> begin
cs
end
| _92_90 -> begin
(t)::[]
end))
in (

let is_guard_free = (fun tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = _92_97; FStar_SMTEncoding_Term.rng = _92_95})::[])::[], iopt, _92_109, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r)::[]); FStar_SMTEncoding_Term.freevars = _92_113; FStar_SMTEncoding_Term.rng = _92_111}) -> begin
true
end
| _92_124 -> begin
false
end))
in (

let is_a_named_continuation = (fun lhs -> (FStar_All.pipe_right (conjuncts lhs) (FStar_Util.for_some is_guard_free)))
in (

let _92_132 = (match (use_env_msg) with
| None -> begin
((false), (""))
end
| Some (f) -> begin
(let _193_41 = (f ())
in ((true), (_193_41)))
end)
in (match (_92_132) with
| (flag, msg_prefix) -> begin
(

let fresh_label = (fun msg ropt rng t -> (

let msg = if flag then begin
(Prims.strcat "Failed to verify implicit argument: " msg)
end else begin
msg
end
in (

let rng = (match (ropt) with
| None -> begin
rng
end
| Some (r) -> begin
(

let _92_142 = r
in {FStar_Range.def_range = rng.FStar_Range.def_range; FStar_Range.use_range = _92_142.FStar_Range.use_range})
end)
in (fresh_label msg rng t))))
in (

let rec aux = (fun default_msg ropt post_name_opt labels q -> (match (q.FStar_SMTEncoding_Term.tm) with
| (FStar_SMTEncoding_Term.BoundV (_)) | (FStar_SMTEncoding_Term.Integer (_)) -> begin
((labels), (q))
end
| FStar_SMTEncoding_Term.LblPos (_92_158) -> begin
(failwith "Impossible")
end
| FStar_SMTEncoding_Term.Labeled (arg, "could not prove post-condition", _92_163) -> begin
(

let fallback = (fun msg -> (aux default_msg ropt post_name_opt labels arg))
in try
(match (()) with
| () -> begin
(match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, (post)::sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = _92_183; FStar_SMTEncoding_Term.rng = rng}) -> begin
(

let post_name = (let _193_64 = (let _193_63 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _193_63))
in (Prims.strcat "^^post_condition_" _193_64))
in (

let names = (let _193_69 = (FStar_List.mapi (fun i s -> (let _193_68 = (let _193_67 = (FStar_Util.string_of_int i)
in (Prims.strcat "^^" _193_67))
in ((_193_68), (s)))) sorts)
in (((post_name), (post)))::_193_69)
in (

let instantiation = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV names)
in (

let _92_200 = (let _193_71 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (let _193_70 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((_193_71), (_193_70))))
in (match (_92_200) with
| (lhs, rhs) -> begin
(

let _92_241 = (match (lhs.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, clauses_lhs) -> begin
(

let _92_207 = (FStar_Util.prefix clauses_lhs)
in (match (_92_207) with
| (req, ens) -> begin
(match (ens.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats_ens, iopt_ens, sorts_ens, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (ensures_conjuncts)::(post)::[]); FStar_SMTEncoding_Term.freevars = _92_214; FStar_SMTEncoding_Term.rng = rng_ens}) when (is_a_post_condition (Some (post_name)) post) -> begin
(

let _92_226 = (aux "could not prove post-condition" None (Some (post_name)) labels ensures_conjuncts)
in (match (_92_226) with
| (labels, ensures_conjuncts) -> begin
(

let pats_ens = (match (pats_ens) with
| ([]) | (([])::[]) -> begin
((post)::[])::[]
end
| _92_231 -> begin
pats_ens
end)
in (

let ens = (let _193_74 = (let _193_73 = (let _193_72 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Imp), ((ensures_conjuncts)::(post)::[])))) rng_ens)
in ((FStar_SMTEncoding_Term.Forall), (pats_ens), (iopt_ens), (sorts_ens), (_193_72)))
in FStar_SMTEncoding_Term.Quant (_193_73))
in (FStar_SMTEncoding_Term.mk _193_74 ens.FStar_SMTEncoding_Term.rng))
in (

let lhs = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.And), ((FStar_List.append req ((ens)::[])))))) lhs.FStar_SMTEncoding_Term.rng)
in (let _193_75 = (FStar_SMTEncoding_Term.abstr names lhs)
in ((labels), (_193_75))))))
end))
end
| _92_236 -> begin
(let _193_80 = (let _193_79 = (let _193_78 = (let _193_77 = (let _193_76 = (FStar_SMTEncoding_Term.print_smt_term ens)
in (Prims.strcat "  ... " _193_76))
in (Prims.strcat post_name _193_77))
in (Prims.strcat "Ensures clause doesn\'t match post name:  " _193_78))
in Not_a_wp_implication (_193_79))
in (Prims.raise _193_80))
end)
end))
end
| _92_238 -> begin
(let _193_83 = (let _193_82 = (let _193_81 = (FStar_SMTEncoding_Term.print_smt_term lhs)
in (Prims.strcat "LHS not a conjunct: " _193_81))
in Not_a_wp_implication (_193_82))
in (Prims.raise _193_83))
end)
in (match (_92_241) with
| (labels, lhs) -> begin
(

let _92_247 = (

let _92_244 = (aux default_msg None (Some (post_name)) labels rhs)
in (match (_92_244) with
| (labels, rhs) -> begin
(let _193_84 = (FStar_SMTEncoding_Term.abstr names rhs)
in ((labels), (_193_84)))
end))
in (match (_92_247) with
| (labels, rhs) -> begin
(

let body = (FStar_SMTEncoding_Term.mkImp ((lhs), (rhs)) rng)
in (let _193_85 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), ((post)::sorts), (body)))) q.FStar_SMTEncoding_Term.rng)
in ((labels), (_193_85))))
end))
end))
end)))))
end
| _92_250 -> begin
(let _193_87 = (let _193_86 = (FStar_SMTEncoding_Term.print_smt_term arg)
in (Prims.strcat "arg not a quant: " _193_86))
in (fallback _193_87))
end)
end)
with
| Not_a_wp_implication (msg) -> begin
(fallback msg)
end)
end
| FStar_SMTEncoding_Term.Labeled (arg, reason, r) -> begin
(aux reason (Some (r)) post_name_opt labels arg)
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, [], None, (post)::[], {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = _92_263; FStar_SMTEncoding_Term.rng = rng}) when (is_a_named_continuation lhs) -> begin
(

let post_name = (let _193_90 = (let _193_89 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _193_89))
in (Prims.strcat "^^post_condition_" _193_90))
in (

let names = ((post_name), (post))
in (

let instantiation = (let _193_91 = (FStar_SMTEncoding_Util.mkFreeV names)
in (_193_91)::[])
in (

let _92_278 = (let _193_93 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (let _193_92 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((_193_93), (_193_92))))
in (match (_92_278) with
| (lhs, rhs) -> begin
(

let _92_317 = (FStar_Util.fold_map (fun labels tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = _92_285; FStar_SMTEncoding_Term.rng = _92_283})::[])::[], iopt, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r)::[]); FStar_SMTEncoding_Term.freevars = _92_300; FStar_SMTEncoding_Term.rng = _92_298}) -> begin
(

let _92_312 = (aux default_msg None post_name_opt labels r)
in (match (_92_312) with
| (labels, r) -> begin
(let _193_99 = (let _193_98 = (let _193_97 = (let _193_96 = (FStar_SMTEncoding_Util.norng FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Iff), ((l)::(r)::[])))))
in ((FStar_SMTEncoding_Term.Forall), (((p)::[])::[]), (Some ((Prims.parse_int "0"))), (sorts), (_193_96)))
in FStar_SMTEncoding_Term.Quant (_193_97))
in (FStar_SMTEncoding_Term.mk _193_98 q.FStar_SMTEncoding_Term.rng))
in ((labels), (_193_99)))
end))
end
| _92_314 -> begin
((labels), (tm))
end)) labels (conjuncts lhs))
in (match (_92_317) with
| (labels, lhs_conjs) -> begin
(

let _92_320 = (aux default_msg None (Some (post_name)) labels rhs)
in (match (_92_320) with
| (labels, rhs) -> begin
(

let body = (let _193_102 = (let _193_101 = (let _193_100 = (FStar_SMTEncoding_Term.mk_and_l lhs_conjs lhs.FStar_SMTEncoding_Term.rng)
in ((_193_100), (rhs)))
in (FStar_SMTEncoding_Term.mkImp _193_101 rng))
in (FStar_All.pipe_right _193_102 (FStar_SMTEncoding_Term.abstr ((names)::[]))))
in (

let q = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), ([]), (None), ((post)::[]), (body)))) q.FStar_SMTEncoding_Term.rng)
in ((labels), (q))))
end))
end))
end)))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]) -> begin
(

let _92_331 = (aux default_msg ropt post_name_opt labels rhs)
in (match (_92_331) with
| (labels, rhs) -> begin
(let _193_103 = (FStar_SMTEncoding_Util.mkImp ((lhs), (rhs)))
in ((labels), (_193_103)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(

let _92_338 = (FStar_Util.fold_map (aux default_msg ropt post_name_opt) labels conjuncts)
in (match (_92_338) with
| (labels, conjuncts) -> begin
(let _193_104 = (FStar_SMTEncoding_Term.mk_and_l conjuncts q.FStar_SMTEncoding_Term.rng)
in ((labels), (_193_104)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]) -> begin
(

let _92_348 = (aux default_msg ropt post_name_opt labels q1)
in (match (_92_348) with
| (labels, q1) -> begin
(

let _92_351 = (aux default_msg ropt post_name_opt labels q2)
in (match (_92_351) with
| (labels, q2) -> begin
(let _193_105 = (FStar_SMTEncoding_Term.mkITE ((hd), (q1), (q2)) q.FStar_SMTEncoding_Term.rng)
in ((labels), (_193_105)))
end))
end))
end
| (FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Exists, _, _, _, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Or, _)) -> begin
(

let _92_375 = (fresh_label default_msg ropt q.FStar_SMTEncoding_Term.rng q)
in (match (_92_375) with
| (lab, q) -> begin
(((lab)::labels), (q))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (_92_377), _92_380) when (is_a_post_condition post_name_opt q) -> begin
((labels), (q))
end
| (FStar_SMTEncoding_Term.FreeV (_)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.FalseOp, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Eq, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LT, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LTE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GT, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GTE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (_), _)) -> begin
(

let _92_435 = (fresh_label default_msg ropt q.FStar_SMTEncoding_Term.rng q)
in (match (_92_435) with
| (lab, q) -> begin
(((lab)::labels), (q))
end))
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Add, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Sub, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Div, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mul, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Minus, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mod, _)) -> begin
(failwith "Impossible: non-propositional term")
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, _)) -> begin
(failwith "Impossible: arity mismatch")
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body) -> begin
(

let _92_485 = (aux default_msg ropt post_name_opt labels body)
in (match (_92_485) with
| (labels, body) -> begin
(let _193_106 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), (sorts), (body)))) q.FStar_SMTEncoding_Term.rng)
in ((labels), (_193_106)))
end))
end))
in (aux "assertion failed" None None [] q)))
end)))))))


let detail_errors : FStar_TypeChecker_Env.env  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  ((FStar_SMTEncoding_Z3.unsat_core, (FStar_SMTEncoding_Term.error_labels * FStar_SMTEncoding_Z3.error_kind)) FStar_Util.either * Prims.int))  ->  FStar_SMTEncoding_Term.error_labels = (fun env all_labels askZ3 -> (

let print_banner = (fun _92_490 -> (match (()) with
| () -> begin
(let _193_123 = (let _193_120 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _193_120))
in (let _193_122 = (FStar_Util.string_of_int (Prims.parse_int "5"))
in (let _193_121 = (FStar_Util.string_of_int (FStar_List.length all_labels))
in (FStar_Util.print3_error "Detailed error report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n" _193_123 _193_122 _193_121))))
end))
in (

let print_result = (fun _92_498 -> (match (_92_498) with
| ((_92_493, msg, r), success) -> begin
if success then begin
(let _193_126 = (FStar_Range.string_of_range r)
in (FStar_Util.print1_error "OK: proof obligation at %s was proven\n" _193_126))
end else begin
(FStar_Errors.report r msg)
end
end))
in (

let elim = (fun labs -> (FStar_All.pipe_right labs (FStar_List.map (fun _92_506 -> (match (_92_506) with
| (l, _92_503, _92_505) -> begin
(let _193_133 = (let _193_132 = (let _193_131 = (let _193_130 = (FStar_SMTEncoding_Util.mkFreeV l)
in ((_193_130), (FStar_SMTEncoding_Util.mkTrue)))
in (FStar_SMTEncoding_Util.mkEq _193_131))
in ((_193_132), (Some ("Disabling label")), (Some ((Prims.strcat "disable_label_" (Prims.fst l))))))
in FStar_SMTEncoding_Term.Assume (_193_133))
end)))))
in (

let rec linear_check = (fun eliminated errors active -> (match (active) with
| [] -> begin
(

let results = (let _193_143 = (FStar_List.map (fun x -> ((x), (true))) eliminated)
in (let _193_142 = (FStar_List.map (fun x -> ((x), (false))) errors)
in (FStar_List.append _193_143 _193_142)))
in (sort_labels results))
end
| (hd)::tl -> begin
(

let _92_521 = (let _193_144 = (FStar_All.pipe_left elim (FStar_List.append eliminated (FStar_List.append errors tl)))
in (askZ3 _193_144))
in (match (_92_521) with
| (result, _92_520) -> begin
if (FStar_Util.is_left result) then begin
(linear_check ((hd)::eliminated) errors tl)
end else begin
(linear_check eliminated ((hd)::errors) tl)
end
end))
end))
in (

let _92_522 = (print_banner ())
in (

let _92_524 = (FStar_Options.set_option "z3rlimit" (FStar_Options.Int ((Prims.parse_int "5"))))
in (

let res = (linear_check [] [] all_labels)
in (

let _92_527 = (FStar_All.pipe_right res (FStar_List.iter print_result))
in [])))))))))




