
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
| Not_a_wp_implication (_90_2) -> begin
_90_2
end))


type label =
FStar_SMTEncoding_Term.error_label


type labels =
FStar_SMTEncoding_Term.error_labels


let sort_labels : (FStar_SMTEncoding_Term.error_label * Prims.bool) Prims.list  ->  (((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) * Prims.bool) Prims.list = (fun l -> (FStar_List.sortWith (fun _90_12 _90_21 -> (match (((_90_12), (_90_21))) with
| (((_90_5, _90_7, r1), _90_11), ((_90_14, _90_16, r2), _90_20)) -> begin
(FStar_Range.compare r1 r2)
end)) l))


let remove_dups : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun l -> (FStar_Util.remove_dups (fun _90_27 _90_32 -> (match (((_90_27), (_90_32))) with
| ((_90_24, m1, r1), (_90_29, m2, r2)) -> begin
((r1 = r2) && (m1 = m2))
end)) l))


type msg =
(Prims.string * FStar_Range.range)


type ranges =
(Prims.string Prims.option * FStar_Range.range) Prims.list


let fresh_label : Prims.string  ->  FStar_Range.range  ->  FStar_SMTEncoding_Term.term  ->  (label * FStar_SMTEncoding_Term.term) = (

let ctr = (FStar_ST.alloc (Prims.parse_int "0"))
in (fun message range t -> (

let l = (

let _90_37 = (FStar_Util.incr ctr)
in (let _189_21 = (let _189_20 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _189_20))
in (FStar_Util.format1 "label_%s" _189_21)))
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
| (None, _90_52) -> begin
false
end
| (Some (nm), FStar_SMTEncoding_Term.FreeV (nm', _90_58)) -> begin
(nm = nm')
end
| ((_, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Valid"), (tm)::[]))) | ((_, FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("ApplyTT"), (tm)::_))) -> begin
(is_a_post_condition post_name_opt tm)
end
| _90_82 -> begin
false
end))
in (

let conjuncts = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, cs) -> begin
cs
end
| _90_90 -> begin
(t)::[]
end))
in (

let is_guard_free = (fun tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = _90_97; FStar_SMTEncoding_Term.rng = _90_95})::[])::[], iopt, _90_109, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r)::[]); FStar_SMTEncoding_Term.freevars = _90_113; FStar_SMTEncoding_Term.rng = _90_111}) -> begin
true
end
| _90_124 -> begin
false
end))
in (

let split_named_continuation = (fun q lhs -> (FStar_All.pipe_right (conjuncts lhs) (FStar_List.partition is_guard_free)))
in (

let is_a_named_continuation = (fun lhs -> (FStar_All.pipe_right (conjuncts lhs) (FStar_Util.for_some is_guard_free)))
in (

let _90_135 = (match (use_env_msg) with
| None -> begin
((false), (""))
end
| Some (f) -> begin
(let _189_45 = (f ())
in ((true), (_189_45)))
end)
in (match (_90_135) with
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

let _90_145 = r
in {FStar_Range.def_range = rng.FStar_Range.def_range; FStar_Range.use_range = _90_145.FStar_Range.use_range})
end)
in (fresh_label msg rng t))))
in (

let rec aux = (fun default_msg ropt post_name_opt labels q -> (match (q.FStar_SMTEncoding_Term.tm) with
| (FStar_SMTEncoding_Term.BoundV (_)) | (FStar_SMTEncoding_Term.Integer (_)) -> begin
((labels), (q))
end
| FStar_SMTEncoding_Term.LblPos (_90_161) -> begin
(failwith "Impossible")
end
| FStar_SMTEncoding_Term.Labeled (arg, "could not prove post-condition", _90_166) -> begin
(

let fallback = (fun msg -> (aux default_msg ropt post_name_opt labels arg))
in try
(match (()) with
| () -> begin
(match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, (post)::sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = _90_186; FStar_SMTEncoding_Term.rng = rng}) -> begin
(

let post_name = (let _189_68 = (let _189_67 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _189_67))
in (Prims.strcat "^^post_condition_" _189_68))
in (

let names = (let _189_73 = (FStar_List.mapi (fun i s -> (let _189_72 = (let _189_71 = (FStar_Util.string_of_int i)
in (Prims.strcat "^^" _189_71))
in ((_189_72), (s)))) sorts)
in (((post_name), (post)))::_189_73)
in (

let instantiation = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV names)
in (

let _90_203 = (let _189_75 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (let _189_74 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((_189_75), (_189_74))))
in (match (_90_203) with
| (lhs, rhs) -> begin
(

let _90_244 = (match (lhs.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, clauses_lhs) -> begin
(

let _90_210 = (FStar_Util.prefix clauses_lhs)
in (match (_90_210) with
| (req, ens) -> begin
(match (ens.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats_ens, iopt_ens, sorts_ens, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (ensures_conjuncts)::(post)::[]); FStar_SMTEncoding_Term.freevars = _90_217; FStar_SMTEncoding_Term.rng = rng_ens}) when (is_a_post_condition (Some (post_name)) post) -> begin
(

let _90_229 = (aux "could not prove post-condition" None (Some (post_name)) labels ensures_conjuncts)
in (match (_90_229) with
| (labels, ensures_conjuncts) -> begin
(

let pats_ens = (match (pats_ens) with
| ([]) | (([])::[]) -> begin
((post)::[])::[]
end
| _90_234 -> begin
pats_ens
end)
in (

let ens = (let _189_78 = (let _189_77 = (let _189_76 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Imp), ((ensures_conjuncts)::(post)::[])))) rng_ens)
in ((FStar_SMTEncoding_Term.Forall), (pats_ens), (iopt_ens), (sorts_ens), (_189_76)))
in FStar_SMTEncoding_Term.Quant (_189_77))
in (FStar_SMTEncoding_Term.mk _189_78 ens.FStar_SMTEncoding_Term.rng))
in (

let lhs = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.And), ((FStar_List.append req ((ens)::[])))))) lhs.FStar_SMTEncoding_Term.rng)
in (let _189_79 = (FStar_SMTEncoding_Term.abstr names lhs)
in ((labels), (_189_79))))))
end))
end
| _90_239 -> begin
(let _189_84 = (let _189_83 = (let _189_82 = (let _189_81 = (let _189_80 = (FStar_SMTEncoding_Term.print_smt_term ens)
in (Prims.strcat "  ... " _189_80))
in (Prims.strcat post_name _189_81))
in (Prims.strcat "Ensures clause doesn\'t match post name:  " _189_82))
in Not_a_wp_implication (_189_83))
in (Prims.raise _189_84))
end)
end))
end
| _90_241 -> begin
(let _189_87 = (let _189_86 = (let _189_85 = (FStar_SMTEncoding_Term.print_smt_term lhs)
in (Prims.strcat "LHS not a conjunct: " _189_85))
in Not_a_wp_implication (_189_86))
in (Prims.raise _189_87))
end)
in (match (_90_244) with
| (labels, lhs) -> begin
(

let _90_250 = (

let _90_247 = (aux default_msg None (Some (post_name)) labels rhs)
in (match (_90_247) with
| (labels, rhs) -> begin
(let _189_88 = (FStar_SMTEncoding_Term.abstr names rhs)
in ((labels), (_189_88)))
end))
in (match (_90_250) with
| (labels, rhs) -> begin
(

let body = (FStar_SMTEncoding_Term.mkImp ((lhs), (rhs)) rng)
in (let _189_89 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), ((post)::sorts), (body)))) q.FStar_SMTEncoding_Term.rng)
in ((labels), (_189_89))))
end))
end))
end)))))
end
| _90_253 -> begin
(let _189_91 = (let _189_90 = (FStar_SMTEncoding_Term.print_smt_term arg)
in (Prims.strcat "arg not a quant: " _189_90))
in (fallback _189_91))
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
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, [], None, (post)::[], {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = _90_266; FStar_SMTEncoding_Term.rng = rng}) when (is_a_named_continuation lhs) -> begin
(

let post_name = (let _189_94 = (let _189_93 = (FStar_Syntax_Syntax.next_id ())
in (FStar_All.pipe_left FStar_Util.string_of_int _189_93))
in (Prims.strcat "^^post_condition_" _189_94))
in (

let names = ((post_name), (post))
in (

let instantiation = (let _189_95 = (FStar_SMTEncoding_Util.mkFreeV names)
in (_189_95)::[])
in (

let _90_281 = (let _189_97 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (let _189_96 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((_189_97), (_189_96))))
in (match (_90_281) with
| (lhs, rhs) -> begin
(

let _90_320 = (FStar_Util.fold_map (fun labels tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = _90_288; FStar_SMTEncoding_Term.rng = _90_286})::[])::[], iopt, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r)::[]); FStar_SMTEncoding_Term.freevars = _90_303; FStar_SMTEncoding_Term.rng = _90_301}) -> begin
(

let _90_315 = (aux default_msg None post_name_opt labels r)
in (match (_90_315) with
| (labels, r) -> begin
(let _189_103 = (let _189_102 = (let _189_101 = (let _189_100 = (FStar_SMTEncoding_Util.norng FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Iff), ((l)::(r)::[])))))
in ((FStar_SMTEncoding_Term.Forall), (((p)::[])::[]), (Some ((Prims.parse_int "0"))), (sorts), (_189_100)))
in FStar_SMTEncoding_Term.Quant (_189_101))
in (FStar_SMTEncoding_Term.mk _189_102 q.FStar_SMTEncoding_Term.rng))
in ((labels), (_189_103)))
end))
end
| _90_317 -> begin
((labels), (tm))
end)) labels (conjuncts lhs))
in (match (_90_320) with
| (labels, lhs_conjs) -> begin
(

let _90_323 = (aux default_msg None (Some (post_name)) labels rhs)
in (match (_90_323) with
| (labels, rhs) -> begin
(

let body = (let _189_106 = (let _189_105 = (let _189_104 = (FStar_SMTEncoding_Term.mk_and_l lhs_conjs lhs.FStar_SMTEncoding_Term.rng)
in ((_189_104), (rhs)))
in (FStar_SMTEncoding_Term.mkImp _189_105 rng))
in (FStar_All.pipe_right _189_106 (FStar_SMTEncoding_Term.abstr ((names)::[]))))
in (

let q = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), ([]), (None), ((post)::[]), (body)))) q.FStar_SMTEncoding_Term.rng)
in ((labels), (q))))
end))
end))
end)))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]) -> begin
(

let _90_334 = (aux default_msg ropt post_name_opt labels rhs)
in (match (_90_334) with
| (labels, rhs) -> begin
(let _189_107 = (FStar_SMTEncoding_Util.mkImp ((lhs), (rhs)))
in ((labels), (_189_107)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(

let _90_341 = (FStar_Util.fold_map (aux default_msg ropt post_name_opt) labels conjuncts)
in (match (_90_341) with
| (labels, conjuncts) -> begin
(let _189_108 = (FStar_SMTEncoding_Term.mk_and_l conjuncts q.FStar_SMTEncoding_Term.rng)
in ((labels), (_189_108)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]) -> begin
(

let _90_351 = (aux default_msg ropt post_name_opt labels q1)
in (match (_90_351) with
| (labels, q1) -> begin
(

let _90_354 = (aux default_msg ropt post_name_opt labels q2)
in (match (_90_354) with
| (labels, q2) -> begin
(let _189_109 = (FStar_SMTEncoding_Term.mkITE ((hd), (q1), (q2)) q.FStar_SMTEncoding_Term.rng)
in ((labels), (_189_109)))
end))
end))
end
| (FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Exists, _, _, _, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Or, _)) -> begin
(

let _90_378 = (fresh_label default_msg ropt q.FStar_SMTEncoding_Term.rng q)
in (match (_90_378) with
| (lab, q) -> begin
(((lab)::labels), (q))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (_90_380), _90_383) when (is_a_post_condition post_name_opt q) -> begin
((labels), (q))
end
| (FStar_SMTEncoding_Term.FreeV (_)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Eq, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LT, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LTE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GT, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GTE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (_), _)) -> begin
(

let _90_438 = (fresh_label default_msg ropt q.FStar_SMTEncoding_Term.rng q)
in (match (_90_438) with
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

let _90_488 = (aux default_msg ropt post_name_opt labels body)
in (match (_90_488) with
| (labels, body) -> begin
(let _189_110 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), (sorts), (body)))) q.FStar_SMTEncoding_Term.rng)
in ((labels), (_189_110)))
end))
end))
in (aux "assertion failed" None None [] q)))
end))))))))


let detail_errors : FStar_TypeChecker_Env.env  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  ((FStar_SMTEncoding_Z3.unsat_core, (FStar_SMTEncoding_Term.error_labels * FStar_SMTEncoding_Z3.error_kind)) FStar_Util.either * Prims.int))  ->  FStar_SMTEncoding_Term.error_labels = (fun env all_labels askZ3 -> (

let print_banner = (fun _90_493 -> (match (()) with
| () -> begin
(let _189_127 = (let _189_124 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _189_124))
in (let _189_126 = (FStar_Util.string_of_int (Prims.parse_int "5"))
in (let _189_125 = (FStar_Util.string_of_int (FStar_List.length all_labels))
in (FStar_Util.print3_error "Detailed error report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n" _189_127 _189_126 _189_125))))
end))
in (

let print_result = (fun _90_501 -> (match (_90_501) with
| ((_90_496, msg, r), success) -> begin
if success then begin
(let _189_130 = (FStar_Range.string_of_range r)
in (FStar_Util.print1_error "OK: proof obligation at %s was proven\n" _189_130))
end else begin
(FStar_TypeChecker_Errors.report r msg)
end
end))
in (

let elim = (fun labs -> (FStar_All.pipe_right labs (FStar_List.map (fun _90_509 -> (match (_90_509) with
| (l, _90_506, _90_508) -> begin
(let _189_137 = (let _189_136 = (let _189_135 = (let _189_134 = (FStar_SMTEncoding_Util.mkFreeV l)
in ((_189_134), (FStar_SMTEncoding_Util.mkTrue)))
in (FStar_SMTEncoding_Util.mkEq _189_135))
in ((_189_136), (Some ("Disabling label")), (Some ((Prims.strcat "disable_label_" (Prims.fst l))))))
in FStar_SMTEncoding_Term.Assume (_189_137))
end)))))
in (

let print_labs = (fun tag l -> (FStar_All.pipe_right l (FStar_List.iter (fun _90_518 -> (match (_90_518) with
| (l, _90_515, _90_517) -> begin
(FStar_Util.print2 "%s : %s; " tag (Prims.fst l))
end)))))
in (

let rec linear_check = (fun eliminated errors active -> (match (active) with
| [] -> begin
(

let results = (let _189_152 = (FStar_List.map (fun x -> ((x), (true))) eliminated)
in (let _189_151 = (FStar_List.map (fun x -> ((x), (false))) errors)
in (FStar_List.append _189_152 _189_151)))
in (sort_labels results))
end
| (hd)::tl -> begin
(

let _90_533 = (let _189_153 = (FStar_All.pipe_left elim (FStar_List.append eliminated (FStar_List.append errors tl)))
in (askZ3 _189_153))
in (match (_90_533) with
| (result, _90_532) -> begin
if (FStar_Util.is_left result) then begin
(linear_check ((hd)::eliminated) errors tl)
end else begin
(linear_check eliminated ((hd)::errors) tl)
end
end))
end))
in (

let _90_534 = (print_banner ())
in (

let _90_536 = (FStar_Options.set_option "z3rlimit" (FStar_Options.Int ((Prims.parse_int "5"))))
in (

let res = (linear_check [] [] all_labels)
in (

let _90_539 = (FStar_All.pipe_right res (FStar_List.iter print_result))
in []))))))))))




