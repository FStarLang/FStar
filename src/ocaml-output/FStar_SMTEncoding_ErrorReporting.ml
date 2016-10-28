
open Prims

exception Not_a_wp_implication


let is_Not_a_wp_implication = (fun _discr_ -> (match (_discr_) with
| Not_a_wp_implication (_) -> begin
true
end
| _ -> begin
false
end))


type label =
FStar_SMTEncoding_Term.error_label


type labels =
FStar_SMTEncoding_Term.error_labels


let sort_labels : (FStar_SMTEncoding_Term.error_label * Prims.bool) Prims.list  ->  (((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) * Prims.bool) Prims.list = (fun l -> (FStar_List.sortWith (fun _87_10 _87_19 -> (match (((_87_10), (_87_19))) with
| (((_87_3, _87_5, r1), _87_9), ((_87_12, _87_14, r2), _87_18)) -> begin
(FStar_Range.compare r1 r2)
end)) l))


let remove_dups : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun l -> (FStar_Util.remove_dups (fun _87_25 _87_30 -> (match (((_87_25), (_87_30))) with
| ((_87_22, m1, r1), (_87_27, m2, r2)) -> begin
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

let _87_35 = (FStar_Util.incr ctr)
in (let _182_17 = (let _182_16 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _182_16))
in (FStar_Util.format1 "label_%s" _182_17)))
in (

let lvar = ((l), (FStar_SMTEncoding_Term.Bool_sort))
in (

let label = ((lvar), (message), (range))
in (

let lterm = (FStar_SMTEncoding_Util.mkFreeV lvar)
in (

let lt = (FStar_SMTEncoding_Util.mkOr ((lterm), (t)))
in ((label), (lt)))))))))


let label_goals = (fun use_env_msg r q -> (

let is_a_post_condition = (fun tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Valid"), ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("ApplyTT"), ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV ("^^post_condition", _87_63); FStar_SMTEncoding_Term.freevars = _87_60; FStar_SMTEncoding_Term.rng = _87_58})::_87_56); FStar_SMTEncoding_Term.freevars = _87_52; FStar_SMTEncoding_Term.rng = _87_50})::[]) -> begin
true
end
| _87_75 -> begin
false
end))
in (

let _87_81 = (match (use_env_msg) with
| None -> begin
((false), (""))
end
| Some (f) -> begin
(let _182_29 = (f ())
in ((true), (_182_29)))
end)
in (match (_87_81) with
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
r
end)
in (fresh_label msg rng t))))
in (

let rec aux = (fun default_msg ropt labels q -> (match (q.FStar_SMTEncoding_Term.tm) with
| (FStar_SMTEncoding_Term.BoundV (_)) | (FStar_SMTEncoding_Term.Integer (_)) -> begin
((labels), (q))
end
| FStar_SMTEncoding_Term.Labeled (arg, "could not prove post-condition", _87_106) -> begin
(

let fallback = (fun _87_110 -> (match (()) with
| () -> begin
(aux default_msg ropt labels arg)
end))
in try
(match (()) with
| () -> begin
(match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, (post)::sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = _87_125; FStar_SMTEncoding_Term.rng = rng}) -> begin
(

let names = (let _182_53 = (FStar_List.mapi (fun i s -> (let _182_52 = (let _182_51 = (FStar_Util.string_of_int i)
in (Prims.strcat "^^" _182_51))
in ((_182_52), (s)))) sorts)
in ((("^^post_condition"), (post)))::_182_53)
in (

let instantiation = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV names)
in (

let _87_141 = (let _182_55 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (let _182_54 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((_182_55), (_182_54))))
in (match (_87_141) with
| (lhs, rhs) -> begin
(

let _87_176 = (match (lhs.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, clauses_lhs) -> begin
(

let _87_148 = (FStar_Util.prefix clauses_lhs)
in (match (_87_148) with
| (req, ens) -> begin
(match (ens.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats_ens, iopt_ens, sorts_ens, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (ensures_conjuncts)::(post)::[]); FStar_SMTEncoding_Term.freevars = _87_155; FStar_SMTEncoding_Term.rng = rng_ens}) when (is_a_post_condition post) -> begin
(

let _87_167 = (aux "could not prove post-condition" None labels ensures_conjuncts)
in (match (_87_167) with
| (labels, ensures_conjuncts) -> begin
(

let ens = (let _182_58 = (let _182_57 = (let _182_56 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Imp), ((ensures_conjuncts)::(post)::[])))) rng_ens)
in ((FStar_SMTEncoding_Term.Forall), (pats_ens), (iopt_ens), (sorts_ens), (_182_56)))
in FStar_SMTEncoding_Term.Quant (_182_57))
in (FStar_SMTEncoding_Term.mk _182_58 ens.FStar_SMTEncoding_Term.rng))
in (

let lhs = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.And), ((FStar_List.append req ((ens)::[])))))) lhs.FStar_SMTEncoding_Term.rng)
in (let _182_59 = (FStar_SMTEncoding_Term.abstr names lhs)
in ((labels), (_182_59)))))
end))
end
| _87_171 -> begin
(Prims.raise Not_a_wp_implication)
end)
end))
end
| _87_173 -> begin
(Prims.raise Not_a_wp_implication)
end)
in (match (_87_176) with
| (labels, lhs) -> begin
(

let _87_182 = (

let _87_179 = (aux default_msg None labels rhs)
in (match (_87_179) with
| (labels, rhs) -> begin
(let _182_60 = (FStar_SMTEncoding_Term.abstr names rhs)
in ((labels), (_182_60)))
end))
in (match (_87_182) with
| (labels, rhs) -> begin
(

let body = (FStar_SMTEncoding_Term.mkImp ((lhs), (rhs)) rng)
in (let _182_61 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), ((post)::sorts), (body)))) q.FStar_SMTEncoding_Term.rng)
in ((labels), (_182_61))))
end))
end))
end))))
end
| _87_185 -> begin
(fallback ())
end)
end)
with
| Not_a_wp_implication -> begin
(fallback ())
end)
end
| FStar_SMTEncoding_Term.Labeled (arg, reason, r) -> begin
(aux reason (Some (r)) labels arg)
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]) -> begin
(

let conjuncts = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, cs) -> begin
cs
end
| _87_204 -> begin
(t)::[]
end))
in (

let _87_239 = (FStar_All.pipe_right (conjuncts lhs) (FStar_List.partition (fun tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = _87_210; FStar_SMTEncoding_Term.rng = _87_208})::[])::[], iopt, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r)::[]); FStar_SMTEncoding_Term.freevars = _87_225; FStar_SMTEncoding_Term.rng = _87_223}) -> begin
true
end
| _87_236 -> begin
false
end))))
in (match (_87_239) with
| (named_continuation_opt, other_lhs_conjuncts) -> begin
(match (named_continuation_opt) with
| (_87_246)::(_87_243)::_87_241 -> begin
(FStar_All.failwith "More than one named continuation; impossible")
end
| [] -> begin
(

let _87_251 = (aux default_msg ropt labels rhs)
in (match (_87_251) with
| (labels, rhs) -> begin
(let _182_66 = (FStar_SMTEncoding_Util.mkImp ((lhs), (rhs)))
in ((labels), (_182_66)))
end))
end
| (q)::[] -> begin
(match (q.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = _87_258; FStar_SMTEncoding_Term.rng = _87_256})::[])::[], iopt, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r)::[]); FStar_SMTEncoding_Term.freevars = _87_273; FStar_SMTEncoding_Term.rng = _87_271}) -> begin
(

let _87_285 = (aux default_msg None labels r)
in (match (_87_285) with
| (labels, r) -> begin
(

let q = (let _182_69 = (let _182_68 = (let _182_67 = (FStar_SMTEncoding_Util.norng FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Iff), ((l)::(r)::[])))))
in ((FStar_SMTEncoding_Term.Forall), (((p)::[])::[]), (Some ((Prims.parse_int "0"))), (sorts), (_182_67)))
in FStar_SMTEncoding_Term.Quant (_182_68))
in (FStar_SMTEncoding_Term.mk _182_69 q.FStar_SMTEncoding_Term.rng))
in (

let lhs = (FStar_SMTEncoding_Term.mk_and_l ((q)::other_lhs_conjuncts) lhs.FStar_SMTEncoding_Term.rng)
in (

let _87_292 = (

let hash_of_p = (FStar_SMTEncoding_Term.hash_of_term p)
in (FStar_All.pipe_right (conjuncts rhs) (FStar_List.partition (fun t -> ((FStar_SMTEncoding_Term.hash_of_term t) = hash_of_p)))))
in (match (_87_292) with
| (rhs_p, rhs_rest) -> begin
(

let _87_295 = (let _182_71 = (FStar_SMTEncoding_Term.mk_and_l rhs_rest rhs.FStar_SMTEncoding_Term.rng)
in (aux default_msg None labels _182_71))
in (match (_87_295) with
| (labels, rhs_rest) -> begin
(

let rhs = (FStar_SMTEncoding_Term.mk_and_l ((rhs_rest)::rhs_p) rhs.FStar_SMTEncoding_Term.rng)
in (let _182_72 = (FStar_SMTEncoding_Util.mkImp ((lhs), (rhs)))
in ((labels), (_182_72))))
end))
end))))
end))
end
| _87_298 -> begin
(FStar_All.failwith "Impossible")
end)
end)
end)))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(

let _87_305 = (FStar_Util.fold_map (aux default_msg ropt) labels conjuncts)
in (match (_87_305) with
| (labels, conjuncts) -> begin
(let _182_73 = (FStar_SMTEncoding_Term.mk_and_l conjuncts q.FStar_SMTEncoding_Term.rng)
in ((labels), (_182_73)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]) -> begin
(

let _87_315 = (aux default_msg ropt labels q1)
in (match (_87_315) with
| (labels, q1) -> begin
(

let _87_318 = (aux default_msg ropt labels q2)
in (match (_87_318) with
| (labels, q2) -> begin
(let _182_74 = (FStar_SMTEncoding_Term.mkITE ((hd), (q1), (q2)) q.FStar_SMTEncoding_Term.rng)
in ((labels), (_182_74)))
end))
end))
end
| (FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Exists, _, _, _, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Or, _)) -> begin
(

let _87_342 = (fresh_label default_msg ropt q.FStar_SMTEncoding_Term.rng q)
in (match (_87_342) with
| (lab, t) -> begin
(((lab)::labels), (q))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (_87_344), _87_347) when (is_a_post_condition q) -> begin
((labels), (q))
end
| (FStar_SMTEncoding_Term.FreeV (_)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Eq, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LT, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LTE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GT, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GTE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (_), _)) -> begin
(

let _87_402 = (fresh_label default_msg ropt q.FStar_SMTEncoding_Term.rng q)
in (match (_87_402) with
| (lab, q) -> begin
(((lab)::labels), (q))
end))
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Add, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Sub, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Div, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mul, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Minus, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mod, _)) -> begin
(FStar_All.failwith "Impossible: non-propositional term")
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, _)) -> begin
(FStar_All.failwith "Impossible: arity mismatch")
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body) -> begin
(

let _87_452 = (aux default_msg ropt labels body)
in (match (_87_452) with
| (labels, body) -> begin
(let _182_75 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), (sorts), (body)))) q.FStar_SMTEncoding_Term.rng)
in ((labels), (_182_75)))
end))
end))
in (aux "assertion failed" None [] q)))
end))))


let detail_errors : FStar_TypeChecker_Env.env  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  ((FStar_SMTEncoding_Z3.unsat_core, (FStar_SMTEncoding_Term.error_labels * FStar_SMTEncoding_Z3.error_kind)) FStar_Util.either * Prims.int))  ->  FStar_SMTEncoding_Term.error_labels = (fun env all_labels askZ3 -> (

let print_banner = (fun _87_457 -> (match (()) with
| () -> begin
(let _182_92 = (let _182_89 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _182_89))
in (let _182_91 = (FStar_Util.string_of_int (Prims.parse_int "5"))
in (let _182_90 = (FStar_Util.string_of_int (FStar_List.length all_labels))
in (FStar_Util.print3_error "Detailed error report follows for %s\nTaking %s seconds per proof obligation (%s proofs in total)\n" _182_92 _182_91 _182_90))))
end))
in (

let print_result = (fun _87_465 -> (match (_87_465) with
| ((_87_460, msg, r), success) -> begin
if success then begin
(let _182_95 = (FStar_Range.string_of_range r)
in (FStar_Util.print1_error "OK: proof obligation at %s was proven\n" _182_95))
end else begin
(FStar_TypeChecker_Errors.report r msg)
end
end))
in (

let elim = (fun labs -> (FStar_All.pipe_right labs (FStar_List.map (fun _87_473 -> (match (_87_473) with
| (l, _87_470, _87_472) -> begin
(let _182_102 = (let _182_101 = (let _182_100 = (let _182_99 = (FStar_SMTEncoding_Util.mkFreeV l)
in ((_182_99), (FStar_SMTEncoding_Util.mkTrue)))
in (FStar_SMTEncoding_Util.mkEq _182_100))
in ((_182_101), (Some ("Disabling label")), (Some ((Prims.strcat "disable_label_" (Prims.fst l))))))
in FStar_SMTEncoding_Term.Assume (_182_102))
end)))))
in (

let print_labs = (fun tag l -> (FStar_All.pipe_right l (FStar_List.iter (fun _87_482 -> (match (_87_482) with
| (l, _87_479, _87_481) -> begin
(FStar_Util.print2 "%s : %s; " tag (Prims.fst l))
end)))))
in (

let rec linear_check = (fun eliminated errors active -> (match (active) with
| [] -> begin
(

let results = (let _182_117 = (FStar_List.map (fun x -> ((x), (true))) eliminated)
in (let _182_116 = (FStar_List.map (fun x -> ((x), (false))) errors)
in (FStar_List.append _182_117 _182_116)))
in (sort_labels results))
end
| (hd)::tl -> begin
(

let _87_497 = (let _182_118 = (FStar_All.pipe_left elim (FStar_List.append eliminated (FStar_List.append errors tl)))
in (askZ3 _182_118))
in (match (_87_497) with
| (result, _87_496) -> begin
if (FStar_Util.is_left result) then begin
(linear_check ((hd)::eliminated) errors tl)
end else begin
(linear_check eliminated ((hd)::errors) tl)
end
end))
end))
in (

let _87_498 = (print_banner ())
in (

let _87_500 = (FStar_Options.set_option "z3timeout" (FStar_Options.Int ((Prims.parse_int "5"))))
in (

let res = (linear_check [] [] all_labels)
in (

let _87_503 = (FStar_All.pipe_right res (FStar_List.iter print_result))
in []))))))))))




