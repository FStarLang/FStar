
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


let sort_labels : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun l -> (FStar_List.sortWith (fun _87_7 _87_13 -> (match (((_87_7), (_87_13))) with
| ((_87_3, _87_5, r1), (_87_9, _87_11, r2)) -> begin
(FStar_Range.compare r1 r2)
end)) l))


let remove_dups : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun l -> (FStar_Util.remove_dups (fun _87_19 _87_24 -> (match (((_87_19), (_87_24))) with
| ((_87_16, m1, r1), (_87_21, m2, r2)) -> begin
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

let _87_29 = (FStar_Util.incr ctr)
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
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Valid"), ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("ApplyTT"), ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV ("^^post_condition", _87_57); FStar_SMTEncoding_Term.freevars = _87_54; FStar_SMTEncoding_Term.rng = _87_52})::_87_50); FStar_SMTEncoding_Term.freevars = _87_46; FStar_SMTEncoding_Term.rng = _87_44})::[]) -> begin
true
end
| _87_69 -> begin
false
end))
in (

let _87_75 = (match (use_env_msg) with
| None -> begin
((false), (""))
end
| Some (f) -> begin
(let _182_29 = (f ())
in ((true), (_182_29)))
end)
in (match (_87_75) with
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
| FStar_SMTEncoding_Term.Labeled (arg, "could not prove post-condition", _87_100) -> begin
(

let fallback = (fun _87_104 -> (match (()) with
| () -> begin
(aux default_msg ropt labels arg)
end))
in try
(match (()) with
| () -> begin
(match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, (post)::sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = _87_119; FStar_SMTEncoding_Term.rng = rng}) -> begin
(

let names = (let _182_53 = (FStar_List.mapi (fun i s -> (let _182_52 = (let _182_51 = (FStar_Util.string_of_int i)
in (Prims.strcat "^^" _182_51))
in ((_182_52), (s)))) sorts)
in ((("^^post_condition"), (post)))::_182_53)
in (

let instantiation = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV names)
in (

let _87_135 = (let _182_55 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (let _182_54 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((_182_55), (_182_54))))
in (match (_87_135) with
| (lhs, rhs) -> begin
(

let _87_170 = (match (lhs.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, clauses_lhs) -> begin
(

let _87_142 = (FStar_Util.prefix clauses_lhs)
in (match (_87_142) with
| (req, ens) -> begin
(match (ens.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats_ens, iopt_ens, sorts_ens, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (ensures_conjuncts)::(post)::[]); FStar_SMTEncoding_Term.freevars = _87_149; FStar_SMTEncoding_Term.rng = rng_ens}) when (is_a_post_condition post) -> begin
(

let _87_161 = (aux "could not prove post-condition" None labels ensures_conjuncts)
in (match (_87_161) with
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
| _87_165 -> begin
(Prims.raise Not_a_wp_implication)
end)
end))
end
| _87_167 -> begin
(Prims.raise Not_a_wp_implication)
end)
in (match (_87_170) with
| (labels, lhs) -> begin
(

let _87_176 = (

let _87_173 = (aux default_msg None labels rhs)
in (match (_87_173) with
| (labels, rhs) -> begin
(let _182_60 = (FStar_SMTEncoding_Term.abstr names rhs)
in ((labels), (_182_60)))
end))
in (match (_87_176) with
| (labels, rhs) -> begin
(

let body = (FStar_SMTEncoding_Term.mkImp ((lhs), (rhs)) rng)
in (let _182_61 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), ((post)::sorts), (body)))) q.FStar_SMTEncoding_Term.rng)
in ((labels), (_182_61))))
end))
end))
end))))
end
| _87_179 -> begin
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
| _87_198 -> begin
(t)::[]
end))
in (

let _87_233 = (FStar_All.pipe_right (conjuncts lhs) (FStar_List.partition (fun tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = _87_204; FStar_SMTEncoding_Term.rng = _87_202})::[])::[], iopt, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r)::[]); FStar_SMTEncoding_Term.freevars = _87_219; FStar_SMTEncoding_Term.rng = _87_217}) -> begin
true
end
| _87_230 -> begin
false
end))))
in (match (_87_233) with
| (named_continuation_opt, other_lhs_conjuncts) -> begin
(match (named_continuation_opt) with
| (_87_240)::(_87_237)::_87_235 -> begin
(FStar_All.failwith "More than one named continuation; impossible")
end
| [] -> begin
(

let _87_245 = (aux default_msg ropt labels rhs)
in (match (_87_245) with
| (labels, rhs) -> begin
(let _182_66 = (FStar_SMTEncoding_Util.mkImp ((lhs), (rhs)))
in ((labels), (_182_66)))
end))
end
| (q)::[] -> begin
(match (q.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = _87_252; FStar_SMTEncoding_Term.rng = _87_250})::[])::[], iopt, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r)::[]); FStar_SMTEncoding_Term.freevars = _87_267; FStar_SMTEncoding_Term.rng = _87_265}) -> begin
(

let _87_279 = (aux default_msg None labels r)
in (match (_87_279) with
| (labels, r) -> begin
(

let q = (let _182_69 = (let _182_68 = (let _182_67 = (FStar_SMTEncoding_Util.norng FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Iff), ((l)::(r)::[])))))
in ((FStar_SMTEncoding_Term.Forall), (((p)::[])::[]), (Some ((Prims.parse_int "0"))), (sorts), (_182_67)))
in FStar_SMTEncoding_Term.Quant (_182_68))
in (FStar_SMTEncoding_Term.mk _182_69 q.FStar_SMTEncoding_Term.rng))
in (

let lhs = (FStar_SMTEncoding_Term.mk_and_l ((q)::other_lhs_conjuncts) lhs.FStar_SMTEncoding_Term.rng)
in (

let _87_286 = (

let hash_of_p = (FStar_SMTEncoding_Term.hash_of_term p)
in (FStar_All.pipe_right (conjuncts rhs) (FStar_List.partition (fun t -> ((FStar_SMTEncoding_Term.hash_of_term t) = hash_of_p)))))
in (match (_87_286) with
| (rhs_p, rhs_rest) -> begin
(

let _87_289 = (let _182_71 = (FStar_SMTEncoding_Term.mk_and_l rhs_rest rhs.FStar_SMTEncoding_Term.rng)
in (aux default_msg None labels _182_71))
in (match (_87_289) with
| (labels, rhs_rest) -> begin
(

let rhs = (FStar_SMTEncoding_Term.mk_and_l ((rhs_rest)::rhs_p) rhs.FStar_SMTEncoding_Term.rng)
in (let _182_72 = (FStar_SMTEncoding_Util.mkImp ((lhs), (rhs)))
in ((labels), (_182_72))))
end))
end))))
end))
end
| _87_292 -> begin
(FStar_All.failwith "Impossible")
end)
end)
end)))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(

let _87_299 = (FStar_Util.fold_map (aux default_msg ropt) labels conjuncts)
in (match (_87_299) with
| (labels, conjuncts) -> begin
(let _182_73 = (FStar_SMTEncoding_Term.mk_and_l conjuncts q.FStar_SMTEncoding_Term.rng)
in ((labels), (_182_73)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]) -> begin
(

let _87_309 = (aux default_msg ropt labels q1)
in (match (_87_309) with
| (labels, q1) -> begin
(

let _87_312 = (aux default_msg ropt labels q2)
in (match (_87_312) with
| (labels, q2) -> begin
(let _182_74 = (FStar_SMTEncoding_Term.mkITE ((hd), (q1), (q2)) q.FStar_SMTEncoding_Term.rng)
in ((labels), (_182_74)))
end))
end))
end
| (FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Exists, _, _, _, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Or, _)) -> begin
(

let _87_336 = (fresh_label default_msg ropt q.FStar_SMTEncoding_Term.rng q)
in (match (_87_336) with
| (lab, t) -> begin
(((lab)::labels), (q))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (_87_338), _87_341) when (is_a_post_condition q) -> begin
((labels), (q))
end
| (FStar_SMTEncoding_Term.FreeV (_)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Eq, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LT, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LTE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GT, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GTE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (_), _)) -> begin
(

let _87_396 = (fresh_label default_msg ropt q.FStar_SMTEncoding_Term.rng q)
in (match (_87_396) with
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

let _87_446 = (aux default_msg ropt labels body)
in (match (_87_446) with
| (labels, body) -> begin
(let _182_75 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), (sorts), (body)))) q.FStar_SMTEncoding_Term.rng)
in ((labels), (_182_75)))
end))
end))
in (aux "assertion failed" None [] q)))
end))))


let detail_errors : labels  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  ((FStar_SMTEncoding_Z3.unsat_core, (FStar_SMTEncoding_Term.error_labels * Prims.bool)) FStar_Util.either * Prims.int))  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun all_labels potential_errors askZ3 -> (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let elim = (fun labs -> (

let _87_453 = (FStar_Util.incr ctr)
in (let _182_98 = (let _182_91 = (let _182_90 = (let _182_89 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _182_89))
in (Prims.strcat "DETAILING ERRORS" _182_90))
in FStar_SMTEncoding_Term.Echo (_182_91))
in (let _182_97 = (FStar_All.pipe_right labs (FStar_List.map (fun _87_460 -> (match (_87_460) with
| (l, _87_457, _87_459) -> begin
(let _182_96 = (let _182_95 = (let _182_94 = (let _182_93 = (FStar_SMTEncoding_Util.mkFreeV l)
in ((_182_93), (FStar_SMTEncoding_Util.mkTrue)))
in (FStar_SMTEncoding_Util.mkEq _182_94))
in ((_182_95), (Some ("Disabling label")), (Some ((Prims.strcat "disable_label_" (Prims.fst l))))))
in FStar_SMTEncoding_Term.Assume (_182_96))
end))))
in (_182_98)::_182_97))))
in (

let print_labs = (fun tag l -> (FStar_All.pipe_right l (FStar_List.iter (fun _87_469 -> (match (_87_469) with
| (l, _87_466, _87_468) -> begin
(FStar_Util.print2 "%s : %s; " tag (Prims.fst l))
end)))))
in (

let minus = (fun l1 l2 -> (FStar_All.pipe_right l1 (FStar_List.filter (fun _87_481 -> (match (_87_481) with
| ((x, _87_475), _87_478, _87_480) -> begin
(not ((FStar_All.pipe_right l2 (FStar_Util.for_some (fun _87_490 -> (match (_87_490) with
| ((y, _87_484), _87_487, _87_489) -> begin
(x = y)
end))))))
end)))))
in (

let rec linear_check = (fun eliminated errors active -> (match (active) with
| [] -> begin
(

let labs = (FStar_All.pipe_right errors sort_labels)
in labs)
end
| (hd)::tl -> begin
(

let _87_503 = (let _182_116 = (FStar_All.pipe_left elim (FStar_List.append eliminated (FStar_List.append errors tl)))
in (askZ3 _182_116))
in (match (_87_503) with
| (result, _87_502) -> begin
if (FStar_Util.is_left result) then begin
(linear_check ((hd)::eliminated) errors tl)
end else begin
(linear_check eliminated ((hd)::errors) tl)
end
end))
end))
in (

let rec bisect = (fun eliminated potential_errors active -> (match (active) with
| [] -> begin
((eliminated), (potential_errors))
end
| _87_510 -> begin
(

let _87_518 = (match (active) with
| (_87_512)::[] -> begin
((active), ([]))
end
| _87_515 -> begin
(FStar_Util.first_N ((FStar_List.length active) / (Prims.parse_int "2")) active)
end)
in (match (_87_518) with
| (pfx, sfx) -> begin
(

let _87_522 = (let _182_123 = (elim (FStar_List.append eliminated (FStar_List.append potential_errors sfx)))
in (askZ3 _182_123))
in (match (_87_522) with
| (result, _87_521) -> begin
(match (result) with
| FStar_Util.Inl (_87_524) -> begin
(bisect (FStar_List.append eliminated pfx) potential_errors sfx)
end
| FStar_Util.Inr ([], timeout) -> begin
(bisect eliminated (FStar_List.append potential_errors pfx) sfx)
end
| FStar_Util.Inr (pfx_subset, timeout) -> begin
(

let potential_errors = (FStar_List.append potential_errors pfx_subset)
in (

let pfx_active = (minus pfx pfx_subset)
in (bisect eliminated potential_errors (FStar_List.append pfx_active sfx))))
end)
end))
end))
end))
in (

let rec until_fixpoint = (fun eliminated potential_errors active -> (

let _87_542 = (bisect eliminated potential_errors active)
in (match (_87_542) with
| (eliminated', potential_errors) -> begin
if (FStar_Util.physical_equality eliminated eliminated') then begin
(linear_check eliminated [] potential_errors)
end else begin
(until_fixpoint eliminated' [] potential_errors)
end
end)))
in (

let active = (minus all_labels potential_errors)
in (until_fixpoint [] potential_errors active))))))))))




