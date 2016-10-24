
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

let fresh_label = (fun msg rng t -> (

let msg = if flag then begin
(Prims.strcat "Failed to verify implicit argument: " msg)
end else begin
msg
end
in (fresh_label msg rng t)))
in (

let rec aux = (fun default_msg labels q -> (match (q.FStar_SMTEncoding_Term.tm) with
| (FStar_SMTEncoding_Term.BoundV (_)) | (FStar_SMTEncoding_Term.Integer (_)) -> begin
((labels), (q))
end
| FStar_SMTEncoding_Term.Labeled (arg, "could not prove post-condition", _87_94) -> begin
(

let fallback = (fun _87_98 -> (match (()) with
| () -> begin
(aux default_msg labels arg)
end))
in try
(match (()) with
| () -> begin
(match (arg.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, (post)::sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]); FStar_SMTEncoding_Term.freevars = _87_113; FStar_SMTEncoding_Term.rng = rng}) -> begin
(

let names = (let _182_49 = (FStar_List.mapi (fun i s -> (let _182_48 = (let _182_47 = (FStar_Util.string_of_int i)
in (Prims.strcat "^^" _182_47))
in ((_182_48), (s)))) sorts)
in ((("^^post_condition"), (post)))::_182_49)
in (

let instantiation = (FStar_List.map FStar_SMTEncoding_Util.mkFreeV names)
in (

let _87_129 = (let _182_51 = (FStar_SMTEncoding_Term.inst instantiation lhs)
in (let _182_50 = (FStar_SMTEncoding_Term.inst instantiation rhs)
in ((_182_51), (_182_50))))
in (match (_87_129) with
| (lhs, rhs) -> begin
(

let _87_164 = (match (lhs.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, clauses_lhs) -> begin
(

let _87_136 = (FStar_Util.prefix clauses_lhs)
in (match (_87_136) with
| (req, ens) -> begin
(match (ens.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats_ens, iopt_ens, sorts_ens, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (ensures_conjuncts)::(post)::[]); FStar_SMTEncoding_Term.freevars = _87_143; FStar_SMTEncoding_Term.rng = rng_ens}) when (is_a_post_condition post) -> begin
(

let _87_155 = (aux "could not prove post-condition" labels ensures_conjuncts)
in (match (_87_155) with
| (labels, ensures_conjuncts) -> begin
(

let ens = (let _182_54 = (let _182_53 = (let _182_52 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Imp), ((ensures_conjuncts)::(post)::[])))) rng_ens)
in ((FStar_SMTEncoding_Term.Forall), (pats_ens), (iopt_ens), (sorts_ens), (_182_52)))
in FStar_SMTEncoding_Term.Quant (_182_53))
in (FStar_SMTEncoding_Term.mk _182_54 ens.FStar_SMTEncoding_Term.rng))
in (

let lhs = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.And), ((FStar_List.append req ((ens)::[])))))) lhs.FStar_SMTEncoding_Term.rng)
in (let _182_55 = (FStar_SMTEncoding_Term.abstr names lhs)
in ((labels), (_182_55)))))
end))
end
| _87_159 -> begin
(Prims.raise Not_a_wp_implication)
end)
end))
end
| _87_161 -> begin
(Prims.raise Not_a_wp_implication)
end)
in (match (_87_164) with
| (labels, lhs) -> begin
(

let _87_170 = (

let _87_167 = (aux default_msg labels rhs)
in (match (_87_167) with
| (labels, rhs) -> begin
(let _182_56 = (FStar_SMTEncoding_Term.abstr names rhs)
in ((labels), (_182_56)))
end))
in (match (_87_170) with
| (labels, rhs) -> begin
(

let body = (FStar_SMTEncoding_Term.mkImp ((lhs), (rhs)) rng)
in (let _182_57 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), ((post)::sorts), (body)))) q.FStar_SMTEncoding_Term.rng)
in ((labels), (_182_57))))
end))
end))
end))))
end
| _87_173 -> begin
(fallback ())
end)
end)
with
| Not_a_wp_implication -> begin
(fallback ())
end)
end
| FStar_SMTEncoding_Term.Labeled (arg, reason, r) -> begin
(

let _87_181 = (fresh_label reason r arg)
in (match (_87_181) with
| (lab, arg) -> begin
(((lab)::labels), (arg))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]) -> begin
(

let conjuncts = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, cs) -> begin
cs
end
| _87_195 -> begin
(t)::[]
end))
in (

let _87_230 = (FStar_All.pipe_right (conjuncts lhs) (FStar_List.partition (fun tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = _87_201; FStar_SMTEncoding_Term.rng = _87_199})::[])::[], iopt, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r)::[]); FStar_SMTEncoding_Term.freevars = _87_216; FStar_SMTEncoding_Term.rng = _87_214}) -> begin
true
end
| _87_227 -> begin
false
end))))
in (match (_87_230) with
| (named_continuation_opt, other_lhs_conjuncts) -> begin
(match (named_continuation_opt) with
| (_87_237)::(_87_234)::_87_232 -> begin
(FStar_All.failwith "More than one named continuation; impossible")
end
| [] -> begin
(

let _87_242 = (aux default_msg labels rhs)
in (match (_87_242) with
| (labels, rhs) -> begin
(let _182_62 = (FStar_SMTEncoding_Util.mkImp ((lhs), (rhs)))
in ((labels), (_182_62)))
end))
end
| (q)::[] -> begin
(match (q.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = _87_249; FStar_SMTEncoding_Term.rng = _87_247})::[])::[], iopt, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r)::[]); FStar_SMTEncoding_Term.freevars = _87_264; FStar_SMTEncoding_Term.rng = _87_262}) -> begin
(

let _87_276 = (aux default_msg labels r)
in (match (_87_276) with
| (labels, r) -> begin
(

let q = (let _182_65 = (let _182_64 = (let _182_63 = (FStar_SMTEncoding_Util.norng FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Iff), ((l)::(r)::[])))))
in ((FStar_SMTEncoding_Term.Forall), (((p)::[])::[]), (Some ((Prims.parse_int "0"))), (sorts), (_182_63)))
in FStar_SMTEncoding_Term.Quant (_182_64))
in (FStar_SMTEncoding_Term.mk _182_65 q.FStar_SMTEncoding_Term.rng))
in (

let lhs = (FStar_SMTEncoding_Term.mk_and_l ((q)::other_lhs_conjuncts) lhs.FStar_SMTEncoding_Term.rng)
in (

let _87_283 = (

let hash_of_p = (FStar_SMTEncoding_Term.hash_of_term p)
in (FStar_All.pipe_right (conjuncts rhs) (FStar_List.partition (fun t -> ((FStar_SMTEncoding_Term.hash_of_term t) = hash_of_p)))))
in (match (_87_283) with
| (rhs_p, rhs_rest) -> begin
(

let _87_286 = (let _182_67 = (FStar_SMTEncoding_Term.mk_and_l rhs_rest rhs.FStar_SMTEncoding_Term.rng)
in (aux default_msg labels _182_67))
in (match (_87_286) with
| (labels, rhs_rest) -> begin
(

let rhs = (FStar_SMTEncoding_Term.mk_and_l ((rhs_rest)::rhs_p) rhs.FStar_SMTEncoding_Term.rng)
in (let _182_68 = (FStar_SMTEncoding_Util.mkImp ((lhs), (rhs)))
in ((labels), (_182_68))))
end))
end))))
end))
end
| _87_289 -> begin
(FStar_All.failwith "Impossible")
end)
end)
end)))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(

let _87_296 = (FStar_Util.fold_map (aux default_msg) labels conjuncts)
in (match (_87_296) with
| (labels, conjuncts) -> begin
(let _182_69 = (FStar_SMTEncoding_Term.mk_and_l conjuncts q.FStar_SMTEncoding_Term.rng)
in ((labels), (_182_69)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]) -> begin
(

let _87_306 = (aux default_msg labels q1)
in (match (_87_306) with
| (labels, q1) -> begin
(

let _87_309 = (aux default_msg labels q2)
in (match (_87_309) with
| (labels, q2) -> begin
(let _182_70 = (FStar_SMTEncoding_Term.mkITE ((hd), (q1), (q2)) q.FStar_SMTEncoding_Term.rng)
in ((labels), (_182_70)))
end))
end))
end
| (FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Exists, _, _, _, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Or, _)) -> begin
(

let _87_333 = (fresh_label default_msg q.FStar_SMTEncoding_Term.rng q)
in (match (_87_333) with
| (lab, t) -> begin
(((lab)::labels), (q))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (_87_335), _87_338) when (is_a_post_condition q) -> begin
((labels), (q))
end
| (FStar_SMTEncoding_Term.FreeV (_)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Eq, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LT, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LTE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GT, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GTE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (_), _)) -> begin
(

let _87_393 = (fresh_label default_msg q.FStar_SMTEncoding_Term.rng q)
in (match (_87_393) with
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

let _87_443 = (aux default_msg labels body)
in (match (_87_443) with
| (labels, body) -> begin
(let _182_71 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), (sorts), (body)))) q.FStar_SMTEncoding_Term.rng)
in ((labels), (_182_71)))
end))
end))
in (aux "assertion failed" [] q)))
end))))


let detail_errors : labels  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  ((FStar_SMTEncoding_Z3.unsat_core, (FStar_SMTEncoding_Term.error_labels * Prims.bool)) FStar_Util.either * Prims.int))  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun all_labels potential_errors askZ3 -> (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let elim = (fun labs -> (

let _87_450 = (FStar_Util.incr ctr)
in (let _182_94 = (let _182_87 = (let _182_86 = (let _182_85 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _182_85))
in (Prims.strcat "DETAILING ERRORS" _182_86))
in FStar_SMTEncoding_Term.Echo (_182_87))
in (let _182_93 = (FStar_All.pipe_right labs (FStar_List.map (fun _87_457 -> (match (_87_457) with
| (l, _87_454, _87_456) -> begin
(let _182_92 = (let _182_91 = (let _182_90 = (let _182_89 = (FStar_SMTEncoding_Util.mkFreeV l)
in ((_182_89), (FStar_SMTEncoding_Util.mkTrue)))
in (FStar_SMTEncoding_Util.mkEq _182_90))
in ((_182_91), (Some ("Disabling label")), (Some ((Prims.strcat "disable_label_" (Prims.fst l))))))
in FStar_SMTEncoding_Term.Assume (_182_92))
end))))
in (_182_94)::_182_93))))
in (

let print_labs = (fun tag l -> (FStar_All.pipe_right l (FStar_List.iter (fun _87_466 -> (match (_87_466) with
| (l, _87_463, _87_465) -> begin
(FStar_Util.print2 "%s : %s; " tag (Prims.fst l))
end)))))
in (

let minus = (fun l1 l2 -> (FStar_All.pipe_right l1 (FStar_List.filter (fun _87_478 -> (match (_87_478) with
| ((x, _87_472), _87_475, _87_477) -> begin
(not ((FStar_All.pipe_right l2 (FStar_Util.for_some (fun _87_487 -> (match (_87_487) with
| ((y, _87_481), _87_484, _87_486) -> begin
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

let _87_500 = (let _182_112 = (FStar_All.pipe_left elim (FStar_List.append eliminated (FStar_List.append errors tl)))
in (askZ3 _182_112))
in (match (_87_500) with
| (result, _87_499) -> begin
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
| _87_507 -> begin
(

let _87_515 = (match (active) with
| (_87_509)::[] -> begin
((active), ([]))
end
| _87_512 -> begin
(FStar_Util.first_N ((FStar_List.length active) / (Prims.parse_int "2")) active)
end)
in (match (_87_515) with
| (pfx, sfx) -> begin
(

let _87_519 = (let _182_119 = (elim (FStar_List.append eliminated (FStar_List.append potential_errors sfx)))
in (askZ3 _182_119))
in (match (_87_519) with
| (result, _87_518) -> begin
(match (result) with
| FStar_Util.Inl (_87_521) -> begin
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

let _87_539 = (bisect eliminated potential_errors active)
in (match (_87_539) with
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




