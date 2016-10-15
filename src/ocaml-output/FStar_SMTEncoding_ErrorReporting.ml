
open Prims

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


let fresh_label : Prims.string Prims.option  ->  FStar_Range.range  ->  FStar_SMTEncoding_Term.term  ->  (label * FStar_SMTEncoding_Term.term) = (

let ctr = (FStar_ST.alloc (Prims.parse_int "0"))
in (fun msg range t -> (

let l = (

let _87_29 = (FStar_Util.incr ctr)
in (let _182_16 = (let _182_15 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _182_15))
in (FStar_Util.format1 "label_%s" _182_16)))
in (

let lvar = ((l), (FStar_SMTEncoding_Term.Bool_sort))
in (

let message = (match (msg) with
| Some (m) -> begin
m
end
| None -> begin
"assertion failed"
end)
in (

let label = ((lvar), (message), (range))
in (

let lterm = (FStar_SMTEncoding_Util.mkFreeV lvar)
in (

let lt = (FStar_SMTEncoding_Util.mkOr ((lterm), (t)))
in ((label), (lt))))))))))


let label_goals = (fun use_env_msg r q -> (

let _87_48 = (match (use_env_msg) with
| None -> begin
((false), (""))
end
| Some (f) -> begin
(let _182_26 = (f ())
in ((true), (_182_26)))
end)
in (match (_87_48) with
| (flag, msg_prefix) -> begin
(

let fresh_label = (fun msg rng t -> (

let msg = if flag then begin
(match (msg) with
| None -> begin
Some ("Failed to verify implicit argument")
end
| Some (msg) -> begin
Some ((Prims.strcat "Failed to verify implicit argument: " msg))
end)
end else begin
msg
end
in (fresh_label msg rng t)))
in (

let rec aux = (fun labels q -> (match (q.FStar_SMTEncoding_Term.tm) with
| (FStar_SMTEncoding_Term.BoundV (_)) | (FStar_SMTEncoding_Term.Integer (_)) -> begin
((labels), (q))
end
| FStar_SMTEncoding_Term.Labeled (arg, "could not prove post-condition", _87_69) -> begin
(aux labels arg)
end
| FStar_SMTEncoding_Term.Labeled (arg, reason, r) -> begin
(

let _87_79 = (fresh_label (Some (reason)) r arg)
in (match (_87_79) with
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
| _87_93 -> begin
(t)::[]
end))
in (

let _87_128 = (FStar_All.pipe_right (conjuncts lhs) (FStar_List.partition (fun tm -> (match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = _87_99; FStar_SMTEncoding_Term.rng = _87_97})::[])::[], iopt, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r)::[]); FStar_SMTEncoding_Term.freevars = _87_114; FStar_SMTEncoding_Term.rng = _87_112}) -> begin
true
end
| _87_125 -> begin
false
end))))
in (match (_87_128) with
| (named_continuation_opt, other_lhs_conjuncts) -> begin
(match (named_continuation_opt) with
| (_87_135)::(_87_132)::_87_130 -> begin
(FStar_All.failwith "More than one named continuation; impossible")
end
| [] -> begin
(

let _87_140 = (aux labels rhs)
in (match (_87_140) with
| (labels, rhs) -> begin
(let _182_40 = (FStar_SMTEncoding_Util.mkImp ((lhs), (rhs)))
in ((labels), (_182_40)))
end))
end
| (q)::[] -> begin
(match (q.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.freevars = _87_147; FStar_SMTEncoding_Term.rng = _87_145})::[])::[], iopt, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r)::[]); FStar_SMTEncoding_Term.freevars = _87_162; FStar_SMTEncoding_Term.rng = _87_160}) -> begin
(

let _87_174 = (aux labels r)
in (match (_87_174) with
| (labels, r) -> begin
(

let q = (let _182_43 = (let _182_42 = (let _182_41 = (FStar_SMTEncoding_Util.norng FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Iff), ((l)::(r)::[])))))
in ((FStar_SMTEncoding_Term.Forall), (((p)::[])::[]), (Some ((Prims.parse_int "0"))), (sorts), (_182_41)))
in FStar_SMTEncoding_Term.Quant (_182_42))
in (FStar_SMTEncoding_Term.mk _182_43 q.FStar_SMTEncoding_Term.rng))
in (

let lhs = (FStar_SMTEncoding_Term.mk_and_l ((q)::other_lhs_conjuncts) lhs.FStar_SMTEncoding_Term.rng)
in (

let _87_181 = (

let hash_of_p = (FStar_SMTEncoding_Term.hash_of_term p)
in (FStar_All.pipe_right (conjuncts rhs) (FStar_List.partition (fun t -> ((FStar_SMTEncoding_Term.hash_of_term t) = hash_of_p)))))
in (match (_87_181) with
| (rhs_p, rhs_rest) -> begin
(

let _87_184 = (let _182_45 = (FStar_SMTEncoding_Term.mk_and_l rhs_rest rhs.FStar_SMTEncoding_Term.rng)
in (aux labels _182_45))
in (match (_87_184) with
| (labels, rhs_rest) -> begin
(

let rhs = (FStar_SMTEncoding_Term.mk_and_l ((rhs_rest)::rhs_p) rhs.FStar_SMTEncoding_Term.rng)
in (let _182_46 = (FStar_SMTEncoding_Util.mkImp ((lhs), (rhs)))
in ((labels), (_182_46))))
end))
end))))
end))
end
| _87_187 -> begin
(FStar_All.failwith "Impossible")
end)
end)
end)))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(

let _87_194 = (FStar_Util.fold_map aux labels conjuncts)
in (match (_87_194) with
| (labels, conjuncts) -> begin
(let _182_47 = (FStar_SMTEncoding_Term.mk_and_l conjuncts q.FStar_SMTEncoding_Term.rng)
in ((labels), (_182_47)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]) -> begin
(

let _87_204 = (aux labels q1)
in (match (_87_204) with
| (labels, q1) -> begin
(

let _87_207 = (aux labels q2)
in (match (_87_207) with
| (labels, q2) -> begin
(let _182_48 = (FStar_SMTEncoding_Term.mkITE ((hd), (q1), (q2)) q.FStar_SMTEncoding_Term.rng)
in ((labels), (_182_48)))
end))
end))
end
| (FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Exists, _, _, _, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Or, _)) -> begin
(

let _87_231 = (fresh_label None q.FStar_SMTEncoding_Term.rng q)
in (match (_87_231) with
| (lab, t) -> begin
(((lab)::labels), (q))
end))
end
| (FStar_SMTEncoding_Term.FreeV (_)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Eq, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LT, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LTE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GT, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GTE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (_), _)) -> begin
(

let _87_284 = (fresh_label None q.FStar_SMTEncoding_Term.rng q)
in (match (_87_284) with
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

let _87_334 = (aux labels body)
in (match (_87_334) with
| (labels, body) -> begin
(let _182_49 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), (sorts), (body)))) q.FStar_SMTEncoding_Term.rng)
in ((labels), (_182_49)))
end))
end))
in (aux [] q)))
end)))


let detail_errors : labels  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  ((FStar_SMTEncoding_Z3.unsat_core, (FStar_SMTEncoding_Term.error_labels * Prims.bool)) FStar_Util.either * Prims.int))  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun all_labels potential_errors askZ3 -> (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let elim = (fun labs -> (

let _87_341 = (FStar_Util.incr ctr)
in (let _182_72 = (let _182_65 = (let _182_64 = (let _182_63 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _182_63))
in (Prims.strcat "DETAILING ERRORS" _182_64))
in FStar_SMTEncoding_Term.Echo (_182_65))
in (let _182_71 = (FStar_All.pipe_right labs (FStar_List.map (fun _87_348 -> (match (_87_348) with
| (l, _87_345, _87_347) -> begin
(let _182_70 = (let _182_69 = (let _182_68 = (let _182_67 = (FStar_SMTEncoding_Util.mkFreeV l)
in ((_182_67), (FStar_SMTEncoding_Util.mkTrue)))
in (FStar_SMTEncoding_Util.mkEq _182_68))
in ((_182_69), (Some ("Disabling label")), (Some ((Prims.strcat "disable_label_" (Prims.fst l))))))
in FStar_SMTEncoding_Term.Assume (_182_70))
end))))
in (_182_72)::_182_71))))
in (

let print_labs = (fun tag l -> (FStar_All.pipe_right l (FStar_List.iter (fun _87_357 -> (match (_87_357) with
| (l, _87_354, _87_356) -> begin
(FStar_Util.print2 "%s : %s; " tag (Prims.fst l))
end)))))
in (

let minus = (fun l1 l2 -> (FStar_All.pipe_right l1 (FStar_List.filter (fun _87_369 -> (match (_87_369) with
| ((x, _87_363), _87_366, _87_368) -> begin
(not ((FStar_All.pipe_right l2 (FStar_Util.for_some (fun _87_378 -> (match (_87_378) with
| ((y, _87_372), _87_375, _87_377) -> begin
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

let _87_391 = (let _182_90 = (FStar_All.pipe_left elim (FStar_List.append eliminated (FStar_List.append errors tl)))
in (askZ3 _182_90))
in (match (_87_391) with
| (result, _87_390) -> begin
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
| _87_398 -> begin
(

let _87_406 = (match (active) with
| (_87_400)::[] -> begin
((active), ([]))
end
| _87_403 -> begin
(FStar_Util.first_N ((FStar_List.length active) / (Prims.parse_int "2")) active)
end)
in (match (_87_406) with
| (pfx, sfx) -> begin
(

let _87_410 = (let _182_97 = (elim (FStar_List.append eliminated (FStar_List.append potential_errors sfx)))
in (askZ3 _182_97))
in (match (_87_410) with
| (result, _87_409) -> begin
(match (result) with
| FStar_Util.Inl (_87_412) -> begin
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

let _87_430 = (bisect eliminated potential_errors active)
in (match (_87_430) with
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




