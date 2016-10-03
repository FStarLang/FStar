
open Prims

type label =
FStar_SMTEncoding_Term.error_label


type labels =
FStar_SMTEncoding_Term.error_labels


let sort_labels : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun l -> (FStar_List.sortWith (fun _89_7 _89_13 -> (match (((_89_7), (_89_13))) with
| ((_89_3, _89_5, r1), (_89_9, _89_11, r2)) -> begin
(FStar_Range.compare r1 r2)
end)) l))


let remove_dups : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list = (fun l -> (FStar_Util.remove_dups (fun _89_19 _89_24 -> (match (((_89_19), (_89_24))) with
| ((_89_16, m1, r1), (_89_21, m2, r2)) -> begin
((r1 = r2) && (m1 = m2))
end)) l))


type msg =
(Prims.string * FStar_Range.range)


type ranges =
(Prims.string Prims.option * FStar_Range.range) Prims.list


let fresh_label : ranges  ->  FStar_SMTEncoding_Term.term  ->  labels  ->  (FStar_SMTEncoding_Term.term * labels) = (

let ctr = (FStar_ST.alloc (Prims.parse_int "0"))
in (fun rs t labs -> (

let l = (

let _89_29 = (FStar_Util.incr ctr)
in (let _186_16 = (let _186_15 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _186_15))
in (FStar_Util.format1 "label_%s" _186_16)))
in (

let lvar = ((l), (FStar_SMTEncoding_Term.Bool_sort))
in (

let _89_49 = (match (rs) with
| [] -> begin
if (FStar_Options.debug_any ()) then begin
((t.FStar_SMTEncoding_Term.hash), (FStar_Range.dummyRange))
end else begin
(("Z3 provided a counterexample, but, unfortunately, F* could not translate it back to something meaningful"), (FStar_Range.dummyRange))
end
end
| ((Some (reason), r))::_89_35 -> begin
((reason), (r))
end
| ((None, r))::_89_42 -> begin
(("failed to prove a pre-condition"), (r))
end)
in (match (_89_49) with
| (message, range) -> begin
(

let label = ((lvar), (message), (range))
in (

let lterm = (FStar_SMTEncoding_Term.mkFreeV lvar)
in (

let lt = (FStar_SMTEncoding_Term.mkOr ((lterm), (t)))
in ((lt), ((label)::labs)))))
end))))))


let label_goals : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Int64.int64  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * labels * ranges) = (fun use_env_msg r q -> (

let _89_61 = (match (use_env_msg) with
| None -> begin
((false), (""))
end
| Some (f) -> begin
(let _186_32 = (f ())
in ((true), (_186_32)))
end)
in (match (_89_61) with
| (flag, msg_prefix) -> begin
(

let fresh_label = (fun rs t labs -> (

let rs' = if (not (flag)) then begin
rs
end else begin
(match (rs) with
| ((Some (reason), _89_71))::_89_67 -> begin
(((Some ((Prims.strcat "Failed to verify implicit argument: " reason))), (r)))::[]
end
| _89_75 -> begin
(((Some ("Failed to verify implicit argument")), (r)))::[]
end)
end
in (

let _89_79 = (fresh_label rs' t labs)
in (match (_89_79) with
| (lt, labs) -> begin
((lt), (labs), (rs))
end))))
in (

let rec aux = (fun rs q labs -> (match (q.FStar_SMTEncoding_Term.tm) with
| (FStar_SMTEncoding_Term.BoundV (_)) | (FStar_SMTEncoding_Term.Integer (_)) -> begin
((q), (labs), (rs))
end
| FStar_SMTEncoding_Term.Labeled (_89_91, "push", r) -> begin
((FStar_SMTEncoding_Term.mkTrue), (labs), ((((None), (r)))::rs))
end
| FStar_SMTEncoding_Term.Labeled (_89_97, "pop", r) -> begin
(let _186_45 = (FStar_List.tl rs)
in ((FStar_SMTEncoding_Term.mkTrue), (labs), (_186_45)))
end
| FStar_SMTEncoding_Term.Labeled (arg, reason, r) -> begin
(

let _89_110 = (aux ((((Some (reason)), (r)))::rs) arg labs)
in (match (_89_110) with
| (tm, labs, rs) -> begin
(let _186_46 = (FStar_List.tl rs)
in ((tm), (labs), (_186_46)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]) -> begin
(

let _89_120 = (aux rs rhs labs)
in (match (_89_120) with
| (rhs, labs, rs) -> begin
(

let _89_178 = (match (lhs.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(

let _89_169 = (FStar_Util.fold_map (fun _89_127 tm -> (match (_89_127) with
| (labs, rs) -> begin
(match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.hash = _89_133; FStar_SMTEncoding_Term.freevars = _89_131})::[])::[], iopt, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r)::[]); FStar_SMTEncoding_Term.hash = _89_148; FStar_SMTEncoding_Term.freevars = _89_146}) -> begin
(

let _89_161 = (aux rs r labs)
in (match (_89_161) with
| (r, labs, rs) -> begin
(

let q = (let _186_51 = (let _186_50 = (let _186_49 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Iff), ((l)::(r)::[])))))
in ((FStar_SMTEncoding_Term.Forall), (((p)::[])::[]), (Some ((Prims.parse_int "0"))), (sorts), (_186_49)))
in FStar_SMTEncoding_Term.Quant (_186_50))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk _186_51))
in ((((labs), (rs))), (q)))
end))
end
| _89_164 -> begin
((((labs), (rs))), (tm))
end)
end)) ((labs), (rs)) conjuncts)
in (match (_89_169) with
| ((labs, rs), conjuncts) -> begin
(

let tm = (FStar_List.fold_right (fun conjunct out -> (FStar_SMTEncoding_Term.mkAnd ((out), (conjunct)))) conjuncts FStar_SMTEncoding_Term.mkTrue)
in ((tm), (labs), (rs)))
end))
end
| _89_174 -> begin
((lhs), (labs), (rs))
end)
in (match (_89_178) with
| (lhs, labs, rs) -> begin
(let _186_54 = (FStar_SMTEncoding_Term.mkImp ((lhs), (rhs)))
in ((_186_54), (labs), (rs)))
end))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(

let _89_195 = (FStar_List.fold_left (fun _89_186 c -> (match (_89_186) with
| (rs, cs, labs) -> begin
(

let _89_191 = (aux rs c labs)
in (match (_89_191) with
| (c, labs, rs) -> begin
((rs), ((c)::cs), (labs))
end))
end)) ((rs), ([]), (labs)) conjuncts)
in (match (_89_195) with
| (rs, conjuncts, labs) -> begin
(

let tm = (FStar_List.fold_left (fun out conjunct -> (FStar_SMTEncoding_Term.mkAnd ((out), (conjunct)))) FStar_SMTEncoding_Term.mkTrue conjuncts)
in ((tm), (labs), (rs)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]) -> begin
(

let _89_210 = (aux rs q1 labs)
in (match (_89_210) with
| (q1, labs, _89_209) -> begin
(

let _89_215 = (aux rs q2 labs)
in (match (_89_215) with
| (q2, labs, _89_214) -> begin
(let _186_59 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.ITE), ((hd)::(q1)::(q2)::[])))))
in ((_186_59), (labs), (rs)))
end))
end))
end
| (FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Exists, _, _, _, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Or, _)) -> begin
(fresh_label rs q labs)
end
| (FStar_SMTEncoding_Term.FreeV (_)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Eq, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LT, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LTE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GT, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GTE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (_), _)) -> begin
(fresh_label rs q labs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Add, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Sub, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Div, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mul, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Minus, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mod, _)) -> begin
(FStar_All.failwith "Impossible: non-propositional term")
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, _)) -> begin
(FStar_All.failwith "Impossible: arity mismatch")
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body) -> begin
(

let _89_337 = (aux rs body labs)
in (match (_89_337) with
| (body, labs, rs) -> begin
(let _186_60 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), (sorts), (body)))))
in ((_186_60), (labs), (rs)))
end))
end))
in (aux [] q [])))
end)))


let detail_errors : labels  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  ((FStar_SMTEncoding_Z3.unsat_core, (FStar_SMTEncoding_Term.error_labels * Prims.bool)) FStar_Util.either * Prims.int))  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun all_labels potential_errors askZ3 -> (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let elim = (fun labs -> (

let _89_344 = (FStar_Util.incr ctr)
in (let _186_83 = (let _186_76 = (let _186_75 = (let _186_74 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _186_74))
in (Prims.strcat "DETAILING ERRORS" _186_75))
in FStar_SMTEncoding_Term.Echo (_186_76))
in (let _186_82 = (FStar_All.pipe_right labs (FStar_List.map (fun _89_351 -> (match (_89_351) with
| (l, _89_348, _89_350) -> begin
(let _186_81 = (let _186_80 = (let _186_79 = (let _186_78 = (FStar_SMTEncoding_Term.mkFreeV l)
in ((_186_78), (FStar_SMTEncoding_Term.mkTrue)))
in (FStar_SMTEncoding_Term.mkEq _186_79))
in ((_186_80), (Some ("Disabling label")), (Some ((Prims.strcat "disable_label_" (Prims.fst l))))))
in FStar_SMTEncoding_Term.Assume (_186_81))
end))))
in (_186_83)::_186_82))))
in (

let print_labs = (fun tag l -> (FStar_All.pipe_right l (FStar_List.iter (fun _89_360 -> (match (_89_360) with
| (l, _89_357, _89_359) -> begin
(FStar_Util.print2 "%s : %s; " tag (Prims.fst l))
end)))))
in (

let minus = (fun l1 l2 -> (FStar_All.pipe_right l1 (FStar_List.filter (fun _89_372 -> (match (_89_372) with
| ((x, _89_366), _89_369, _89_371) -> begin
(not ((FStar_All.pipe_right l2 (FStar_Util.for_some (fun _89_381 -> (match (_89_381) with
| ((y, _89_375), _89_378, _89_380) -> begin
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

let _89_394 = (let _186_101 = (FStar_All.pipe_left elim (FStar_List.append eliminated (FStar_List.append errors tl)))
in (askZ3 _186_101))
in (match (_89_394) with
| (result, _89_393) -> begin
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
| _89_401 -> begin
(

let _89_409 = (match (active) with
| (_89_403)::[] -> begin
((active), ([]))
end
| _89_406 -> begin
(FStar_Util.first_N ((FStar_List.length active) / (Prims.parse_int "2")) active)
end)
in (match (_89_409) with
| (pfx, sfx) -> begin
(

let _89_413 = (let _186_108 = (elim (FStar_List.append eliminated (FStar_List.append potential_errors sfx)))
in (askZ3 _186_108))
in (match (_89_413) with
| (result, _89_412) -> begin
(match (result) with
| FStar_Util.Inl (_89_415) -> begin
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

let _89_433 = (bisect eliminated potential_errors active)
in (match (_89_433) with
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




