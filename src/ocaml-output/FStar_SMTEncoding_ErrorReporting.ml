
open Prims

type label =
FStar_SMTEncoding_Term.error_label


type labels =
FStar_SMTEncoding_Term.error_labels


let sort_labels : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun l -> (FStar_List.sortWith (fun _86_7 _86_13 -> (match (((_86_7), (_86_13))) with
| ((_86_3, _86_5, r1), (_86_9, _86_11, r2)) -> begin
(FStar_Range.compare r1 r2)
end)) l))


let remove_dups : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list = (fun l -> (FStar_Util.remove_dups (fun _86_19 _86_24 -> (match (((_86_19), (_86_24))) with
| ((_86_16, m1, r1), (_86_21, m2, r2)) -> begin
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

let _86_29 = (FStar_Util.incr ctr)
in (let _180_16 = (let _180_15 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _180_15))
in (FStar_Util.format1 "label_%s" _180_16)))
in (

let lvar = ((l), (FStar_SMTEncoding_Term.Bool_sort))
in (

let _86_49 = (match (rs) with
| [] -> begin
if (FStar_Options.debug_any ()) then begin
((t.FStar_SMTEncoding_Term.hash), (FStar_Range.dummyRange))
end else begin
(("Z3 provided a counterexample, but, unfortunately, F* could not translate it back to something meaningful"), (FStar_Range.dummyRange))
end
end
| ((Some (reason), r))::_86_35 -> begin
((reason), (r))
end
| ((None, r))::_86_42 -> begin
(("failed to prove a pre-condition"), (r))
end)
in (match (_86_49) with
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

let _86_61 = (match (use_env_msg) with
| None -> begin
((false), (""))
end
| Some (f) -> begin
(let _180_32 = (f ())
in ((true), (_180_32)))
end)
in (match (_86_61) with
| (flag, msg_prefix) -> begin
(

let fresh_label = (fun rs t labs -> (

let rs' = if (not (flag)) then begin
rs
end else begin
(match (rs) with
| ((Some (reason), _86_71))::_86_67 -> begin
(((Some ((Prims.strcat "Failed to verify implicit argument: " reason))), (r)))::[]
end
| _86_75 -> begin
(((Some ("Failed to verify implicit argument")), (r)))::[]
end)
end
in (

let _86_79 = (fresh_label rs' t labs)
in (match (_86_79) with
| (lt, labs) -> begin
((lt), (labs), (rs))
end))))
in (

let rec aux = (fun rs q labs -> (match (q.FStar_SMTEncoding_Term.tm) with
| (FStar_SMTEncoding_Term.BoundV (_)) | (FStar_SMTEncoding_Term.Integer (_)) -> begin
((q), (labs), (rs))
end
| FStar_SMTEncoding_Term.Labeled (_86_91, "push", r) -> begin
((FStar_SMTEncoding_Term.mkTrue), (labs), ((((None), (r)))::rs))
end
| FStar_SMTEncoding_Term.Labeled (_86_97, "pop", r) -> begin
(let _180_45 = (FStar_List.tl rs)
in ((FStar_SMTEncoding_Term.mkTrue), (labs), (_180_45)))
end
| FStar_SMTEncoding_Term.Labeled (arg, reason, r) -> begin
(

let _86_110 = (aux ((((Some (reason)), (r)))::rs) arg labs)
in (match (_86_110) with
| (tm, labs, rs) -> begin
(let _180_46 = (FStar_List.tl rs)
in ((tm), (labs), (_180_46)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]) -> begin
(

let _86_120 = (aux rs rhs labs)
in (match (_86_120) with
| (rhs, labs, rs) -> begin
(

let _86_178 = (match (lhs.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(

let _86_169 = (FStar_Util.fold_map (fun _86_127 tm -> (match (_86_127) with
| (labs, rs) -> begin
(match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.hash = _86_133; FStar_SMTEncoding_Term.freevars = _86_131})::[])::[], iopt, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r)::[]); FStar_SMTEncoding_Term.hash = _86_148; FStar_SMTEncoding_Term.freevars = _86_146}) -> begin
(

let _86_161 = (aux rs r labs)
in (match (_86_161) with
| (r, labs, rs) -> begin
(

let q = (let _180_51 = (let _180_50 = (let _180_49 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.Iff), ((l)::(r)::[])))))
in ((FStar_SMTEncoding_Term.Forall), (((p)::[])::[]), (Some ((Prims.parse_int "0"))), (sorts), (_180_49)))
in FStar_SMTEncoding_Term.Quant (_180_50))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk _180_51))
in ((((labs), (rs))), (q)))
end))
end
| _86_164 -> begin
((((labs), (rs))), (tm))
end)
end)) ((labs), (rs)) conjuncts)
in (match (_86_169) with
| ((labs, rs), conjuncts) -> begin
(

let tm = (FStar_List.fold_right (fun conjunct out -> (FStar_SMTEncoding_Term.mkAnd ((out), (conjunct)))) conjuncts FStar_SMTEncoding_Term.mkTrue)
in ((tm), (labs), (rs)))
end))
end
| _86_174 -> begin
((lhs), (labs), (rs))
end)
in (match (_86_178) with
| (lhs, labs, rs) -> begin
(let _180_54 = (FStar_SMTEncoding_Term.mkImp ((lhs), (rhs)))
in ((_180_54), (labs), (rs)))
end))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(

let _86_195 = (FStar_List.fold_left (fun _86_186 c -> (match (_86_186) with
| (rs, cs, labs) -> begin
(

let _86_191 = (aux rs c labs)
in (match (_86_191) with
| (c, labs, rs) -> begin
((rs), ((c)::cs), (labs))
end))
end)) ((rs), ([]), (labs)) conjuncts)
in (match (_86_195) with
| (rs, conjuncts, labs) -> begin
(

let tm = (FStar_List.fold_left (fun out conjunct -> (FStar_SMTEncoding_Term.mkAnd ((out), (conjunct)))) FStar_SMTEncoding_Term.mkTrue conjuncts)
in ((tm), (labs), (rs)))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]) -> begin
(

let _86_210 = (aux rs q1 labs)
in (match (_86_210) with
| (q1, labs, _86_209) -> begin
(

let _86_215 = (aux rs q2 labs)
in (match (_86_215) with
| (q2, labs, _86_214) -> begin
(let _180_59 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App (((FStar_SMTEncoding_Term.ITE), ((hd)::(q1)::(q2)::[])))))
in ((_180_59), (labs), (rs)))
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

let _86_337 = (aux rs body labs)
in (match (_86_337) with
| (body, labs, rs) -> begin
(let _180_60 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant (((FStar_SMTEncoding_Term.Forall), (pats), (iopt), (sorts), (body)))))
in ((_180_60), (labs), (rs)))
end))
end))
in (aux [] q [])))
end)))


let detail_errors : labels  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  ((FStar_SMTEncoding_Z3.unsat_core, (FStar_SMTEncoding_Term.error_labels * Prims.bool)) FStar_Util.either * Prims.int))  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun all_labels potential_errors askZ3 -> (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (

let elim = (fun labs -> (

let _86_344 = (FStar_Util.incr ctr)
in (let _180_83 = (let _180_76 = (let _180_75 = (let _180_74 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _180_74))
in (Prims.strcat "DETAILING ERRORS" _180_75))
in FStar_SMTEncoding_Term.Echo (_180_76))
in (let _180_82 = (FStar_All.pipe_right labs (FStar_List.map (fun _86_351 -> (match (_86_351) with
| (l, _86_348, _86_350) -> begin
(let _180_81 = (let _180_80 = (let _180_79 = (let _180_78 = (FStar_SMTEncoding_Term.mkFreeV l)
in ((_180_78), (FStar_SMTEncoding_Term.mkTrue)))
in (FStar_SMTEncoding_Term.mkEq _180_79))
in ((_180_80), (Some ("Disabling label")), (Some ((Prims.strcat "disable_label_" (Prims.fst l))))))
in FStar_SMTEncoding_Term.Assume (_180_81))
end))))
in (_180_83)::_180_82))))
in (

let print_labs = (fun tag l -> (FStar_All.pipe_right l (FStar_List.iter (fun _86_360 -> (match (_86_360) with
| (l, _86_357, _86_359) -> begin
(FStar_Util.print2 "%s : %s; " tag (Prims.fst l))
end)))))
in (

let minus = (fun l1 l2 -> (FStar_All.pipe_right l1 (FStar_List.filter (fun _86_372 -> (match (_86_372) with
| ((x, _86_366), _86_369, _86_371) -> begin
(not ((FStar_All.pipe_right l2 (FStar_Util.for_some (fun _86_381 -> (match (_86_381) with
| ((y, _86_375), _86_378, _86_380) -> begin
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

let _86_394 = (let _180_101 = (FStar_All.pipe_left elim (FStar_List.append eliminated (FStar_List.append errors tl)))
in (askZ3 _180_101))
in (match (_86_394) with
| (result, _86_393) -> begin
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
| _86_401 -> begin
(

let _86_409 = (match (active) with
| (_86_403)::[] -> begin
((active), ([]))
end
| _86_406 -> begin
(FStar_Util.first_N ((FStar_List.length active) / (Prims.parse_int "2")) active)
end)
in (match (_86_409) with
| (pfx, sfx) -> begin
(

let _86_413 = (let _180_108 = (elim (FStar_List.append eliminated (FStar_List.append potential_errors sfx)))
in (askZ3 _180_108))
in (match (_86_413) with
| (result, _86_412) -> begin
(match (result) with
| FStar_Util.Inl (_86_415) -> begin
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

let _86_433 = (bisect eliminated potential_errors active)
in (match (_86_433) with
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




