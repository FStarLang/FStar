
open Prims

type label =
FStar_SMTEncoding_Term.error_label


type labels =
FStar_SMTEncoding_Term.error_labels


let sort_labels : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun l -> (FStar_List.sortWith (fun _82_7 _82_13 -> (match ((_82_7, _82_13)) with
| ((_82_3, _82_5, r1), (_82_9, _82_11, r2)) -> begin
(FStar_Range.compare r1 r2)
end)) l))


let remove_dups : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list = (fun l -> (FStar_Util.remove_dups (fun _82_19 _82_24 -> (match ((_82_19, _82_24)) with
| ((_82_16, m1, r1), (_82_21, m2, r2)) -> begin
((r1 = r2) && (m1 = m2))
end)) l))


type msg =
(Prims.string * FStar_Range.range)


type ranges =
(Prims.string Prims.option * FStar_Range.range) Prims.list


let fresh_label : ranges  ->  FStar_SMTEncoding_Term.term  ->  labels  ->  (FStar_SMTEncoding_Term.term * labels) = (

let ctr = (FStar_ST.alloc 0)
in (fun rs t labs -> (

let l = (

let _82_29 = (FStar_Util.incr ctr)
in (let _172_16 = (let _172_15 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _172_15))
in (FStar_Util.format1 "label_%s" _172_16)))
in (

let lvar = (l, FStar_SMTEncoding_Term.Bool_sort)
in (

let _82_49 = (match (rs) with
| [] -> begin
(t.FStar_SMTEncoding_Term.hash, FStar_Range.dummyRange)
end
| ((Some (reason), r))::_82_35 -> begin
(reason, r)
end
| ((None, r))::_82_42 -> begin
("failed to prove a pre-condition", r)
end)
in (match (_82_49) with
| (message, range) -> begin
(

let label = (lvar, message, range)
in (

let lterm = (FStar_SMTEncoding_Term.mkFreeV lvar)
in (

let lt = (FStar_SMTEncoding_Term.mkOr (lterm, t))
in (lt, (label)::labs))))
end))))))


let label_goals : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Int64.int64  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * labels * ranges) = (fun use_env_msg r q -> (

let _82_61 = (match (use_env_msg) with
| None -> begin
(false, "")
end
| Some (f) -> begin
(let _172_32 = (f ())
in (true, _172_32))
end)
in (match (_82_61) with
| (flag, msg_prefix) -> begin
(

let fresh_label = (fun rs t labs -> (

let rs' = if (not (flag)) then begin
rs
end else begin
(match (rs) with
| ((Some (reason), _82_71))::_82_67 -> begin
((Some ((Prims.strcat "Failed to verify implicit argument: " reason)), r))::[]
end
| _82_75 -> begin
((Some ("Failed to verify implicit argument"), r))::[]
end)
end
in (

let _82_79 = (fresh_label rs' t labs)
in (match (_82_79) with
| (lt, labs) -> begin
(lt, labs, rs)
end))))
in (

let rec aux = (fun rs q labs -> (match (q.FStar_SMTEncoding_Term.tm) with
| (FStar_SMTEncoding_Term.BoundV (_)) | (FStar_SMTEncoding_Term.Integer (_)) -> begin
(q, labs, rs)
end
| FStar_SMTEncoding_Term.Labeled (_82_91, "push", r) -> begin
(FStar_SMTEncoding_Term.mkTrue, labs, ((None, r))::rs)
end
| FStar_SMTEncoding_Term.Labeled (_82_97, "pop", r) -> begin
(let _172_45 = (FStar_List.tl rs)
in (FStar_SMTEncoding_Term.mkTrue, labs, _172_45))
end
| FStar_SMTEncoding_Term.Labeled (arg, reason, r) -> begin
(

let _82_110 = (aux (((Some (reason), r))::rs) arg labs)
in (match (_82_110) with
| (tm, labs, rs) -> begin
(let _172_46 = (FStar_List.tl rs)
in (tm, labs, _172_46))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]) -> begin
(

let _82_120 = (aux rs rhs labs)
in (match (_82_120) with
| (rhs, labs, rs) -> begin
(

let _82_178 = (match (lhs.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(

let _82_169 = (FStar_Util.fold_map (fun _82_127 tm -> (match (_82_127) with
| (labs, rs) -> begin
(match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.hash = _82_133; FStar_SMTEncoding_Term.freevars = _82_131})::[])::[], iopt, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r)::[]); FStar_SMTEncoding_Term.hash = _82_148; FStar_SMTEncoding_Term.freevars = _82_146}) -> begin
(

let _82_161 = (aux rs r labs)
in (match (_82_161) with
| (r, labs, rs) -> begin
(

let q = (let _172_51 = (let _172_50 = (let _172_49 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.Iff, (l)::(r)::[]))))
in (FStar_SMTEncoding_Term.Forall, ((p)::[])::[], Some (0), sorts, _172_49))
in FStar_SMTEncoding_Term.Quant (_172_50))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk _172_51))
in ((labs, rs), q))
end))
end
| _82_164 -> begin
((labs, rs), tm)
end)
end)) (labs, rs) conjuncts)
in (match (_82_169) with
| ((labs, rs), conjuncts) -> begin
(

let tm = (FStar_List.fold_right (fun conjunct out -> (FStar_SMTEncoding_Term.mkAnd (out, conjunct))) conjuncts FStar_SMTEncoding_Term.mkTrue)
in (tm, labs, rs))
end))
end
| _82_174 -> begin
(lhs, labs, rs)
end)
in (match (_82_178) with
| (lhs, labs, rs) -> begin
(let _172_54 = (FStar_SMTEncoding_Term.mkImp (lhs, rhs))
in (_172_54, labs, rs))
end))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(

let _82_195 = (FStar_List.fold_left (fun _82_186 c -> (match (_82_186) with
| (rs, cs, labs) -> begin
(

let _82_191 = (aux rs c labs)
in (match (_82_191) with
| (c, labs, rs) -> begin
(rs, (c)::cs, labs)
end))
end)) (rs, [], labs) conjuncts)
in (match (_82_195) with
| (rs, conjuncts, labs) -> begin
(

let tm = (FStar_List.fold_left (fun out conjunct -> (FStar_SMTEncoding_Term.mkAnd (out, conjunct))) FStar_SMTEncoding_Term.mkTrue conjuncts)
in (tm, labs, rs))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]) -> begin
(

let _82_210 = (aux rs q1 labs)
in (match (_82_210) with
| (q1, labs, _82_209) -> begin
(

let _82_215 = (aux rs q2 labs)
in (match (_82_215) with
| (q2, labs, _82_214) -> begin
(let _172_59 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]))))
in (_172_59, labs, rs))
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

let _82_337 = (aux rs body labs)
in (match (_82_337) with
| (body, labs, rs) -> begin
(let _172_60 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant ((FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body))))
in (_172_60, labs, rs))
end))
end))
in (aux [] q [])))
end)))


let detail_errors : labels  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  ((FStar_SMTEncoding_Z3.unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either * Prims.int))  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun all_labels potential_errors askZ3 -> (

let ctr = (FStar_Util.mk_ref 0)
in (

let elim = (fun labs -> (

let _82_344 = (FStar_Util.incr ctr)
in (let _172_83 = (let _172_76 = (let _172_75 = (let _172_74 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _172_74))
in (Prims.strcat "DETAILING ERRORS" _172_75))
in FStar_SMTEncoding_Term.Echo (_172_76))
in (let _172_82 = (FStar_All.pipe_right labs (FStar_List.map (fun _82_351 -> (match (_82_351) with
| (l, _82_348, _82_350) -> begin
(let _172_81 = (let _172_80 = (let _172_79 = (let _172_78 = (FStar_SMTEncoding_Term.mkFreeV l)
in (_172_78, FStar_SMTEncoding_Term.mkTrue))
in (FStar_SMTEncoding_Term.mkEq _172_79))
in (_172_80, Some ("Disabling label"), Some ((Prims.strcat "disable_label_" (Prims.fst l)))))
in FStar_SMTEncoding_Term.Assume (_172_81))
end))))
in (_172_83)::_172_82))))
in (

let print_labs = (fun tag l -> (FStar_All.pipe_right l (FStar_List.iter (fun _82_360 -> (match (_82_360) with
| (l, _82_357, _82_359) -> begin
(FStar_Util.print2 "%s : %s; " tag (Prims.fst l))
end)))))
in (

let minus = (fun l1 l2 -> (FStar_All.pipe_right l1 (FStar_List.filter (fun _82_372 -> (match (_82_372) with
| ((x, _82_366), _82_369, _82_371) -> begin
(not ((FStar_All.pipe_right l2 (FStar_Util.for_some (fun _82_381 -> (match (_82_381) with
| ((y, _82_375), _82_378, _82_380) -> begin
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

let _82_394 = (let _172_101 = (FStar_All.pipe_left elim (FStar_List.append (FStar_List.append eliminated errors) tl))
in (askZ3 _172_101))
in (match (_82_394) with
| (result, _82_393) -> begin
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
(eliminated, potential_errors)
end
| _82_401 -> begin
(

let _82_409 = (match (active) with
| (_82_403)::[] -> begin
(active, [])
end
| _82_406 -> begin
(FStar_Util.first_N ((FStar_List.length active) / 2) active)
end)
in (match (_82_409) with
| (pfx, sfx) -> begin
(

let _82_413 = (let _172_108 = (elim (FStar_List.append (FStar_List.append eliminated potential_errors) sfx))
in (askZ3 _172_108))
in (match (_82_413) with
| (result, _82_412) -> begin
(match (result) with
| FStar_Util.Inl (_82_415) -> begin
(bisect (FStar_List.append eliminated pfx) potential_errors sfx)
end
| FStar_Util.Inr ([]) -> begin
(bisect eliminated (FStar_List.append potential_errors pfx) sfx)
end
| FStar_Util.Inr (pfx_subset) -> begin
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

let _82_429 = (bisect eliminated potential_errors active)
in (match (_82_429) with
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




