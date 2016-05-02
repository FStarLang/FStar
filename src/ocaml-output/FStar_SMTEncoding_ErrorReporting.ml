
open Prims
# 24 "FStar.SMTEncoding.ErrorReporting.fst"
type fuel_trace_identity =
{source_digest : Prims.string}

# 24 "FStar.SMTEncoding.ErrorReporting.fst"
let is_Mkfuel_trace_identity : fuel_trace_identity  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkfuel_trace_identity"))))

# 29 "FStar.SMTEncoding.ErrorReporting.fst"
type fuel_trace_state =
{identity : fuel_trace_identity; fuels : (Prims.int * Prims.int) Prims.list}

# 29 "FStar.SMTEncoding.ErrorReporting.fst"
let is_Mkfuel_trace_state : fuel_trace_state  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkfuel_trace_state"))))

# 35 "FStar.SMTEncoding.ErrorReporting.fst"
type fuel_trace_status =
| FuelTraceUnavailable
| RecordFuelTrace of (Prims.int * Prims.int) Prims.list
| ReplayFuelTrace of (Prims.string * (Prims.int * Prims.int) Prims.list)

# 36 "FStar.SMTEncoding.ErrorReporting.fst"
let is_FuelTraceUnavailable = (fun _discr_ -> (match (_discr_) with
| FuelTraceUnavailable (_) -> begin
true
end
| _ -> begin
false
end))

# 37 "FStar.SMTEncoding.ErrorReporting.fst"
let is_RecordFuelTrace = (fun _discr_ -> (match (_discr_) with
| RecordFuelTrace (_) -> begin
true
end
| _ -> begin
false
end))

# 38 "FStar.SMTEncoding.ErrorReporting.fst"
let is_ReplayFuelTrace = (fun _discr_ -> (match (_discr_) with
| ReplayFuelTrace (_) -> begin
true
end
| _ -> begin
false
end))

# 37 "FStar.SMTEncoding.ErrorReporting.fst"
let ___RecordFuelTrace____0 = (fun projectee -> (match (projectee) with
| RecordFuelTrace (_82_9) -> begin
_82_9
end))

# 38 "FStar.SMTEncoding.ErrorReporting.fst"
let ___ReplayFuelTrace____0 = (fun projectee -> (match (projectee) with
| ReplayFuelTrace (_82_12) -> begin
_82_12
end))

# 40 "FStar.SMTEncoding.ErrorReporting.fst"
let fuel_trace : fuel_trace_status FStar_ST.ref = (FStar_All.pipe_left FStar_Util.mk_ref FuelTraceUnavailable)

# 42 "FStar.SMTEncoding.ErrorReporting.fst"
let format_fuel_trace_file_name : Prims.string  ->  Prims.string = (fun src_fn -> (let _171_43 = (FStar_Util.format1 "%s.fuel" src_fn)
in (FStar_All.pipe_left FStar_Util.format_value_file_name _171_43)))

# 45 "FStar.SMTEncoding.ErrorReporting.fst"
let compute_transitive_digest : Prims.string  ->  Prims.string Prims.list  ->  Prims.string = (fun src_fn deps -> (
# 47 "FStar.SMTEncoding.ErrorReporting.fst"
let digests = (let _171_48 = (FStar_All.pipe_left (FStar_List.map FStar_Util.digest_of_file) ((src_fn)::[]))
in (FStar_List.append _171_48 deps))
in (
# 48 "FStar.SMTEncoding.ErrorReporting.fst"
let s = (let _171_49 = (FStar_List.sortWith FStar_String.compare digests)
in (FStar_All.pipe_left (FStar_Util.concat_l ",") _171_49))
in (FStar_Util.digest_of_string s))))

# 51 "FStar.SMTEncoding.ErrorReporting.fst"
let initialize_fuel_trace : Prims.string  ->  Prims.string Prims.list  ->  Prims.unit = (fun src_fn deps -> if (FStar_ST.read FStar_Options.explicit_deps) then begin
(FStar_ST.op_Colon_Equals fuel_trace FuelTraceUnavailable)
end else begin
(
# 56 "FStar.SMTEncoding.ErrorReporting.fst"
let val_fn = (format_fuel_trace_file_name src_fn)
in (match ((FStar_Util.load_value_from_file val_fn)) with
| Some (state) -> begin
(
# 59 "FStar.SMTEncoding.ErrorReporting.fst"
let digest = (compute_transitive_digest src_fn deps)
in if (state.identity.source_digest = digest) then begin
(FStar_ST.op_Colon_Equals fuel_trace (ReplayFuelTrace ((val_fn, state.fuels))))
end else begin
(FStar_ST.op_Colon_Equals fuel_trace (RecordFuelTrace ([])))
end)
end
| None -> begin
(FStar_ST.op_Colon_Equals fuel_trace (RecordFuelTrace ([])))
end))
end)

# 68 "FStar.SMTEncoding.ErrorReporting.fst"
let finalize_fuel_trace : Prims.string  ->  Prims.string Prims.list  ->  Prims.unit = (fun src_fn deps -> (
# 69 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_37 = (match ((FStar_ST.read fuel_trace)) with
| (ReplayFuelTrace (_)) | (FuelTraceUnavailable) | (RecordFuelTrace ([])) -> begin
()
end
| RecordFuelTrace (l) -> begin
(
# 78 "FStar.SMTEncoding.ErrorReporting.fst"
let val_fn = (format_fuel_trace_file_name src_fn)
in (
# 79 "FStar.SMTEncoding.ErrorReporting.fst"
let state = (let _171_59 = (let _171_58 = (compute_transitive_digest src_fn deps)
in {source_digest = _171_58})
in {identity = _171_59; fuels = l})
in (FStar_Util.save_value_to_file val_fn state)))
end)
in (FStar_ST.op_Colon_Equals fuel_trace FuelTraceUnavailable)))

# 90 "FStar.SMTEncoding.ErrorReporting.fst"
type label =
FStar_SMTEncoding_Term.error_label

# 91 "FStar.SMTEncoding.ErrorReporting.fst"
type labels =
FStar_SMTEncoding_Term.error_labels

# 92 "FStar.SMTEncoding.ErrorReporting.fst"
let sort_labels : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun l -> (FStar_List.sortWith (fun _82_45 _82_51 -> (match ((_82_45, _82_51)) with
| ((_82_41, _82_43, r1), (_82_47, _82_49, r2)) -> begin
(FStar_Range.compare r1 r2)
end)) l))

# 93 "FStar.SMTEncoding.ErrorReporting.fst"
let remove_dups : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list = (fun l -> (FStar_Util.remove_dups (fun _82_57 _82_62 -> (match ((_82_57, _82_62)) with
| ((_82_54, m1, r1), (_82_59, m2, r2)) -> begin
((r1 = r2) && (m1 = m2))
end)) l))

# 94 "FStar.SMTEncoding.ErrorReporting.fst"
type msg =
(Prims.string * FStar_Range.range)

# 95 "FStar.SMTEncoding.ErrorReporting.fst"
type ranges =
(Prims.string Prims.option * FStar_Range.range) Prims.list

# 97 "FStar.SMTEncoding.ErrorReporting.fst"
let fresh_label : ranges  ->  FStar_SMTEncoding_Term.term  ->  labels  ->  (FStar_SMTEncoding_Term.term * labels) = (
# 98 "FStar.SMTEncoding.ErrorReporting.fst"
let ctr = (FStar_ST.alloc 0)
in (fun rs t labs -> (
# 100 "FStar.SMTEncoding.ErrorReporting.fst"
let l = (
# 100 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_67 = (FStar_Util.incr ctr)
in (let _171_75 = (let _171_74 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _171_74))
in (FStar_Util.format1 "label_%s" _171_75)))
in (
# 101 "FStar.SMTEncoding.ErrorReporting.fst"
let lvar = (l, FStar_SMTEncoding_Term.Bool_sort)
in (
# 102 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_87 = (match (rs) with
| [] -> begin
(t.FStar_SMTEncoding_Term.hash, FStar_Range.dummyRange)
end
| (Some (reason), r)::_82_73 -> begin
(reason, r)
end
| (None, r)::_82_80 -> begin
("failed to prove a pre-condition", r)
end)
in (match (_82_87) with
| (message, range) -> begin
(
# 106 "FStar.SMTEncoding.ErrorReporting.fst"
let label = (lvar, message, range)
in (
# 107 "FStar.SMTEncoding.ErrorReporting.fst"
let lterm = (FStar_SMTEncoding_Term.mkFreeV lvar)
in (
# 108 "FStar.SMTEncoding.ErrorReporting.fst"
let lt = (FStar_SMTEncoding_Term.mkOr (lterm, t))
in (lt, (label)::labs))))
end))))))

# 118 "FStar.SMTEncoding.ErrorReporting.fst"
let label_goals : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Int64.int64  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * labels * ranges) = (fun use_env_msg r q -> (
# 119 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_99 = (match (use_env_msg) with
| None -> begin
(false, "")
end
| Some (f) -> begin
(let _171_91 = (f ())
in (true, _171_91))
end)
in (match (_82_99) with
| (flag, msg_prefix) -> begin
(
# 122 "FStar.SMTEncoding.ErrorReporting.fst"
let fresh_label = (fun rs t labs -> (
# 123 "FStar.SMTEncoding.ErrorReporting.fst"
let rs' = if (not (flag)) then begin
rs
end else begin
(match (rs) with
| (Some (reason), _82_109)::_82_105 -> begin
((Some ((Prims.strcat "Failed to verify implicit argument: " reason)), r))::[]
end
| _82_113 -> begin
((Some ("Failed to verify implicit argument"), r))::[]
end)
end
in (
# 128 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_117 = (fresh_label rs' t labs)
in (match (_82_117) with
| (lt, labs) -> begin
(lt, labs, rs)
end))))
in (
# 130 "FStar.SMTEncoding.ErrorReporting.fst"
let rec aux = (fun rs q labs -> (match (q.FStar_SMTEncoding_Term.tm) with
| (FStar_SMTEncoding_Term.BoundV (_)) | (FStar_SMTEncoding_Term.Integer (_)) -> begin
(q, labs, rs)
end
| FStar_SMTEncoding_Term.Labeled (_82_129, "push", r) -> begin
(FStar_SMTEncoding_Term.mkTrue, labs, ((None, r))::rs)
end
| FStar_SMTEncoding_Term.Labeled (_82_135, "pop", r) -> begin
(let _171_104 = (FStar_List.tl rs)
in (FStar_SMTEncoding_Term.mkTrue, labs, _171_104))
end
| FStar_SMTEncoding_Term.Labeled (arg, reason, r) -> begin
(
# 142 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_148 = (aux (((Some (reason), r))::rs) arg labs)
in (match (_82_148) with
| (tm, labs, rs) -> begin
(let _171_105 = (FStar_List.tl rs)
in (tm, labs, _171_105))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, lhs::rhs::[]) -> begin
(
# 146 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_158 = (aux rs rhs labs)
in (match (_82_158) with
| (rhs, labs, rs) -> begin
(let _171_106 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]))))
in (_171_106, labs, rs))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(
# 150 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_175 = (FStar_List.fold_left (fun _82_166 c -> (match (_82_166) with
| (rs, cs, labs) -> begin
(
# 151 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_171 = (aux rs c labs)
in (match (_82_171) with
| (c, labs, rs) -> begin
(rs, (c)::cs, labs)
end))
end)) (rs, [], labs) conjuncts)
in (match (_82_175) with
| (rs, conjuncts, labs) -> begin
(let _171_109 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.And, (FStar_List.rev conjuncts)))))
in (_171_109, labs, rs))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, hd::q1::q2::[]) -> begin
(
# 158 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_187 = (aux rs q1 labs)
in (match (_82_187) with
| (q1, labs, _82_186) -> begin
(
# 159 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_192 = (aux rs q2 labs)
in (match (_82_192) with
| (q2, labs, _82_191) -> begin
(let _171_110 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]))))
in (_171_110, labs, rs))
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
# 192 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_314 = (aux rs body labs)
in (match (_82_314) with
| (body, labs, rs) -> begin
(let _171_111 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant ((FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body))))
in (_171_111, labs, rs))
end))
end))
in (aux [] q [])))
end)))

# 206 "FStar.SMTEncoding.ErrorReporting.fst"
let detail_errors : labels  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  (Prims.bool * labels))  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun all_labels potential_errors askZ3 -> (
# 207 "FStar.SMTEncoding.ErrorReporting.fst"
let ctr = (FStar_Util.mk_ref 0)
in (
# 208 "FStar.SMTEncoding.ErrorReporting.fst"
let elim = (fun labs -> (
# 209 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_321 = (FStar_Util.incr ctr)
in (let _171_134 = (let _171_127 = (let _171_126 = (let _171_125 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _171_125))
in (Prims.strcat "DETAILING ERRORS" _171_126))
in FStar_SMTEncoding_Term.Echo (_171_127))
in (let _171_133 = (FStar_All.pipe_right labs (FStar_List.map (fun _82_328 -> (match (_82_328) with
| (l, _82_325, _82_327) -> begin
(let _171_132 = (let _171_131 = (let _171_130 = (let _171_129 = (FStar_SMTEncoding_Term.mkFreeV l)
in (_171_129, FStar_SMTEncoding_Term.mkTrue))
in (FStar_SMTEncoding_Term.mkEq _171_130))
in (_171_131, Some ("Disabling label")))
in FStar_SMTEncoding_Term.Assume (_171_132))
end))))
in (_171_134)::_171_133))))
in (
# 212 "FStar.SMTEncoding.ErrorReporting.fst"
let print_labs = (fun tag l -> (FStar_All.pipe_right l (FStar_List.iter (fun _82_337 -> (match (_82_337) with
| (l, _82_334, _82_336) -> begin
(FStar_Util.print2 "%s : %s; " tag (Prims.fst l))
end)))))
in (
# 214 "FStar.SMTEncoding.ErrorReporting.fst"
let minus = (fun l1 l2 -> (FStar_All.pipe_right l1 (FStar_List.filter (fun _82_349 -> (match (_82_349) with
| ((x, _82_343), _82_346, _82_348) -> begin
(not ((FStar_All.pipe_right l2 (FStar_Util.for_some (fun _82_358 -> (match (_82_358) with
| ((y, _82_352), _82_355, _82_357) -> begin
(x = y)
end))))))
end)))))
in (
# 219 "FStar.SMTEncoding.ErrorReporting.fst"
let rec linear_check = (fun eliminated errors active -> (match (active) with
| [] -> begin
(
# 221 "FStar.SMTEncoding.ErrorReporting.fst"
let labs = (FStar_All.pipe_right errors sort_labels)
in labs)
end
| hd::tl -> begin
(
# 225 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_371 = (let _171_152 = (FStar_All.pipe_left elim (FStar_List.append (FStar_List.append eliminated errors) tl))
in (askZ3 _171_152))
in (match (_82_371) with
| (ok, _82_370) -> begin
if ok then begin
(linear_check ((hd)::eliminated) errors tl)
end else begin
(linear_check eliminated ((hd)::errors) tl)
end
end))
end))
in (
# 231 "FStar.SMTEncoding.ErrorReporting.fst"
let rec bisect = (fun eliminated potential_errors active -> (match (active) with
| [] -> begin
(eliminated, potential_errors)
end
| _82_378 -> begin
(
# 235 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_386 = (match (active) with
| _82_380::[] -> begin
(active, [])
end
| _82_383 -> begin
(FStar_Util.first_N ((FStar_List.length active) / 2) active)
end)
in (match (_82_386) with
| (pfx, sfx) -> begin
(
# 238 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_389 = (let _171_159 = (elim (FStar_List.append (FStar_List.append eliminated potential_errors) sfx))
in (askZ3 _171_159))
in (match (_82_389) with
| (ok, pfx_subset) -> begin
if ok then begin
(bisect (FStar_List.append eliminated pfx) potential_errors sfx)
end else begin
(match (pfx_subset) with
| [] -> begin
(bisect eliminated (FStar_List.append potential_errors pfx) sfx)
end
| _82_392 -> begin
(
# 247 "FStar.SMTEncoding.ErrorReporting.fst"
let potential_errors = (FStar_List.append potential_errors pfx_subset)
in (
# 248 "FStar.SMTEncoding.ErrorReporting.fst"
let pfx_active = (minus pfx pfx_subset)
in (bisect eliminated potential_errors (FStar_List.append pfx_active sfx))))
end)
end
end))
end))
end))
in (
# 253 "FStar.SMTEncoding.ErrorReporting.fst"
let rec until_fixpoint = (fun eliminated potential_errors active -> (
# 254 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_401 = (bisect eliminated potential_errors active)
in (match (_82_401) with
| (eliminated', potential_errors) -> begin
if (FStar_Util.physical_equality eliminated eliminated') then begin
(linear_check eliminated [] potential_errors)
end else begin
(until_fixpoint eliminated' [] potential_errors)
end
end)))
in (
# 259 "FStar.SMTEncoding.ErrorReporting.fst"
let active = (minus all_labels potential_errors)
in (until_fixpoint [] potential_errors active))))))))))

# 264 "FStar.SMTEncoding.ErrorReporting.fst"
let askZ3_and_report_errors : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun env use_fresh_z3_context all_labels prefix query suffix -> (
# 265 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_409 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (
# 266 "FStar.SMTEncoding.ErrorReporting.fst"
let minimum_workable_fuel = (FStar_Util.mk_ref None)
in (
# 267 "FStar.SMTEncoding.ErrorReporting.fst"
let set_minimum_workable_fuel = (fun f _82_1 -> (match (_82_1) with
| [] -> begin
()
end
| errs -> begin
(match ((FStar_ST.read minimum_workable_fuel)) with
| Some (_82_418) -> begin
()
end
| None -> begin
(FStar_ST.op_Colon_Equals minimum_workable_fuel (Some ((f, errs))))
end)
end))
in (
# 273 "FStar.SMTEncoding.ErrorReporting.fst"
let with_fuel = (fun label_assumptions p _82_426 -> (match (_82_426) with
| (n, i) -> begin
(let _171_208 = (let _171_207 = (let _171_206 = (let _171_205 = (let _171_190 = (let _171_189 = (FStar_Util.string_of_int n)
in (let _171_188 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _171_189 _171_188)))
in FStar_SMTEncoding_Term.Caption (_171_190))
in (let _171_204 = (let _171_203 = (let _171_195 = (let _171_194 = (let _171_193 = (let _171_192 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (let _171_191 = (FStar_SMTEncoding_Term.n_fuel n)
in (_171_192, _171_191)))
in (FStar_SMTEncoding_Term.mkEq _171_193))
in (_171_194, None))
in FStar_SMTEncoding_Term.Assume (_171_195))
in (let _171_202 = (let _171_201 = (let _171_200 = (let _171_199 = (let _171_198 = (let _171_197 = (FStar_SMTEncoding_Term.mkApp ("MaxIFuel", []))
in (let _171_196 = (FStar_SMTEncoding_Term.n_fuel i)
in (_171_197, _171_196)))
in (FStar_SMTEncoding_Term.mkEq _171_198))
in (_171_199, None))
in FStar_SMTEncoding_Term.Assume (_171_200))
in (_171_201)::(p)::[])
in (_171_203)::_171_202))
in (_171_205)::_171_204))
in (FStar_List.append _171_206 label_assumptions))
in (FStar_List.append _171_207 ((FStar_SMTEncoding_Term.CheckSat)::[])))
in (FStar_List.append _171_208 suffix))
end))
in (
# 282 "FStar.SMTEncoding.ErrorReporting.fst"
let check = (fun p -> (
# 283 "FStar.SMTEncoding.ErrorReporting.fst"
let cached_config = (match ((FStar_ST.read fuel_trace)) with
| ReplayFuelTrace (fname, hd::tl) -> begin
(
# 286 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_437 = hd
in (match (_82_437) with
| (fuel, ifuel) -> begin
(
# 287 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_438 = (FStar_ST.op_Colon_Equals fuel_trace (ReplayFuelTrace ((fname, tl))))
in Some ((fname, fuel, ifuel)))
end))
end
| _82_441 -> begin
None
end)
in (
# 292 "FStar.SMTEncoding.ErrorReporting.fst"
let initial_config = (match (cached_config) with
| Some (_82_444, fuel, ifuel) -> begin
(fuel, ifuel)
end
| None -> begin
(let _171_212 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _171_211 = (FStar_ST.read FStar_Options.initial_ifuel)
in (_171_212, _171_211)))
end)
in (
# 297 "FStar.SMTEncoding.ErrorReporting.fst"
let alt_configs = (match (cached_config) with
| Some (_82_452) -> begin
[]
end
| None -> begin
(let _171_231 = (let _171_230 = if ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel)) then begin
(let _171_215 = (let _171_214 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _171_213 = (FStar_ST.read FStar_Options.max_ifuel)
in (_171_214, _171_213)))
in (_171_215)::[])
end else begin
[]
end
in (let _171_229 = (let _171_228 = if (((FStar_ST.read FStar_Options.max_fuel) / 2) > (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _171_218 = (let _171_217 = ((FStar_ST.read FStar_Options.max_fuel) / 2)
in (let _171_216 = (FStar_ST.read FStar_Options.max_ifuel)
in (_171_217, _171_216)))
in (_171_218)::[])
end else begin
[]
end
in (let _171_227 = (let _171_226 = if (((FStar_ST.read FStar_Options.max_fuel) > (FStar_ST.read FStar_Options.initial_fuel)) && ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel))) then begin
(let _171_221 = (let _171_220 = (FStar_ST.read FStar_Options.max_fuel)
in (let _171_219 = (FStar_ST.read FStar_Options.max_ifuel)
in (_171_220, _171_219)))
in (_171_221)::[])
end else begin
[]
end
in (let _171_225 = (let _171_224 = if ((FStar_ST.read FStar_Options.min_fuel) < (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _171_223 = (let _171_222 = (FStar_ST.read FStar_Options.min_fuel)
in (_171_222, 1))
in (_171_223)::[])
end else begin
[]
end
in (_171_224)::[])
in (_171_226)::_171_225))
in (_171_228)::_171_227))
in (_171_230)::_171_229))
in (FStar_List.flatten _171_231))
end)
in (
# 306 "FStar.SMTEncoding.ErrorReporting.fst"
let report = (fun p errs -> (
# 307 "FStar.SMTEncoding.ErrorReporting.fst"
let errs = if ((FStar_ST.read FStar_Options.detail_errors) && ((FStar_ST.read FStar_Options.n_cores) = 1)) then begin
(
# 308 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_466 = (match ((FStar_ST.read minimum_workable_fuel)) with
| Some (f, errs) -> begin
(f, errs)
end
| None -> begin
(let _171_237 = (let _171_236 = (FStar_ST.read FStar_Options.min_fuel)
in (_171_236, 1))
in (_171_237, errs))
end)
in (match (_82_466) with
| (min_fuel, potential_errors) -> begin
(
# 311 "FStar.SMTEncoding.ErrorReporting.fst"
let ask_z3 = (fun label_assumptions -> (
# 312 "FStar.SMTEncoding.ErrorReporting.fst"
let res = (FStar_Util.mk_ref None)
in (
# 313 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_471 = (let _171_241 = (with_fuel label_assumptions p min_fuel)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _171_241 (fun r -> (FStar_ST.op_Colon_Equals res (Some (r))))))
in (let _171_242 = (FStar_ST.read res)
in (FStar_Option.get _171_242)))))
in (detail_errors all_labels errs ask_z3))
end))
end else begin
errs
end
in (
# 318 "FStar.SMTEncoding.ErrorReporting.fst"
let errs = (match (errs) with
| [] -> begin
((("", FStar_SMTEncoding_Term.Term_sort), "Unknown assertion failed", FStar_Range.dummyRange))::[]
end
| _82_476 -> begin
errs
end)
in (
# 321 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_485 = (match ((FStar_ST.read fuel_trace)) with
| ReplayFuelTrace (fname, _82_480) -> begin
(let _171_244 = (let _171_243 = (FStar_Util.format1 "Query failed while replaying cached fuel trace; please delete the related file (%s) and try again" fname)
in FStar_Util.Failure (_171_243))
in (FStar_All.pipe_left Prims.raise _171_244))
end
| _82_484 -> begin
(FStar_ST.op_Colon_Equals fuel_trace FuelTraceUnavailable)
end)
in (
# 327 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_487 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _171_250 = (let _171_245 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _171_245))
in (let _171_249 = (let _171_246 = (FStar_ST.read FStar_Options.max_fuel)
in (FStar_All.pipe_right _171_246 FStar_Util.string_of_int))
in (let _171_248 = (let _171_247 = (FStar_ST.read FStar_Options.max_ifuel)
in (FStar_All.pipe_right _171_247 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _171_250 _171_249 _171_248))))
end else begin
()
end
in (
# 332 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_494 = (let _171_252 = (FStar_All.pipe_right errs (FStar_List.map (fun _82_493 -> (match (_82_493) with
| (_82_490, x, y) -> begin
(x, y)
end))))
in (FStar_TypeChecker_Errors.add_errors env _171_252))
in if (FStar_ST.read FStar_Options.detail_errors) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Detailed error report follows\n")))
end else begin
()
end))))))
in (
# 336 "FStar.SMTEncoding.ErrorReporting.fst"
let rec try_alt_configs = (fun prev_f p errs cfgs -> (
# 337 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_502 = (set_minimum_workable_fuel prev_f errs)
in (match (cfgs) with
| [] -> begin
(report p errs)
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _171_265 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _171_265 (cb mi p [])))
end
| _82_509 -> begin
(
# 343 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_510 = (set_minimum_workable_fuel prev_f errs)
in (report p errs))
end)
end
| mi::tl -> begin
(let _171_267 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _171_267 (fun _82_517 -> (match (_82_517) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _82_520 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end)))
and cb = (fun _82_523 p alt _82_528 -> (match ((_82_523, _82_528)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
(
# 356 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_535 = (match ((FStar_ST.read fuel_trace)) with
| (ReplayFuelTrace (_)) | (FuelTraceUnavailable) -> begin
()
end
| RecordFuelTrace (l) -> begin
(FStar_ST.op_Colon_Equals fuel_trace (RecordFuelTrace ((FStar_List.append l (((prev_fuel, prev_ifuel))::[])))))
end)
in if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _171_275 = (let _171_272 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _171_272))
in (let _171_274 = (FStar_Util.string_of_int prev_fuel)
in (let _171_273 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print4 "(%s) Query succeeded with fuel %s and ifuel %s%s\n" _171_275 _171_274 _171_273 (match (cached_config) with
| Some (_82_538) -> begin
" (cached)"
end
| None -> begin
""
end)))))
end else begin
()
end)
end else begin
(try_alt_configs (prev_fuel, prev_ifuel) p errs alt)
end
end))
in (let _171_276 = (with_fuel [] p initial_config)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _171_276 (cb initial_config p alt_configs)))))))))
in (
# 380 "FStar.SMTEncoding.ErrorReporting.fst"
let process_query = (fun q -> if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(
# 382 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_545 = (let _171_282 = (FStar_ST.read FStar_Options.split_cases)
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _171_282 q))
in (match (_82_545) with
| (b, cb) -> begin
if b then begin
(FStar_SMTEncoding_SplitQueryCases.handle_query cb check)
end else begin
(check q)
end
end))
end else begin
(check q)
end)
in if (FStar_ST.read FStar_Options.admit_smt_queries) then begin
()
end else begin
(process_query query)
end)))))))




