
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
| ReplayFuelTrace of (Prims.int * Prims.int) Prims.list

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
let initialize_fuel_trace : Prims.string  ->  Prims.unit = (fun src_fn -> (
# 46 "FStar.SMTEncoding.ErrorReporting.fst"
let val_fn = (format_fuel_trace_file_name src_fn)
in (match ((FStar_Util.load_value_from_file val_fn)) with
| Some (state) -> begin
(
# 49 "FStar.SMTEncoding.ErrorReporting.fst"
let digest = (FStar_Util.md5_of_file src_fn)
in if (state.identity.source_digest = digest) then begin
(FStar_ST.op_Colon_Equals fuel_trace (ReplayFuelTrace (state.fuels)))
end else begin
(FStar_ST.op_Colon_Equals fuel_trace (RecordFuelTrace ([])))
end)
end
| None -> begin
(FStar_ST.op_Colon_Equals fuel_trace (RecordFuelTrace ([])))
end)))

# 57 "FStar.SMTEncoding.ErrorReporting.fst"
let finalize_fuel_trace : Prims.string  ->  Prims.unit = (fun src_fn -> (
# 58 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_31 = (match ((FStar_ST.read fuel_trace)) with
| (ReplayFuelTrace (_)) | (FuelTraceUnavailable) | (RecordFuelTrace ([])) -> begin
()
end
| RecordFuelTrace (l) -> begin
(
# 67 "FStar.SMTEncoding.ErrorReporting.fst"
let val_fn = (format_fuel_trace_file_name src_fn)
in (
# 68 "FStar.SMTEncoding.ErrorReporting.fst"
let state = (let _171_49 = (let _171_48 = (FStar_Util.md5_of_file src_fn)
in {source_digest = _171_48})
in {identity = _171_49; fuels = l})
in (FStar_Util.save_value_to_file val_fn state)))
end)
in (FStar_ST.op_Colon_Equals fuel_trace FuelTraceUnavailable)))

# 79 "FStar.SMTEncoding.ErrorReporting.fst"
type label =
FStar_SMTEncoding_Term.error_label

# 80 "FStar.SMTEncoding.ErrorReporting.fst"
type labels =
FStar_SMTEncoding_Term.error_labels

# 81 "FStar.SMTEncoding.ErrorReporting.fst"
let sort_labels : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun l -> (FStar_List.sortWith (fun _82_39 _82_45 -> (match ((_82_39, _82_45)) with
| ((_82_35, _82_37, r1), (_82_41, _82_43, r2)) -> begin
(FStar_Range.compare r1 r2)
end)) l))

# 82 "FStar.SMTEncoding.ErrorReporting.fst"
let remove_dups : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list = (fun l -> (FStar_Util.remove_dups (fun _82_51 _82_56 -> (match ((_82_51, _82_56)) with
| ((_82_48, m1, r1), (_82_53, m2, r2)) -> begin
((r1 = r2) && (m1 = m2))
end)) l))

# 83 "FStar.SMTEncoding.ErrorReporting.fst"
type msg =
(Prims.string * FStar_Range.range)

# 84 "FStar.SMTEncoding.ErrorReporting.fst"
type ranges =
(Prims.string Prims.option * FStar_Range.range) Prims.list

# 86 "FStar.SMTEncoding.ErrorReporting.fst"
let fresh_label : ranges  ->  FStar_SMTEncoding_Term.term  ->  labels  ->  (FStar_SMTEncoding_Term.term * labels) = (
# 87 "FStar.SMTEncoding.ErrorReporting.fst"
let ctr = (FStar_ST.alloc 0)
in (fun rs t labs -> (
# 89 "FStar.SMTEncoding.ErrorReporting.fst"
let l = (
# 89 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_61 = (FStar_Util.incr ctr)
in (let _171_65 = (let _171_64 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _171_64))
in (FStar_Util.format1 "label_%s" _171_65)))
in (
# 90 "FStar.SMTEncoding.ErrorReporting.fst"
let lvar = (l, FStar_SMTEncoding_Term.Bool_sort)
in (
# 91 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_81 = (match (rs) with
| [] -> begin
(t.FStar_SMTEncoding_Term.hash, FStar_Range.dummyRange)
end
| (Some (reason), r)::_82_67 -> begin
(reason, r)
end
| (None, r)::_82_74 -> begin
("failed to prove a pre-condition", r)
end)
in (match (_82_81) with
| (message, range) -> begin
(
# 95 "FStar.SMTEncoding.ErrorReporting.fst"
let label = (lvar, message, range)
in (
# 96 "FStar.SMTEncoding.ErrorReporting.fst"
let lterm = (FStar_SMTEncoding_Term.mkFreeV lvar)
in (
# 97 "FStar.SMTEncoding.ErrorReporting.fst"
let lt = (FStar_SMTEncoding_Term.mkOr (lterm, t))
in (lt, (label)::labs))))
end))))))

# 107 "FStar.SMTEncoding.ErrorReporting.fst"
let label_goals : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Int64.int64  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * labels * ranges) = (fun use_env_msg r q -> (
# 108 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_93 = (match (use_env_msg) with
| None -> begin
(false, "")
end
| Some (f) -> begin
(let _171_81 = (f ())
in (true, _171_81))
end)
in (match (_82_93) with
| (flag, msg_prefix) -> begin
(
# 111 "FStar.SMTEncoding.ErrorReporting.fst"
let fresh_label = (fun rs t labs -> (
# 112 "FStar.SMTEncoding.ErrorReporting.fst"
let rs' = if (not (flag)) then begin
rs
end else begin
(match (rs) with
| (Some (reason), _82_103)::_82_99 -> begin
((Some ((Prims.strcat "Failed to verify implicit argument: " reason)), r))::[]
end
| _82_107 -> begin
((Some ("Failed to verify implicit argument"), r))::[]
end)
end
in (
# 117 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_111 = (fresh_label rs' t labs)
in (match (_82_111) with
| (lt, labs) -> begin
(lt, labs, rs)
end))))
in (
# 119 "FStar.SMTEncoding.ErrorReporting.fst"
let rec aux = (fun rs q labs -> (match (q.FStar_SMTEncoding_Term.tm) with
| (FStar_SMTEncoding_Term.BoundV (_)) | (FStar_SMTEncoding_Term.Integer (_)) -> begin
(q, labs, rs)
end
| FStar_SMTEncoding_Term.Labeled (_82_123, "push", r) -> begin
(FStar_SMTEncoding_Term.mkTrue, labs, ((None, r))::rs)
end
| FStar_SMTEncoding_Term.Labeled (_82_129, "pop", r) -> begin
(let _171_94 = (FStar_List.tl rs)
in (FStar_SMTEncoding_Term.mkTrue, labs, _171_94))
end
| FStar_SMTEncoding_Term.Labeled (arg, reason, r) -> begin
(
# 131 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_142 = (aux (((Some (reason), r))::rs) arg labs)
in (match (_82_142) with
| (tm, labs, rs) -> begin
(let _171_95 = (FStar_List.tl rs)
in (tm, labs, _171_95))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, lhs::rhs::[]) -> begin
(
# 135 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_152 = (aux rs rhs labs)
in (match (_82_152) with
| (rhs, labs, rs) -> begin
(let _171_96 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]))))
in (_171_96, labs, rs))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(
# 139 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_169 = (FStar_List.fold_left (fun _82_160 c -> (match (_82_160) with
| (rs, cs, labs) -> begin
(
# 140 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_165 = (aux rs c labs)
in (match (_82_165) with
| (c, labs, rs) -> begin
(rs, (c)::cs, labs)
end))
end)) (rs, [], labs) conjuncts)
in (match (_82_169) with
| (rs, conjuncts, labs) -> begin
(let _171_99 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.And, (FStar_List.rev conjuncts)))))
in (_171_99, labs, rs))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, hd::q1::q2::[]) -> begin
(
# 147 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_181 = (aux rs q1 labs)
in (match (_82_181) with
| (q1, labs, _82_180) -> begin
(
# 148 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_186 = (aux rs q2 labs)
in (match (_82_186) with
| (q2, labs, _82_185) -> begin
(let _171_100 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]))))
in (_171_100, labs, rs))
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
# 181 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_308 = (aux rs body labs)
in (match (_82_308) with
| (body, labs, rs) -> begin
(let _171_101 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant ((FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body))))
in (_171_101, labs, rs))
end))
end))
in (aux [] q [])))
end)))

# 195 "FStar.SMTEncoding.ErrorReporting.fst"
let detail_errors : labels  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  (Prims.bool * labels))  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun all_labels potential_errors askZ3 -> (
# 196 "FStar.SMTEncoding.ErrorReporting.fst"
let ctr = (FStar_Util.mk_ref 0)
in (
# 197 "FStar.SMTEncoding.ErrorReporting.fst"
let elim = (fun labs -> (
# 198 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_315 = (FStar_Util.incr ctr)
in (let _171_124 = (let _171_117 = (let _171_116 = (let _171_115 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _171_115))
in (Prims.strcat "DETAILING ERRORS" _171_116))
in FStar_SMTEncoding_Term.Echo (_171_117))
in (let _171_123 = (FStar_All.pipe_right labs (FStar_List.map (fun _82_322 -> (match (_82_322) with
| (l, _82_319, _82_321) -> begin
(let _171_122 = (let _171_121 = (let _171_120 = (let _171_119 = (FStar_SMTEncoding_Term.mkFreeV l)
in (_171_119, FStar_SMTEncoding_Term.mkTrue))
in (FStar_SMTEncoding_Term.mkEq _171_120))
in (_171_121, Some ("Disabling label")))
in FStar_SMTEncoding_Term.Assume (_171_122))
end))))
in (_171_124)::_171_123))))
in (
# 201 "FStar.SMTEncoding.ErrorReporting.fst"
let print_labs = (fun tag l -> (FStar_All.pipe_right l (FStar_List.iter (fun _82_331 -> (match (_82_331) with
| (l, _82_328, _82_330) -> begin
(FStar_Util.print2 "%s : %s; " tag (Prims.fst l))
end)))))
in (
# 203 "FStar.SMTEncoding.ErrorReporting.fst"
let minus = (fun l1 l2 -> (FStar_All.pipe_right l1 (FStar_List.filter (fun _82_343 -> (match (_82_343) with
| ((x, _82_337), _82_340, _82_342) -> begin
(not ((FStar_All.pipe_right l2 (FStar_Util.for_some (fun _82_352 -> (match (_82_352) with
| ((y, _82_346), _82_349, _82_351) -> begin
(x = y)
end))))))
end)))))
in (
# 208 "FStar.SMTEncoding.ErrorReporting.fst"
let rec linear_check = (fun eliminated errors active -> (match (active) with
| [] -> begin
(
# 210 "FStar.SMTEncoding.ErrorReporting.fst"
let labs = (FStar_All.pipe_right errors sort_labels)
in labs)
end
| hd::tl -> begin
(
# 214 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_365 = (let _171_142 = (FStar_All.pipe_left elim (FStar_List.append (FStar_List.append eliminated errors) tl))
in (askZ3 _171_142))
in (match (_82_365) with
| (ok, _82_364) -> begin
if ok then begin
(linear_check ((hd)::eliminated) errors tl)
end else begin
(linear_check eliminated ((hd)::errors) tl)
end
end))
end))
in (
# 220 "FStar.SMTEncoding.ErrorReporting.fst"
let rec bisect = (fun eliminated potential_errors active -> (match (active) with
| [] -> begin
(eliminated, potential_errors)
end
| _82_372 -> begin
(
# 224 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_380 = (match (active) with
| _82_374::[] -> begin
(active, [])
end
| _82_377 -> begin
(FStar_Util.first_N ((FStar_List.length active) / 2) active)
end)
in (match (_82_380) with
| (pfx, sfx) -> begin
(
# 227 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_383 = (let _171_149 = (elim (FStar_List.append (FStar_List.append eliminated potential_errors) sfx))
in (askZ3 _171_149))
in (match (_82_383) with
| (ok, pfx_subset) -> begin
if ok then begin
(bisect (FStar_List.append eliminated pfx) potential_errors sfx)
end else begin
(match (pfx_subset) with
| [] -> begin
(bisect eliminated (FStar_List.append potential_errors pfx) sfx)
end
| _82_386 -> begin
(
# 236 "FStar.SMTEncoding.ErrorReporting.fst"
let potential_errors = (FStar_List.append potential_errors pfx_subset)
in (
# 237 "FStar.SMTEncoding.ErrorReporting.fst"
let pfx_active = (minus pfx pfx_subset)
in (bisect eliminated potential_errors (FStar_List.append pfx_active sfx))))
end)
end
end))
end))
end))
in (
# 242 "FStar.SMTEncoding.ErrorReporting.fst"
let rec until_fixpoint = (fun eliminated potential_errors active -> (
# 243 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_395 = (bisect eliminated potential_errors active)
in (match (_82_395) with
| (eliminated', potential_errors) -> begin
if (FStar_Util.physical_equality eliminated eliminated') then begin
(linear_check eliminated [] potential_errors)
end else begin
(until_fixpoint eliminated' [] potential_errors)
end
end)))
in (
# 248 "FStar.SMTEncoding.ErrorReporting.fst"
let active = (minus all_labels potential_errors)
in (until_fixpoint [] potential_errors active))))))))))

# 253 "FStar.SMTEncoding.ErrorReporting.fst"
let askZ3_and_report_errors : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun env use_fresh_z3_context all_labels prefix query suffix -> (
# 254 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_403 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (
# 255 "FStar.SMTEncoding.ErrorReporting.fst"
let minimum_workable_fuel = (FStar_Util.mk_ref None)
in (
# 256 "FStar.SMTEncoding.ErrorReporting.fst"
let set_minimum_workable_fuel = (fun f _82_1 -> (match (_82_1) with
| [] -> begin
()
end
| errs -> begin
(match ((FStar_ST.read minimum_workable_fuel)) with
| Some (_82_412) -> begin
()
end
| None -> begin
(FStar_ST.op_Colon_Equals minimum_workable_fuel (Some ((f, errs))))
end)
end))
in (
# 262 "FStar.SMTEncoding.ErrorReporting.fst"
let with_fuel = (fun label_assumptions p _82_420 -> (match (_82_420) with
| (n, i) -> begin
(let _171_198 = (let _171_197 = (let _171_196 = (let _171_195 = (let _171_180 = (let _171_179 = (FStar_Util.string_of_int n)
in (let _171_178 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _171_179 _171_178)))
in FStar_SMTEncoding_Term.Caption (_171_180))
in (let _171_194 = (let _171_193 = (let _171_185 = (let _171_184 = (let _171_183 = (let _171_182 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (let _171_181 = (FStar_SMTEncoding_Term.n_fuel n)
in (_171_182, _171_181)))
in (FStar_SMTEncoding_Term.mkEq _171_183))
in (_171_184, None))
in FStar_SMTEncoding_Term.Assume (_171_185))
in (let _171_192 = (let _171_191 = (let _171_190 = (let _171_189 = (let _171_188 = (let _171_187 = (FStar_SMTEncoding_Term.mkApp ("MaxIFuel", []))
in (let _171_186 = (FStar_SMTEncoding_Term.n_fuel i)
in (_171_187, _171_186)))
in (FStar_SMTEncoding_Term.mkEq _171_188))
in (_171_189, None))
in FStar_SMTEncoding_Term.Assume (_171_190))
in (_171_191)::(p)::[])
in (_171_193)::_171_192))
in (_171_195)::_171_194))
in (FStar_List.append _171_196 label_assumptions))
in (FStar_List.append _171_197 ((FStar_SMTEncoding_Term.CheckSat)::[])))
in (FStar_List.append _171_198 suffix))
end))
in (
# 271 "FStar.SMTEncoding.ErrorReporting.fst"
let check = (fun p -> (
# 272 "FStar.SMTEncoding.ErrorReporting.fst"
let cached_config = (match ((FStar_ST.read fuel_trace)) with
| ReplayFuelTrace (hd::tl) -> begin
(
# 275 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_429 = hd
in (match (_82_429) with
| (fuel, ifuel) -> begin
(
# 276 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_430 = (FStar_ST.op_Colon_Equals fuel_trace (ReplayFuelTrace (tl)))
in Some ((fuel, ifuel)))
end))
end
| _82_433 -> begin
None
end)
in (
# 281 "FStar.SMTEncoding.ErrorReporting.fst"
let initial_config = (match (cached_config) with
| Some (x) -> begin
x
end
| None -> begin
(let _171_202 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _171_201 = (FStar_ST.read FStar_Options.initial_ifuel)
in (_171_202, _171_201)))
end)
in (
# 286 "FStar.SMTEncoding.ErrorReporting.fst"
let alt_configs = (match (cached_config) with
| Some (_82_440) -> begin
[]
end
| None -> begin
(let _171_221 = (let _171_220 = if ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel)) then begin
(let _171_205 = (let _171_204 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _171_203 = (FStar_ST.read FStar_Options.max_ifuel)
in (_171_204, _171_203)))
in (_171_205)::[])
end else begin
[]
end
in (let _171_219 = (let _171_218 = if (((FStar_ST.read FStar_Options.max_fuel) / 2) > (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _171_208 = (let _171_207 = ((FStar_ST.read FStar_Options.max_fuel) / 2)
in (let _171_206 = (FStar_ST.read FStar_Options.max_ifuel)
in (_171_207, _171_206)))
in (_171_208)::[])
end else begin
[]
end
in (let _171_217 = (let _171_216 = if (((FStar_ST.read FStar_Options.max_fuel) > (FStar_ST.read FStar_Options.initial_fuel)) && ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel))) then begin
(let _171_211 = (let _171_210 = (FStar_ST.read FStar_Options.max_fuel)
in (let _171_209 = (FStar_ST.read FStar_Options.max_ifuel)
in (_171_210, _171_209)))
in (_171_211)::[])
end else begin
[]
end
in (let _171_215 = (let _171_214 = if ((FStar_ST.read FStar_Options.min_fuel) < (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _171_213 = (let _171_212 = (FStar_ST.read FStar_Options.min_fuel)
in (_171_212, 1))
in (_171_213)::[])
end else begin
[]
end
in (_171_214)::[])
in (_171_216)::_171_215))
in (_171_218)::_171_217))
in (_171_220)::_171_219))
in (FStar_List.flatten _171_221))
end)
in (
# 295 "FStar.SMTEncoding.ErrorReporting.fst"
let report = (fun p errs -> (
# 296 "FStar.SMTEncoding.ErrorReporting.fst"
let errs = if ((FStar_ST.read FStar_Options.detail_errors) && ((FStar_ST.read FStar_Options.n_cores) = 1)) then begin
(
# 297 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_454 = (match ((FStar_ST.read minimum_workable_fuel)) with
| Some (f, errs) -> begin
(f, errs)
end
| None -> begin
(let _171_227 = (let _171_226 = (FStar_ST.read FStar_Options.min_fuel)
in (_171_226, 1))
in (_171_227, errs))
end)
in (match (_82_454) with
| (min_fuel, potential_errors) -> begin
(
# 300 "FStar.SMTEncoding.ErrorReporting.fst"
let ask_z3 = (fun label_assumptions -> (
# 301 "FStar.SMTEncoding.ErrorReporting.fst"
let res = (FStar_Util.mk_ref None)
in (
# 302 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_459 = (let _171_231 = (with_fuel label_assumptions p min_fuel)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _171_231 (fun r -> (FStar_ST.op_Colon_Equals res (Some (r))))))
in (let _171_232 = (FStar_ST.read res)
in (FStar_Option.get _171_232)))))
in (detail_errors all_labels errs ask_z3))
end))
end else begin
errs
end
in (
# 307 "FStar.SMTEncoding.ErrorReporting.fst"
let errs = (match (errs) with
| [] -> begin
((("", FStar_SMTEncoding_Term.Term_sort), "Unknown assertion failed", FStar_Range.dummyRange))::[]
end
| _82_464 -> begin
errs
end)
in (
# 310 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_471 = (match ((FStar_ST.read fuel_trace)) with
| ReplayFuelTrace (_82_467) -> begin
(FStar_All.pipe_left Prims.raise (FStar_Util.Failure ("Query should not fail when replaying fuel trace.")))
end
| _82_470 -> begin
(FStar_ST.op_Colon_Equals fuel_trace FuelTraceUnavailable)
end)
in (
# 316 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_473 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _171_238 = (let _171_233 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _171_233))
in (let _171_237 = (let _171_234 = (FStar_ST.read FStar_Options.max_fuel)
in (FStar_All.pipe_right _171_234 FStar_Util.string_of_int))
in (let _171_236 = (let _171_235 = (FStar_ST.read FStar_Options.max_ifuel)
in (FStar_All.pipe_right _171_235 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _171_238 _171_237 _171_236))))
end else begin
()
end
in (
# 321 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_480 = (let _171_240 = (FStar_All.pipe_right errs (FStar_List.map (fun _82_479 -> (match (_82_479) with
| (_82_476, x, y) -> begin
(x, y)
end))))
in (FStar_TypeChecker_Errors.add_errors env _171_240))
in if (FStar_ST.read FStar_Options.detail_errors) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Detailed error report follows\n")))
end else begin
()
end))))))
in (
# 325 "FStar.SMTEncoding.ErrorReporting.fst"
let rec try_alt_configs = (fun prev_f p errs cfgs -> (
# 326 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_488 = (set_minimum_workable_fuel prev_f errs)
in (match (cfgs) with
| [] -> begin
(report p errs)
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _171_253 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _171_253 (cb mi p [])))
end
| _82_495 -> begin
(
# 332 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_496 = (set_minimum_workable_fuel prev_f errs)
in (report p errs))
end)
end
| mi::tl -> begin
(let _171_255 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _171_255 (fun _82_503 -> (match (_82_503) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _82_506 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end)))
and cb = (fun _82_509 p alt _82_514 -> (match ((_82_509, _82_514)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
(
# 345 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_521 = (match ((FStar_ST.read fuel_trace)) with
| (ReplayFuelTrace (_)) | (FuelTraceUnavailable) -> begin
()
end
| RecordFuelTrace (l) -> begin
(FStar_ST.op_Colon_Equals fuel_trace (RecordFuelTrace ((FStar_List.append l (((prev_fuel, prev_ifuel))::[])))))
end)
in if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _171_263 = (let _171_260 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _171_260))
in (let _171_262 = (FStar_Util.string_of_int prev_fuel)
in (let _171_261 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print4 "(%s) Query succeeded with fuel %s and ifuel %s%s\n" _171_263 _171_262 _171_261 (match (cached_config) with
| Some (_82_524) -> begin
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
in (let _171_264 = (with_fuel [] p initial_config)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _171_264 (cb initial_config p alt_configs)))))))))
in (
# 369 "FStar.SMTEncoding.ErrorReporting.fst"
let process_query = (fun q -> if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(
# 371 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_531 = (let _171_270 = (FStar_ST.read FStar_Options.split_cases)
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _171_270 q))
in (match (_82_531) with
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




