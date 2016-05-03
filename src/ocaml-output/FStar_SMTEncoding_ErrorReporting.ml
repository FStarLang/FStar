
open Prims
# 24 "FStar.SMTEncoding.ErrorReporting.fst"
type fuel_trace_identity =
{module_digest : Prims.string; transitive_digest : Prims.string Prims.option}

# 24 "FStar.SMTEncoding.ErrorReporting.fst"
let is_Mkfuel_trace_identity : fuel_trace_identity  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkfuel_trace_identity"))))

# 30 "FStar.SMTEncoding.ErrorReporting.fst"
type fuel_trace_state =
{identity : fuel_trace_identity; fuels : (Prims.int * Prims.int) Prims.list}

# 30 "FStar.SMTEncoding.ErrorReporting.fst"
let is_Mkfuel_trace_state : fuel_trace_state  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkfuel_trace_state"))))

# 36 "FStar.SMTEncoding.ErrorReporting.fst"
type fuel_trace_status =
| FuelTraceUnavailable
| RecordFuelTrace of (Prims.int * Prims.int) Prims.list
| ReplayFuelTrace of (Prims.string * (Prims.int * Prims.int) Prims.list)

# 37 "FStar.SMTEncoding.ErrorReporting.fst"
let is_FuelTraceUnavailable = (fun _discr_ -> (match (_discr_) with
| FuelTraceUnavailable (_) -> begin
true
end
| _ -> begin
false
end))

# 38 "FStar.SMTEncoding.ErrorReporting.fst"
let is_RecordFuelTrace = (fun _discr_ -> (match (_discr_) with
| RecordFuelTrace (_) -> begin
true
end
| _ -> begin
false
end))

# 39 "FStar.SMTEncoding.ErrorReporting.fst"
let is_ReplayFuelTrace = (fun _discr_ -> (match (_discr_) with
| ReplayFuelTrace (_) -> begin
true
end
| _ -> begin
false
end))

# 38 "FStar.SMTEncoding.ErrorReporting.fst"
let ___RecordFuelTrace____0 = (fun projectee -> (match (projectee) with
| RecordFuelTrace (_82_10) -> begin
_82_10
end))

# 39 "FStar.SMTEncoding.ErrorReporting.fst"
let ___ReplayFuelTrace____0 = (fun projectee -> (match (projectee) with
| ReplayFuelTrace (_82_13) -> begin
_82_13
end))

# 41 "FStar.SMTEncoding.ErrorReporting.fst"
let fuel_trace : fuel_trace_status FStar_ST.ref = (FStar_All.pipe_left FStar_Util.mk_ref FuelTraceUnavailable)

# 43 "FStar.SMTEncoding.ErrorReporting.fst"
let format_fuel_trace_file_name : Prims.string  ->  Prims.string = (fun src_fn -> (let _171_46 = (FStar_Util.format1 "%s.fuel" src_fn)
in (FStar_All.pipe_left FStar_Util.format_value_file_name _171_46)))

# 46 "FStar.SMTEncoding.ErrorReporting.fst"
let compute_transitive_digest : Prims.string  ->  Prims.string Prims.list  ->  Prims.string = (fun src_fn deps -> (
# 48 "FStar.SMTEncoding.ErrorReporting.fst"
let digests = (let _171_51 = (FStar_All.pipe_left (FStar_List.map FStar_Util.digest_of_file) ((src_fn)::[]))
in (FStar_List.append _171_51 deps))
in (
# 49 "FStar.SMTEncoding.ErrorReporting.fst"
let s = (let _171_52 = (FStar_List.sortWith FStar_String.compare digests)
in (FStar_All.pipe_left (FStar_Util.concat_l ",") _171_52))
in (FStar_Util.digest_of_string s))))

# 52 "FStar.SMTEncoding.ErrorReporting.fst"
let initialize_fuel_trace : Prims.string  ->  Prims.string Prims.list  ->  Prims.unit = (fun src_fn deps -> (
# 53 "FStar.SMTEncoding.ErrorReporting.fst"
let norm_src_fn = (FStar_Util.normalize_file_path src_fn)
in (
# 54 "FStar.SMTEncoding.ErrorReporting.fst"
let val_fn = (format_fuel_trace_file_name norm_src_fn)
in (match ((FStar_Util.load_value_from_file val_fn)) with
| Some (state) -> begin
(
# 57 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_32 = if (FStar_ST.read FStar_Options.explicit_deps) then begin
(
# 60 "FStar.SMTEncoding.ErrorReporting.fst"
let expected = (FStar_Util.digest_of_file norm_src_fn)
in ("Module", (state.identity.module_digest = expected)))
end else begin
(let _171_57 = (match (state.identity.transitive_digest) with
| None -> begin
false
end
| Some (d) -> begin
(
# 69 "FStar.SMTEncoding.ErrorReporting.fst"
let expected = (compute_transitive_digest norm_src_fn deps)
in (d = expected))
end)
in ("Transitive", _171_57))
end
in (match (_82_32) with
| (means, validated) -> begin
if validated then begin
(
# 74 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_33 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(FStar_Util.print2 "(%s) %s digest is valid.\n" norm_src_fn means)
end else begin
()
end
in (FStar_ST.op_Colon_Equals fuel_trace (ReplayFuelTrace ((val_fn, state.fuels)))))
end else begin
(
# 81 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_35 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(FStar_Util.print2 "(%s) %s digest is invalid.\n" norm_src_fn means)
end else begin
()
end
in (FStar_ST.op_Colon_Equals fuel_trace (RecordFuelTrace ([]))))
end
end))
end
| None -> begin
(
# 88 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_38 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(FStar_Util.print1 "(%s) Unable to read cached fuel trace.\n" norm_src_fn)
end else begin
()
end
in (FStar_ST.op_Colon_Equals fuel_trace (RecordFuelTrace ([]))))
end))))

# 94 "FStar.SMTEncoding.ErrorReporting.fst"
let finalize_fuel_trace : Prims.string  ->  Prims.string Prims.list  ->  Prims.unit = (fun src_fn deps -> (
# 95 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_53 = (match ((FStar_ST.read fuel_trace)) with
| (ReplayFuelTrace (_)) | (FuelTraceUnavailable) | (RecordFuelTrace ([])) -> begin
()
end
| RecordFuelTrace (l) -> begin
(
# 104 "FStar.SMTEncoding.ErrorReporting.fst"
let val_fn = (format_fuel_trace_file_name src_fn)
in (
# 105 "FStar.SMTEncoding.ErrorReporting.fst"
let xd = if (FStar_ST.read FStar_Options.explicit_deps) then begin
None
end else begin
(let _171_63 = (compute_transitive_digest src_fn deps)
in (FStar_All.pipe_left (fun _171_62 -> Some (_171_62)) _171_63))
end
in (
# 112 "FStar.SMTEncoding.ErrorReporting.fst"
let state = (let _171_65 = (let _171_64 = (FStar_Util.digest_of_file src_fn)
in {module_digest = _171_64; transitive_digest = xd})
in {identity = _171_65; fuels = l})
in (FStar_Util.save_value_to_file val_fn state))))
end)
in (FStar_ST.op_Colon_Equals fuel_trace FuelTraceUnavailable)))

# 124 "FStar.SMTEncoding.ErrorReporting.fst"
type label =
FStar_SMTEncoding_Term.error_label

# 125 "FStar.SMTEncoding.ErrorReporting.fst"
type labels =
FStar_SMTEncoding_Term.error_labels

# 126 "FStar.SMTEncoding.ErrorReporting.fst"
let sort_labels : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun l -> (FStar_List.sortWith (fun _82_61 _82_67 -> (match ((_82_61, _82_67)) with
| ((_82_57, _82_59, r1), (_82_63, _82_65, r2)) -> begin
(FStar_Range.compare r1 r2)
end)) l))

# 127 "FStar.SMTEncoding.ErrorReporting.fst"
let remove_dups : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list = (fun l -> (FStar_Util.remove_dups (fun _82_73 _82_78 -> (match ((_82_73, _82_78)) with
| ((_82_70, m1, r1), (_82_75, m2, r2)) -> begin
((r1 = r2) && (m1 = m2))
end)) l))

# 128 "FStar.SMTEncoding.ErrorReporting.fst"
type msg =
(Prims.string * FStar_Range.range)

# 129 "FStar.SMTEncoding.ErrorReporting.fst"
type ranges =
(Prims.string Prims.option * FStar_Range.range) Prims.list

# 131 "FStar.SMTEncoding.ErrorReporting.fst"
let fresh_label : ranges  ->  FStar_SMTEncoding_Term.term  ->  labels  ->  (FStar_SMTEncoding_Term.term * labels) = (
# 132 "FStar.SMTEncoding.ErrorReporting.fst"
let ctr = (FStar_ST.alloc 0)
in (fun rs t labs -> (
# 134 "FStar.SMTEncoding.ErrorReporting.fst"
let l = (
# 134 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_83 = (FStar_Util.incr ctr)
in (let _171_81 = (let _171_80 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _171_80))
in (FStar_Util.format1 "label_%s" _171_81)))
in (
# 135 "FStar.SMTEncoding.ErrorReporting.fst"
let lvar = (l, FStar_SMTEncoding_Term.Bool_sort)
in (
# 136 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_103 = (match (rs) with
| [] -> begin
(t.FStar_SMTEncoding_Term.hash, FStar_Range.dummyRange)
end
| (Some (reason), r)::_82_89 -> begin
(reason, r)
end
| (None, r)::_82_96 -> begin
("failed to prove a pre-condition", r)
end)
in (match (_82_103) with
| (message, range) -> begin
(
# 140 "FStar.SMTEncoding.ErrorReporting.fst"
let label = (lvar, message, range)
in (
# 141 "FStar.SMTEncoding.ErrorReporting.fst"
let lterm = (FStar_SMTEncoding_Term.mkFreeV lvar)
in (
# 142 "FStar.SMTEncoding.ErrorReporting.fst"
let lt = (FStar_SMTEncoding_Term.mkOr (lterm, t))
in (lt, (label)::labs))))
end))))))

# 152 "FStar.SMTEncoding.ErrorReporting.fst"
let label_goals : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Int64.int64  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * labels * ranges) = (fun use_env_msg r q -> (
# 153 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_115 = (match (use_env_msg) with
| None -> begin
(false, "")
end
| Some (f) -> begin
(let _171_97 = (f ())
in (true, _171_97))
end)
in (match (_82_115) with
| (flag, msg_prefix) -> begin
(
# 156 "FStar.SMTEncoding.ErrorReporting.fst"
let fresh_label = (fun rs t labs -> (
# 157 "FStar.SMTEncoding.ErrorReporting.fst"
let rs' = if (not (flag)) then begin
rs
end else begin
(match (rs) with
| (Some (reason), _82_125)::_82_121 -> begin
((Some ((Prims.strcat "Failed to verify implicit argument: " reason)), r))::[]
end
| _82_129 -> begin
((Some ("Failed to verify implicit argument"), r))::[]
end)
end
in (
# 162 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_133 = (fresh_label rs' t labs)
in (match (_82_133) with
| (lt, labs) -> begin
(lt, labs, rs)
end))))
in (
# 164 "FStar.SMTEncoding.ErrorReporting.fst"
let rec aux = (fun rs q labs -> (match (q.FStar_SMTEncoding_Term.tm) with
| (FStar_SMTEncoding_Term.BoundV (_)) | (FStar_SMTEncoding_Term.Integer (_)) -> begin
(q, labs, rs)
end
| FStar_SMTEncoding_Term.Labeled (_82_145, "push", r) -> begin
(FStar_SMTEncoding_Term.mkTrue, labs, ((None, r))::rs)
end
| FStar_SMTEncoding_Term.Labeled (_82_151, "pop", r) -> begin
(let _171_110 = (FStar_List.tl rs)
in (FStar_SMTEncoding_Term.mkTrue, labs, _171_110))
end
| FStar_SMTEncoding_Term.Labeled (arg, reason, r) -> begin
(
# 176 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_164 = (aux (((Some (reason), r))::rs) arg labs)
in (match (_82_164) with
| (tm, labs, rs) -> begin
(let _171_111 = (FStar_List.tl rs)
in (tm, labs, _171_111))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, lhs::rhs::[]) -> begin
(
# 180 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_174 = (aux rs rhs labs)
in (match (_82_174) with
| (rhs, labs, rs) -> begin
(let _171_112 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]))))
in (_171_112, labs, rs))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(
# 184 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_191 = (FStar_List.fold_left (fun _82_182 c -> (match (_82_182) with
| (rs, cs, labs) -> begin
(
# 185 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_187 = (aux rs c labs)
in (match (_82_187) with
| (c, labs, rs) -> begin
(rs, (c)::cs, labs)
end))
end)) (rs, [], labs) conjuncts)
in (match (_82_191) with
| (rs, conjuncts, labs) -> begin
(let _171_115 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.And, (FStar_List.rev conjuncts)))))
in (_171_115, labs, rs))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, hd::q1::q2::[]) -> begin
(
# 192 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_203 = (aux rs q1 labs)
in (match (_82_203) with
| (q1, labs, _82_202) -> begin
(
# 193 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_208 = (aux rs q2 labs)
in (match (_82_208) with
| (q2, labs, _82_207) -> begin
(let _171_116 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]))))
in (_171_116, labs, rs))
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
# 226 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_330 = (aux rs body labs)
in (match (_82_330) with
| (body, labs, rs) -> begin
(let _171_117 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant ((FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body))))
in (_171_117, labs, rs))
end))
end))
in (aux [] q [])))
end)))

# 240 "FStar.SMTEncoding.ErrorReporting.fst"
let detail_errors : labels  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  (Prims.bool * labels))  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun all_labels potential_errors askZ3 -> (
# 241 "FStar.SMTEncoding.ErrorReporting.fst"
let ctr = (FStar_Util.mk_ref 0)
in (
# 242 "FStar.SMTEncoding.ErrorReporting.fst"
let elim = (fun labs -> (
# 243 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_337 = (FStar_Util.incr ctr)
in (let _171_140 = (let _171_133 = (let _171_132 = (let _171_131 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _171_131))
in (Prims.strcat "DETAILING ERRORS" _171_132))
in FStar_SMTEncoding_Term.Echo (_171_133))
in (let _171_139 = (FStar_All.pipe_right labs (FStar_List.map (fun _82_344 -> (match (_82_344) with
| (l, _82_341, _82_343) -> begin
(let _171_138 = (let _171_137 = (let _171_136 = (let _171_135 = (FStar_SMTEncoding_Term.mkFreeV l)
in (_171_135, FStar_SMTEncoding_Term.mkTrue))
in (FStar_SMTEncoding_Term.mkEq _171_136))
in (_171_137, Some ("Disabling label")))
in FStar_SMTEncoding_Term.Assume (_171_138))
end))))
in (_171_140)::_171_139))))
in (
# 246 "FStar.SMTEncoding.ErrorReporting.fst"
let print_labs = (fun tag l -> (FStar_All.pipe_right l (FStar_List.iter (fun _82_353 -> (match (_82_353) with
| (l, _82_350, _82_352) -> begin
(FStar_Util.print2 "%s : %s; " tag (Prims.fst l))
end)))))
in (
# 248 "FStar.SMTEncoding.ErrorReporting.fst"
let minus = (fun l1 l2 -> (FStar_All.pipe_right l1 (FStar_List.filter (fun _82_365 -> (match (_82_365) with
| ((x, _82_359), _82_362, _82_364) -> begin
(not ((FStar_All.pipe_right l2 (FStar_Util.for_some (fun _82_374 -> (match (_82_374) with
| ((y, _82_368), _82_371, _82_373) -> begin
(x = y)
end))))))
end)))))
in (
# 253 "FStar.SMTEncoding.ErrorReporting.fst"
let rec linear_check = (fun eliminated errors active -> (match (active) with
| [] -> begin
(
# 255 "FStar.SMTEncoding.ErrorReporting.fst"
let labs = (FStar_All.pipe_right errors sort_labels)
in labs)
end
| hd::tl -> begin
(
# 259 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_387 = (let _171_158 = (FStar_All.pipe_left elim (FStar_List.append (FStar_List.append eliminated errors) tl))
in (askZ3 _171_158))
in (match (_82_387) with
| (ok, _82_386) -> begin
if ok then begin
(linear_check ((hd)::eliminated) errors tl)
end else begin
(linear_check eliminated ((hd)::errors) tl)
end
end))
end))
in (
# 265 "FStar.SMTEncoding.ErrorReporting.fst"
let rec bisect = (fun eliminated potential_errors active -> (match (active) with
| [] -> begin
(eliminated, potential_errors)
end
| _82_394 -> begin
(
# 269 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_402 = (match (active) with
| _82_396::[] -> begin
(active, [])
end
| _82_399 -> begin
(FStar_Util.first_N ((FStar_List.length active) / 2) active)
end)
in (match (_82_402) with
| (pfx, sfx) -> begin
(
# 272 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_405 = (let _171_165 = (elim (FStar_List.append (FStar_List.append eliminated potential_errors) sfx))
in (askZ3 _171_165))
in (match (_82_405) with
| (ok, pfx_subset) -> begin
if ok then begin
(bisect (FStar_List.append eliminated pfx) potential_errors sfx)
end else begin
(match (pfx_subset) with
| [] -> begin
(bisect eliminated (FStar_List.append potential_errors pfx) sfx)
end
| _82_408 -> begin
(
# 281 "FStar.SMTEncoding.ErrorReporting.fst"
let potential_errors = (FStar_List.append potential_errors pfx_subset)
in (
# 282 "FStar.SMTEncoding.ErrorReporting.fst"
let pfx_active = (minus pfx pfx_subset)
in (bisect eliminated potential_errors (FStar_List.append pfx_active sfx))))
end)
end
end))
end))
end))
in (
# 287 "FStar.SMTEncoding.ErrorReporting.fst"
let rec until_fixpoint = (fun eliminated potential_errors active -> (
# 288 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_417 = (bisect eliminated potential_errors active)
in (match (_82_417) with
| (eliminated', potential_errors) -> begin
if (FStar_Util.physical_equality eliminated eliminated') then begin
(linear_check eliminated [] potential_errors)
end else begin
(until_fixpoint eliminated' [] potential_errors)
end
end)))
in (
# 293 "FStar.SMTEncoding.ErrorReporting.fst"
let active = (minus all_labels potential_errors)
in (until_fixpoint [] potential_errors active))))))))))

# 298 "FStar.SMTEncoding.ErrorReporting.fst"
let askZ3_and_report_errors : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun env use_fresh_z3_context all_labels prefix query suffix -> (
# 299 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_425 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (
# 300 "FStar.SMTEncoding.ErrorReporting.fst"
let minimum_workable_fuel = (FStar_Util.mk_ref None)
in (
# 301 "FStar.SMTEncoding.ErrorReporting.fst"
let set_minimum_workable_fuel = (fun f _82_1 -> (match (_82_1) with
| [] -> begin
()
end
| errs -> begin
(match ((FStar_ST.read minimum_workable_fuel)) with
| Some (_82_434) -> begin
()
end
| None -> begin
(FStar_ST.op_Colon_Equals minimum_workable_fuel (Some ((f, errs))))
end)
end))
in (
# 307 "FStar.SMTEncoding.ErrorReporting.fst"
let with_fuel = (fun label_assumptions p _82_442 -> (match (_82_442) with
| (n, i) -> begin
(let _171_214 = (let _171_213 = (let _171_212 = (let _171_211 = (let _171_196 = (let _171_195 = (FStar_Util.string_of_int n)
in (let _171_194 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _171_195 _171_194)))
in FStar_SMTEncoding_Term.Caption (_171_196))
in (let _171_210 = (let _171_209 = (let _171_201 = (let _171_200 = (let _171_199 = (let _171_198 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (let _171_197 = (FStar_SMTEncoding_Term.n_fuel n)
in (_171_198, _171_197)))
in (FStar_SMTEncoding_Term.mkEq _171_199))
in (_171_200, None))
in FStar_SMTEncoding_Term.Assume (_171_201))
in (let _171_208 = (let _171_207 = (let _171_206 = (let _171_205 = (let _171_204 = (let _171_203 = (FStar_SMTEncoding_Term.mkApp ("MaxIFuel", []))
in (let _171_202 = (FStar_SMTEncoding_Term.n_fuel i)
in (_171_203, _171_202)))
in (FStar_SMTEncoding_Term.mkEq _171_204))
in (_171_205, None))
in FStar_SMTEncoding_Term.Assume (_171_206))
in (_171_207)::(p)::[])
in (_171_209)::_171_208))
in (_171_211)::_171_210))
in (FStar_List.append _171_212 label_assumptions))
in (FStar_List.append _171_213 ((FStar_SMTEncoding_Term.CheckSat)::[])))
in (FStar_List.append _171_214 suffix))
end))
in (
# 316 "FStar.SMTEncoding.ErrorReporting.fst"
let check = (fun p -> (
# 317 "FStar.SMTEncoding.ErrorReporting.fst"
let cached_config = (match ((FStar_ST.read fuel_trace)) with
| ReplayFuelTrace (fname, hd::tl) -> begin
(
# 320 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_453 = hd
in (match (_82_453) with
| (fuel, ifuel) -> begin
(
# 321 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_454 = (FStar_ST.op_Colon_Equals fuel_trace (ReplayFuelTrace ((fname, tl))))
in Some ((fname, fuel, ifuel)))
end))
end
| _82_457 -> begin
None
end)
in (
# 326 "FStar.SMTEncoding.ErrorReporting.fst"
let initial_config = (match (cached_config) with
| Some (_82_460, fuel, ifuel) -> begin
(fuel, ifuel)
end
| None -> begin
(let _171_218 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _171_217 = (FStar_ST.read FStar_Options.initial_ifuel)
in (_171_218, _171_217)))
end)
in (
# 331 "FStar.SMTEncoding.ErrorReporting.fst"
let alt_configs = (match (cached_config) with
| Some (_82_468) -> begin
[]
end
| None -> begin
(let _171_237 = (let _171_236 = if ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel)) then begin
(let _171_221 = (let _171_220 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _171_219 = (FStar_ST.read FStar_Options.max_ifuel)
in (_171_220, _171_219)))
in (_171_221)::[])
end else begin
[]
end
in (let _171_235 = (let _171_234 = if (((FStar_ST.read FStar_Options.max_fuel) / 2) > (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _171_224 = (let _171_223 = ((FStar_ST.read FStar_Options.max_fuel) / 2)
in (let _171_222 = (FStar_ST.read FStar_Options.max_ifuel)
in (_171_223, _171_222)))
in (_171_224)::[])
end else begin
[]
end
in (let _171_233 = (let _171_232 = if (((FStar_ST.read FStar_Options.max_fuel) > (FStar_ST.read FStar_Options.initial_fuel)) && ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel))) then begin
(let _171_227 = (let _171_226 = (FStar_ST.read FStar_Options.max_fuel)
in (let _171_225 = (FStar_ST.read FStar_Options.max_ifuel)
in (_171_226, _171_225)))
in (_171_227)::[])
end else begin
[]
end
in (let _171_231 = (let _171_230 = if ((FStar_ST.read FStar_Options.min_fuel) < (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _171_229 = (let _171_228 = (FStar_ST.read FStar_Options.min_fuel)
in (_171_228, 1))
in (_171_229)::[])
end else begin
[]
end
in (_171_230)::[])
in (_171_232)::_171_231))
in (_171_234)::_171_233))
in (_171_236)::_171_235))
in (FStar_List.flatten _171_237))
end)
in (
# 340 "FStar.SMTEncoding.ErrorReporting.fst"
let report = (fun p errs -> (
# 341 "FStar.SMTEncoding.ErrorReporting.fst"
let errs = if ((FStar_ST.read FStar_Options.detail_errors) && ((FStar_ST.read FStar_Options.n_cores) = 1)) then begin
(
# 342 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_482 = (match ((FStar_ST.read minimum_workable_fuel)) with
| Some (f, errs) -> begin
(f, errs)
end
| None -> begin
(let _171_243 = (let _171_242 = (FStar_ST.read FStar_Options.min_fuel)
in (_171_242, 1))
in (_171_243, errs))
end)
in (match (_82_482) with
| (min_fuel, potential_errors) -> begin
(
# 345 "FStar.SMTEncoding.ErrorReporting.fst"
let ask_z3 = (fun label_assumptions -> (
# 346 "FStar.SMTEncoding.ErrorReporting.fst"
let res = (FStar_Util.mk_ref None)
in (
# 347 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_487 = (let _171_247 = (with_fuel label_assumptions p min_fuel)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _171_247 (fun r -> (FStar_ST.op_Colon_Equals res (Some (r))))))
in (let _171_248 = (FStar_ST.read res)
in (FStar_Option.get _171_248)))))
in (detail_errors all_labels errs ask_z3))
end))
end else begin
errs
end
in (
# 352 "FStar.SMTEncoding.ErrorReporting.fst"
let errs = (match (errs) with
| [] -> begin
((("", FStar_SMTEncoding_Term.Term_sort), "Unknown assertion failed", FStar_Range.dummyRange))::[]
end
| _82_492 -> begin
errs
end)
in (
# 355 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_501 = (match ((FStar_ST.read fuel_trace)) with
| ReplayFuelTrace (fname, _82_496) -> begin
(let _171_250 = (let _171_249 = (FStar_Util.format1 "Query failed while replaying cached fuel trace; please delete the related file (%s) and try again" fname)
in FStar_Util.Failure (_171_249))
in (FStar_All.pipe_left Prims.raise _171_250))
end
| _82_500 -> begin
(FStar_ST.op_Colon_Equals fuel_trace FuelTraceUnavailable)
end)
in (
# 361 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_503 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _171_256 = (let _171_251 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _171_251))
in (let _171_255 = (let _171_252 = (FStar_ST.read FStar_Options.max_fuel)
in (FStar_All.pipe_right _171_252 FStar_Util.string_of_int))
in (let _171_254 = (let _171_253 = (FStar_ST.read FStar_Options.max_ifuel)
in (FStar_All.pipe_right _171_253 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _171_256 _171_255 _171_254))))
end else begin
()
end
in (
# 366 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_510 = (let _171_258 = (FStar_All.pipe_right errs (FStar_List.map (fun _82_509 -> (match (_82_509) with
| (_82_506, x, y) -> begin
(x, y)
end))))
in (FStar_TypeChecker_Errors.add_errors env _171_258))
in if (FStar_ST.read FStar_Options.detail_errors) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Detailed error report follows\n")))
end else begin
()
end))))))
in (
# 370 "FStar.SMTEncoding.ErrorReporting.fst"
let rec try_alt_configs = (fun prev_f p errs cfgs -> (
# 371 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_518 = (set_minimum_workable_fuel prev_f errs)
in (match (cfgs) with
| [] -> begin
(report p errs)
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _171_271 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _171_271 (cb mi p [])))
end
| _82_525 -> begin
(
# 377 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_526 = (set_minimum_workable_fuel prev_f errs)
in (report p errs))
end)
end
| mi::tl -> begin
(let _171_273 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _171_273 (fun _82_533 -> (match (_82_533) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _82_536 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end)))
and cb = (fun _82_539 p alt _82_544 -> (match ((_82_539, _82_544)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
(
# 390 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_551 = (match ((FStar_ST.read fuel_trace)) with
| (ReplayFuelTrace (_)) | (FuelTraceUnavailable) -> begin
()
end
| RecordFuelTrace (l) -> begin
(FStar_ST.op_Colon_Equals fuel_trace (RecordFuelTrace ((FStar_List.append l (((prev_fuel, prev_ifuel))::[])))))
end)
in if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _171_281 = (let _171_278 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _171_278))
in (let _171_280 = (FStar_Util.string_of_int prev_fuel)
in (let _171_279 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print4 "(%s) Query succeeded with fuel %s and ifuel %s%s\n" _171_281 _171_280 _171_279 (match (cached_config) with
| Some (_82_554) -> begin
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
in (let _171_282 = (with_fuel [] p initial_config)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _171_282 (cb initial_config p alt_configs)))))))))
in (
# 414 "FStar.SMTEncoding.ErrorReporting.fst"
let process_query = (fun q -> if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(
# 416 "FStar.SMTEncoding.ErrorReporting.fst"
let _82_561 = (let _171_288 = (FStar_ST.read FStar_Options.split_cases)
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _171_288 q))
in (match (_82_561) with
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




