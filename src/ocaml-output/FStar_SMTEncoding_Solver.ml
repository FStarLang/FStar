
open Prims
open FStar_Pervasives

type z3_replay_result =
(FStar_SMTEncoding_Z3.unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either


let z3_result_as_replay_result : 'Auu____13 'Auu____14 'Auu____15 . ('Auu____15, ('Auu____14 * 'Auu____13)) FStar_Util.either  ->  ('Auu____15, 'Auu____14) FStar_Util.either = (fun uu___87_31 -> (match (uu___87_31) with
| FStar_Util.Inl (l) -> begin
FStar_Util.Inl (l)
end
| FStar_Util.Inr (r, uu____46) -> begin
FStar_Util.Inr (r)
end))


let recorded_hints : FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let replaying_hints : FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let format_hints_file_name : Prims.string  ->  Prims.string = (fun src_filename -> (FStar_Util.format1 "%s.hints" src_filename))


let initialize_hints_db : 'Auu____87 . Prims.string  ->  'Auu____87  ->  Prims.unit = (fun src_filename format_filename -> ((

let uu____97 = (FStar_Options.record_hints ())
in (match (uu____97) with
| true -> begin
(FStar_ST.op_Colon_Equals recorded_hints (FStar_Pervasives_Native.Some ([])))
end
| uu____154 -> begin
()
end));
(

let uu____155 = (FStar_Options.use_hints ())
in (match (uu____155) with
| true -> begin
(

let norm_src_filename = (FStar_Util.normalize_file_path src_filename)
in (

let val_filename = (

let uu____158 = (FStar_Options.hint_file ())
in (match (uu____158) with
| FStar_Pervasives_Native.Some (fn) -> begin
fn
end
| FStar_Pervasives_Native.None -> begin
(format_hints_file_name norm_src_filename)
end))
in (

let uu____162 = (FStar_Util.read_hints val_filename)
in (match (uu____162) with
| FStar_Pervasives_Native.Some (hints) -> begin
(

let expected_digest = (FStar_Util.digest_of_file norm_src_filename)
in ((

let uu____168 = (FStar_Options.hint_info ())
in (match (uu____168) with
| true -> begin
(

let uu____169 = (

let uu____170 = (FStar_Options.hint_file ())
in (match (uu____170) with
| FStar_Pervasives_Native.Some (fn) -> begin
(Prims.strcat " from \'" (Prims.strcat val_filename "\'"))
end
| uu____174 -> begin
""
end))
in (FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename (match ((Prims.op_Equality hints.FStar_Util.module_digest expected_digest)) with
| true -> begin
"valid; using hints"
end
| uu____177 -> begin
"invalid; using potentially stale hints"
end) uu____169))
end
| uu____178 -> begin
()
end));
(FStar_ST.op_Colon_Equals replaying_hints (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)));
))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____229 = (FStar_Options.hint_info ())
in (match (uu____229) with
| true -> begin
(FStar_Util.print1 "(%s) Unable to read hint file.\n" norm_src_filename)
end
| uu____230 -> begin
()
end))
end))))
end
| uu____231 -> begin
()
end));
))


let finalize_hints_db : Prims.string  ->  Prims.unit = (fun src_filename -> ((

let uu____237 = (FStar_Options.record_hints ())
in (match (uu____237) with
| true -> begin
(

let hints = (

let uu____239 = (FStar_ST.op_Bang recorded_hints)
in (FStar_Option.get uu____239))
in (

let hints_db = (

let uu____293 = (FStar_Util.digest_of_file src_filename)
in {FStar_Util.module_digest = uu____293; FStar_Util.hints = hints})
in (

let norm_src_filename = (FStar_Util.normalize_file_path src_filename)
in (

let val_filename = (

let uu____296 = (FStar_Options.hint_file ())
in (match (uu____296) with
| FStar_Pervasives_Native.Some (fn) -> begin
fn
end
| FStar_Pervasives_Native.None -> begin
(format_hints_file_name norm_src_filename)
end))
in (FStar_Util.write_hints val_filename hints_db)))))
end
| uu____300 -> begin
()
end));
(FStar_ST.op_Colon_Equals recorded_hints FStar_Pervasives_Native.None);
(FStar_ST.op_Colon_Equals replaying_hints FStar_Pervasives_Native.None);
))


let with_hints_db : 'a . Prims.string  ->  (Prims.unit  ->  'a)  ->  'a = (fun fname f -> ((initialize_hints_db fname false);
(

let result = (f ())
in ((finalize_hints_db fname);
result;
));
))


let filter_using_facts_from : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Term.decls_t  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun e theory -> (

let should_enc_fid = (fun fid -> (match (fid) with
| FStar_SMTEncoding_Term.Namespace (lid) -> begin
(FStar_TypeChecker_Env.should_enc_lid e lid)
end
| uu____440 -> begin
false
end))
in (

let matches_fact_ids = (fun include_assumption_names a -> (match (a.FStar_SMTEncoding_Term.assumption_fact_ids) with
| [] -> begin
true
end
| uu____452 -> begin
((FStar_List.contains a.FStar_SMTEncoding_Term.assumption_name include_assumption_names) || (FStar_All.pipe_right a.FStar_SMTEncoding_Term.assumption_fact_ids (FStar_Util.for_some (fun fid -> (should_enc_fid fid)))))
end))
in (

let theory_rev = (FStar_List.rev theory)
in (

let uu____462 = (FStar_List.fold_left (fun uu____485 d -> (match (uu____485) with
| (out, include_assumption_names) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(

let uu____522 = (matches_fact_ids include_assumption_names a)
in (match (uu____522) with
| true -> begin
(((d)::out), (include_assumption_names))
end
| uu____535 -> begin
((out), (include_assumption_names))
end))
end
| FStar_SMTEncoding_Term.RetainAssumptions (names1) -> begin
(((d)::out), ((FStar_List.append names1 include_assumption_names)))
end
| uu____547 -> begin
(((d)::out), (include_assumption_names))
end)
end)) (([]), ([])) theory_rev)
in (match (uu____462) with
| (pruned_theory, uu____559) -> begin
pruned_theory
end))))))


let filter_assertions : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Z3.unsat_core  ->  FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool) = (fun e core theory -> (match (core) with
| FStar_Pervasives_Native.None -> begin
(

let uu____594 = (filter_using_facts_from e theory)
in ((uu____594), (false)))
end
| FStar_Pervasives_Native.Some (core1) -> begin
(

let uu____604 = (FStar_List.fold_right (fun d uu____628 -> (match (uu____628) with
| (theory1, n_retained, n_pruned) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(match ((FStar_List.contains a.FStar_SMTEncoding_Term.assumption_name core1)) with
| true -> begin
(((d)::theory1), ((n_retained + (Prims.parse_int "1"))), (n_pruned))
end
| uu____671 -> begin
(match ((FStar_Util.starts_with a.FStar_SMTEncoding_Term.assumption_name "@")) with
| true -> begin
(((d)::theory1), (n_retained), (n_pruned))
end
| uu____682 -> begin
((theory1), (n_retained), ((n_pruned + (Prims.parse_int "1"))))
end)
end)
end
| uu____685 -> begin
(((d)::theory1), (n_retained), (n_pruned))
end)
end)) theory (([]), ((Prims.parse_int "0")), ((Prims.parse_int "0"))))
in (match (uu____604) with
| (theory', n_retained, n_pruned) -> begin
(

let uu____703 = (

let uu____706 = (

let uu____709 = (

let uu____710 = (

let uu____711 = (FStar_All.pipe_right core1 (FStar_String.concat ", "))
in (Prims.strcat "UNSAT CORE: " uu____711))
in FStar_SMTEncoding_Term.Caption (uu____710))
in (uu____709)::[])
in (FStar_List.append theory' uu____706))
in ((uu____703), (true)))
end))
end))


let filter_facts_without_core : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool) = (fun e x -> (

let uu____730 = (filter_using_facts_from e x)
in ((uu____730), (false))))

type errors =
{error_reason : Prims.string; error_fuel : Prims.int; error_ifuel : Prims.int; error_hint : Prims.string Prims.list FStar_Pervasives_Native.option; error_messages : (Prims.string * FStar_Range.range) Prims.list}


let __proj__Mkerrors__item__error_reason : errors  ->  Prims.string = (fun projectee -> (match (projectee) with
| {error_reason = __fname__error_reason; error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel; error_hint = __fname__error_hint; error_messages = __fname__error_messages} -> begin
__fname__error_reason
end))


let __proj__Mkerrors__item__error_fuel : errors  ->  Prims.int = (fun projectee -> (match (projectee) with
| {error_reason = __fname__error_reason; error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel; error_hint = __fname__error_hint; error_messages = __fname__error_messages} -> begin
__fname__error_fuel
end))


let __proj__Mkerrors__item__error_ifuel : errors  ->  Prims.int = (fun projectee -> (match (projectee) with
| {error_reason = __fname__error_reason; error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel; error_hint = __fname__error_hint; error_messages = __fname__error_messages} -> begin
__fname__error_ifuel
end))


let __proj__Mkerrors__item__error_hint : errors  ->  Prims.string Prims.list FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {error_reason = __fname__error_reason; error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel; error_hint = __fname__error_hint; error_messages = __fname__error_messages} -> begin
__fname__error_hint
end))


let __proj__Mkerrors__item__error_messages : errors  ->  (Prims.string * FStar_Range.range) Prims.list = (fun projectee -> (match (projectee) with
| {error_reason = __fname__error_reason; error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel; error_hint = __fname__error_hint; error_messages = __fname__error_messages} -> begin
__fname__error_messages
end))


let error_to_short_string : errors  ->  Prims.string = (fun err1 -> (

let uu____884 = (FStar_Util.string_of_int err1.error_fuel)
in (

let uu____885 = (FStar_Util.string_of_int err1.error_ifuel)
in (FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err1.error_reason uu____884 uu____885 (match ((FStar_Option.isSome err1.error_hint)) with
| true -> begin
"with hint"
end
| uu____888 -> begin
""
end)))))

type query_settings =
{query_env : FStar_TypeChecker_Env.env; query_decl : FStar_SMTEncoding_Term.decl; query_name : Prims.string; query_index : Prims.int; query_range : FStar_Range.range; query_fuel : Prims.int; query_ifuel : Prims.int; query_rlimit : Prims.int; query_hint : Prims.string Prims.list FStar_Pervasives_Native.option; query_errors : errors Prims.list; query_all_labels : FStar_SMTEncoding_Term.error_labels; query_suffix : FStar_SMTEncoding_Term.decl Prims.list}


let __proj__Mkquery_settings__item__query_env : query_settings  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix} -> begin
__fname__query_env
end))


let __proj__Mkquery_settings__item__query_decl : query_settings  ->  FStar_SMTEncoding_Term.decl = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix} -> begin
__fname__query_decl
end))


let __proj__Mkquery_settings__item__query_name : query_settings  ->  Prims.string = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix} -> begin
__fname__query_name
end))


let __proj__Mkquery_settings__item__query_index : query_settings  ->  Prims.int = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix} -> begin
__fname__query_index
end))


let __proj__Mkquery_settings__item__query_range : query_settings  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix} -> begin
__fname__query_range
end))


let __proj__Mkquery_settings__item__query_fuel : query_settings  ->  Prims.int = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix} -> begin
__fname__query_fuel
end))


let __proj__Mkquery_settings__item__query_ifuel : query_settings  ->  Prims.int = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix} -> begin
__fname__query_ifuel
end))


let __proj__Mkquery_settings__item__query_rlimit : query_settings  ->  Prims.int = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix} -> begin
__fname__query_rlimit
end))


let __proj__Mkquery_settings__item__query_hint : query_settings  ->  Prims.string Prims.list FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix} -> begin
__fname__query_hint
end))


let __proj__Mkquery_settings__item__query_errors : query_settings  ->  errors Prims.list = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix} -> begin
__fname__query_errors
end))


let __proj__Mkquery_settings__item__query_all_labels : query_settings  ->  FStar_SMTEncoding_Term.error_labels = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix} -> begin
__fname__query_all_labels
end))


let __proj__Mkquery_settings__item__query_suffix : query_settings  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix} -> begin
__fname__query_suffix
end))


let with_fuel_and_diagnostics : query_settings  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun settings label_assumptions -> (

let n1 = settings.query_fuel
in (

let i = settings.query_ifuel
in (

let rlimit = settings.query_rlimit
in (

let uu____1266 = (

let uu____1269 = (

let uu____1270 = (

let uu____1271 = (FStar_Util.string_of_int n1)
in (

let uu____1272 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" uu____1271 uu____1272)))
in FStar_SMTEncoding_Term.Caption (uu____1270))
in (

let uu____1273 = (

let uu____1276 = (

let uu____1277 = (

let uu____1284 = (

let uu____1285 = (

let uu____1290 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (

let uu____1293 = (FStar_SMTEncoding_Term.n_fuel n1)
in ((uu____1290), (uu____1293))))
in (FStar_SMTEncoding_Util.mkEq uu____1285))
in ((uu____1284), (FStar_Pervasives_Native.None), ("@MaxFuel_assumption")))
in (FStar_SMTEncoding_Util.mkAssume uu____1277))
in (

let uu____1296 = (

let uu____1299 = (

let uu____1300 = (

let uu____1307 = (

let uu____1308 = (

let uu____1313 = (FStar_SMTEncoding_Util.mkApp (("MaxIFuel"), ([])))
in (

let uu____1316 = (FStar_SMTEncoding_Term.n_fuel i)
in ((uu____1313), (uu____1316))))
in (FStar_SMTEncoding_Util.mkEq uu____1308))
in ((uu____1307), (FStar_Pervasives_Native.None), ("@MaxIFuel_assumption")))
in (FStar_SMTEncoding_Util.mkAssume uu____1300))
in (uu____1299)::(settings.query_decl)::[])
in (uu____1276)::uu____1296))
in (uu____1269)::uu____1273))
in (

let uu____1319 = (

let uu____1322 = (

let uu____1325 = (

let uu____1328 = (

let uu____1329 = (

let uu____1334 = (FStar_Util.string_of_int rlimit)
in (("rlimit"), (uu____1334)))
in FStar_SMTEncoding_Term.SetOption (uu____1329))
in (uu____1328)::(FStar_SMTEncoding_Term.CheckSat)::(FStar_SMTEncoding_Term.GetReasonUnknown)::[])
in (

let uu____1335 = (

let uu____1338 = (

let uu____1341 = (FStar_Options.record_hints ())
in (match (uu____1341) with
| true -> begin
(FStar_SMTEncoding_Term.GetUnsatCore)::[]
end
| uu____1344 -> begin
[]
end))
in (

let uu____1345 = (

let uu____1348 = (

let uu____1351 = (FStar_Options.print_z3_statistics ())
in (match (uu____1351) with
| true -> begin
(FStar_SMTEncoding_Term.GetStatistics)::[]
end
| uu____1354 -> begin
[]
end))
in (FStar_List.append uu____1348 settings.query_suffix))
in (FStar_List.append uu____1338 uu____1345)))
in (FStar_List.append uu____1325 uu____1335)))
in (FStar_List.append label_assumptions uu____1322))
in (FStar_List.append uu____1266 uu____1319)))))))


let used_hint : query_settings  ->  Prims.bool = (fun s -> (FStar_Option.isSome s.query_hint))


let next_hint : query_settings  ->  FStar_Util.hint FStar_Pervasives_Native.option = (fun uu____1366 -> (match (uu____1366) with
| {query_env = uu____1369; query_decl = uu____1370; query_name = qname; query_index = qindex; query_range = uu____1373; query_fuel = uu____1374; query_ifuel = uu____1375; query_rlimit = uu____1376; query_hint = uu____1377; query_errors = uu____1378; query_all_labels = uu____1379; query_suffix = uu____1380} -> begin
(

let uu____1389 = (FStar_ST.op_Bang replaying_hints)
in (match (uu____1389) with
| FStar_Pervasives_Native.Some (hints) -> begin
(FStar_Util.find_map hints (fun uu___88_1449 -> (match (uu___88_1449) with
| FStar_Pervasives_Native.Some (hint) when ((Prims.op_Equality hint.FStar_Util.hint_name qname) && (Prims.op_Equality hint.FStar_Util.hint_index qindex)) -> begin
FStar_Pervasives_Native.Some (hint)
end
| uu____1455 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____1458 -> begin
FStar_Pervasives_Native.None
end))
end))


let query_errors : 'Auu____1469 'Auu____1470 . query_settings  ->  (FStar_SMTEncoding_Z3.z3status * 'Auu____1470 * 'Auu____1469)  ->  errors FStar_Pervasives_Native.option = (fun settings uu____1486 -> (match (uu____1486) with
| (z3status, elapsed_time, stats) -> begin
(match (z3status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____1498) -> begin
FStar_Pervasives_Native.None
end
| uu____1499 -> begin
(

let uu____1500 = (FStar_SMTEncoding_Z3.status_string_and_errors z3status)
in (match (uu____1500) with
| (msg, error_labels) -> begin
(

let err1 = (

let uu____1510 = (FStar_List.map (fun uu____1531 -> (match (uu____1531) with
| (uu____1542, x, y) -> begin
((x), (y))
end)) error_labels)
in {error_reason = msg; error_fuel = settings.query_fuel; error_ifuel = settings.query_ifuel; error_hint = settings.query_hint; error_messages = uu____1510})
in FStar_Pervasives_Native.Some (err1))
end))
end)
end))


let detail_hint_replay : 'Auu____1553 'Auu____1554 . query_settings  ->  (FStar_SMTEncoding_Z3.z3status * 'Auu____1554 * 'Auu____1553)  ->  Prims.unit = (fun settings uu____1568 -> (match (uu____1568) with
| (z3status, uu____1576, uu____1577) -> begin
(

let uu____1578 = ((used_hint settings) && (FStar_Options.detail_hint_replay ()))
in (match (uu____1578) with
| true -> begin
(match (z3status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____1579) -> begin
()
end
| _failed -> begin
(

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((

let uu____1597 = (with_fuel_and_diagnostics settings label_assumptions)
in (FStar_SMTEncoding_Z3.ask (filter_assertions settings.query_env settings.query_hint) settings.query_all_labels uu____1597 FStar_Pervasives_Native.None (fun r -> (FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some (r))))));
(

let uu____1666 = (FStar_ST.op_Bang res)
in (FStar_Option.get uu____1666));
)))
in (FStar_SMTEncoding_ErrorReporting.detail_errors true settings.query_env settings.query_all_labels ask_z3))
end)
end
| uu____1733 -> begin
()
end))
end))


let find_localized_errors : errors Prims.list  ->  errors FStar_Pervasives_Native.option = (fun errs -> (FStar_All.pipe_right errs (FStar_List.tryFind (fun err1 -> (match (err1.error_messages) with
| [] -> begin
false
end
| uu____1754 -> begin
true
end)))))


let has_localized_errors : errors Prims.list  ->  Prims.bool = (fun errs -> (

let uu____1769 = (find_localized_errors errs)
in (FStar_Option.isSome uu____1769)))


let report_errors : query_settings  ->  Prims.unit = (fun settings -> (

let uu____1776 = ((FStar_Options.detail_errors ()) && (

let uu____1778 = (FStar_Options.n_cores ())
in (Prims.op_Equality uu____1778 (Prims.parse_int "1"))))
in (match (uu____1776) with
| true -> begin
(

let initial_fuel1 = (

let uu___89_1780 = settings
in (

let uu____1781 = (FStar_Options.initial_fuel ())
in (

let uu____1782 = (FStar_Options.initial_ifuel ())
in {query_env = uu___89_1780.query_env; query_decl = uu___89_1780.query_decl; query_name = uu___89_1780.query_name; query_index = uu___89_1780.query_index; query_range = uu___89_1780.query_range; query_fuel = uu____1781; query_ifuel = uu____1782; query_rlimit = uu___89_1780.query_rlimit; query_hint = FStar_Pervasives_Native.None; query_errors = uu___89_1780.query_errors; query_all_labels = uu___89_1780.query_all_labels; query_suffix = uu___89_1780.query_suffix})))
in (

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((

let uu____1801 = (with_fuel_and_diagnostics initial_fuel1 label_assumptions)
in (FStar_SMTEncoding_Z3.ask (filter_facts_without_core settings.query_env) settings.query_all_labels uu____1801 FStar_Pervasives_Native.None (fun r -> (FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some (r))))));
(

let uu____1870 = (FStar_ST.op_Bang res)
in (FStar_Option.get uu____1870));
)))
in (FStar_SMTEncoding_ErrorReporting.detail_errors false settings.query_env settings.query_all_labels ask_z3)))
end
| uu____1937 -> begin
(

let uu____1938 = (find_localized_errors settings.query_errors)
in (match (uu____1938) with
| FStar_Pervasives_Native.Some (err1) -> begin
((FStar_All.pipe_right settings.query_errors (FStar_List.iter (fun e -> (

let uu____1948 = (

let uu____1949 = (error_to_short_string e)
in (Prims.strcat "SMT solver says: " uu____1949))
in (FStar_Errors.diag settings.query_range uu____1948)))));
(FStar_TypeChecker_Err.add_errors settings.query_env err1.error_messages);
)
end
| FStar_Pervasives_Native.None -> begin
(

let err_detail = (

let uu____1951 = (FStar_All.pipe_right settings.query_errors (FStar_List.map (fun e -> (

let uu____1961 = (error_to_short_string e)
in (Prims.strcat "SMT solver says: " uu____1961)))))
in (FStar_All.pipe_right uu____1951 (FStar_String.concat "; ")))
in (

let uu____1964 = (

let uu____1971 = (

let uu____1976 = (FStar_Util.format1 "Unknown assertion failed (%s)" err_detail)
in ((uu____1976), (settings.query_range)))
in (uu____1971)::[])
in (FStar_TypeChecker_Err.add_errors settings.query_env uu____1964)))
end))
end)))


let query_info : query_settings  ->  (FStar_SMTEncoding_Z3.z3status * Prims.int * Prims.string FStar_Util.smap)  ->  Prims.unit = (fun settings z3result -> (

let uu____2009 = ((FStar_Options.hint_info ()) || (FStar_Options.print_z3_statistics ()))
in (match (uu____2009) with
| true -> begin
(

let uu____2010 = z3result
in (match (uu____2010) with
| (z3status, elapsed_time, statistics) -> begin
(

let uu____2026 = (FStar_SMTEncoding_Z3.status_string_and_errors z3status)
in (match (uu____2026) with
| (status_string, errs) -> begin
(

let tag = (match (z3status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____2034) -> begin
"succeeded"
end
| uu____2035 -> begin
(Prims.strcat "failed {reason-unknown=" (Prims.strcat status_string "}"))
end)
in (

let range = (

let uu____2037 = (

let uu____2038 = (FStar_Range.string_of_range settings.query_range)
in (

let uu____2039 = (

let uu____2040 = (FStar_SMTEncoding_Z3.at_log_file ())
in (Prims.strcat uu____2040 ")"))
in (Prims.strcat uu____2038 uu____2039)))
in (Prims.strcat "(" uu____2037))
in (

let used_hint_tag = (match ((used_hint settings)) with
| true -> begin
" (with hint)"
end
| uu____2042 -> begin
""
end)
in (

let stats = (

let uu____2044 = (FStar_Options.print_z3_statistics ())
in (match (uu____2044) with
| true -> begin
(

let f = (fun k v1 a -> (Prims.strcat a (Prims.strcat k (Prims.strcat "=" (Prims.strcat v1 " ")))))
in (

let str = (FStar_Util.smap_fold statistics f "statistics={")
in (

let uu____2056 = (FStar_Util.substring str (Prims.parse_int "0") ((FStar_String.length str) - (Prims.parse_int "1")))
in (Prims.strcat uu____2056 "}"))))
end
| uu____2057 -> begin
""
end))
in ((

let uu____2059 = (

let uu____2062 = (

let uu____2065 = (

let uu____2068 = (FStar_Util.string_of_int settings.query_index)
in (

let uu____2069 = (

let uu____2072 = (

let uu____2075 = (

let uu____2078 = (FStar_Util.string_of_int elapsed_time)
in (

let uu____2079 = (

let uu____2082 = (FStar_Util.string_of_int settings.query_fuel)
in (

let uu____2083 = (

let uu____2086 = (FStar_Util.string_of_int settings.query_ifuel)
in (

let uu____2087 = (

let uu____2090 = (FStar_Util.string_of_int settings.query_rlimit)
in (uu____2090)::(stats)::[])
in (uu____2086)::uu____2087))
in (uu____2082)::uu____2083))
in (uu____2078)::uu____2079))
in (used_hint_tag)::uu____2075)
in (tag)::uu____2072)
in (uu____2068)::uu____2069))
in (settings.query_name)::uu____2065)
in (range)::uu____2062)
in (FStar_Util.print "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n" uu____2059));
(FStar_All.pipe_right errs (FStar_List.iter (fun uu____2104 -> (match (uu____2104) with
| (uu____2111, msg, range1) -> begin
(

let e = (FStar_Errors.mk_issue FStar_Errors.EInfo (FStar_Pervasives_Native.Some (range1)) msg)
in (

let tag1 = (match ((used_hint settings)) with
| true -> begin
"(Hint-replay failed): "
end
| uu____2116 -> begin
""
end)
in (

let uu____2117 = (FStar_Errors.format_issue e)
in (FStar_Util.print2 "\t\t%s%s\n" tag1 uu____2117))))
end))));
)))))
end))
end))
end
| uu____2118 -> begin
()
end)))


let record_hint : 'Auu____2127 'Auu____2128 . query_settings  ->  (FStar_SMTEncoding_Z3.z3status * 'Auu____2128 * 'Auu____2127)  ->  Prims.unit = (fun settings z3result -> (

let uu____2149 = (

let uu____2150 = (FStar_Options.record_hints ())
in (not (uu____2150)))
in (match (uu____2149) with
| true -> begin
()
end
| uu____2151 -> begin
(

let uu____2152 = z3result
in (match (uu____2152) with
| (z3status, uu____2160, uu____2161) -> begin
(

let mk_hint = (fun core -> {FStar_Util.hint_name = settings.query_name; FStar_Util.hint_index = settings.query_index; FStar_Util.fuel = settings.query_fuel; FStar_Util.ifuel = settings.query_ifuel; FStar_Util.unsat_core = core; FStar_Util.query_elapsed_time = (Prims.parse_int "0")})
in (

let store_hint = (fun hint -> (

let uu____2178 = (FStar_ST.op_Bang recorded_hints)
in (match (uu____2178) with
| FStar_Pervasives_Native.Some (l) -> begin
(FStar_ST.op_Colon_Equals recorded_hints (FStar_Pervasives_Native.Some ((FStar_List.append l ((FStar_Pervasives_Native.Some (hint))::[])))))
end
| uu____2292 -> begin
()
end)))
in (match (z3status) with
| FStar_SMTEncoding_Z3.UNSAT (unsat_core) -> begin
(match ((used_hint settings)) with
| true -> begin
(store_hint (mk_hint settings.query_hint))
end
| uu____2299 -> begin
(store_hint (mk_hint unsat_core))
end)
end
| uu____2300 -> begin
()
end)))
end))
end)))


let process_result : query_settings  ->  (FStar_SMTEncoding_Z3.z3status * Prims.int * Prims.string FStar_Util.smap)  ->  errors FStar_Pervasives_Native.option = (fun settings result -> ((

let uu____2330 = ((used_hint settings) && (

let uu____2332 = (FStar_Options.z3_refresh ())
in (not (uu____2332))))
in (match (uu____2330) with
| true -> begin
(FStar_SMTEncoding_Z3.refresh ())
end
| uu____2333 -> begin
()
end));
(

let errs = (query_errors settings result)
in ((query_info settings result);
(record_hint settings result);
(detail_hint_replay settings result);
errs;
));
))


let fold_queries : query_settings Prims.list  ->  (query_settings  ->  (FStar_SMTEncoding_Z3.z3result  ->  Prims.unit)  ->  Prims.unit)  ->  (query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  errors FStar_Pervasives_Native.option)  ->  (errors Prims.list  ->  Prims.unit)  ->  Prims.unit = (fun qs ask1 f report1 -> (

let rec aux = (fun acc qs1 -> (match (qs1) with
| [] -> begin
(report1 acc)
end
| (q)::qs2 -> begin
(ask1 q (fun res -> (

let uu____2428 = (f q res)
in (match (uu____2428) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (errs) -> begin
(aux ((errs)::acc) qs2)
end))))
end))
in (aux [] qs)))


let ask_and_report_errors : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun env all_labels prefix1 query suffix -> ((FStar_SMTEncoding_Z3.giveZ3 prefix1);
(

let default_settings = (

let uu____2462 = (match (env.FStar_TypeChecker_Env.qname_and_index) with
| FStar_Pervasives_Native.None -> begin
(failwith "No query name set!")
end
| FStar_Pervasives_Native.Some (q, n1) -> begin
(((FStar_Ident.text_of_lid q)), (n1))
end)
in (match (uu____2462) with
| (qname, index1) -> begin
(

let rlimit = (

let uu____2488 = (FStar_Options.z3_rlimit_factor ())
in (

let uu____2489 = (

let uu____2490 = (FStar_Options.z3_rlimit ())
in (uu____2490 * (Prims.parse_int "544656")))
in (uu____2488 * uu____2489)))
in (

let uu____2491 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____2492 = (FStar_Options.initial_fuel ())
in (

let uu____2493 = (FStar_Options.initial_ifuel ())
in {query_env = env; query_decl = query; query_name = qname; query_index = index1; query_range = uu____2491; query_fuel = uu____2492; query_ifuel = uu____2493; query_rlimit = rlimit; query_hint = FStar_Pervasives_Native.None; query_errors = []; query_all_labels = all_labels; query_suffix = suffix}))))
end))
in (

let use_hints_setting = (

let uu____2499 = (next_hint default_settings)
in (match (uu____2499) with
| FStar_Pervasives_Native.Some ({FStar_Util.hint_name = uu____2504; FStar_Util.hint_index = uu____2505; FStar_Util.fuel = i; FStar_Util.ifuel = j; FStar_Util.unsat_core = FStar_Pervasives_Native.Some (core); FStar_Util.query_elapsed_time = uu____2509}) -> begin
((

let uu___90_2515 = default_settings
in {query_env = uu___90_2515.query_env; query_decl = uu___90_2515.query_decl; query_name = uu___90_2515.query_name; query_index = uu___90_2515.query_index; query_range = uu___90_2515.query_range; query_fuel = i; query_ifuel = j; query_rlimit = uu___90_2515.query_rlimit; query_hint = FStar_Pervasives_Native.Some (core); query_errors = uu___90_2515.query_errors; query_all_labels = uu___90_2515.query_all_labels; query_suffix = uu___90_2515.query_suffix}))::[]
end
| uu____2518 -> begin
[]
end))
in (

let initial_fuel_max_ifuel = (

let uu____2524 = (

let uu____2525 = (FStar_Options.max_ifuel ())
in (

let uu____2526 = (FStar_Options.initial_ifuel ())
in (uu____2525 > uu____2526)))
in (match (uu____2524) with
| true -> begin
(

let uu____2529 = (

let uu___91_2530 = default_settings
in (

let uu____2531 = (FStar_Options.max_ifuel ())
in {query_env = uu___91_2530.query_env; query_decl = uu___91_2530.query_decl; query_name = uu___91_2530.query_name; query_index = uu___91_2530.query_index; query_range = uu___91_2530.query_range; query_fuel = uu___91_2530.query_fuel; query_ifuel = uu____2531; query_rlimit = uu___91_2530.query_rlimit; query_hint = uu___91_2530.query_hint; query_errors = uu___91_2530.query_errors; query_all_labels = uu___91_2530.query_all_labels; query_suffix = uu___91_2530.query_suffix}))
in (uu____2529)::[])
end
| uu____2532 -> begin
[]
end))
in (

let half_max_fuel_max_ifuel = (

let uu____2536 = (

let uu____2537 = (

let uu____2538 = (FStar_Options.max_fuel ())
in (uu____2538 / (Prims.parse_int "2")))
in (

let uu____2545 = (FStar_Options.initial_fuel ())
in (uu____2537 > uu____2545)))
in (match (uu____2536) with
| true -> begin
(

let uu____2548 = (

let uu___92_2549 = default_settings
in (

let uu____2550 = (

let uu____2551 = (FStar_Options.max_fuel ())
in (uu____2551 / (Prims.parse_int "2")))
in (

let uu____2558 = (FStar_Options.max_ifuel ())
in {query_env = uu___92_2549.query_env; query_decl = uu___92_2549.query_decl; query_name = uu___92_2549.query_name; query_index = uu___92_2549.query_index; query_range = uu___92_2549.query_range; query_fuel = uu____2550; query_ifuel = uu____2558; query_rlimit = uu___92_2549.query_rlimit; query_hint = uu___92_2549.query_hint; query_errors = uu___92_2549.query_errors; query_all_labels = uu___92_2549.query_all_labels; query_suffix = uu___92_2549.query_suffix})))
in (uu____2548)::[])
end
| uu____2559 -> begin
[]
end))
in (

let max_fuel_max_ifuel = (

let uu____2563 = ((

let uu____2568 = (FStar_Options.max_fuel ())
in (

let uu____2569 = (FStar_Options.initial_fuel ())
in (uu____2568 > uu____2569))) && (

let uu____2572 = (FStar_Options.max_ifuel ())
in (

let uu____2573 = (FStar_Options.initial_ifuel ())
in (uu____2572 >= uu____2573))))
in (match (uu____2563) with
| true -> begin
(

let uu____2576 = (

let uu___93_2577 = default_settings
in (

let uu____2578 = (FStar_Options.max_fuel ())
in (

let uu____2579 = (FStar_Options.max_ifuel ())
in {query_env = uu___93_2577.query_env; query_decl = uu___93_2577.query_decl; query_name = uu___93_2577.query_name; query_index = uu___93_2577.query_index; query_range = uu___93_2577.query_range; query_fuel = uu____2578; query_ifuel = uu____2579; query_rlimit = uu___93_2577.query_rlimit; query_hint = uu___93_2577.query_hint; query_errors = uu___93_2577.query_errors; query_all_labels = uu___93_2577.query_all_labels; query_suffix = uu___93_2577.query_suffix})))
in (uu____2576)::[])
end
| uu____2580 -> begin
[]
end))
in (

let min_fuel1 = (

let uu____2584 = (

let uu____2585 = (FStar_Options.min_fuel ())
in (

let uu____2586 = (FStar_Options.initial_fuel ())
in (uu____2585 < uu____2586)))
in (match (uu____2584) with
| true -> begin
(

let uu____2589 = (

let uu___94_2590 = default_settings
in (

let uu____2591 = (FStar_Options.min_fuel ())
in {query_env = uu___94_2590.query_env; query_decl = uu___94_2590.query_decl; query_name = uu___94_2590.query_name; query_index = uu___94_2590.query_index; query_range = uu___94_2590.query_range; query_fuel = uu____2591; query_ifuel = (Prims.parse_int "1"); query_rlimit = uu___94_2590.query_rlimit; query_hint = uu___94_2590.query_hint; query_errors = uu___94_2590.query_errors; query_all_labels = uu___94_2590.query_all_labels; query_suffix = uu___94_2590.query_suffix}))
in (uu____2589)::[])
end
| uu____2592 -> begin
[]
end))
in (

let all_configs = (FStar_List.append use_hints_setting (FStar_List.append ((default_settings)::[]) (FStar_List.append initial_fuel_max_ifuel (FStar_List.append half_max_fuel_max_ifuel max_fuel_max_ifuel))))
in (

let check_one_config = (fun config k -> ((

let uu____2609 = ((used_hint config) || (FStar_Options.z3_refresh ()))
in (match (uu____2609) with
| true -> begin
(FStar_SMTEncoding_Z3.refresh ())
end
| uu____2610 -> begin
()
end));
(

let uu____2611 = (with_fuel_and_diagnostics config [])
in (

let uu____2614 = (

let uu____2617 = (FStar_SMTEncoding_Z3.mk_fresh_scope ())
in FStar_Pervasives_Native.Some (uu____2617))
in (FStar_SMTEncoding_Z3.ask (filter_assertions config.query_env config.query_hint) config.query_all_labels uu____2611 uu____2614 k)));
))
in (

let check_all_configs = (fun configs -> (

let report1 = (fun errs -> (report_errors (

let uu___95_2636 = default_settings
in {query_env = uu___95_2636.query_env; query_decl = uu___95_2636.query_decl; query_name = uu___95_2636.query_name; query_index = uu___95_2636.query_index; query_range = uu___95_2636.query_range; query_fuel = uu___95_2636.query_fuel; query_ifuel = uu___95_2636.query_ifuel; query_rlimit = uu___95_2636.query_rlimit; query_hint = uu___95_2636.query_hint; query_errors = errs; query_all_labels = uu___95_2636.query_all_labels; query_suffix = uu___95_2636.query_suffix})))
in (fold_queries configs check_one_config process_result report1)))
in (

let uu____2637 = (

let uu____2644 = (FStar_Options.admit_smt_queries ())
in (

let uu____2645 = (FStar_Options.admit_except ())
in ((uu____2644), (uu____2645))))
in (match (uu____2637) with
| (true, uu____2650) -> begin
()
end
| (false, FStar_Pervasives_Native.None) -> begin
(check_all_configs all_configs)
end
| (false, FStar_Pervasives_Native.Some (id)) -> begin
(

let skip = (match ((FStar_Util.starts_with id "(")) with
| true -> begin
(

let full_query_id = (

let uu____2662 = (

let uu____2663 = (

let uu____2664 = (

let uu____2665 = (FStar_Util.string_of_int default_settings.query_index)
in (Prims.strcat uu____2665 ")"))
in (Prims.strcat ", " uu____2664))
in (Prims.strcat default_settings.query_name uu____2663))
in (Prims.strcat "(" uu____2662))
in (Prims.op_disEquality full_query_id id))
end
| uu____2666 -> begin
(Prims.op_disEquality default_settings.query_name id)
end)
in (match ((not (skip))) with
| true -> begin
(check_all_configs all_configs)
end
| uu____2667 -> begin
()
end))
end)))))))))));
))


let solve : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun use_env_msg tcenv q -> ((

let uu____2690 = (

let uu____2691 = (

let uu____2692 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____2692))
in (FStar_Util.format1 "Starting query at %s" uu____2691))
in (FStar_SMTEncoding_Encode.push uu____2690));
(

let tcenv1 = (FStar_TypeChecker_Env.incr_query_index tcenv)
in (

let uu____2694 = (FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q)
in (match (uu____2694) with
| (prefix1, labels, qry, suffix) -> begin
(

let pop1 = (fun uu____2728 -> (

let uu____2729 = (

let uu____2730 = (

let uu____2731 = (FStar_TypeChecker_Env.get_range tcenv1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____2731))
in (FStar_Util.format1 "Ending query at %s" uu____2730))
in (FStar_SMTEncoding_Encode.pop uu____2729)))
in (match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.assumption_term = {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.FalseOp, uu____2732); FStar_SMTEncoding_Term.freevars = uu____2733; FStar_SMTEncoding_Term.rng = uu____2734}; FStar_SMTEncoding_Term.assumption_caption = uu____2735; FStar_SMTEncoding_Term.assumption_name = uu____2736; FStar_SMTEncoding_Term.assumption_fact_ids = uu____2737}) -> begin
(pop1 ())
end
| uu____2752 when tcenv1.FStar_TypeChecker_Env.admit -> begin
(pop1 ())
end
| FStar_SMTEncoding_Term.Assume (uu____2753) -> begin
((ask_and_report_errors tcenv1 labels prefix1 qry suffix);
(pop1 ());
)
end
| uu____2755 -> begin
(failwith "Impossible")
end))
end)));
))


let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init; FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push; FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop; FStar_TypeChecker_Env.encode_modul = FStar_SMTEncoding_Encode.encode_modul; FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig; FStar_TypeChecker_Env.preprocess = (fun e g -> (

let uu____2761 = (

let uu____2768 = (FStar_Options.peek ())
in ((e), (g), (uu____2768)))
in (uu____2761)::[])); FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = FStar_SMTEncoding_Encode.is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}


let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun uu____2783 -> ()); FStar_TypeChecker_Env.push = (fun uu____2785 -> ()); FStar_TypeChecker_Env.pop = (fun uu____2787 -> ()); FStar_TypeChecker_Env.encode_modul = (fun uu____2790 uu____2791 -> ()); FStar_TypeChecker_Env.encode_sig = (fun uu____2794 uu____2795 -> ()); FStar_TypeChecker_Env.preprocess = (fun e g -> (

let uu____2801 = (

let uu____2808 = (FStar_Options.peek ())
in ((e), (g), (uu____2808)))
in (uu____2801)::[])); FStar_TypeChecker_Env.solve = (fun uu____2824 uu____2825 uu____2826 -> ()); FStar_TypeChecker_Env.is_trivial = (fun uu____2833 uu____2834 -> false); FStar_TypeChecker_Env.finish = (fun uu____2836 -> ()); FStar_TypeChecker_Env.refresh = (fun uu____2838 -> ())}




