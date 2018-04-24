
open Prims
open FStar_Pervasives

type z3_replay_result =
(FStar_SMTEncoding_Z3.unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either


let z3_result_as_replay_result : 'Auu____13 'Auu____14 'Auu____15 . ('Auu____13, ('Auu____14 * 'Auu____15)) FStar_Util.either  ->  ('Auu____13, 'Auu____14) FStar_Util.either = (fun uu___63_32 -> (match (uu___63_32) with
| FStar_Util.Inl (l) -> begin
FStar_Util.Inl (l)
end
| FStar_Util.Inr (r, uu____47) -> begin
FStar_Util.Inr (r)
end))


let recorded_hints : FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let replaying_hints : FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let format_hints_file_name : Prims.string  ->  Prims.string = (fun src_filename -> (FStar_Util.format1 "%s.hints" src_filename))


let initialize_hints_db : 'Auu____145 . Prims.string  ->  'Auu____145  ->  unit = (fun src_filename format_filename -> ((

let uu____157 = (FStar_Options.record_hints ())
in (match (uu____157) with
| true -> begin
(FStar_ST.op_Colon_Equals recorded_hints (FStar_Pervasives_Native.Some ([])))
end
| uu____197 -> begin
()
end));
(

let uu____198 = (FStar_Options.use_hints ())
in (match (uu____198) with
| true -> begin
(

let norm_src_filename = (FStar_Util.normalize_file_path src_filename)
in (

let val_filename = (

let uu____201 = (FStar_Options.hint_file ())
in (match (uu____201) with
| FStar_Pervasives_Native.Some (fn) -> begin
fn
end
| FStar_Pervasives_Native.None -> begin
(format_hints_file_name norm_src_filename)
end))
in (

let uu____205 = (FStar_Util.read_hints val_filename)
in (match (uu____205) with
| FStar_Pervasives_Native.Some (hints) -> begin
(

let expected_digest = (FStar_Util.digest_of_file norm_src_filename)
in ((

let uu____211 = (FStar_Options.hint_info ())
in (match (uu____211) with
| true -> begin
(

let uu____212 = (

let uu____213 = (FStar_Options.hint_file ())
in (match (uu____213) with
| FStar_Pervasives_Native.Some (fn) -> begin
(Prims.strcat " from \'" (Prims.strcat val_filename "\'"))
end
| uu____217 -> begin
""
end))
in (FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename (match ((Prims.op_Equality hints.FStar_Util.module_digest expected_digest)) with
| true -> begin
"valid; using hints"
end
| uu____220 -> begin
"invalid; using potentially stale hints"
end) uu____212))
end
| uu____221 -> begin
()
end));
(FStar_ST.op_Colon_Equals replaying_hints (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)));
))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____255 = (FStar_Options.hint_info ())
in (match (uu____255) with
| true -> begin
(FStar_Util.print1 "(%s) Unable to read hint file.\n" norm_src_filename)
end
| uu____256 -> begin
()
end))
end))))
end
| uu____257 -> begin
()
end));
))


let finalize_hints_db : Prims.string  ->  unit = (fun src_filename -> ((

let uu____264 = (FStar_Options.record_hints ())
in (match (uu____264) with
| true -> begin
(

let hints = (

let uu____266 = (FStar_ST.op_Bang recorded_hints)
in (FStar_Option.get uu____266))
in (

let hints_db = (

let uu____303 = (FStar_Util.digest_of_file src_filename)
in {FStar_Util.module_digest = uu____303; FStar_Util.hints = hints})
in (

let norm_src_filename = (FStar_Util.normalize_file_path src_filename)
in (

let val_filename = (

let uu____306 = (FStar_Options.hint_file ())
in (match (uu____306) with
| FStar_Pervasives_Native.Some (fn) -> begin
fn
end
| FStar_Pervasives_Native.None -> begin
(format_hints_file_name norm_src_filename)
end))
in (FStar_Util.write_hints val_filename hints_db)))))
end
| uu____310 -> begin
()
end));
(FStar_ST.op_Colon_Equals recorded_hints FStar_Pervasives_Native.None);
(FStar_ST.op_Colon_Equals replaying_hints FStar_Pervasives_Native.None);
))


let with_hints_db : 'a . Prims.string  ->  (unit  ->  'a)  ->  'a = (fun fname f -> ((initialize_hints_db fname false);
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
| uu____422 -> begin
false
end))
in (

let matches_fact_ids = (fun include_assumption_names a -> (match (a.FStar_SMTEncoding_Term.assumption_fact_ids) with
| [] -> begin
true
end
| uu____438 -> begin
((FStar_All.pipe_right a.FStar_SMTEncoding_Term.assumption_fact_ids (FStar_Util.for_some should_enc_fid)) || (

let uu____444 = (FStar_Util.smap_try_find include_assumption_names a.FStar_SMTEncoding_Term.assumption_name)
in (FStar_Option.isSome uu____444)))
end))
in (

let theory_rev = (FStar_List.rev theory)
in (

let pruned_theory = (

let include_assumption_names = (FStar_Util.smap_create (Prims.parse_int "10000"))
in (FStar_List.fold_left (fun out d -> (match (d) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(

let uu____469 = (matches_fact_ids include_assumption_names a)
in (match (uu____469) with
| true -> begin
(d)::out
end
| uu____472 -> begin
out
end))
end
| FStar_SMTEncoding_Term.RetainAssumptions (names1) -> begin
((FStar_List.iter (fun x -> (FStar_Util.smap_add include_assumption_names x true)) names1);
(d)::out;
)
end
| uu____479 -> begin
(d)::out
end)) [] theory_rev))
in pruned_theory)))))


let filter_assertions : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Z3.unsat_core  ->  FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool) = (fun e core theory -> (match (core) with
| FStar_Pervasives_Native.None -> begin
(

let uu____509 = (filter_using_facts_from e theory)
in ((uu____509), (false)))
end
| FStar_Pervasives_Native.Some (core1) -> begin
(

let uu____519 = (FStar_List.fold_right (fun d uu____543 -> (match (uu____543) with
| (theory1, n_retained, n_pruned) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(match ((FStar_List.contains a.FStar_SMTEncoding_Term.assumption_name core1)) with
| true -> begin
(((d)::theory1), ((n_retained + (Prims.parse_int "1"))), (n_pruned))
end
| uu____586 -> begin
(match ((FStar_Util.starts_with a.FStar_SMTEncoding_Term.assumption_name "@")) with
| true -> begin
(((d)::theory1), (n_retained), (n_pruned))
end
| uu____597 -> begin
((theory1), (n_retained), ((n_pruned + (Prims.parse_int "1"))))
end)
end)
end
| uu____600 -> begin
(((d)::theory1), (n_retained), (n_pruned))
end)
end)) theory (([]), ((Prims.parse_int "0")), ((Prims.parse_int "0"))))
in (match (uu____519) with
| (theory', n_retained, n_pruned) -> begin
(

let uu____618 = (

let uu____621 = (

let uu____624 = (

let uu____625 = (

let uu____626 = (FStar_All.pipe_right core1 (FStar_String.concat ", "))
in (Prims.strcat "UNSAT CORE: " uu____626))
in FStar_SMTEncoding_Term.Caption (uu____625))
in (uu____624)::[])
in (FStar_List.append theory' uu____621))
in ((uu____618), (true)))
end))
end))


let filter_facts_without_core : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool) = (fun e x -> (

let uu____647 = (filter_using_facts_from e x)
in ((uu____647), (false))))

type errors =
{error_reason : Prims.string; error_fuel : Prims.int; error_ifuel : Prims.int; error_hint : Prims.string Prims.list FStar_Pervasives_Native.option; error_messages : (FStar_Errors.raw_error * Prims.string * FStar_Range.range) Prims.list}


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


let __proj__Mkerrors__item__error_messages : errors  ->  (FStar_Errors.raw_error * Prims.string * FStar_Range.range) Prims.list = (fun projectee -> (match (projectee) with
| {error_reason = __fname__error_reason; error_fuel = __fname__error_fuel; error_ifuel = __fname__error_ifuel; error_hint = __fname__error_hint; error_messages = __fname__error_messages} -> begin
__fname__error_messages
end))


let error_to_short_string : errors  ->  Prims.string = (fun err -> (

let uu____828 = (FStar_Util.string_of_int err.error_fuel)
in (

let uu____829 = (FStar_Util.string_of_int err.error_ifuel)
in (FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err.error_reason uu____828 uu____829 (match ((FStar_Option.isSome err.error_hint)) with
| true -> begin
"with hint"
end
| uu____832 -> begin
""
end)))))

type query_settings =
{query_env : FStar_TypeChecker_Env.env; query_decl : FStar_SMTEncoding_Term.decl; query_name : Prims.string; query_index : Prims.int; query_range : FStar_Range.range; query_fuel : Prims.int; query_ifuel : Prims.int; query_rlimit : Prims.int; query_hint : FStar_SMTEncoding_Z3.unsat_core; query_errors : errors Prims.list; query_all_labels : FStar_SMTEncoding_Term.error_labels; query_suffix : FStar_SMTEncoding_Term.decl Prims.list; query_hash : Prims.string FStar_Pervasives_Native.option}


let __proj__Mkquery_settings__item__query_env : query_settings  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix; query_hash = __fname__query_hash} -> begin
__fname__query_env
end))


let __proj__Mkquery_settings__item__query_decl : query_settings  ->  FStar_SMTEncoding_Term.decl = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix; query_hash = __fname__query_hash} -> begin
__fname__query_decl
end))


let __proj__Mkquery_settings__item__query_name : query_settings  ->  Prims.string = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix; query_hash = __fname__query_hash} -> begin
__fname__query_name
end))


let __proj__Mkquery_settings__item__query_index : query_settings  ->  Prims.int = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix; query_hash = __fname__query_hash} -> begin
__fname__query_index
end))


let __proj__Mkquery_settings__item__query_range : query_settings  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix; query_hash = __fname__query_hash} -> begin
__fname__query_range
end))


let __proj__Mkquery_settings__item__query_fuel : query_settings  ->  Prims.int = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix; query_hash = __fname__query_hash} -> begin
__fname__query_fuel
end))


let __proj__Mkquery_settings__item__query_ifuel : query_settings  ->  Prims.int = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix; query_hash = __fname__query_hash} -> begin
__fname__query_ifuel
end))


let __proj__Mkquery_settings__item__query_rlimit : query_settings  ->  Prims.int = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix; query_hash = __fname__query_hash} -> begin
__fname__query_rlimit
end))


let __proj__Mkquery_settings__item__query_hint : query_settings  ->  FStar_SMTEncoding_Z3.unsat_core = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix; query_hash = __fname__query_hash} -> begin
__fname__query_hint
end))


let __proj__Mkquery_settings__item__query_errors : query_settings  ->  errors Prims.list = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix; query_hash = __fname__query_hash} -> begin
__fname__query_errors
end))


let __proj__Mkquery_settings__item__query_all_labels : query_settings  ->  FStar_SMTEncoding_Term.error_labels = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix; query_hash = __fname__query_hash} -> begin
__fname__query_all_labels
end))


let __proj__Mkquery_settings__item__query_suffix : query_settings  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix; query_hash = __fname__query_hash} -> begin
__fname__query_suffix
end))


let __proj__Mkquery_settings__item__query_hash : query_settings  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {query_env = __fname__query_env; query_decl = __fname__query_decl; query_name = __fname__query_name; query_index = __fname__query_index; query_range = __fname__query_range; query_fuel = __fname__query_fuel; query_ifuel = __fname__query_ifuel; query_rlimit = __fname__query_rlimit; query_hint = __fname__query_hint; query_errors = __fname__query_errors; query_all_labels = __fname__query_all_labels; query_suffix = __fname__query_suffix; query_hash = __fname__query_hash} -> begin
__fname__query_hash
end))


let with_fuel_and_diagnostics : query_settings  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun settings label_assumptions -> (

let n1 = settings.query_fuel
in (

let i = settings.query_ifuel
in (

let rlimit = settings.query_rlimit
in (

let uu____1247 = (

let uu____1250 = (

let uu____1251 = (

let uu____1252 = (FStar_Util.string_of_int n1)
in (

let uu____1253 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" uu____1252 uu____1253)))
in FStar_SMTEncoding_Term.Caption (uu____1251))
in (

let uu____1254 = (

let uu____1257 = (

let uu____1258 = (

let uu____1265 = (

let uu____1266 = (

let uu____1271 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (

let uu____1274 = (FStar_SMTEncoding_Term.n_fuel n1)
in ((uu____1271), (uu____1274))))
in (FStar_SMTEncoding_Util.mkEq uu____1266))
in ((uu____1265), (FStar_Pervasives_Native.None), ("@MaxFuel_assumption")))
in (FStar_SMTEncoding_Util.mkAssume uu____1258))
in (

let uu____1277 = (

let uu____1280 = (

let uu____1281 = (

let uu____1288 = (

let uu____1289 = (

let uu____1294 = (FStar_SMTEncoding_Util.mkApp (("MaxIFuel"), ([])))
in (

let uu____1297 = (FStar_SMTEncoding_Term.n_fuel i)
in ((uu____1294), (uu____1297))))
in (FStar_SMTEncoding_Util.mkEq uu____1289))
in ((uu____1288), (FStar_Pervasives_Native.None), ("@MaxIFuel_assumption")))
in (FStar_SMTEncoding_Util.mkAssume uu____1281))
in (uu____1280)::(settings.query_decl)::[])
in (uu____1257)::uu____1277))
in (uu____1250)::uu____1254))
in (

let uu____1300 = (

let uu____1303 = (

let uu____1306 = (

let uu____1309 = (

let uu____1310 = (

let uu____1315 = (FStar_Util.string_of_int rlimit)
in (("rlimit"), (uu____1315)))
in FStar_SMTEncoding_Term.SetOption (uu____1310))
in (uu____1309)::(FStar_SMTEncoding_Term.CheckSat)::(FStar_SMTEncoding_Term.GetReasonUnknown)::[])
in (

let uu____1316 = (

let uu____1319 = (

let uu____1322 = (FStar_Options.record_hints ())
in (match (uu____1322) with
| true -> begin
(FStar_SMTEncoding_Term.GetUnsatCore)::[]
end
| uu____1325 -> begin
[]
end))
in (

let uu____1326 = (

let uu____1329 = (

let uu____1332 = (FStar_Options.print_z3_statistics ())
in (match (uu____1332) with
| true -> begin
(FStar_SMTEncoding_Term.GetStatistics)::[]
end
| uu____1335 -> begin
[]
end))
in (FStar_List.append uu____1329 settings.query_suffix))
in (FStar_List.append uu____1319 uu____1326)))
in (FStar_List.append uu____1306 uu____1316)))
in (FStar_List.append label_assumptions uu____1303))
in (FStar_List.append uu____1247 uu____1300)))))))


let used_hint : query_settings  ->  Prims.bool = (fun s -> (FStar_Option.isSome s.query_hint))


let get_hint_for : Prims.string  ->  Prims.int  ->  FStar_Util.hint FStar_Pervasives_Native.option = (fun qname qindex -> (

let uu____1355 = (FStar_ST.op_Bang replaying_hints)
in (match (uu____1355) with
| FStar_Pervasives_Native.Some (hints) -> begin
(FStar_Util.find_map hints (fun uu___64_1398 -> (match (uu___64_1398) with
| FStar_Pervasives_Native.Some (hint) when ((Prims.op_Equality hint.FStar_Util.hint_name qname) && (Prims.op_Equality hint.FStar_Util.hint_index qindex)) -> begin
FStar_Pervasives_Native.Some (hint)
end
| uu____1404 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____1407 -> begin
FStar_Pervasives_Native.None
end)))


let query_errors : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  errors FStar_Pervasives_Native.option = (fun settings z3result -> (match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____1424) -> begin
FStar_Pervasives_Native.None
end
| uu____1425 -> begin
(

let uu____1426 = (FStar_SMTEncoding_Z3.status_string_and_errors z3result.FStar_SMTEncoding_Z3.z3result_status)
in (match (uu____1426) with
| (msg, error_labels) -> begin
(

let err = (

let uu____1436 = (FStar_List.map (fun uu____1461 -> (match (uu____1461) with
| (uu____1474, x, y) -> begin
((FStar_Errors.Error_Z3SolverError), (x), (y))
end)) error_labels)
in {error_reason = msg; error_fuel = settings.query_fuel; error_ifuel = settings.query_ifuel; error_hint = settings.query_hint; error_messages = uu____1436})
in FStar_Pervasives_Native.Some (err))
end))
end))


let detail_hint_replay : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  unit = (fun settings z3result -> (

let uu____1487 = ((used_hint settings) && (FStar_Options.detail_hint_replay ()))
in (match (uu____1487) with
| true -> begin
(match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____1488) -> begin
()
end
| _failed -> begin
(

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((

let uu____1508 = (with_fuel_and_diagnostics settings label_assumptions)
in (FStar_SMTEncoding_Z3.ask settings.query_range (filter_assertions settings.query_env settings.query_hint) settings.query_hash settings.query_all_labels uu____1508 FStar_Pervasives_Native.None (fun r -> (FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some (r))))));
(

let uu____1616 = (FStar_ST.op_Bang res)
in (FStar_Option.get uu____1616));
)))
in (FStar_SMTEncoding_ErrorReporting.detail_errors true settings.query_env settings.query_all_labels ask_z3))
end)
end
| uu____1722 -> begin
()
end)))


let find_localized_errors : errors Prims.list  ->  errors FStar_Pervasives_Native.option = (fun errs -> (FStar_All.pipe_right errs (FStar_List.tryFind (fun err -> (match (err.error_messages) with
| [] -> begin
false
end
| uu____1746 -> begin
true
end)))))


let has_localized_errors : errors Prims.list  ->  Prims.bool = (fun errs -> (

let uu____1764 = (find_localized_errors errs)
in (FStar_Option.isSome uu____1764)))


let report_errors : query_settings  ->  unit = (fun settings -> (

let uu____1772 = ((FStar_Options.detail_errors ()) && (

let uu____1774 = (FStar_Options.n_cores ())
in (Prims.op_Equality uu____1774 (Prims.parse_int "1"))))
in (match (uu____1772) with
| true -> begin
(

let initial_fuel1 = (

let uu___65_1776 = settings
in (

let uu____1777 = (FStar_Options.initial_fuel ())
in (

let uu____1778 = (FStar_Options.initial_ifuel ())
in {query_env = uu___65_1776.query_env; query_decl = uu___65_1776.query_decl; query_name = uu___65_1776.query_name; query_index = uu___65_1776.query_index; query_range = uu___65_1776.query_range; query_fuel = uu____1777; query_ifuel = uu____1778; query_rlimit = uu___65_1776.query_rlimit; query_hint = FStar_Pervasives_Native.None; query_errors = uu___65_1776.query_errors; query_all_labels = uu___65_1776.query_all_labels; query_suffix = uu___65_1776.query_suffix; query_hash = uu___65_1776.query_hash})))
in (

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((

let uu____1799 = (with_fuel_and_diagnostics initial_fuel1 label_assumptions)
in (FStar_SMTEncoding_Z3.ask settings.query_range (filter_facts_without_core settings.query_env) settings.query_hash settings.query_all_labels uu____1799 FStar_Pervasives_Native.None (fun r -> (FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some (r))))));
(

let uu____1907 = (FStar_ST.op_Bang res)
in (FStar_Option.get uu____1907));
)))
in (FStar_SMTEncoding_ErrorReporting.detail_errors false settings.query_env settings.query_all_labels ask_z3)))
end
| uu____2013 -> begin
(

let uu____2014 = (find_localized_errors settings.query_errors)
in (match (uu____2014) with
| FStar_Pervasives_Native.Some (err) -> begin
((FStar_All.pipe_right settings.query_errors (FStar_List.iter (fun e -> (

let uu____2024 = (

let uu____2025 = (error_to_short_string e)
in (Prims.strcat "SMT solver says: " uu____2025))
in (FStar_Errors.diag settings.query_range uu____2024)))));
(FStar_TypeChecker_Err.add_errors settings.query_env err.error_messages);
)
end
| FStar_Pervasives_Native.None -> begin
(

let err_detail = (

let uu____2027 = (FStar_All.pipe_right settings.query_errors (FStar_List.map (fun e -> (

let uu____2037 = (error_to_short_string e)
in (Prims.strcat "SMT solver says: " uu____2037)))))
in (FStar_All.pipe_right uu____2027 (FStar_String.concat "; ")))
in (

let uu____2040 = (

let uu____2049 = (

let uu____2056 = (FStar_Util.format1 "Unknown assertion failed (%s)" err_detail)
in ((FStar_Errors.Error_UnknownFatal_AssertionFailure), (uu____2056), (settings.query_range)))
in (uu____2049)::[])
in (FStar_TypeChecker_Err.add_errors settings.query_env uu____2040)))
end))
end)))


let query_info : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  unit = (fun settings z3result -> (

let uu____2079 = ((FStar_Options.hint_info ()) || (FStar_Options.print_z3_statistics ()))
in (match (uu____2079) with
| true -> begin
(

let uu____2080 = (FStar_SMTEncoding_Z3.status_string_and_errors z3result.FStar_SMTEncoding_Z3.z3result_status)
in (match (uu____2080) with
| (status_string, errs) -> begin
(

let tag = (match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____2088) -> begin
"succeeded"
end
| uu____2089 -> begin
(Prims.strcat "failed {reason-unknown=" (Prims.strcat status_string "}"))
end)
in (

let range = (

let uu____2091 = (

let uu____2092 = (FStar_Range.string_of_range settings.query_range)
in (

let uu____2093 = (

let uu____2094 = (FStar_SMTEncoding_Z3.at_log_file ())
in (Prims.strcat uu____2094 ")"))
in (Prims.strcat uu____2092 uu____2093)))
in (Prims.strcat "(" uu____2091))
in (

let used_hint_tag = (match ((used_hint settings)) with
| true -> begin
" (with hint)"
end
| uu____2096 -> begin
""
end)
in (

let stats = (

let uu____2098 = (FStar_Options.print_z3_statistics ())
in (match (uu____2098) with
| true -> begin
(

let f = (fun k v1 a -> (Prims.strcat a (Prims.strcat k (Prims.strcat "=" (Prims.strcat v1 " ")))))
in (

let str = (FStar_Util.smap_fold z3result.FStar_SMTEncoding_Z3.z3result_statistics f "statistics={")
in (

let uu____2116 = (FStar_Util.substring str (Prims.parse_int "0") ((FStar_String.length str) - (Prims.parse_int "1")))
in (Prims.strcat uu____2116 "}"))))
end
| uu____2117 -> begin
""
end))
in ((

let uu____2119 = (

let uu____2122 = (

let uu____2125 = (

let uu____2128 = (FStar_Util.string_of_int settings.query_index)
in (

let uu____2129 = (

let uu____2132 = (

let uu____2135 = (

let uu____2138 = (FStar_Util.string_of_int z3result.FStar_SMTEncoding_Z3.z3result_time)
in (

let uu____2139 = (

let uu____2142 = (FStar_Util.string_of_int settings.query_fuel)
in (

let uu____2143 = (

let uu____2146 = (FStar_Util.string_of_int settings.query_ifuel)
in (

let uu____2147 = (

let uu____2150 = (FStar_Util.string_of_int settings.query_rlimit)
in (uu____2150)::(stats)::[])
in (uu____2146)::uu____2147))
in (uu____2142)::uu____2143))
in (uu____2138)::uu____2139))
in (used_hint_tag)::uu____2135)
in (tag)::uu____2132)
in (uu____2128)::uu____2129))
in (settings.query_name)::uu____2125)
in (range)::uu____2122)
in (FStar_Util.print "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n" uu____2119));
(FStar_All.pipe_right errs (FStar_List.iter (fun uu____2162 -> (match (uu____2162) with
| (uu____2169, msg, range1) -> begin
(

let tag1 = (match ((used_hint settings)) with
| true -> begin
"(Hint-replay failed): "
end
| uu____2173 -> begin
""
end)
in (FStar_Errors.log_issue range1 ((FStar_Errors.Warning_HitReplayFailed), ((Prims.strcat tag1 msg)))))
end))));
)))))
end))
end
| uu____2174 -> begin
()
end)))


let record_hint : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  unit = (fun settings z3result -> (

let uu____2185 = (

let uu____2186 = (FStar_Options.record_hints ())
in (not (uu____2186)))
in (match (uu____2185) with
| true -> begin
()
end
| uu____2187 -> begin
(

let mk_hint = (fun core -> {FStar_Util.hint_name = settings.query_name; FStar_Util.hint_index = settings.query_index; FStar_Util.fuel = settings.query_fuel; FStar_Util.ifuel = settings.query_ifuel; FStar_Util.unsat_core = core; FStar_Util.query_elapsed_time = (Prims.parse_int "0"); FStar_Util.hash = (match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (core1) -> begin
z3result.FStar_SMTEncoding_Z3.z3result_query_hash
end
| uu____2206 -> begin
FStar_Pervasives_Native.None
end)})
in (

let store_hint = (fun hint -> (

let uu____2213 = (FStar_ST.op_Bang recorded_hints)
in (match (uu____2213) with
| FStar_Pervasives_Native.Some (l) -> begin
(FStar_ST.op_Colon_Equals recorded_hints (FStar_Pervasives_Native.Some ((FStar_List.append l ((FStar_Pervasives_Native.Some (hint))::[])))))
end
| uu____2293 -> begin
()
end)))
in (match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None) -> begin
(

let uu____2299 = (

let uu____2300 = (get_hint_for settings.query_name settings.query_index)
in (FStar_Option.get uu____2300))
in (store_hint uu____2299))
end
| FStar_SMTEncoding_Z3.UNSAT (unsat_core) -> begin
(match ((used_hint settings)) with
| true -> begin
(store_hint (mk_hint settings.query_hint))
end
| uu____2304 -> begin
(store_hint (mk_hint unsat_core))
end)
end
| uu____2305 -> begin
()
end)))
end)))


let process_result : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  errors FStar_Pervasives_Native.option = (fun settings result -> ((

let uu____2321 = ((used_hint settings) && (

let uu____2323 = (FStar_Options.z3_refresh ())
in (not (uu____2323))))
in (match (uu____2321) with
| true -> begin
(FStar_SMTEncoding_Z3.refresh ())
end
| uu____2324 -> begin
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


let fold_queries : query_settings Prims.list  ->  (query_settings  ->  (FStar_SMTEncoding_Z3.z3result  ->  unit)  ->  unit)  ->  (query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  errors FStar_Pervasives_Native.option)  ->  (errors Prims.list  ->  unit)  ->  unit = (fun qs ask1 f report1 -> (

let rec aux = (fun acc qs1 -> (match (qs1) with
| [] -> begin
(report1 acc)
end
| (q)::qs2 -> begin
(ask1 q (fun res -> (

let uu____2419 = (f q res)
in (match (uu____2419) with
| FStar_Pervasives_Native.None -> begin
()
end
| FStar_Pervasives_Native.Some (errs) -> begin
(aux ((errs)::acc) qs2)
end))))
end))
in (aux [] qs)))


let ask_and_report_errors : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  unit = (fun env all_labels prefix1 query suffix -> ((FStar_SMTEncoding_Z3.giveZ3 prefix1);
(

let uu____2457 = (

let uu____2464 = (match (env.FStar_TypeChecker_Env.qtbl_name_and_index) with
| (uu____2473, FStar_Pervasives_Native.None) -> begin
(failwith "No query name set!")
end
| (uu____2492, FStar_Pervasives_Native.Some (q, n1)) -> begin
(

let uu____2509 = (FStar_Ident.text_of_lid q)
in ((uu____2509), (n1)))
end)
in (match (uu____2464) with
| (qname, index1) -> begin
(

let rlimit = (

let uu____2519 = (FStar_Options.z3_rlimit_factor ())
in (

let uu____2520 = (

let uu____2521 = (FStar_Options.z3_rlimit ())
in (uu____2521 * (Prims.parse_int "544656")))
in (uu____2519 * uu____2520)))
in (

let next_hint = (get_hint_for qname index1)
in (

let default_settings = (

let uu____2526 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____2527 = (FStar_Options.initial_fuel ())
in (

let uu____2528 = (FStar_Options.initial_ifuel ())
in {query_env = env; query_decl = query; query_name = qname; query_index = index1; query_range = uu____2526; query_fuel = uu____2527; query_ifuel = uu____2528; query_rlimit = rlimit; query_hint = FStar_Pervasives_Native.None; query_errors = []; query_all_labels = all_labels; query_suffix = suffix; query_hash = (match (next_hint) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ({FStar_Util.hint_name = uu____2533; FStar_Util.hint_index = uu____2534; FStar_Util.fuel = uu____2535; FStar_Util.ifuel = uu____2536; FStar_Util.unsat_core = uu____2537; FStar_Util.query_elapsed_time = uu____2538; FStar_Util.hash = h}) -> begin
h
end)})))
in ((default_settings), (next_hint)))))
end))
in (match (uu____2457) with
| (default_settings, next_hint) -> begin
(

let use_hints_setting = (match (next_hint) with
| FStar_Pervasives_Native.Some ({FStar_Util.hint_name = uu____2559; FStar_Util.hint_index = uu____2560; FStar_Util.fuel = i; FStar_Util.ifuel = j; FStar_Util.unsat_core = FStar_Pervasives_Native.Some (core); FStar_Util.query_elapsed_time = uu____2564; FStar_Util.hash = h}) -> begin
((

let uu___66_2573 = default_settings
in {query_env = uu___66_2573.query_env; query_decl = uu___66_2573.query_decl; query_name = uu___66_2573.query_name; query_index = uu___66_2573.query_index; query_range = uu___66_2573.query_range; query_fuel = i; query_ifuel = j; query_rlimit = uu___66_2573.query_rlimit; query_hint = FStar_Pervasives_Native.Some (core); query_errors = uu___66_2573.query_errors; query_all_labels = uu___66_2573.query_all_labels; query_suffix = uu___66_2573.query_suffix; query_hash = uu___66_2573.query_hash}))::[]
end
| uu____2576 -> begin
[]
end)
in (

let initial_fuel_max_ifuel = (

let uu____2582 = (

let uu____2583 = (FStar_Options.max_ifuel ())
in (

let uu____2584 = (FStar_Options.initial_ifuel ())
in (uu____2583 > uu____2584)))
in (match (uu____2582) with
| true -> begin
(

let uu____2587 = (

let uu___67_2588 = default_settings
in (

let uu____2589 = (FStar_Options.max_ifuel ())
in {query_env = uu___67_2588.query_env; query_decl = uu___67_2588.query_decl; query_name = uu___67_2588.query_name; query_index = uu___67_2588.query_index; query_range = uu___67_2588.query_range; query_fuel = uu___67_2588.query_fuel; query_ifuel = uu____2589; query_rlimit = uu___67_2588.query_rlimit; query_hint = uu___67_2588.query_hint; query_errors = uu___67_2588.query_errors; query_all_labels = uu___67_2588.query_all_labels; query_suffix = uu___67_2588.query_suffix; query_hash = uu___67_2588.query_hash}))
in (uu____2587)::[])
end
| uu____2590 -> begin
[]
end))
in (

let half_max_fuel_max_ifuel = (

let uu____2594 = (

let uu____2595 = (

let uu____2596 = (FStar_Options.max_fuel ())
in (uu____2596 / (Prims.parse_int "2")))
in (

let uu____2597 = (FStar_Options.initial_fuel ())
in (uu____2595 > uu____2597)))
in (match (uu____2594) with
| true -> begin
(

let uu____2600 = (

let uu___68_2601 = default_settings
in (

let uu____2602 = (

let uu____2603 = (FStar_Options.max_fuel ())
in (uu____2603 / (Prims.parse_int "2")))
in (

let uu____2604 = (FStar_Options.max_ifuel ())
in {query_env = uu___68_2601.query_env; query_decl = uu___68_2601.query_decl; query_name = uu___68_2601.query_name; query_index = uu___68_2601.query_index; query_range = uu___68_2601.query_range; query_fuel = uu____2602; query_ifuel = uu____2604; query_rlimit = uu___68_2601.query_rlimit; query_hint = uu___68_2601.query_hint; query_errors = uu___68_2601.query_errors; query_all_labels = uu___68_2601.query_all_labels; query_suffix = uu___68_2601.query_suffix; query_hash = uu___68_2601.query_hash})))
in (uu____2600)::[])
end
| uu____2605 -> begin
[]
end))
in (

let max_fuel_max_ifuel = (

let uu____2609 = ((

let uu____2614 = (FStar_Options.max_fuel ())
in (

let uu____2615 = (FStar_Options.initial_fuel ())
in (uu____2614 > uu____2615))) && (

let uu____2618 = (FStar_Options.max_ifuel ())
in (

let uu____2619 = (FStar_Options.initial_ifuel ())
in (uu____2618 >= uu____2619))))
in (match (uu____2609) with
| true -> begin
(

let uu____2622 = (

let uu___69_2623 = default_settings
in (

let uu____2624 = (FStar_Options.max_fuel ())
in (

let uu____2625 = (FStar_Options.max_ifuel ())
in {query_env = uu___69_2623.query_env; query_decl = uu___69_2623.query_decl; query_name = uu___69_2623.query_name; query_index = uu___69_2623.query_index; query_range = uu___69_2623.query_range; query_fuel = uu____2624; query_ifuel = uu____2625; query_rlimit = uu___69_2623.query_rlimit; query_hint = uu___69_2623.query_hint; query_errors = uu___69_2623.query_errors; query_all_labels = uu___69_2623.query_all_labels; query_suffix = uu___69_2623.query_suffix; query_hash = uu___69_2623.query_hash})))
in (uu____2622)::[])
end
| uu____2626 -> begin
[]
end))
in (

let min_fuel1 = (

let uu____2630 = (

let uu____2631 = (FStar_Options.min_fuel ())
in (

let uu____2632 = (FStar_Options.initial_fuel ())
in (uu____2631 < uu____2632)))
in (match (uu____2630) with
| true -> begin
(

let uu____2635 = (

let uu___70_2636 = default_settings
in (

let uu____2637 = (FStar_Options.min_fuel ())
in {query_env = uu___70_2636.query_env; query_decl = uu___70_2636.query_decl; query_name = uu___70_2636.query_name; query_index = uu___70_2636.query_index; query_range = uu___70_2636.query_range; query_fuel = uu____2637; query_ifuel = (Prims.parse_int "1"); query_rlimit = uu___70_2636.query_rlimit; query_hint = uu___70_2636.query_hint; query_errors = uu___70_2636.query_errors; query_all_labels = uu___70_2636.query_all_labels; query_suffix = uu___70_2636.query_suffix; query_hash = uu___70_2636.query_hash}))
in (uu____2635)::[])
end
| uu____2638 -> begin
[]
end))
in (

let all_configs = (FStar_List.append use_hints_setting (FStar_List.append ((default_settings)::[]) (FStar_List.append initial_fuel_max_ifuel (FStar_List.append half_max_fuel_max_ifuel max_fuel_max_ifuel))))
in (

let check_one_config = (fun config k -> ((

let uu____2659 = ((used_hint config) || (FStar_Options.z3_refresh ()))
in (match (uu____2659) with
| true -> begin
(FStar_SMTEncoding_Z3.refresh ())
end
| uu____2660 -> begin
()
end));
(

let uu____2661 = (with_fuel_and_diagnostics config [])
in (

let uu____2664 = (

let uu____2667 = (FStar_SMTEncoding_Z3.mk_fresh_scope ())
in FStar_Pervasives_Native.Some (uu____2667))
in (FStar_SMTEncoding_Z3.ask config.query_range (filter_assertions config.query_env config.query_hint) config.query_hash config.query_all_labels uu____2661 uu____2664 k)));
))
in (

let check_all_configs = (fun configs -> (

let report1 = (fun errs -> (report_errors (

let uu___71_2690 = default_settings
in {query_env = uu___71_2690.query_env; query_decl = uu___71_2690.query_decl; query_name = uu___71_2690.query_name; query_index = uu___71_2690.query_index; query_range = uu___71_2690.query_range; query_fuel = uu___71_2690.query_fuel; query_ifuel = uu___71_2690.query_ifuel; query_rlimit = uu___71_2690.query_rlimit; query_hint = uu___71_2690.query_hint; query_errors = errs; query_all_labels = uu___71_2690.query_all_labels; query_suffix = uu___71_2690.query_suffix; query_hash = uu___71_2690.query_hash})))
in (fold_queries configs check_one_config process_result report1)))
in (

let uu____2691 = (

let uu____2698 = (FStar_Options.admit_smt_queries ())
in (

let uu____2699 = (FStar_Options.admit_except ())
in ((uu____2698), (uu____2699))))
in (match (uu____2691) with
| (true, uu____2704) -> begin
()
end
| (false, FStar_Pervasives_Native.None) -> begin
(check_all_configs all_configs)
end
| (false, FStar_Pervasives_Native.Some (id1)) -> begin
(

let skip = (match ((FStar_Util.starts_with id1 "(")) with
| true -> begin
(

let full_query_id = (

let uu____2716 = (

let uu____2717 = (

let uu____2718 = (

let uu____2719 = (FStar_Util.string_of_int default_settings.query_index)
in (Prims.strcat uu____2719 ")"))
in (Prims.strcat ", " uu____2718))
in (Prims.strcat default_settings.query_name uu____2717))
in (Prims.strcat "(" uu____2716))
in (Prims.op_disEquality full_query_id id1))
end
| uu____2720 -> begin
(Prims.op_disEquality default_settings.query_name id1)
end)
in (match ((not (skip))) with
| true -> begin
(check_all_configs all_configs)
end
| uu____2721 -> begin
()
end))
end))))))))))
end));
))


let solve : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  unit = (fun use_env_msg tcenv q -> ((

let uu____2747 = (

let uu____2748 = (

let uu____2749 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____2749))
in (FStar_Util.format1 "Starting query at %s" uu____2748))
in (FStar_SMTEncoding_Encode.push uu____2747));
(

let uu____2750 = (FStar_Options.no_smt ())
in (match (uu____2750) with
| true -> begin
(

let uu____2751 = (

let uu____2760 = (

let uu____2767 = (

let uu____2768 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.format1 "Q = %s\nA query could not be solved internally, and --no_smt was given" uu____2768))
in ((FStar_Errors.Error_NoSMTButNeeded), (uu____2767), (tcenv.FStar_TypeChecker_Env.range)))
in (uu____2760)::[])
in (FStar_TypeChecker_Err.add_errors tcenv uu____2751))
end
| uu____2781 -> begin
(

let tcenv1 = (FStar_TypeChecker_Env.incr_query_index tcenv)
in (

let uu____2783 = (FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q)
in (match (uu____2783) with
| (prefix1, labels, qry, suffix) -> begin
(

let pop1 = (fun uu____2819 -> (

let uu____2820 = (

let uu____2821 = (

let uu____2822 = (FStar_TypeChecker_Env.get_range tcenv1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____2822))
in (FStar_Util.format1 "Ending query at %s" uu____2821))
in (FStar_SMTEncoding_Encode.pop uu____2820)))
in (match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.assumption_term = {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.FalseOp, uu____2823); FStar_SMTEncoding_Term.freevars = uu____2824; FStar_SMTEncoding_Term.rng = uu____2825}; FStar_SMTEncoding_Term.assumption_caption = uu____2826; FStar_SMTEncoding_Term.assumption_name = uu____2827; FStar_SMTEncoding_Term.assumption_fact_ids = uu____2828}) -> begin
(pop1 ())
end
| uu____2843 when tcenv1.FStar_TypeChecker_Env.admit -> begin
(pop1 ())
end
| FStar_SMTEncoding_Term.Assume (uu____2844) -> begin
((ask_and_report_errors tcenv1 labels prefix1 qry suffix);
(pop1 ());
)
end
| uu____2846 -> begin
(failwith "Impossible")
end))
end)))
end));
))


let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init; FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push; FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop; FStar_TypeChecker_Env.encode_modul = FStar_SMTEncoding_Encode.encode_modul; FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig; FStar_TypeChecker_Env.preprocess = (fun e g -> (

let uu____2852 = (

let uu____2859 = (FStar_Options.peek ())
in ((e), (g), (uu____2859)))
in (uu____2852)::[])); FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}


let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun uu____2874 -> ()); FStar_TypeChecker_Env.push = (fun uu____2876 -> ()); FStar_TypeChecker_Env.pop = (fun uu____2878 -> ()); FStar_TypeChecker_Env.encode_modul = (fun uu____2881 uu____2882 -> ()); FStar_TypeChecker_Env.encode_sig = (fun uu____2885 uu____2886 -> ()); FStar_TypeChecker_Env.preprocess = (fun e g -> (

let uu____2892 = (

let uu____2899 = (FStar_Options.peek ())
in ((e), (g), (uu____2899)))
in (uu____2892)::[])); FStar_TypeChecker_Env.solve = (fun uu____2915 uu____2916 uu____2917 -> ()); FStar_TypeChecker_Env.finish = (fun uu____2923 -> ()); FStar_TypeChecker_Env.refresh = (fun uu____2925 -> ())}




