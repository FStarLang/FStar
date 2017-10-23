
open Prims
open FStar_Pervasives

type z3_replay_result =
(FStar_SMTEncoding_Z3.unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either


let z3_result_as_replay_result : 'Auu____13 'Auu____14 'Auu____15 . ('Auu____15, ('Auu____14 * 'Auu____13)) FStar_Util.either  ->  ('Auu____15, 'Auu____14) FStar_Util.either = (fun uu___111_31 -> (match (uu___111_31) with
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
((FStar_All.pipe_right a.FStar_SMTEncoding_Term.assumption_fact_ids (FStar_Util.for_some should_enc_fid)) || (

let uu____458 = (FStar_Util.smap_try_find include_assumption_names a.FStar_SMTEncoding_Term.assumption_name)
in (FStar_Option.isSome uu____458)))
end))
in (

let theory_rev = (FStar_List.rev theory)
in (

let pruned_theory = (

let include_assumption_names = (FStar_Util.smap_create (Prims.parse_int "10000"))
in (FStar_List.fold_left (fun out d -> (match (d) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(

let uu____483 = (matches_fact_ids include_assumption_names a)
in (match (uu____483) with
| true -> begin
(d)::out
end
| uu____486 -> begin
out
end))
end
| FStar_SMTEncoding_Term.RetainAssumptions (names1) -> begin
((FStar_List.iter (fun x -> (FStar_Util.smap_add include_assumption_names x true)) names1);
(d)::out;
)
end
| uu____493 -> begin
(d)::out
end)) [] theory_rev))
in pruned_theory)))))


let filter_assertions : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Z3.unsat_core  ->  FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool) = (fun e core theory -> (match (core) with
| FStar_Pervasives_Native.None -> begin
(

let uu____520 = (filter_using_facts_from e theory)
in ((uu____520), (false)))
end
| FStar_Pervasives_Native.Some (core1) -> begin
(

let uu____530 = (FStar_List.fold_right (fun d uu____554 -> (match (uu____554) with
| (theory1, n_retained, n_pruned) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(match ((FStar_List.contains a.FStar_SMTEncoding_Term.assumption_name core1)) with
| true -> begin
(((d)::theory1), ((n_retained + (Prims.parse_int "1"))), (n_pruned))
end
| uu____597 -> begin
(match ((FStar_Util.starts_with a.FStar_SMTEncoding_Term.assumption_name "@")) with
| true -> begin
(((d)::theory1), (n_retained), (n_pruned))
end
| uu____608 -> begin
((theory1), (n_retained), ((n_pruned + (Prims.parse_int "1"))))
end)
end)
end
| uu____611 -> begin
(((d)::theory1), (n_retained), (n_pruned))
end)
end)) theory (([]), ((Prims.parse_int "0")), ((Prims.parse_int "0"))))
in (match (uu____530) with
| (theory', n_retained, n_pruned) -> begin
(

let uu____629 = (

let uu____632 = (

let uu____635 = (

let uu____636 = (

let uu____637 = (FStar_All.pipe_right core1 (FStar_String.concat ", "))
in (Prims.strcat "UNSAT CORE: " uu____637))
in FStar_SMTEncoding_Term.Caption (uu____636))
in (uu____635)::[])
in (FStar_List.append theory' uu____632))
in ((uu____629), (true)))
end))
end))


let filter_facts_without_core : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool) = (fun e x -> (

let uu____656 = (filter_using_facts_from e x)
in ((uu____656), (false))))

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

let uu____810 = (FStar_Util.string_of_int err1.error_fuel)
in (

let uu____811 = (FStar_Util.string_of_int err1.error_ifuel)
in (FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err1.error_reason uu____810 uu____811 (match ((FStar_Option.isSome err1.error_hint)) with
| true -> begin
"with hint"
end
| uu____814 -> begin
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

let uu____1201 = (

let uu____1204 = (

let uu____1205 = (

let uu____1206 = (FStar_Util.string_of_int n1)
in (

let uu____1207 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" uu____1206 uu____1207)))
in FStar_SMTEncoding_Term.Caption (uu____1205))
in (

let uu____1208 = (

let uu____1211 = (

let uu____1212 = (

let uu____1219 = (

let uu____1220 = (

let uu____1225 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (

let uu____1228 = (FStar_SMTEncoding_Term.n_fuel n1)
in ((uu____1225), (uu____1228))))
in (FStar_SMTEncoding_Util.mkEq uu____1220))
in ((uu____1219), (FStar_Pervasives_Native.None), ("@MaxFuel_assumption")))
in (FStar_SMTEncoding_Util.mkAssume uu____1212))
in (

let uu____1231 = (

let uu____1234 = (

let uu____1235 = (

let uu____1242 = (

let uu____1243 = (

let uu____1248 = (FStar_SMTEncoding_Util.mkApp (("MaxIFuel"), ([])))
in (

let uu____1251 = (FStar_SMTEncoding_Term.n_fuel i)
in ((uu____1248), (uu____1251))))
in (FStar_SMTEncoding_Util.mkEq uu____1243))
in ((uu____1242), (FStar_Pervasives_Native.None), ("@MaxIFuel_assumption")))
in (FStar_SMTEncoding_Util.mkAssume uu____1235))
in (uu____1234)::(settings.query_decl)::[])
in (uu____1211)::uu____1231))
in (uu____1204)::uu____1208))
in (

let uu____1254 = (

let uu____1257 = (

let uu____1260 = (

let uu____1263 = (

let uu____1264 = (

let uu____1269 = (FStar_Util.string_of_int rlimit)
in (("rlimit"), (uu____1269)))
in FStar_SMTEncoding_Term.SetOption (uu____1264))
in (uu____1263)::(FStar_SMTEncoding_Term.CheckSat)::(FStar_SMTEncoding_Term.GetReasonUnknown)::[])
in (

let uu____1270 = (

let uu____1273 = (

let uu____1276 = (FStar_Options.record_hints ())
in (match (uu____1276) with
| true -> begin
(FStar_SMTEncoding_Term.GetUnsatCore)::[]
end
| uu____1279 -> begin
[]
end))
in (

let uu____1280 = (

let uu____1283 = (

let uu____1286 = (FStar_Options.print_z3_statistics ())
in (match (uu____1286) with
| true -> begin
(FStar_SMTEncoding_Term.GetStatistics)::[]
end
| uu____1289 -> begin
[]
end))
in (FStar_List.append uu____1283 settings.query_suffix))
in (FStar_List.append uu____1273 uu____1280)))
in (FStar_List.append uu____1260 uu____1270)))
in (FStar_List.append label_assumptions uu____1257))
in (FStar_List.append uu____1201 uu____1254)))))))


let used_hint : query_settings  ->  Prims.bool = (fun s -> (FStar_Option.isSome s.query_hint))


let next_hint : Prims.string  ->  Prims.int  ->  FStar_Util.hint FStar_Pervasives_Native.option = (fun qname qindex -> (

let uu____1306 = (FStar_ST.op_Bang replaying_hints)
in (match (uu____1306) with
| FStar_Pervasives_Native.Some (hints) -> begin
(FStar_Util.find_map hints (fun uu___112_1366 -> (match (uu___112_1366) with
| FStar_Pervasives_Native.Some (hint) when ((Prims.op_Equality hint.FStar_Util.hint_name qname) && (Prims.op_Equality hint.FStar_Util.hint_index qindex)) -> begin
FStar_Pervasives_Native.Some (hint)
end
| uu____1372 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____1375 -> begin
FStar_Pervasives_Native.None
end)))


let query_errors : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  errors FStar_Pervasives_Native.option = (fun settings z3result -> (match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____1390) -> begin
FStar_Pervasives_Native.None
end
| uu____1391 -> begin
(

let uu____1392 = (FStar_SMTEncoding_Z3.status_string_and_errors z3result.FStar_SMTEncoding_Z3.z3result_status)
in (match (uu____1392) with
| (msg, error_labels) -> begin
(

let err1 = (

let uu____1402 = (FStar_List.map (fun uu____1423 -> (match (uu____1423) with
| (uu____1434, x, y) -> begin
((x), (y))
end)) error_labels)
in {error_reason = msg; error_fuel = settings.query_fuel; error_ifuel = settings.query_ifuel; error_hint = settings.query_hint; error_messages = uu____1402})
in FStar_Pervasives_Native.Some (err1))
end))
end))


let detail_hint_replay : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  Prims.unit = (fun settings z3result -> (

let uu____1445 = ((used_hint settings) && (FStar_Options.detail_hint_replay ()))
in (match (uu____1445) with
| true -> begin
(match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____1446) -> begin
()
end
| _failed -> begin
(

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((

let uu____1464 = (with_fuel_and_diagnostics settings label_assumptions)
in (FStar_SMTEncoding_Z3.ask (filter_assertions settings.query_env settings.query_hint) ((settings.query_hash), (settings.query_hint)) settings.query_all_labels uu____1464 FStar_Pervasives_Native.None (fun r -> (FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some (r))))));
(

let uu____1535 = (FStar_ST.op_Bang res)
in (FStar_Option.get uu____1535));
)))
in (FStar_SMTEncoding_ErrorReporting.detail_errors true settings.query_env settings.query_all_labels ask_z3))
end)
end
| uu____1602 -> begin
()
end)))


let find_localized_errors : errors Prims.list  ->  errors FStar_Pervasives_Native.option = (fun errs -> (FStar_All.pipe_right errs (FStar_List.tryFind (fun err1 -> (match (err1.error_messages) with
| [] -> begin
false
end
| uu____1623 -> begin
true
end)))))


let has_localized_errors : errors Prims.list  ->  Prims.bool = (fun errs -> (

let uu____1638 = (find_localized_errors errs)
in (FStar_Option.isSome uu____1638)))


let report_errors : query_settings  ->  Prims.unit = (fun settings -> (

let uu____1645 = ((FStar_Options.detail_errors ()) && (

let uu____1647 = (FStar_Options.n_cores ())
in (Prims.op_Equality uu____1647 (Prims.parse_int "1"))))
in (match (uu____1645) with
| true -> begin
(

let initial_fuel1 = (

let uu___113_1649 = settings
in (

let uu____1650 = (FStar_Options.initial_fuel ())
in (

let uu____1651 = (FStar_Options.initial_ifuel ())
in {query_env = uu___113_1649.query_env; query_decl = uu___113_1649.query_decl; query_name = uu___113_1649.query_name; query_index = uu___113_1649.query_index; query_range = uu___113_1649.query_range; query_fuel = uu____1650; query_ifuel = uu____1651; query_rlimit = uu___113_1649.query_rlimit; query_hint = FStar_Pervasives_Native.None; query_errors = uu___113_1649.query_errors; query_all_labels = uu___113_1649.query_all_labels; query_suffix = uu___113_1649.query_suffix; query_hash = uu___113_1649.query_hash})))
in (

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((

let uu____1670 = (with_fuel_and_diagnostics initial_fuel1 label_assumptions)
in (FStar_SMTEncoding_Z3.ask (filter_facts_without_core settings.query_env) ((settings.query_hash), (FStar_Pervasives_Native.None)) settings.query_all_labels uu____1670 FStar_Pervasives_Native.None (fun r -> (FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some (r))))));
(

let uu____1747 = (FStar_ST.op_Bang res)
in (FStar_Option.get uu____1747));
)))
in (FStar_SMTEncoding_ErrorReporting.detail_errors false settings.query_env settings.query_all_labels ask_z3)))
end
| uu____1814 -> begin
(

let uu____1815 = (find_localized_errors settings.query_errors)
in (match (uu____1815) with
| FStar_Pervasives_Native.Some (err1) -> begin
((FStar_All.pipe_right settings.query_errors (FStar_List.iter (fun e -> (

let uu____1825 = (

let uu____1826 = (error_to_short_string e)
in (Prims.strcat "SMT solver says: " uu____1826))
in (FStar_Errors.diag settings.query_range uu____1825)))));
(FStar_TypeChecker_Err.add_errors settings.query_env err1.error_messages);
)
end
| FStar_Pervasives_Native.None -> begin
(

let err_detail = (

let uu____1828 = (FStar_All.pipe_right settings.query_errors (FStar_List.map (fun e -> (

let uu____1838 = (error_to_short_string e)
in (Prims.strcat "SMT solver says: " uu____1838)))))
in (FStar_All.pipe_right uu____1828 (FStar_String.concat "; ")))
in (

let uu____1841 = (

let uu____1848 = (

let uu____1853 = (FStar_Util.format1 "Unknown assertion failed (%s)" err_detail)
in ((uu____1853), (settings.query_range)))
in (uu____1848)::[])
in (FStar_TypeChecker_Err.add_errors settings.query_env uu____1841)))
end))
end)))


let query_info : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  Prims.unit = (fun settings z3result -> (

let uu____1870 = ((FStar_Options.hint_info ()) || (FStar_Options.print_z3_statistics ()))
in (match (uu____1870) with
| true -> begin
(

let uu____1871 = (FStar_SMTEncoding_Z3.status_string_and_errors z3result.FStar_SMTEncoding_Z3.z3result_status)
in (match (uu____1871) with
| (status_string, errs) -> begin
(

let tag = (match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____1879) -> begin
"succeeded"
end
| uu____1880 -> begin
(Prims.strcat "failed {reason-unknown=" (Prims.strcat status_string "}"))
end)
in (

let range = (

let uu____1882 = (

let uu____1883 = (FStar_Range.string_of_range settings.query_range)
in (

let uu____1884 = (

let uu____1885 = (FStar_SMTEncoding_Z3.at_log_file ())
in (Prims.strcat uu____1885 ")"))
in (Prims.strcat uu____1883 uu____1884)))
in (Prims.strcat "(" uu____1882))
in (

let used_hint_tag = (match ((used_hint settings)) with
| true -> begin
" (with hint)"
end
| uu____1887 -> begin
""
end)
in (

let stats = (

let uu____1889 = (FStar_Options.print_z3_statistics ())
in (match (uu____1889) with
| true -> begin
(

let f = (fun k v1 a -> (Prims.strcat a (Prims.strcat k (Prims.strcat "=" (Prims.strcat v1 " ")))))
in (

let str = (FStar_Util.smap_fold z3result.FStar_SMTEncoding_Z3.z3result_statistics f "statistics={")
in (

let uu____1901 = (FStar_Util.substring str (Prims.parse_int "0") ((FStar_String.length str) - (Prims.parse_int "1")))
in (Prims.strcat uu____1901 "}"))))
end
| uu____1902 -> begin
""
end))
in ((

let uu____1904 = (

let uu____1907 = (

let uu____1910 = (

let uu____1913 = (FStar_Util.string_of_int settings.query_index)
in (

let uu____1914 = (

let uu____1917 = (

let uu____1920 = (

let uu____1923 = (FStar_Util.string_of_int z3result.FStar_SMTEncoding_Z3.z3result_time)
in (

let uu____1924 = (

let uu____1927 = (FStar_Util.string_of_int settings.query_fuel)
in (

let uu____1928 = (

let uu____1931 = (FStar_Util.string_of_int settings.query_ifuel)
in (

let uu____1932 = (

let uu____1935 = (FStar_Util.string_of_int settings.query_rlimit)
in (uu____1935)::(stats)::[])
in (uu____1931)::uu____1932))
in (uu____1927)::uu____1928))
in (uu____1923)::uu____1924))
in (used_hint_tag)::uu____1920)
in (tag)::uu____1917)
in (uu____1913)::uu____1914))
in (settings.query_name)::uu____1910)
in (range)::uu____1907)
in (FStar_Util.print "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n" uu____1904));
(FStar_All.pipe_right errs (FStar_List.iter (fun uu____1949 -> (match (uu____1949) with
| (uu____1956, msg, range1) -> begin
(

let e = (FStar_Errors.mk_issue FStar_Errors.EInfo (FStar_Pervasives_Native.Some (range1)) msg)
in (

let tag1 = (match ((used_hint settings)) with
| true -> begin
"(Hint-replay failed): "
end
| uu____1961 -> begin
""
end)
in (

let uu____1962 = (FStar_Errors.format_issue e)
in (FStar_Util.print2 "\t\t%s%s\n" tag1 uu____1962))))
end))));
)))))
end))
end
| uu____1963 -> begin
()
end)))


let record_hint : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  Prims.unit = (fun settings z3result -> (

let uu____1972 = (

let uu____1973 = (FStar_Options.record_hints ())
in (not (uu____1973)))
in (match (uu____1972) with
| true -> begin
()
end
| uu____1974 -> begin
(

let mk_hint = (fun core -> {FStar_Util.hint_name = settings.query_name; FStar_Util.hint_index = settings.query_index; FStar_Util.fuel = settings.query_fuel; FStar_Util.ifuel = settings.query_ifuel; FStar_Util.unsat_core = core; FStar_Util.query_elapsed_time = (Prims.parse_int "0"); FStar_Util.hash = (match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (core1) -> begin
z3result.FStar_SMTEncoding_Z3.z3result_query_hash
end
| uu____1991 -> begin
FStar_Pervasives_Native.None
end)})
in (

let store_hint = (fun hint -> (

let uu____1996 = (FStar_ST.op_Bang recorded_hints)
in (match (uu____1996) with
| FStar_Pervasives_Native.Some (l) -> begin
(FStar_ST.op_Colon_Equals recorded_hints (FStar_Pervasives_Native.Some ((FStar_List.append l ((FStar_Pervasives_Native.Some (hint))::[])))))
end
| uu____2110 -> begin
()
end)))
in (match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (unsat_core) -> begin
(match ((used_hint settings)) with
| true -> begin
(store_hint (mk_hint settings.query_hint))
end
| uu____2117 -> begin
(store_hint (mk_hint unsat_core))
end)
end
| uu____2118 -> begin
()
end)))
end)))


let process_result : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  errors FStar_Pervasives_Native.option = (fun settings result -> ((

let uu____2132 = ((used_hint settings) && (

let uu____2134 = (FStar_Options.z3_refresh ())
in (not (uu____2134))))
in (match (uu____2132) with
| true -> begin
(FStar_SMTEncoding_Z3.refresh ())
end
| uu____2135 -> begin
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

let uu____2224 = (f q res)
in (match (uu____2224) with
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

let uu____2257 = (

let uu____2264 = (match (env.FStar_TypeChecker_Env.qname_and_index) with
| FStar_Pervasives_Native.None -> begin
(failwith "No query name set!")
end
| FStar_Pervasives_Native.Some (q, n1) -> begin
(((FStar_Ident.text_of_lid q)), (n1))
end)
in (match (uu____2264) with
| (qname, index1) -> begin
(

let rlimit = (

let uu____2296 = (FStar_Options.z3_rlimit_factor ())
in (

let uu____2297 = (

let uu____2298 = (FStar_Options.z3_rlimit ())
in (uu____2298 * (Prims.parse_int "544656")))
in (uu____2296 * uu____2297)))
in (

let next_hint1 = (next_hint qname index1)
in (

let default_settings = (

let uu____2303 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____2304 = (FStar_Options.initial_fuel ())
in (

let uu____2305 = (FStar_Options.initial_ifuel ())
in {query_env = env; query_decl = query; query_name = qname; query_index = index1; query_range = uu____2303; query_fuel = uu____2304; query_ifuel = uu____2305; query_rlimit = rlimit; query_hint = FStar_Pervasives_Native.None; query_errors = []; query_all_labels = all_labels; query_suffix = suffix; query_hash = (match (next_hint1) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ({FStar_Util.hint_name = uu____2310; FStar_Util.hint_index = uu____2311; FStar_Util.fuel = uu____2312; FStar_Util.ifuel = uu____2313; FStar_Util.unsat_core = uu____2314; FStar_Util.query_elapsed_time = uu____2315; FStar_Util.hash = h}) -> begin
h
end)})))
in ((default_settings), (next_hint1)))))
end))
in (match (uu____2257) with
| (default_settings, next_hint1) -> begin
(

let use_hints_setting = (match (next_hint1) with
| FStar_Pervasives_Native.Some ({FStar_Util.hint_name = uu____2336; FStar_Util.hint_index = uu____2337; FStar_Util.fuel = i; FStar_Util.ifuel = j; FStar_Util.unsat_core = FStar_Pervasives_Native.Some (core); FStar_Util.query_elapsed_time = uu____2341; FStar_Util.hash = h}) -> begin
((

let uu___114_2350 = default_settings
in {query_env = uu___114_2350.query_env; query_decl = uu___114_2350.query_decl; query_name = uu___114_2350.query_name; query_index = uu___114_2350.query_index; query_range = uu___114_2350.query_range; query_fuel = i; query_ifuel = j; query_rlimit = uu___114_2350.query_rlimit; query_hint = FStar_Pervasives_Native.Some (core); query_errors = uu___114_2350.query_errors; query_all_labels = uu___114_2350.query_all_labels; query_suffix = uu___114_2350.query_suffix; query_hash = uu___114_2350.query_hash}))::[]
end
| uu____2353 -> begin
[]
end)
in (

let initial_fuel_max_ifuel = (

let uu____2359 = (

let uu____2360 = (FStar_Options.max_ifuel ())
in (

let uu____2361 = (FStar_Options.initial_ifuel ())
in (uu____2360 > uu____2361)))
in (match (uu____2359) with
| true -> begin
(

let uu____2364 = (

let uu___115_2365 = default_settings
in (

let uu____2366 = (FStar_Options.max_ifuel ())
in {query_env = uu___115_2365.query_env; query_decl = uu___115_2365.query_decl; query_name = uu___115_2365.query_name; query_index = uu___115_2365.query_index; query_range = uu___115_2365.query_range; query_fuel = uu___115_2365.query_fuel; query_ifuel = uu____2366; query_rlimit = uu___115_2365.query_rlimit; query_hint = uu___115_2365.query_hint; query_errors = uu___115_2365.query_errors; query_all_labels = uu___115_2365.query_all_labels; query_suffix = uu___115_2365.query_suffix; query_hash = uu___115_2365.query_hash}))
in (uu____2364)::[])
end
| uu____2367 -> begin
[]
end))
in (

let half_max_fuel_max_ifuel = (

let uu____2371 = (

let uu____2372 = (

let uu____2373 = (FStar_Options.max_fuel ())
in (uu____2373 / (Prims.parse_int "2")))
in (

let uu____2380 = (FStar_Options.initial_fuel ())
in (uu____2372 > uu____2380)))
in (match (uu____2371) with
| true -> begin
(

let uu____2383 = (

let uu___116_2384 = default_settings
in (

let uu____2385 = (

let uu____2386 = (FStar_Options.max_fuel ())
in (uu____2386 / (Prims.parse_int "2")))
in (

let uu____2393 = (FStar_Options.max_ifuel ())
in {query_env = uu___116_2384.query_env; query_decl = uu___116_2384.query_decl; query_name = uu___116_2384.query_name; query_index = uu___116_2384.query_index; query_range = uu___116_2384.query_range; query_fuel = uu____2385; query_ifuel = uu____2393; query_rlimit = uu___116_2384.query_rlimit; query_hint = uu___116_2384.query_hint; query_errors = uu___116_2384.query_errors; query_all_labels = uu___116_2384.query_all_labels; query_suffix = uu___116_2384.query_suffix; query_hash = uu___116_2384.query_hash})))
in (uu____2383)::[])
end
| uu____2394 -> begin
[]
end))
in (

let max_fuel_max_ifuel = (

let uu____2398 = ((

let uu____2403 = (FStar_Options.max_fuel ())
in (

let uu____2404 = (FStar_Options.initial_fuel ())
in (uu____2403 > uu____2404))) && (

let uu____2407 = (FStar_Options.max_ifuel ())
in (

let uu____2408 = (FStar_Options.initial_ifuel ())
in (uu____2407 >= uu____2408))))
in (match (uu____2398) with
| true -> begin
(

let uu____2411 = (

let uu___117_2412 = default_settings
in (

let uu____2413 = (FStar_Options.max_fuel ())
in (

let uu____2414 = (FStar_Options.max_ifuel ())
in {query_env = uu___117_2412.query_env; query_decl = uu___117_2412.query_decl; query_name = uu___117_2412.query_name; query_index = uu___117_2412.query_index; query_range = uu___117_2412.query_range; query_fuel = uu____2413; query_ifuel = uu____2414; query_rlimit = uu___117_2412.query_rlimit; query_hint = uu___117_2412.query_hint; query_errors = uu___117_2412.query_errors; query_all_labels = uu___117_2412.query_all_labels; query_suffix = uu___117_2412.query_suffix; query_hash = uu___117_2412.query_hash})))
in (uu____2411)::[])
end
| uu____2415 -> begin
[]
end))
in (

let min_fuel1 = (

let uu____2419 = (

let uu____2420 = (FStar_Options.min_fuel ())
in (

let uu____2421 = (FStar_Options.initial_fuel ())
in (uu____2420 < uu____2421)))
in (match (uu____2419) with
| true -> begin
(

let uu____2424 = (

let uu___118_2425 = default_settings
in (

let uu____2426 = (FStar_Options.min_fuel ())
in {query_env = uu___118_2425.query_env; query_decl = uu___118_2425.query_decl; query_name = uu___118_2425.query_name; query_index = uu___118_2425.query_index; query_range = uu___118_2425.query_range; query_fuel = uu____2426; query_ifuel = (Prims.parse_int "1"); query_rlimit = uu___118_2425.query_rlimit; query_hint = uu___118_2425.query_hint; query_errors = uu___118_2425.query_errors; query_all_labels = uu___118_2425.query_all_labels; query_suffix = uu___118_2425.query_suffix; query_hash = uu___118_2425.query_hash}))
in (uu____2424)::[])
end
| uu____2427 -> begin
[]
end))
in (

let all_configs = (FStar_List.append use_hints_setting (FStar_List.append ((default_settings)::[]) (FStar_List.append initial_fuel_max_ifuel (FStar_List.append half_max_fuel_max_ifuel max_fuel_max_ifuel))))
in (

let check_one_config = (fun config k -> ((

let uu____2444 = ((used_hint config) || (FStar_Options.z3_refresh ()))
in (match (uu____2444) with
| true -> begin
(FStar_SMTEncoding_Z3.refresh ())
end
| uu____2445 -> begin
()
end));
(

let uu____2446 = (with_fuel_and_diagnostics config [])
in (

let uu____2449 = (

let uu____2452 = (FStar_SMTEncoding_Z3.mk_fresh_scope ())
in FStar_Pervasives_Native.Some (uu____2452))
in (FStar_SMTEncoding_Z3.ask (filter_assertions config.query_env config.query_hint) ((config.query_hash), (config.query_hint)) config.query_all_labels uu____2446 uu____2449 k)));
))
in (

let check_all_configs = (fun configs -> (

let report1 = (fun errs -> (report_errors (

let uu___119_2473 = default_settings
in {query_env = uu___119_2473.query_env; query_decl = uu___119_2473.query_decl; query_name = uu___119_2473.query_name; query_index = uu___119_2473.query_index; query_range = uu___119_2473.query_range; query_fuel = uu___119_2473.query_fuel; query_ifuel = uu___119_2473.query_ifuel; query_rlimit = uu___119_2473.query_rlimit; query_hint = uu___119_2473.query_hint; query_errors = errs; query_all_labels = uu___119_2473.query_all_labels; query_suffix = uu___119_2473.query_suffix; query_hash = uu___119_2473.query_hash})))
in (fold_queries configs check_one_config process_result report1)))
in (

let uu____2474 = (

let uu____2481 = (FStar_Options.admit_smt_queries ())
in (

let uu____2482 = (FStar_Options.admit_except ())
in ((uu____2481), (uu____2482))))
in (match (uu____2474) with
| (true, uu____2487) -> begin
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

let uu____2499 = (

let uu____2500 = (

let uu____2501 = (

let uu____2502 = (FStar_Util.string_of_int default_settings.query_index)
in (Prims.strcat uu____2502 ")"))
in (Prims.strcat ", " uu____2501))
in (Prims.strcat default_settings.query_name uu____2500))
in (Prims.strcat "(" uu____2499))
in (Prims.op_disEquality full_query_id id))
end
| uu____2503 -> begin
(Prims.op_disEquality default_settings.query_name id)
end)
in (match ((not (skip))) with
| true -> begin
(check_all_configs all_configs)
end
| uu____2504 -> begin
()
end))
end))))))))))
end));
))


let solve : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun use_env_msg tcenv q -> ((

let uu____2527 = (

let uu____2528 = (

let uu____2529 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____2529))
in (FStar_Util.format1 "Starting query at %s" uu____2528))
in (FStar_SMTEncoding_Encode.push uu____2527));
(

let tcenv1 = (FStar_TypeChecker_Env.incr_query_index tcenv)
in (

let uu____2531 = (FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q)
in (match (uu____2531) with
| (prefix1, labels, qry, suffix) -> begin
(

let pop1 = (fun uu____2565 -> (

let uu____2566 = (

let uu____2567 = (

let uu____2568 = (FStar_TypeChecker_Env.get_range tcenv1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____2568))
in (FStar_Util.format1 "Ending query at %s" uu____2567))
in (FStar_SMTEncoding_Encode.pop uu____2566)))
in (match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.assumption_term = {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.FalseOp, uu____2569); FStar_SMTEncoding_Term.freevars = uu____2570; FStar_SMTEncoding_Term.rng = uu____2571}; FStar_SMTEncoding_Term.assumption_caption = uu____2572; FStar_SMTEncoding_Term.assumption_name = uu____2573; FStar_SMTEncoding_Term.assumption_fact_ids = uu____2574}) -> begin
(pop1 ())
end
| uu____2589 when tcenv1.FStar_TypeChecker_Env.admit -> begin
(pop1 ())
end
| FStar_SMTEncoding_Term.Assume (uu____2590) -> begin
((ask_and_report_errors tcenv1 labels prefix1 qry suffix);
(pop1 ());
)
end
| uu____2592 -> begin
(failwith "Impossible")
end))
end)));
))


let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init; FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push; FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop; FStar_TypeChecker_Env.encode_modul = FStar_SMTEncoding_Encode.encode_modul; FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig; FStar_TypeChecker_Env.preprocess = (fun e g -> (

let uu____2598 = (

let uu____2605 = (FStar_Options.peek ())
in ((e), (g), (uu____2605)))
in (uu____2598)::[])); FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}


let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun uu____2620 -> ()); FStar_TypeChecker_Env.push = (fun uu____2622 -> ()); FStar_TypeChecker_Env.pop = (fun uu____2624 -> ()); FStar_TypeChecker_Env.encode_modul = (fun uu____2627 uu____2628 -> ()); FStar_TypeChecker_Env.encode_sig = (fun uu____2631 uu____2632 -> ()); FStar_TypeChecker_Env.preprocess = (fun e g -> (

let uu____2638 = (

let uu____2645 = (FStar_Options.peek ())
in ((e), (g), (uu____2645)))
in (uu____2638)::[])); FStar_TypeChecker_Env.solve = (fun uu____2661 uu____2662 uu____2663 -> ()); FStar_TypeChecker_Env.finish = (fun uu____2669 -> ()); FStar_TypeChecker_Env.refresh = (fun uu____2671 -> ())}




