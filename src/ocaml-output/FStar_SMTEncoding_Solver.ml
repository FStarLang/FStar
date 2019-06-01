
open Prims
open FStar_Pervasives

type z3_replay_result =
(FStar_SMTEncoding_Z3.unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either


let z3_result_as_replay_result : 'Auu____30 'Auu____31 'Auu____32 . ('Auu____30, ('Auu____31 * 'Auu____32)) FStar_Util.either  ->  ('Auu____30, 'Auu____31) FStar_Util.either = (fun uu___0_49 -> (match (uu___0_49) with
| FStar_Util.Inl (l) -> begin
FStar_Util.Inl (l)
end
| FStar_Util.Inr (r, uu____64) -> begin
FStar_Util.Inr (r)
end))


let recorded_hints : FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let replaying_hints : FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let format_hints_file_name : Prims.string  ->  Prims.string = (fun src_filename -> (FStar_Util.format1 "%s.hints" src_filename))


let initialize_hints_db : 'Auu____100 . Prims.string  ->  'Auu____100  ->  unit = (fun src_filename format_filename -> ((

let uu____114 = (FStar_Options.record_hints ())
in (match (uu____114) with
| true -> begin
(FStar_ST.op_Colon_Equals recorded_hints (FStar_Pervasives_Native.Some ([])))
end
| uu____142 -> begin
()
end));
(

let uu____144 = (FStar_Options.use_hints ())
in (match (uu____144) with
| true -> begin
(

let norm_src_filename = (FStar_Util.normalize_file_path src_filename)
in (

let val_filename = (

let uu____151 = (FStar_Options.hint_file ())
in (match (uu____151) with
| FStar_Pervasives_Native.Some (fn) -> begin
fn
end
| FStar_Pervasives_Native.None -> begin
(format_hints_file_name norm_src_filename)
end))
in (

let uu____160 = (FStar_Util.read_hints val_filename)
in (match (uu____160) with
| FStar_Pervasives_Native.Some (hints) -> begin
(

let expected_digest = (FStar_Util.digest_of_file norm_src_filename)
in ((

let uu____167 = (FStar_Options.hint_info ())
in (match (uu____167) with
| true -> begin
(

let uu____170 = (

let uu____172 = (FStar_Options.hint_file ())
in (match (uu____172) with
| FStar_Pervasives_Native.Some (fn) -> begin
(Prims.op_Hat " from \'" (Prims.op_Hat val_filename "\'"))
end
| uu____182 -> begin
""
end))
in (FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename (match ((Prims.op_Equality hints.FStar_Util.module_digest expected_digest)) with
| true -> begin
"valid; using hints"
end
| uu____192 -> begin
"invalid; using potentially stale hints"
end) uu____170))
end
| uu____195 -> begin
()
end));
(FStar_ST.op_Colon_Equals replaying_hints (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)));
))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____220 = (FStar_Options.hint_info ())
in (match (uu____220) with
| true -> begin
(FStar_Util.print1 "(%s) Unable to read hint file.\n" norm_src_filename)
end
| uu____224 -> begin
()
end))
end))))
end
| uu____226 -> begin
()
end));
))


let finalize_hints_db : Prims.string  ->  unit = (fun src_filename -> ((

let uu____237 = (FStar_Options.record_hints ())
in (match (uu____237) with
| true -> begin
(

let hints = (

let uu____241 = (FStar_ST.op_Bang recorded_hints)
in (FStar_Option.get uu____241))
in (

let hints_db = (

let uu____268 = (FStar_Util.digest_of_file src_filename)
in {FStar_Util.module_digest = uu____268; FStar_Util.hints = hints})
in (

let norm_src_filename = (FStar_Util.normalize_file_path src_filename)
in (

let val_filename = (

let uu____274 = (FStar_Options.hint_file ())
in (match (uu____274) with
| FStar_Pervasives_Native.Some (fn) -> begin
fn
end
| FStar_Pervasives_Native.None -> begin
(format_hints_file_name norm_src_filename)
end))
in (FStar_Util.write_hints val_filename hints_db)))))
end
| uu____283 -> begin
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


let filter_using_facts_from : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun e theory -> (

let matches_fact_ids = (fun include_assumption_names a -> (match (a.FStar_SMTEncoding_Term.assumption_fact_ids) with
| [] -> begin
true
end
| uu____399 -> begin
((FStar_All.pipe_right a.FStar_SMTEncoding_Term.assumption_fact_ids (FStar_Util.for_some (fun uu___1_407 -> (match (uu___1_407) with
| FStar_SMTEncoding_Term.Name (lid) -> begin
(FStar_TypeChecker_Env.should_enc_lid e lid)
end
| uu____410 -> begin
false
end)))) || (

let uu____413 = (FStar_Util.smap_try_find include_assumption_names a.FStar_SMTEncoding_Term.assumption_name)
in (FStar_Option.isSome uu____413)))
end))
in (

let theory_rev = (FStar_List.rev theory)
in (

let pruned_theory = (

let include_assumption_names = (FStar_Util.smap_create (Prims.parse_int "10000"))
in (

let keep_decl = (fun uu___2_437 -> (match (uu___2_437) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(matches_fact_ids include_assumption_names a)
end
| FStar_SMTEncoding_Term.RetainAssumptions (names1) -> begin
((FStar_List.iter (fun x -> (FStar_Util.smap_add include_assumption_names x true)) names1);
true;
)
end
| FStar_SMTEncoding_Term.Module (uu____452) -> begin
(failwith "Solver.fs::keep_decl should never have been called with a Module decl")
end
| uu____462 -> begin
true
end))
in (FStar_List.fold_left (fun out d -> (match (d) with
| FStar_SMTEncoding_Term.Module (name, decls) -> begin
(

let uu____485 = (FStar_All.pipe_right decls (FStar_List.filter keep_decl))
in (FStar_All.pipe_right uu____485 (fun decls1 -> (FStar_SMTEncoding_Term.Module (((name), (decls1))))::out)))
end
| uu____503 -> begin
(

let uu____504 = (keep_decl d)
in (match (uu____504) with
| true -> begin
(d)::out
end
| uu____509 -> begin
out
end))
end)) [] theory_rev)))
in pruned_theory))))


let rec filter_assertions_with_stats : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Z3.unsat_core  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool * Prims.int * Prims.int) = (fun e core theory -> (match (core) with
| FStar_Pervasives_Native.None -> begin
(

let uu____560 = (filter_using_facts_from e theory)
in ((uu____560), (false), ((Prims.parse_int "0")), ((Prims.parse_int "0"))))
end
| FStar_Pervasives_Native.Some (core1) -> begin
(

let theory_rev = (FStar_List.rev theory)
in (

let uu____581 = (

let uu____592 = (

let uu____603 = (

let uu____606 = (

let uu____607 = (

let uu____609 = (FStar_All.pipe_right core1 (FStar_String.concat ", "))
in (Prims.op_Hat "UNSAT CORE: " uu____609))
in FStar_SMTEncoding_Term.Caption (uu____607))
in (uu____606)::[])
in ((uu____603), ((Prims.parse_int "0")), ((Prims.parse_int "0"))))
in (FStar_List.fold_left (fun uu____639 d -> (match (uu____639) with
| (theory1, n_retained, n_pruned) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(match ((FStar_List.contains a.FStar_SMTEncoding_Term.assumption_name core1)) with
| true -> begin
(((d)::theory1), ((n_retained + (Prims.parse_int "1"))), (n_pruned))
end
| uu____700 -> begin
(match ((FStar_Util.starts_with a.FStar_SMTEncoding_Term.assumption_name "@")) with
| true -> begin
(((d)::theory1), (n_retained), (n_pruned))
end
| uu____718 -> begin
((theory1), (n_retained), ((n_pruned + (Prims.parse_int "1"))))
end)
end)
end
| FStar_SMTEncoding_Term.Module (name, decls) -> begin
(

let uu____733 = (FStar_All.pipe_right decls (filter_assertions_with_stats e (FStar_Pervasives_Native.Some (core1))))
in (FStar_All.pipe_right uu____733 (fun uu____793 -> (match (uu____793) with
| (decls1, uu____818, r, p) -> begin
(((FStar_SMTEncoding_Term.Module (((name), (decls1))))::theory1), ((n_retained + r)), ((n_pruned + p)))
end))))
end
| uu____838 -> begin
(((d)::theory1), (n_retained), (n_pruned))
end)
end)) uu____592 theory_rev))
in (match (uu____581) with
| (theory', n_retained, n_pruned) -> begin
((theory'), (true), (n_retained), (n_pruned))
end)))
end))


let filter_assertions : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Z3.unsat_core  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool) = (fun e core theory -> (

let uu____900 = (filter_assertions_with_stats e core theory)
in (match (uu____900) with
| (theory1, b, uu____923, uu____924) -> begin
((theory1), (b))
end)))


let filter_facts_without_core : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool) = (fun e x -> (

let uu____960 = (filter_using_facts_from e x)
in ((uu____960), (false))))

type errors =
{error_reason : Prims.string; error_fuel : Prims.int; error_ifuel : Prims.int; error_hint : Prims.string Prims.list FStar_Pervasives_Native.option; error_messages : (FStar_Errors.raw_error * Prims.string * FStar_Range.range) Prims.list}


let __proj__Mkerrors__item__error_reason : errors  ->  Prims.string = (fun projectee -> (match (projectee) with
| {error_reason = error_reason; error_fuel = error_fuel; error_ifuel = error_ifuel; error_hint = error_hint; error_messages = error_messages} -> begin
error_reason
end))


let __proj__Mkerrors__item__error_fuel : errors  ->  Prims.int = (fun projectee -> (match (projectee) with
| {error_reason = error_reason; error_fuel = error_fuel; error_ifuel = error_ifuel; error_hint = error_hint; error_messages = error_messages} -> begin
error_fuel
end))


let __proj__Mkerrors__item__error_ifuel : errors  ->  Prims.int = (fun projectee -> (match (projectee) with
| {error_reason = error_reason; error_fuel = error_fuel; error_ifuel = error_ifuel; error_hint = error_hint; error_messages = error_messages} -> begin
error_ifuel
end))


let __proj__Mkerrors__item__error_hint : errors  ->  Prims.string Prims.list FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {error_reason = error_reason; error_fuel = error_fuel; error_ifuel = error_ifuel; error_hint = error_hint; error_messages = error_messages} -> begin
error_hint
end))


let __proj__Mkerrors__item__error_messages : errors  ->  (FStar_Errors.raw_error * Prims.string * FStar_Range.range) Prims.list = (fun projectee -> (match (projectee) with
| {error_reason = error_reason; error_fuel = error_fuel; error_ifuel = error_ifuel; error_hint = error_hint; error_messages = error_messages} -> begin
error_messages
end))


let error_to_short_string : errors  ->  Prims.string = (fun err -> (

let uu____1190 = (FStar_Util.string_of_int err.error_fuel)
in (

let uu____1192 = (FStar_Util.string_of_int err.error_ifuel)
in (FStar_Util.format4 "%s (fuel=%s; ifuel=%s; %s)" err.error_reason uu____1190 uu____1192 (match ((FStar_Option.isSome err.error_hint)) with
| true -> begin
"with hint"
end
| uu____1201 -> begin
""
end)))))

type query_settings =
{query_env : FStar_TypeChecker_Env.env; query_decl : FStar_SMTEncoding_Term.decl; query_name : Prims.string; query_index : Prims.int; query_range : FStar_Range.range; query_fuel : Prims.int; query_ifuel : Prims.int; query_rlimit : Prims.int; query_hint : FStar_SMTEncoding_Z3.unsat_core; query_errors : errors Prims.list; query_all_labels : FStar_SMTEncoding_Term.error_labels; query_suffix : FStar_SMTEncoding_Term.decl Prims.list; query_hash : Prims.string FStar_Pervasives_Native.option}


let __proj__Mkquery_settings__item__query_env : query_settings  ->  FStar_TypeChecker_Env.env = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_env
end))


let __proj__Mkquery_settings__item__query_decl : query_settings  ->  FStar_SMTEncoding_Term.decl = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_decl
end))


let __proj__Mkquery_settings__item__query_name : query_settings  ->  Prims.string = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_name
end))


let __proj__Mkquery_settings__item__query_index : query_settings  ->  Prims.int = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_index
end))


let __proj__Mkquery_settings__item__query_range : query_settings  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_range
end))


let __proj__Mkquery_settings__item__query_fuel : query_settings  ->  Prims.int = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_fuel
end))


let __proj__Mkquery_settings__item__query_ifuel : query_settings  ->  Prims.int = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_ifuel
end))


let __proj__Mkquery_settings__item__query_rlimit : query_settings  ->  Prims.int = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_rlimit
end))


let __proj__Mkquery_settings__item__query_hint : query_settings  ->  FStar_SMTEncoding_Z3.unsat_core = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_hint
end))


let __proj__Mkquery_settings__item__query_errors : query_settings  ->  errors Prims.list = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_errors
end))


let __proj__Mkquery_settings__item__query_all_labels : query_settings  ->  FStar_SMTEncoding_Term.error_labels = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_all_labels
end))


let __proj__Mkquery_settings__item__query_suffix : query_settings  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_suffix
end))


let __proj__Mkquery_settings__item__query_hash : query_settings  ->  Prims.string FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {query_env = query_env; query_decl = query_decl; query_name = query_name; query_index = query_index; query_range = query_range; query_fuel = query_fuel; query_ifuel = query_ifuel; query_rlimit = query_rlimit; query_hint = query_hint; query_errors = query_errors; query_all_labels = query_all_labels; query_suffix = query_suffix; query_hash = query_hash} -> begin
query_hash
end))


let settings_to_info : query_settings  ->  FStar_SMTEncoding_QIReport.query_info = (fun s -> {FStar_SMTEncoding_QIReport.query_info_name = s.query_name; FStar_SMTEncoding_QIReport.query_info_index = s.query_index; FStar_SMTEncoding_QIReport.query_info_range = s.query_range})


let with_fuel_and_diagnostics : query_settings  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun settings label_assumptions -> (

let n1 = settings.query_fuel
in (

let i = settings.query_ifuel
in (

let rlimit = settings.query_rlimit
in (

let uu____1737 = (

let uu____1740 = (

let uu____1741 = (

let uu____1743 = (FStar_Util.string_of_int n1)
in (

let uu____1745 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" uu____1743 uu____1745)))
in FStar_SMTEncoding_Term.Caption (uu____1741))
in (

let uu____1748 = (

let uu____1751 = (

let uu____1752 = (

let uu____1760 = (

let uu____1761 = (

let uu____1766 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (

let uu____1771 = (FStar_SMTEncoding_Term.n_fuel n1)
in ((uu____1766), (uu____1771))))
in (FStar_SMTEncoding_Util.mkEq uu____1761))
in ((uu____1760), (FStar_Pervasives_Native.None), ("@MaxFuel_assumption")))
in (FStar_SMTEncoding_Util.mkAssume uu____1752))
in (

let uu____1775 = (

let uu____1778 = (

let uu____1779 = (

let uu____1787 = (

let uu____1788 = (

let uu____1793 = (FStar_SMTEncoding_Util.mkApp (("MaxIFuel"), ([])))
in (

let uu____1798 = (FStar_SMTEncoding_Term.n_fuel i)
in ((uu____1793), (uu____1798))))
in (FStar_SMTEncoding_Util.mkEq uu____1788))
in ((uu____1787), (FStar_Pervasives_Native.None), ("@MaxIFuel_assumption")))
in (FStar_SMTEncoding_Util.mkAssume uu____1779))
in (uu____1778)::(settings.query_decl)::[])
in (uu____1751)::uu____1775))
in (uu____1740)::uu____1748))
in (

let uu____1802 = (

let uu____1805 = (

let uu____1808 = (

let uu____1811 = (

let uu____1812 = (

let uu____1819 = (FStar_Util.string_of_int rlimit)
in (("rlimit"), (uu____1819)))
in FStar_SMTEncoding_Term.SetOption (uu____1812))
in (uu____1811)::(FStar_SMTEncoding_Term.CheckSat)::(FStar_SMTEncoding_Term.GetReasonUnknown)::(FStar_SMTEncoding_Term.GetUnsatCore)::[])
in (

let uu____1824 = (

let uu____1827 = (

let uu____1830 = ((FStar_Options.print_z3_statistics ()) || (FStar_Options.query_stats ()))
in (match (uu____1830) with
| true -> begin
(FStar_SMTEncoding_Term.GetStatistics)::[]
end
| uu____1835 -> begin
[]
end))
in (FStar_List.append uu____1827 settings.query_suffix))
in (FStar_List.append uu____1808 uu____1824)))
in (FStar_List.append label_assumptions uu____1805))
in (FStar_List.append uu____1737 uu____1802)))))))


let used_hint : query_settings  ->  Prims.bool = (fun s -> (FStar_Option.isSome s.query_hint))


let get_hint_for : Prims.string  ->  Prims.int  ->  FStar_Util.hint FStar_Pervasives_Native.option = (fun qname qindex -> (

let uu____1864 = (FStar_ST.op_Bang replaying_hints)
in (match (uu____1864) with
| FStar_Pervasives_Native.Some (hints) -> begin
(FStar_Util.find_map hints (fun uu___3_1897 -> (match (uu___3_1897) with
| FStar_Pervasives_Native.Some (hint) when ((Prims.op_Equality hint.FStar_Util.hint_name qname) && (Prims.op_Equality hint.FStar_Util.hint_index qindex)) -> begin
FStar_Pervasives_Native.Some (hint)
end
| uu____1905 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____1908 -> begin
FStar_Pervasives_Native.None
end)))


let query_errors : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  errors FStar_Pervasives_Native.option = (fun settings z3result -> (match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____1926) -> begin
FStar_Pervasives_Native.None
end
| uu____1927 -> begin
(

let uu____1928 = (FStar_SMTEncoding_Z3.status_string_and_errors z3result.FStar_SMTEncoding_Z3.z3result_status)
in (match (uu____1928) with
| (msg, error_labels) -> begin
(

let err = (

let uu____1941 = (FStar_List.map (fun uu____1969 -> (match (uu____1969) with
| (uu____1984, x, y) -> begin
((FStar_Errors.Error_Z3SolverError), (x), (y))
end)) error_labels)
in {error_reason = msg; error_fuel = settings.query_fuel; error_ifuel = settings.query_ifuel; error_hint = settings.query_hint; error_messages = uu____1941})
in FStar_Pervasives_Native.Some (err))
end))
end))


let detail_hint_replay : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  unit = (fun settings z3result -> (

let uu____2001 = ((used_hint settings) && (FStar_Options.detail_hint_replay ()))
in (match (uu____2001) with
| true -> begin
(match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____2004) -> begin
()
end
| _failed -> begin
(

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((

let uu____2024 = (with_fuel_and_diagnostics settings label_assumptions)
in (FStar_SMTEncoding_Z3.ask (settings_to_info settings) (filter_assertions settings.query_env settings.query_hint) settings.query_hash settings.query_all_labels uu____2024 FStar_Pervasives_Native.None (fun r -> (FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some (r)))) false));
(

let uu____2053 = (FStar_ST.op_Bang res)
in (FStar_Option.get uu____2053));
)))
in (FStar_SMTEncoding_ErrorReporting.detail_errors true settings.query_env settings.query_all_labels ask_z3))
end)
end
| uu____2080 -> begin
()
end)))


let find_localized_errors : errors Prims.list  ->  errors FStar_Pervasives_Native.option = (fun errs -> (FStar_All.pipe_right errs (FStar_List.tryFind (fun err -> (match (err.error_messages) with
| [] -> begin
false
end
| uu____2109 -> begin
true
end)))))


let has_localized_errors : errors Prims.list  ->  Prims.bool = (fun errs -> (

let uu____2131 = (find_localized_errors errs)
in (FStar_Option.isSome uu____2131)))


let report_errors : query_settings  ->  unit = (fun settings -> ((

let uu____2141 = (find_localized_errors settings.query_errors)
in (match (uu____2141) with
| FStar_Pervasives_Native.Some (err) -> begin
((FStar_All.pipe_right settings.query_errors (FStar_List.iter (fun e -> (

let uu____2151 = (

let uu____2153 = (error_to_short_string e)
in (Prims.op_Hat "SMT solver says: " uu____2153))
in (FStar_Errors.diag settings.query_range uu____2151)))));
(FStar_TypeChecker_Err.add_errors settings.query_env err.error_messages);
)
end
| FStar_Pervasives_Native.None -> begin
(

let err_detail = (

let uu____2158 = (FStar_All.pipe_right settings.query_errors (FStar_List.map (fun e -> (

let uu____2171 = (error_to_short_string e)
in (Prims.op_Hat "SMT solver says: " uu____2171)))))
in (FStar_All.pipe_right uu____2158 (FStar_String.concat "; ")))
in (

let uu____2179 = (

let uu____2189 = (

let uu____2197 = (FStar_Util.format1 "Unknown assertion failed (%s)" err_detail)
in ((FStar_Errors.Error_UnknownFatal_AssertionFailure), (uu____2197), (settings.query_range)))
in (uu____2189)::[])
in (FStar_TypeChecker_Err.add_errors settings.query_env uu____2179)))
end));
(

let uu____2215 = ((FStar_Options.detail_errors ()) && (

let uu____2218 = (FStar_Options.n_cores ())
in (Prims.op_Equality uu____2218 (Prims.parse_int "1"))))
in (match (uu____2215) with
| true -> begin
(

let initial_fuel1 = (

let uu___236_2224 = settings
in (

let uu____2225 = (FStar_Options.initial_fuel ())
in (

let uu____2227 = (FStar_Options.initial_ifuel ())
in {query_env = uu___236_2224.query_env; query_decl = uu___236_2224.query_decl; query_name = uu___236_2224.query_name; query_index = uu___236_2224.query_index; query_range = uu___236_2224.query_range; query_fuel = uu____2225; query_ifuel = uu____2227; query_rlimit = uu___236_2224.query_rlimit; query_hint = FStar_Pervasives_Native.None; query_errors = uu___236_2224.query_errors; query_all_labels = uu___236_2224.query_all_labels; query_suffix = uu___236_2224.query_suffix; query_hash = uu___236_2224.query_hash})))
in (

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((

let uu____2250 = (with_fuel_and_diagnostics initial_fuel1 label_assumptions)
in (FStar_SMTEncoding_Z3.ask (settings_to_info settings) (filter_facts_without_core settings.query_env) settings.query_hash settings.query_all_labels uu____2250 FStar_Pervasives_Native.None (fun r -> (FStar_ST.op_Colon_Equals res (FStar_Pervasives_Native.Some (r)))) false));
(

let uu____2279 = (FStar_ST.op_Bang res)
in (FStar_Option.get uu____2279));
)))
in (FStar_SMTEncoding_ErrorReporting.detail_errors false settings.query_env settings.query_all_labels ask_z3)))
end
| uu____2306 -> begin
()
end));
))


let query_info : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  unit = (fun settings z3result -> (

let process_unsat_core = (fun core -> (

let accumulator = (fun uu____2344 -> (

let r = (FStar_Util.mk_ref [])
in (

let uu____2355 = (

let module_names = (FStar_Util.mk_ref [])
in (((fun m -> (

let ms = (FStar_ST.op_Bang module_names)
in (match ((FStar_List.contains m ms)) with
| true -> begin
()
end
| uu____2425 -> begin
(FStar_ST.op_Colon_Equals module_names ((m)::ms))
end)))), ((fun uu____2455 -> (

let uu____2456 = (FStar_ST.op_Bang module_names)
in (FStar_All.pipe_right uu____2456 (FStar_Util.sort_with FStar_String.compare)))))))
in (match (uu____2355) with
| (add1, get1) -> begin
((add1), (get1))
end))))
in (

let uu____2538 = (accumulator ())
in (match (uu____2538) with
| (add_module_name, get_module_names) -> begin
(

let uu____2575 = (accumulator ())
in (match (uu____2575) with
| (add_discarded_name, get_discarded_names) -> begin
(

let parse_axiom_name = (fun s -> (

let chars = (FStar_String.list_of_string s)
in (

let first_upper_index = (FStar_Util.try_find_index FStar_Util.is_upper chars)
in (match (first_upper_index) with
| FStar_Pervasives_Native.None -> begin
((add_discarded_name s);
[];
)
end
| FStar_Pervasives_Native.Some (first_upper_index1) -> begin
(

let name_and_suffix = (FStar_Util.substring_from s first_upper_index1)
in (

let components = (FStar_String.split ((46 (*.*))::[]) name_and_suffix)
in (

let excluded_suffixes = ("fuel_instrumented")::("_pretyping")::("_Tm_refine")::("_Tm_abs")::("@")::("_interpretation_Tm_arrow")::("MaxFuel_assumption")::("MaxIFuel_assumption")::[]
in (

let exclude_suffix = (fun s1 -> (

let s2 = (FStar_Util.trim_string s1)
in (

let sopt = (FStar_Util.find_map excluded_suffixes (fun sfx -> (match ((FStar_Util.contains s2 sfx)) with
| true -> begin
(

let uu____2698 = (FStar_List.hd (FStar_Util.split s2 sfx))
in FStar_Pervasives_Native.Some (uu____2698))
end
| uu____2702 -> begin
FStar_Pervasives_Native.None
end)))
in (match (sopt) with
| FStar_Pervasives_Native.None -> begin
(match ((Prims.op_Equality s2 "")) with
| true -> begin
[]
end
| uu____2716 -> begin
(s2)::[]
end)
end
| FStar_Pervasives_Native.Some (s3) -> begin
(match ((Prims.op_Equality s3 "")) with
| true -> begin
[]
end
| uu____2730 -> begin
(s3)::[]
end)
end))))
in (

let components1 = (match (components) with
| [] -> begin
[]
end
| uu____2743 -> begin
(

let uu____2747 = (FStar_Util.prefix components)
in (match (uu____2747) with
| (module_name, last1) -> begin
(

let components1 = (

let uu____2774 = (exclude_suffix last1)
in (FStar_List.append module_name uu____2774))
in ((match (components1) with
| [] -> begin
()
end
| (uu____2781)::[] -> begin
()
end
| uu____2785 -> begin
(add_module_name (FStar_String.concat "." module_name))
end);
components1;
))
end))
end)
in (match ((Prims.op_Equality components1 [])) with
| true -> begin
((add_discarded_name s);
[];
)
end
| uu____2800 -> begin
(

let uu____2802 = (FStar_All.pipe_right components1 (FStar_String.concat "."))
in (uu____2802)::[])
end))))))
end))))
in (match (core) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.print_string "no unsat core\n")
end
| FStar_Pervasives_Native.Some (core1) -> begin
(

let core2 = (FStar_List.collect parse_axiom_name core1)
in ((

let uu____2829 = (

let uu____2831 = (get_module_names ())
in (FStar_All.pipe_right uu____2831 (FStar_String.concat "\nZ3 Proof Stats:\t")))
in (FStar_Util.print1 "Z3 Proof Stats: Modules relevant to this proof:\nZ3 Proof Stats:\t%s\n" uu____2829));
(FStar_Util.print1 "Z3 Proof Stats (Detail 1): Specifically:\nZ3 Proof Stats (Detail 1):\t%s\n" (FStar_String.concat "\nZ3 Proof Stats (Detail 1):\t" core2));
(

let uu____2844 = (

let uu____2846 = (get_discarded_names ())
in (FStar_All.pipe_right uu____2846 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Z3 Proof Stats (Detail 2): Note, this report ignored the following names in the context: %s\n" uu____2844));
))
end))
end))
end))))
in (

let uu____2856 = ((FStar_Options.hint_info ()) || (FStar_Options.query_stats ()))
in (match (uu____2856) with
| true -> begin
(

let uu____2859 = (FStar_SMTEncoding_Z3.status_string_and_errors z3result.FStar_SMTEncoding_Z3.z3result_status)
in (match (uu____2859) with
| (status_string, errs) -> begin
(

let at_log_file = (match (z3result.FStar_SMTEncoding_Z3.z3result_log_file) with
| FStar_Pervasives_Native.None -> begin
""
end
| FStar_Pervasives_Native.Some (s) -> begin
(Prims.op_Hat "@" s)
end)
in (

let uu____2878 = (match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (core) -> begin
(("succeeded"), (core))
end
| uu____2892 -> begin
(((Prims.op_Hat "failed {reason-unknown=" (Prims.op_Hat status_string "}"))), (FStar_Pervasives_Native.None))
end)
in (match (uu____2878) with
| (tag, core) -> begin
(

let range = (

let uu____2905 = (

let uu____2907 = (FStar_Range.string_of_range settings.query_range)
in (Prims.op_Hat uu____2907 (Prims.op_Hat at_log_file ")")))
in (Prims.op_Hat "(" uu____2905))
in (

let used_hint_tag = (match ((used_hint settings)) with
| true -> begin
" (with hint)"
end
| uu____2916 -> begin
""
end)
in (

let stats = (

let uu____2921 = (FStar_Options.query_stats ())
in (match (uu____2921) with
| true -> begin
(

let f = (fun k v1 a -> (Prims.op_Hat a (Prims.op_Hat k (Prims.op_Hat "=" (Prims.op_Hat v1 " ")))))
in (

let str = (FStar_Util.smap_fold z3result.FStar_SMTEncoding_Z3.z3result_statistics f "statistics={")
in (

let uu____2955 = (FStar_Util.substring str (Prims.parse_int "0") ((FStar_String.length str) - (Prims.parse_int "1")))
in (Prims.op_Hat uu____2955 "}"))))
end
| uu____2960 -> begin
""
end))
in ((

let uu____2964 = (

let uu____2968 = (

let uu____2972 = (

let uu____2976 = (FStar_Util.string_of_int settings.query_index)
in (

let uu____2978 = (

let uu____2982 = (

let uu____2986 = (

let uu____2990 = (FStar_Util.string_of_int z3result.FStar_SMTEncoding_Z3.z3result_time)
in (

let uu____2992 = (

let uu____2996 = (FStar_Util.string_of_int settings.query_fuel)
in (

let uu____2998 = (

let uu____3002 = (FStar_Util.string_of_int settings.query_ifuel)
in (

let uu____3004 = (

let uu____3008 = (FStar_Util.string_of_int settings.query_rlimit)
in (uu____3008)::(stats)::[])
in (uu____3002)::uu____3004))
in (uu____2996)::uu____2998))
in (uu____2990)::uu____2992))
in (used_hint_tag)::uu____2986)
in (tag)::uu____2982)
in (uu____2976)::uu____2978))
in (settings.query_name)::uu____2972)
in (range)::uu____2968)
in (FStar_Util.print "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n" uu____2964));
(

let uu____3023 = (FStar_Options.print_z3_statistics ())
in (match (uu____3023) with
| true -> begin
(process_unsat_core core)
end
| uu____3026 -> begin
()
end));
(FStar_All.pipe_right errs (FStar_List.iter (fun uu____3049 -> (match (uu____3049) with
| (uu____3057, msg, range1) -> begin
(

let tag1 = (match ((used_hint settings)) with
| true -> begin
"(Hint-replay failed): "
end
| uu____3067 -> begin
""
end)
in (FStar_Errors.log_issue range1 ((FStar_Errors.Warning_HitReplayFailed), ((Prims.op_Hat tag1 msg)))))
end))));
))))
end)))
end))
end
| uu____3071 -> begin
()
end))))


let record_hint : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  unit = (fun settings z3result -> (

let uu____3084 = (

let uu____3086 = (FStar_Options.record_hints ())
in (not (uu____3086)))
in (match (uu____3084) with
| true -> begin
()
end
| uu____3089 -> begin
(

let mk_hint = (fun core -> {FStar_Util.hint_name = settings.query_name; FStar_Util.hint_index = settings.query_index; FStar_Util.fuel = settings.query_fuel; FStar_Util.ifuel = settings.query_ifuel; FStar_Util.unsat_core = core; FStar_Util.query_elapsed_time = (Prims.parse_int "0"); FStar_Util.hash = (match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____3112) -> begin
z3result.FStar_SMTEncoding_Z3.z3result_query_hash
end
| uu____3113 -> begin
FStar_Pervasives_Native.None
end)})
in (

let store_hint = (fun hint -> (

let uu____3121 = (FStar_ST.op_Bang recorded_hints)
in (match (uu____3121) with
| FStar_Pervasives_Native.Some (l) -> begin
(FStar_ST.op_Colon_Equals recorded_hints (FStar_Pervasives_Native.Some ((FStar_List.append l ((FStar_Pervasives_Native.Some (hint))::[])))))
end
| uu____3177 -> begin
()
end)))
in (match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None) -> begin
(

let uu____3184 = (

let uu____3185 = (get_hint_for settings.query_name settings.query_index)
in (FStar_Option.get uu____3185))
in (store_hint uu____3184))
end
| FStar_SMTEncoding_Z3.UNSAT (unsat_core) -> begin
(match ((used_hint settings)) with
| true -> begin
(store_hint (mk_hint settings.query_hint))
end
| uu____3190 -> begin
(store_hint (mk_hint unsat_core))
end)
end
| uu____3192 -> begin
()
end)))
end)))


let process_result : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  errors FStar_Pervasives_Native.option = (fun settings result -> (

let errs = (query_errors settings result)
in ((query_info settings result);
(record_hint settings result);
(detail_hint_replay settings result);
errs;
)))


let fold_queries : query_settings Prims.list  ->  (query_settings  ->  (FStar_SMTEncoding_Z3.z3result  ->  unit)  ->  unit)  ->  (query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  errors FStar_Pervasives_Native.option)  ->  (errors Prims.list  ->  unit)  ->  unit = (fun qs ask1 f report1 -> (

let rec aux = (fun acc qs1 -> (match (qs1) with
| [] -> begin
(report1 acc)
end
| (q)::qs2 -> begin
(ask1 q (fun res -> (

let uu____3303 = (f q res)
in (match (uu____3303) with
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

let uu____3342 = (

let uu____3349 = (match (env.FStar_TypeChecker_Env.qtbl_name_and_index) with
| (uu____3362, FStar_Pervasives_Native.None) -> begin
(failwith "No query name set!")
end
| (uu____3388, FStar_Pervasives_Native.Some (q, n1)) -> begin
(

let uu____3411 = (FStar_Ident.text_of_lid q)
in ((uu____3411), (n1)))
end)
in (match (uu____3349) with
| (qname, index1) -> begin
(

let rlimit = (

let uu____3429 = (FStar_Options.z3_rlimit_factor ())
in (

let uu____3431 = (

let uu____3433 = (FStar_Options.z3_rlimit ())
in (uu____3433 * (Prims.parse_int "544656")))
in (uu____3429 * uu____3431)))
in (

let next_hint = (get_hint_for qname index1)
in (

let default_settings = (

let uu____3440 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____3441 = (FStar_Options.initial_fuel ())
in (

let uu____3443 = (FStar_Options.initial_ifuel ())
in {query_env = env; query_decl = query; query_name = qname; query_index = index1; query_range = uu____3440; query_fuel = uu____3441; query_ifuel = uu____3443; query_rlimit = rlimit; query_hint = FStar_Pervasives_Native.None; query_errors = []; query_all_labels = all_labels; query_suffix = suffix; query_hash = (match (next_hint) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ({FStar_Util.hint_name = uu____3452; FStar_Util.hint_index = uu____3453; FStar_Util.fuel = uu____3454; FStar_Util.ifuel = uu____3455; FStar_Util.unsat_core = uu____3456; FStar_Util.query_elapsed_time = uu____3457; FStar_Util.hash = h}) -> begin
h
end)})))
in ((default_settings), (next_hint)))))
end))
in (match (uu____3342) with
| (default_settings, next_hint) -> begin
(

let use_hints_setting = (match (next_hint) with
| FStar_Pervasives_Native.Some ({FStar_Util.hint_name = uu____3485; FStar_Util.hint_index = uu____3486; FStar_Util.fuel = i; FStar_Util.ifuel = j; FStar_Util.unsat_core = FStar_Pervasives_Native.Some (core); FStar_Util.query_elapsed_time = uu____3490; FStar_Util.hash = h}) -> begin
((

let uu___425_3507 = default_settings
in {query_env = uu___425_3507.query_env; query_decl = uu___425_3507.query_decl; query_name = uu___425_3507.query_name; query_index = uu___425_3507.query_index; query_range = uu___425_3507.query_range; query_fuel = i; query_ifuel = j; query_rlimit = uu___425_3507.query_rlimit; query_hint = FStar_Pervasives_Native.Some (core); query_errors = uu___425_3507.query_errors; query_all_labels = uu___425_3507.query_all_labels; query_suffix = uu___425_3507.query_suffix; query_hash = uu___425_3507.query_hash}))::[]
end
| uu____3511 -> begin
[]
end)
in (

let initial_fuel_max_ifuel = (

let uu____3517 = (

let uu____3519 = (FStar_Options.max_ifuel ())
in (

let uu____3521 = (FStar_Options.initial_ifuel ())
in (uu____3519 > uu____3521)))
in (match (uu____3517) with
| true -> begin
(

let uu____3526 = (

let uu___430_3527 = default_settings
in (

let uu____3528 = (FStar_Options.max_ifuel ())
in {query_env = uu___430_3527.query_env; query_decl = uu___430_3527.query_decl; query_name = uu___430_3527.query_name; query_index = uu___430_3527.query_index; query_range = uu___430_3527.query_range; query_fuel = uu___430_3527.query_fuel; query_ifuel = uu____3528; query_rlimit = uu___430_3527.query_rlimit; query_hint = uu___430_3527.query_hint; query_errors = uu___430_3527.query_errors; query_all_labels = uu___430_3527.query_all_labels; query_suffix = uu___430_3527.query_suffix; query_hash = uu___430_3527.query_hash}))
in (uu____3526)::[])
end
| uu____3530 -> begin
[]
end))
in (

let half_max_fuel_max_ifuel = (

let uu____3535 = (

let uu____3537 = (

let uu____3539 = (FStar_Options.max_fuel ())
in (uu____3539 / (Prims.parse_int "2")))
in (

let uu____3542 = (FStar_Options.initial_fuel ())
in (uu____3537 > uu____3542)))
in (match (uu____3535) with
| true -> begin
(

let uu____3547 = (

let uu___434_3548 = default_settings
in (

let uu____3549 = (

let uu____3551 = (FStar_Options.max_fuel ())
in (uu____3551 / (Prims.parse_int "2")))
in (

let uu____3554 = (FStar_Options.max_ifuel ())
in {query_env = uu___434_3548.query_env; query_decl = uu___434_3548.query_decl; query_name = uu___434_3548.query_name; query_index = uu___434_3548.query_index; query_range = uu___434_3548.query_range; query_fuel = uu____3549; query_ifuel = uu____3554; query_rlimit = uu___434_3548.query_rlimit; query_hint = uu___434_3548.query_hint; query_errors = uu___434_3548.query_errors; query_all_labels = uu___434_3548.query_all_labels; query_suffix = uu___434_3548.query_suffix; query_hash = uu___434_3548.query_hash})))
in (uu____3547)::[])
end
| uu____3556 -> begin
[]
end))
in (

let max_fuel_max_ifuel = (

let uu____3561 = ((

let uu____3567 = (FStar_Options.max_fuel ())
in (

let uu____3569 = (FStar_Options.initial_fuel ())
in (uu____3567 > uu____3569))) && (

let uu____3573 = (FStar_Options.max_ifuel ())
in (

let uu____3575 = (FStar_Options.initial_ifuel ())
in (uu____3573 >= uu____3575))))
in (match (uu____3561) with
| true -> begin
(

let uu____3580 = (

let uu___438_3581 = default_settings
in (

let uu____3582 = (FStar_Options.max_fuel ())
in (

let uu____3584 = (FStar_Options.max_ifuel ())
in {query_env = uu___438_3581.query_env; query_decl = uu___438_3581.query_decl; query_name = uu___438_3581.query_name; query_index = uu___438_3581.query_index; query_range = uu___438_3581.query_range; query_fuel = uu____3582; query_ifuel = uu____3584; query_rlimit = uu___438_3581.query_rlimit; query_hint = uu___438_3581.query_hint; query_errors = uu___438_3581.query_errors; query_all_labels = uu___438_3581.query_all_labels; query_suffix = uu___438_3581.query_suffix; query_hash = uu___438_3581.query_hash})))
in (uu____3580)::[])
end
| uu____3586 -> begin
[]
end))
in (

let min_fuel1 = (

let uu____3591 = (

let uu____3593 = (FStar_Options.min_fuel ())
in (

let uu____3595 = (FStar_Options.initial_fuel ())
in (uu____3593 < uu____3595)))
in (match (uu____3591) with
| true -> begin
(

let uu____3600 = (

let uu___442_3601 = default_settings
in (

let uu____3602 = (FStar_Options.min_fuel ())
in {query_env = uu___442_3601.query_env; query_decl = uu___442_3601.query_decl; query_name = uu___442_3601.query_name; query_index = uu___442_3601.query_index; query_range = uu___442_3601.query_range; query_fuel = uu____3602; query_ifuel = (Prims.parse_int "1"); query_rlimit = uu___442_3601.query_rlimit; query_hint = uu___442_3601.query_hint; query_errors = uu___442_3601.query_errors; query_all_labels = uu___442_3601.query_all_labels; query_suffix = uu___442_3601.query_suffix; query_hash = uu___442_3601.query_hash}))
in (uu____3600)::[])
end
| uu____3605 -> begin
[]
end))
in (

let all_configs = (FStar_List.append use_hints_setting (FStar_List.append ((default_settings)::[]) (FStar_List.append initial_fuel_max_ifuel (FStar_List.append half_max_fuel_max_ifuel max_fuel_max_ifuel))))
in (

let check_one_config = (fun config1 k -> ((

let uu____3627 = (FStar_Options.z3_refresh ())
in (match (uu____3627) with
| true -> begin
(FStar_SMTEncoding_Z3.refresh ())
end
| uu____3630 -> begin
()
end));
(

let uu____3632 = (with_fuel_and_diagnostics config1 [])
in (

let uu____3635 = (

let uu____3638 = (FStar_SMTEncoding_Z3.mk_fresh_scope ())
in FStar_Pervasives_Native.Some (uu____3638))
in (FStar_SMTEncoding_Z3.ask (settings_to_info config1) (filter_assertions config1.query_env config1.query_hint) config1.query_hash config1.query_all_labels uu____3632 uu____3635 k (used_hint config1))));
))
in (

let check_all_configs = (fun configs -> (

let report1 = (fun errs -> (report_errors (

let uu___455_3661 = default_settings
in {query_env = uu___455_3661.query_env; query_decl = uu___455_3661.query_decl; query_name = uu___455_3661.query_name; query_index = uu___455_3661.query_index; query_range = uu___455_3661.query_range; query_fuel = uu___455_3661.query_fuel; query_ifuel = uu___455_3661.query_ifuel; query_rlimit = uu___455_3661.query_rlimit; query_hint = uu___455_3661.query_hint; query_errors = errs; query_all_labels = uu___455_3661.query_all_labels; query_suffix = uu___455_3661.query_suffix; query_hash = uu___455_3661.query_hash})))
in (fold_queries configs check_one_config process_result report1)))
in (

let uu____3662 = (

let uu____3671 = (FStar_Options.admit_smt_queries ())
in (

let uu____3673 = (FStar_Options.admit_except ())
in ((uu____3671), (uu____3673))))
in (match (uu____3662) with
| (true, uu____3681) -> begin
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

let uu____3711 = (

let uu____3713 = (

let uu____3715 = (

let uu____3717 = (FStar_Util.string_of_int default_settings.query_index)
in (Prims.op_Hat uu____3717 ")"))
in (Prims.op_Hat ", " uu____3715))
in (Prims.op_Hat default_settings.query_name uu____3713))
in (Prims.op_Hat "(" uu____3711))
in (Prims.op_disEquality full_query_id id1))
end
| uu____3723 -> begin
(Prims.op_disEquality default_settings.query_name id1)
end)
in (match ((not (skip))) with
| true -> begin
(check_all_configs all_configs)
end
| uu____3727 -> begin
()
end))
end))))))))))
end));
))


let solve : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  unit = (fun use_env_msg tcenv q -> ((

let uu____3757 = (

let uu____3759 = (

let uu____3761 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____3761))
in (FStar_Util.format1 "Starting query at %s" uu____3759))
in (FStar_SMTEncoding_Encode.push uu____3757));
(

let uu____3764 = (FStar_Options.no_smt ())
in (match (uu____3764) with
| true -> begin
(

let uu____3767 = (

let uu____3777 = (

let uu____3785 = (

let uu____3787 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.format1 "Q = %s\nA query could not be solved internally, and --no_smt was given" uu____3787))
in ((FStar_Errors.Error_NoSMTButNeeded), (uu____3785), (tcenv.FStar_TypeChecker_Env.range)))
in (uu____3777)::[])
in (FStar_TypeChecker_Err.add_errors tcenv uu____3767))
end
| uu____3805 -> begin
(

let tcenv1 = (FStar_TypeChecker_Env.incr_query_index tcenv)
in (

let uu____3808 = (FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q)
in (match (uu____3808) with
| (prefix1, labels, qry, suffix) -> begin
(

let pop1 = (fun uu____3844 -> (

let uu____3845 = (

let uu____3847 = (

let uu____3849 = (FStar_TypeChecker_Env.get_range tcenv1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____3849))
in (FStar_Util.format1 "Ending query at %s" uu____3847))
in (FStar_SMTEncoding_Encode.pop uu____3845)))
in (match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.assumption_term = {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.FalseOp, uu____3852); FStar_SMTEncoding_Term.freevars = uu____3853; FStar_SMTEncoding_Term.rng = uu____3854}; FStar_SMTEncoding_Term.assumption_caption = uu____3855; FStar_SMTEncoding_Term.assumption_name = uu____3856; FStar_SMTEncoding_Term.assumption_fact_ids = uu____3857}) -> begin
(pop1 ())
end
| uu____3877 when tcenv1.FStar_TypeChecker_Env.admit -> begin
(pop1 ())
end
| FStar_SMTEncoding_Term.Assume (uu____3878) -> begin
((ask_and_report_errors tcenv1 labels prefix1 qry suffix);
(pop1 ());
)
end
| uu____3880 -> begin
(failwith "Impossible")
end))
end)))
end));
))


let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init; FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push; FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop; FStar_TypeChecker_Env.snapshot = FStar_SMTEncoding_Encode.snapshot; FStar_TypeChecker_Env.rollback = FStar_SMTEncoding_Encode.rollback; FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig; FStar_TypeChecker_Env.preprocess = (fun e g -> (

let uu____3888 = (

let uu____3895 = (FStar_Options.peek ())
in ((e), (g), (uu____3895)))
in (uu____3888)::[])); FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}


let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun uu____3911 -> ()); FStar_TypeChecker_Env.push = (fun uu____3913 -> ()); FStar_TypeChecker_Env.pop = (fun uu____3916 -> ()); FStar_TypeChecker_Env.snapshot = (fun uu____3919 -> (((((Prims.parse_int "0")), ((Prims.parse_int "0")), ((Prims.parse_int "0")))), (()))); FStar_TypeChecker_Env.rollback = (fun uu____3938 uu____3939 -> ()); FStar_TypeChecker_Env.encode_sig = (fun uu____3954 uu____3955 -> ()); FStar_TypeChecker_Env.preprocess = (fun e g -> (

let uu____3961 = (

let uu____3968 = (FStar_Options.peek ())
in ((e), (g), (uu____3968)))
in (uu____3961)::[])); FStar_TypeChecker_Env.solve = (fun uu____3984 uu____3985 uu____3986 -> ()); FStar_TypeChecker_Env.finish = (fun uu____3993 -> ()); FStar_TypeChecker_Env.refresh = (fun uu____3995 -> ())}




