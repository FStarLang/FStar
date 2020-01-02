
open Prims
open FStar_Pervasives

type z3_replay_result =
(FStar_SMTEncoding_Z3.unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either


let z3_result_as_replay_result : 'Auu____35 'Auu____36 'Auu____37 . ('Auu____35, ('Auu____36 * 'Auu____37)) FStar_Util.either  ->  ('Auu____35, 'Auu____36) FStar_Util.either = (fun uu___0_54 -> (match (uu___0_54) with
| FStar_Util.Inl (l) -> begin
FStar_Util.Inl (l)
end
| FStar_Util.Inr (r, uu____69) -> begin
FStar_Util.Inr (r)
end))


let recorded_hints : FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let replaying_hints : FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let initialize_hints_db : 'Auu____95 . Prims.string  ->  'Auu____95  ->  unit = (fun src_filename format_filename -> ((

let uu____109 = (FStar_Options.record_hints ())
in (match (uu____109) with
| true -> begin
(FStar_ST.op_Colon_Equals recorded_hints (FStar_Pervasives_Native.Some ([])))
end
| uu____137 -> begin
()
end));
(

let uu____139 = (FStar_Options.use_hints ())
in (match (uu____139) with
| true -> begin
(

let norm_src_filename = (FStar_Util.normalize_file_path src_filename)
in (

let val_filename = (FStar_Options.hint_file_for_src norm_src_filename)
in (

let uu____146 = (FStar_Util.read_hints val_filename)
in (match (uu____146) with
| FStar_Pervasives_Native.Some (hints) -> begin
(

let expected_digest = (FStar_Util.digest_of_file norm_src_filename)
in ((

let uu____153 = (FStar_Options.hint_info ())
in (match (uu____153) with
| true -> begin
(FStar_Util.print3 "(%s) digest is %s from %s.\n" norm_src_filename (match ((Prims.op_Equality hints.FStar_Util.module_digest expected_digest)) with
| true -> begin
"valid; using hints"
end
| uu____161 -> begin
"invalid; using potentially stale hints"
end) val_filename)
end
| uu____164 -> begin
()
end));
(FStar_ST.op_Colon_Equals replaying_hints (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)));
))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____189 = (FStar_Options.hint_info ())
in (match (uu____189) with
| true -> begin
(FStar_Util.print1 "(%s) Unable to read hint file.\n" norm_src_filename)
end
| uu____193 -> begin
()
end))
end))))
end
| uu____195 -> begin
()
end));
))


let finalize_hints_db : Prims.string  ->  unit = (fun src_filename -> ((

let uu____206 = (FStar_Options.record_hints ())
in (match (uu____206) with
| true -> begin
(

let hints = (

let uu____210 = (FStar_ST.op_Bang recorded_hints)
in (FStar_Option.get uu____210))
in (

let hints_db = (

let uu____237 = (FStar_Util.digest_of_file src_filename)
in {FStar_Util.module_digest = uu____237; FStar_Util.hints = hints})
in (

let norm_src_filename = (FStar_Util.normalize_file_path src_filename)
in (

let val_filename = (FStar_Options.hint_file_for_src norm_src_filename)
in (FStar_Util.write_hints val_filename hints_db)))))
end
| uu____243 -> begin
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
| uu____359 -> begin
((FStar_All.pipe_right a.FStar_SMTEncoding_Term.assumption_fact_ids (FStar_Util.for_some (fun uu___1_367 -> (match (uu___1_367) with
| FStar_SMTEncoding_Term.Name (lid) -> begin
(FStar_TypeChecker_Env.should_enc_lid e lid)
end
| uu____370 -> begin
false
end)))) || (

let uu____373 = (FStar_Util.smap_try_find include_assumption_names a.FStar_SMTEncoding_Term.assumption_name)
in (FStar_Option.isSome uu____373)))
end))
in (

let theory_rev = (FStar_List.rev theory)
in (

let pruned_theory = (

let include_assumption_names = (FStar_Util.smap_create (Prims.parse_int "10000"))
in (

let keep_decl = (fun uu___2_397 -> (match (uu___2_397) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(matches_fact_ids include_assumption_names a)
end
| FStar_SMTEncoding_Term.RetainAssumptions (names1) -> begin
((FStar_List.iter (fun x -> (FStar_Util.smap_add include_assumption_names x true)) names1);
true;
)
end
| FStar_SMTEncoding_Term.Module (uu____412) -> begin
(failwith "Solver.fs::keep_decl should never have been called with a Module decl")
end
| uu____422 -> begin
true
end))
in (FStar_List.fold_left (fun out d -> (match (d) with
| FStar_SMTEncoding_Term.Module (name, decls) -> begin
(

let uu____445 = (FStar_All.pipe_right decls (FStar_List.filter keep_decl))
in (FStar_All.pipe_right uu____445 (fun decls1 -> (FStar_SMTEncoding_Term.Module (((name), (decls1))))::out)))
end
| uu____463 -> begin
(

let uu____464 = (keep_decl d)
in (match (uu____464) with
| true -> begin
(d)::out
end
| uu____469 -> begin
out
end))
end)) [] theory_rev)))
in pruned_theory))))


let rec filter_assertions_with_stats : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Z3.unsat_core  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool * Prims.int * Prims.int) = (fun e core theory -> (match (core) with
| FStar_Pervasives_Native.None -> begin
(

let uu____520 = (filter_using_facts_from e theory)
in ((uu____520), (false), ((Prims.parse_int "0")), ((Prims.parse_int "0"))))
end
| FStar_Pervasives_Native.Some (core1) -> begin
(

let theory_rev = (FStar_List.rev theory)
in (

let uu____541 = (

let uu____552 = (

let uu____563 = (

let uu____566 = (

let uu____567 = (

let uu____569 = (FStar_All.pipe_right core1 (FStar_String.concat ", "))
in (Prims.op_Hat "UNSAT CORE: " uu____569))
in FStar_SMTEncoding_Term.Caption (uu____567))
in (uu____566)::[])
in ((uu____563), ((Prims.parse_int "0")), ((Prims.parse_int "0"))))
in (FStar_List.fold_left (fun uu____599 d -> (match (uu____599) with
| (theory1, n_retained, n_pruned) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(match ((FStar_List.contains a.FStar_SMTEncoding_Term.assumption_name core1)) with
| true -> begin
(((d)::theory1), ((n_retained + (Prims.parse_int "1"))), (n_pruned))
end
| uu____660 -> begin
(match ((FStar_Util.starts_with a.FStar_SMTEncoding_Term.assumption_name "@")) with
| true -> begin
(((d)::theory1), (n_retained), (n_pruned))
end
| uu____678 -> begin
((theory1), (n_retained), ((n_pruned + (Prims.parse_int "1"))))
end)
end)
end
| FStar_SMTEncoding_Term.Module (name, decls) -> begin
(

let uu____693 = (FStar_All.pipe_right decls (filter_assertions_with_stats e (FStar_Pervasives_Native.Some (core1))))
in (FStar_All.pipe_right uu____693 (fun uu____753 -> (match (uu____753) with
| (decls1, uu____778, r, p) -> begin
(((FStar_SMTEncoding_Term.Module (((name), (decls1))))::theory1), ((n_retained + r)), ((n_pruned + p)))
end))))
end
| uu____798 -> begin
(((d)::theory1), (n_retained), (n_pruned))
end)
end)) uu____552 theory_rev))
in (match (uu____541) with
| (theory', n_retained, n_pruned) -> begin
((theory'), (true), (n_retained), (n_pruned))
end)))
end))


let filter_assertions : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Z3.unsat_core  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool) = (fun e core theory -> (

let uu____860 = (filter_assertions_with_stats e core theory)
in (match (uu____860) with
| (theory1, b, uu____883, uu____884) -> begin
((theory1), (b))
end)))


let filter_facts_without_core : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool) = (fun e x -> (

let uu____920 = (filter_using_facts_from e x)
in ((uu____920), (false))))

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

let uu____1150 = (FStar_Util.string_of_int err.error_fuel)
in (

let uu____1152 = (FStar_Util.string_of_int err.error_ifuel)
in (FStar_Util.format4 "%s (fuel=%s; ifuel=%s%s)" err.error_reason uu____1150 uu____1152 (match ((FStar_Option.isSome err.error_hint)) with
| true -> begin
"; with hint"
end
| uu____1161 -> begin
""
end)))))


let error_to_is_timeout : errors  ->  Prims.string Prims.list = (fun err -> (match ((FStar_Util.ends_with err.error_reason "canceled")) with
| true -> begin
(

let uu____1178 = (

let uu____1180 = (FStar_Util.string_of_int err.error_fuel)
in (

let uu____1182 = (FStar_Util.string_of_int err.error_ifuel)
in (FStar_Util.format4 "timeout (fuel=%s; ifuel=%s; %s)" err.error_reason uu____1180 uu____1182 (match ((FStar_Option.isSome err.error_hint)) with
| true -> begin
"with hint"
end
| uu____1191 -> begin
""
end))))
in (uu____1178)::[])
end
| uu____1196 -> begin
[]
end))

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

let uu____1732 = (

let uu____1735 = (

let uu____1736 = (

let uu____1738 = (FStar_Util.string_of_int n1)
in (

let uu____1740 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" uu____1738 uu____1740)))
in FStar_SMTEncoding_Term.Caption (uu____1736))
in (

let uu____1743 = (

let uu____1746 = (

let uu____1747 = (

let uu____1755 = (

let uu____1756 = (

let uu____1761 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (

let uu____1766 = (FStar_SMTEncoding_Term.n_fuel n1)
in ((uu____1761), (uu____1766))))
in (FStar_SMTEncoding_Util.mkEq uu____1756))
in ((uu____1755), (FStar_Pervasives_Native.None), ("@MaxFuel_assumption")))
in (FStar_SMTEncoding_Util.mkAssume uu____1747))
in (

let uu____1770 = (

let uu____1773 = (

let uu____1774 = (

let uu____1782 = (

let uu____1783 = (

let uu____1788 = (FStar_SMTEncoding_Util.mkApp (("MaxIFuel"), ([])))
in (

let uu____1793 = (FStar_SMTEncoding_Term.n_fuel i)
in ((uu____1788), (uu____1793))))
in (FStar_SMTEncoding_Util.mkEq uu____1783))
in ((uu____1782), (FStar_Pervasives_Native.None), ("@MaxIFuel_assumption")))
in (FStar_SMTEncoding_Util.mkAssume uu____1774))
in (uu____1773)::(settings.query_decl)::[])
in (uu____1746)::uu____1770))
in (uu____1735)::uu____1743))
in (

let uu____1797 = (

let uu____1800 = (

let uu____1803 = (

let uu____1806 = (

let uu____1807 = (

let uu____1814 = (FStar_Util.string_of_int rlimit)
in (("rlimit"), (uu____1814)))
in FStar_SMTEncoding_Term.SetOption (uu____1807))
in (uu____1806)::(FStar_SMTEncoding_Term.CheckSat)::(FStar_SMTEncoding_Term.SetOption ((("rlimit"), ("0"))))::(FStar_SMTEncoding_Term.GetReasonUnknown)::(FStar_SMTEncoding_Term.GetUnsatCore)::[])
in (

let uu____1823 = (

let uu____1826 = (

let uu____1829 = ((FStar_Options.print_z3_statistics ()) || (FStar_Options.query_stats ()))
in (match (uu____1829) with
| true -> begin
(FStar_SMTEncoding_Term.GetStatistics)::[]
end
| uu____1834 -> begin
[]
end))
in (FStar_List.append uu____1826 settings.query_suffix))
in (FStar_List.append uu____1803 uu____1823)))
in (FStar_List.append label_assumptions uu____1800))
in (FStar_List.append uu____1732 uu____1797)))))))


let used_hint : query_settings  ->  Prims.bool = (fun s -> (FStar_Option.isSome s.query_hint))


let get_hint_for : Prims.string  ->  Prims.int  ->  FStar_Util.hint FStar_Pervasives_Native.option = (fun qname qindex -> (

let uu____1863 = (FStar_ST.op_Bang replaying_hints)
in (match (uu____1863) with
| FStar_Pervasives_Native.Some (hints) -> begin
(FStar_Util.find_map hints (fun uu___3_1896 -> (match (uu___3_1896) with
| FStar_Pervasives_Native.Some (hint) when ((Prims.op_Equality hint.FStar_Util.hint_name qname) && (Prims.op_Equality hint.FStar_Util.hint_index qindex)) -> begin
FStar_Pervasives_Native.Some (hint)
end
| uu____1904 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____1907 -> begin
FStar_Pervasives_Native.None
end)))


let query_errors : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  errors FStar_Pervasives_Native.option = (fun settings z3result -> (match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____1925) -> begin
FStar_Pervasives_Native.None
end
| uu____1926 -> begin
(

let uu____1927 = (FStar_SMTEncoding_Z3.status_string_and_errors z3result.FStar_SMTEncoding_Z3.z3result_status)
in (match (uu____1927) with
| (msg, error_labels) -> begin
(

let err = (

let uu____1940 = (FStar_List.map (fun uu____1968 -> (match (uu____1968) with
| (uu____1983, x, y) -> begin
((FStar_Errors.Error_Z3SolverError), (x), (y))
end)) error_labels)
in {error_reason = msg; error_fuel = settings.query_fuel; error_ifuel = settings.query_ifuel; error_hint = settings.query_hint; error_messages = uu____1940})
in FStar_Pervasives_Native.Some (err))
end))
end))


let detail_hint_replay : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  unit = (fun settings z3result -> (

let uu____2000 = ((used_hint settings) && (FStar_Options.detail_hint_replay ()))
in (match (uu____2000) with
| true -> begin
(match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (uu____2003) -> begin
()
end
| _failed -> begin
(

let ask_z3 = (fun label_assumptions -> (

let uu____2015 = (with_fuel_and_diagnostics settings label_assumptions)
in (FStar_SMTEncoding_Z3.ask (settings_to_info settings) (filter_assertions settings.query_env settings.query_hint) settings.query_hash settings.query_all_labels uu____2015 FStar_Pervasives_Native.None false)))
in (FStar_SMTEncoding_ErrorReporting.detail_errors true settings.query_env settings.query_all_labels ask_z3))
end)
end
| uu____2020 -> begin
()
end)))


let find_localized_errors : errors Prims.list  ->  errors FStar_Pervasives_Native.option = (fun errs -> (FStar_All.pipe_right errs (FStar_List.tryFind (fun err -> (match (err.error_messages) with
| [] -> begin
false
end
| uu____2049 -> begin
true
end)))))


let errors_to_report : query_settings  ->  FStar_Errors.error Prims.list = (fun settings -> (

let format_smt_error = (fun msg -> (FStar_Util.format1 "SMT solver says:\n\t%s;\n\tNote: \'canceled\' or \'resource limits reached\' means the SMT query timed out, so you might want to increase the rlimit;\n\t\'incomplete quantifiers\' means a (partial) counterexample was found, so try to spell your proof out in greater detail, increase fuel or ifuel\n\t\'unknown\' means Z3 provided no further reason for the proof failing" msg))
in (

let basic_errors = (

let smt_error = (

let uu____2090 = (FStar_Options.query_stats ())
in (match (uu____2090) with
| true -> begin
(

let uu____2099 = (

let uu____2101 = (

let uu____2103 = (FStar_All.pipe_right settings.query_errors (FStar_List.map error_to_short_string))
in (FStar_All.pipe_right uu____2103 (FStar_String.concat ";\n\t")))
in (FStar_All.pipe_right uu____2101 format_smt_error))
in (FStar_All.pipe_right uu____2099 (fun _2129 -> FStar_Util.Inr (_2129))))
end
| uu____2130 -> begin
(

let uu____2132 = (FStar_List.fold_left (fun uu____2157 err -> (match (uu____2157) with
| (ic, cc, uc) -> begin
(

let err1 = (FStar_Util.substring_from err.error_reason (FStar_String.length "unknown because "))
in (match ((((FStar_Util.starts_with err1 "canceled") || (FStar_Util.starts_with err1 "(resource")) || (FStar_Util.starts_with err1 "timeout"))) with
| true -> begin
((ic), ((cc + (Prims.parse_int "1"))), (uc))
end
| uu____2206 -> begin
(match ((FStar_Util.starts_with err1 "(incomplete")) with
| true -> begin
(((ic + (Prims.parse_int "1"))), (cc), (uc))
end
| uu____2223 -> begin
((ic), (cc), ((uc + (Prims.parse_int "1"))))
end)
end))
end)) (((Prims.parse_int "0")), ((Prims.parse_int "0")), ((Prims.parse_int "0"))) settings.query_errors)
in (match (uu____2132) with
| (incomplete_count, canceled_count, unknown_count) -> begin
(FStar_All.pipe_right (match (((incomplete_count), (canceled_count), (unknown_count))) with
| (uu____2262, _2267, _2268) when (((_2267 = (Prims.parse_int "0")) && (_2268 = (Prims.parse_int "0"))) && (incomplete_count > (Prims.parse_int "0"))) -> begin
"The solver found a (partial) counterexample, try to spell your proof in more detail or increase fuel/ifuel"
end
| (_2275, uu____2271, _2277) when (((_2275 = (Prims.parse_int "0")) && (_2277 = (Prims.parse_int "0"))) && (canceled_count > (Prims.parse_int "0"))) -> begin
"The SMT query timed out, you might want to increase the rlimit"
end
| (uu____2280, uu____2281, uu____2282) -> begin
"Try with --query_stats to get more details"
end) (fun _2292 -> FStar_Util.Inl (_2292)))
end))
end))
in (

let uu____2293 = (find_localized_errors settings.query_errors)
in (match (uu____2293) with
| FStar_Pervasives_Native.Some (err) -> begin
(FStar_TypeChecker_Err.errors_smt_detail settings.query_env err.error_messages smt_error)
end
| FStar_Pervasives_Native.None -> begin
(FStar_TypeChecker_Err.errors_smt_detail settings.query_env ((((FStar_Errors.Error_UnknownFatal_AssertionFailure), ("Unknown assertion failed"), (settings.query_range)))::[]) smt_error)
end)))
in ((

let uu____2316 = (FStar_Options.detail_errors ())
in (match (uu____2316) with
| true -> begin
(

let initial_fuel1 = (

let uu___250_2320 = settings
in (

let uu____2321 = (FStar_Options.initial_fuel ())
in (

let uu____2323 = (FStar_Options.initial_ifuel ())
in {query_env = uu___250_2320.query_env; query_decl = uu___250_2320.query_decl; query_name = uu___250_2320.query_name; query_index = uu___250_2320.query_index; query_range = uu___250_2320.query_range; query_fuel = uu____2321; query_ifuel = uu____2323; query_rlimit = uu___250_2320.query_rlimit; query_hint = FStar_Pervasives_Native.None; query_errors = uu___250_2320.query_errors; query_all_labels = uu___250_2320.query_all_labels; query_suffix = uu___250_2320.query_suffix; query_hash = uu___250_2320.query_hash})))
in (

let ask_z3 = (fun label_assumptions -> (

let uu____2338 = (with_fuel_and_diagnostics initial_fuel1 label_assumptions)
in (FStar_SMTEncoding_Z3.ask (settings_to_info settings) (filter_facts_without_core settings.query_env) settings.query_hash settings.query_all_labels uu____2338 FStar_Pervasives_Native.None false)))
in (FStar_SMTEncoding_ErrorReporting.detail_errors false settings.query_env settings.query_all_labels ask_z3)))
end
| uu____2343 -> begin
()
end));
basic_errors;
))))


let report_errors : query_settings  ->  unit = (fun qry_settings -> (

let uu____2351 = (errors_to_report qry_settings)
in (FStar_Errors.add_errors uu____2351)))


let query_info : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  unit = (fun settings z3result -> (

let process_unsat_core = (fun core -> (

let accumulator = (fun uu____2397 -> (

let r = (FStar_Util.mk_ref [])
in (

let uu____2408 = (

let module_names = (FStar_Util.mk_ref [])
in (((fun m -> (

let ms = (FStar_ST.op_Bang module_names)
in (match ((FStar_List.contains m ms)) with
| true -> begin
()
end
| uu____2478 -> begin
(FStar_ST.op_Colon_Equals module_names ((m)::ms))
end)))), ((fun uu____2508 -> (

let uu____2509 = (FStar_ST.op_Bang module_names)
in (FStar_All.pipe_right uu____2509 (FStar_Util.sort_with FStar_String.compare)))))))
in (match (uu____2408) with
| (add1, get1) -> begin
((add1), (get1))
end))))
in (

let uu____2591 = (accumulator ())
in (match (uu____2591) with
| (add_module_name, get_module_names) -> begin
(

let uu____2628 = (accumulator ())
in (match (uu____2628) with
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

let uu____2751 = (FStar_List.hd (FStar_Util.split s2 sfx))
in FStar_Pervasives_Native.Some (uu____2751))
end
| uu____2755 -> begin
FStar_Pervasives_Native.None
end)))
in (match (sopt) with
| FStar_Pervasives_Native.None -> begin
(match ((Prims.op_Equality s2 "")) with
| true -> begin
[]
end
| uu____2769 -> begin
(s2)::[]
end)
end
| FStar_Pervasives_Native.Some (s3) -> begin
(match ((Prims.op_Equality s3 "")) with
| true -> begin
[]
end
| uu____2783 -> begin
(s3)::[]
end)
end))))
in (

let components1 = (match (components) with
| [] -> begin
[]
end
| uu____2796 -> begin
(

let uu____2800 = (FStar_Util.prefix components)
in (match (uu____2800) with
| (module_name, last1) -> begin
(

let components1 = (

let uu____2827 = (exclude_suffix last1)
in (FStar_List.append module_name uu____2827))
in ((match (components1) with
| [] -> begin
()
end
| (uu____2834)::[] -> begin
()
end
| uu____2838 -> begin
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
| uu____2853 -> begin
(

let uu____2855 = (FStar_All.pipe_right components1 (FStar_String.concat "."))
in (uu____2855)::[])
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

let uu____2882 = (

let uu____2884 = (get_module_names ())
in (FStar_All.pipe_right uu____2884 (FStar_String.concat "\nZ3 Proof Stats:\t")))
in (FStar_Util.print1 "Z3 Proof Stats: Modules relevant to this proof:\nZ3 Proof Stats:\t%s\n" uu____2882));
(FStar_Util.print1 "Z3 Proof Stats (Detail 1): Specifically:\nZ3 Proof Stats (Detail 1):\t%s\n" (FStar_String.concat "\nZ3 Proof Stats (Detail 1):\t" core2));
(

let uu____2897 = (

let uu____2899 = (get_discarded_names ())
in (FStar_All.pipe_right uu____2899 (FStar_String.concat ", ")))
in (FStar_Util.print1 "Z3 Proof Stats (Detail 2): Note, this report ignored the following names in the context: %s\n" uu____2897));
))
end))
end))
end))))
in (

let uu____2909 = ((FStar_Options.hint_info ()) || (FStar_Options.query_stats ()))
in (match (uu____2909) with
| true -> begin
(

let uu____2912 = (FStar_SMTEncoding_Z3.status_string_and_errors z3result.FStar_SMTEncoding_Z3.z3result_status)
in (match (uu____2912) with
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

let uu____2931 = (match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (core) -> begin
(("succeeded"), (core))
end
| uu____2945 -> begin
(((Prims.op_Hat "failed {reason-unknown=" (Prims.op_Hat status_string "}"))), (FStar_Pervasives_Native.None))
end)
in (match (uu____2931) with
| (tag, core) -> begin
(

let range = (

let uu____2958 = (

let uu____2960 = (FStar_Range.string_of_range settings.query_range)
in (Prims.op_Hat uu____2960 (Prims.op_Hat at_log_file ")")))
in (Prims.op_Hat "(" uu____2958))
in (

let used_hint_tag = (match ((used_hint settings)) with
| true -> begin
" (with hint)"
end
| uu____2969 -> begin
""
end)
in (

let stats = (

let uu____2974 = (FStar_Options.query_stats ())
in (match (uu____2974) with
| true -> begin
(

let f = (fun k v1 a -> (Prims.op_Hat a (Prims.op_Hat k (Prims.op_Hat "=" (Prims.op_Hat v1 " ")))))
in (

let str = (FStar_Util.smap_fold z3result.FStar_SMTEncoding_Z3.z3result_statistics f "statistics={")
in (

let uu____3008 = (FStar_Util.substring str (Prims.parse_int "0") ((FStar_String.length str) - (Prims.parse_int "1")))
in (Prims.op_Hat uu____3008 "}"))))
end
| uu____3013 -> begin
""
end))
in ((

let uu____3017 = (

let uu____3021 = (

let uu____3025 = (

let uu____3029 = (FStar_Util.string_of_int settings.query_index)
in (

let uu____3031 = (

let uu____3035 = (

let uu____3039 = (

let uu____3043 = (FStar_Util.string_of_int z3result.FStar_SMTEncoding_Z3.z3result_time)
in (

let uu____3045 = (

let uu____3049 = (FStar_Util.string_of_int settings.query_fuel)
in (

let uu____3051 = (

let uu____3055 = (FStar_Util.string_of_int settings.query_ifuel)
in (

let uu____3057 = (

let uu____3061 = (FStar_Util.string_of_int settings.query_rlimit)
in (uu____3061)::(stats)::[])
in (uu____3055)::uu____3057))
in (uu____3049)::uu____3051))
in (uu____3043)::uu____3045))
in (used_hint_tag)::uu____3039)
in (tag)::uu____3035)
in (uu____3029)::uu____3031))
in (settings.query_name)::uu____3025)
in (range)::uu____3021)
in (FStar_Util.print "%s\tQuery-stats (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n" uu____3017));
(

let uu____3076 = (FStar_Options.print_z3_statistics ())
in (match (uu____3076) with
| true -> begin
(process_unsat_core core)
end
| uu____3079 -> begin
()
end));
(FStar_All.pipe_right errs (FStar_List.iter (fun uu____3102 -> (match (uu____3102) with
| (uu____3110, msg, range1) -> begin
(

let tag1 = (match ((used_hint settings)) with
| true -> begin
"(Hint-replay failed): "
end
| uu____3120 -> begin
""
end)
in (FStar_Errors.log_issue range1 ((FStar_Errors.Warning_HitReplayFailed), ((Prims.op_Hat tag1 msg)))))
end))));
))))
end)))
end))
end
| uu____3124 -> begin
()
end))))


let record_hint : query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  unit = (fun settings z3result -> (

let uu____3137 = (

let uu____3139 = (FStar_Options.record_hints ())
in (not (uu____3139)))
in (match (uu____3137) with
| true -> begin
()
end
| uu____3142 -> begin
(

let mk_hint = (fun core -> {FStar_Util.hint_name = settings.query_name; FStar_Util.hint_index = settings.query_index; FStar_Util.fuel = settings.query_fuel; FStar_Util.ifuel = settings.query_ifuel; FStar_Util.unsat_core = core; FStar_Util.query_elapsed_time = (Prims.parse_int "0"); FStar_Util.hash = (match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (core1) -> begin
z3result.FStar_SMTEncoding_Z3.z3result_query_hash
end
| uu____3166 -> begin
FStar_Pervasives_Native.None
end)})
in (

let store_hint = (fun hint -> (

let uu____3174 = (FStar_ST.op_Bang recorded_hints)
in (match (uu____3174) with
| FStar_Pervasives_Native.Some (l) -> begin
(FStar_ST.op_Colon_Equals recorded_hints (FStar_Pervasives_Native.Some ((FStar_List.append l ((FStar_Pervasives_Native.Some (hint))::[])))))
end
| uu____3230 -> begin
()
end)))
in (match (z3result.FStar_SMTEncoding_Z3.z3result_status) with
| FStar_SMTEncoding_Z3.UNSAT (FStar_Pervasives_Native.None) -> begin
(

let uu____3237 = (

let uu____3238 = (get_hint_for settings.query_name settings.query_index)
in (FStar_Option.get uu____3238))
in (store_hint uu____3237))
end
| FStar_SMTEncoding_Z3.UNSAT (unsat_core) -> begin
(match ((used_hint settings)) with
| true -> begin
(store_hint (mk_hint settings.query_hint))
end
| uu____3243 -> begin
(store_hint (mk_hint unsat_core))
end)
end
| uu____3245 -> begin
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


let fold_queries : query_settings Prims.list  ->  (query_settings  ->  FStar_SMTEncoding_Z3.z3result)  ->  (query_settings  ->  FStar_SMTEncoding_Z3.z3result  ->  errors FStar_Pervasives_Native.option)  ->  (errors Prims.list, query_settings) FStar_Util.either = (fun qs ask1 f -> (

let rec aux = (fun acc qs1 -> (match (qs1) with
| [] -> begin
FStar_Util.Inl (acc)
end
| (q)::qs2 -> begin
(

let res = (ask1 q)
in (

let uu____3356 = (f q res)
in (match (uu____3356) with
| FStar_Pervasives_Native.None -> begin
FStar_Util.Inr (q)
end
| FStar_Pervasives_Native.Some (errs) -> begin
(aux ((errs)::acc) qs2)
end)))
end))
in (aux [] qs)))


let full_query_id : query_settings  ->  Prims.string = (fun settings -> (

let uu____3375 = (

let uu____3377 = (

let uu____3379 = (

let uu____3381 = (FStar_Util.string_of_int settings.query_index)
in (Prims.op_Hat uu____3381 ")"))
in (Prims.op_Hat ", " uu____3379))
in (Prims.op_Hat settings.query_name uu____3377))
in (Prims.op_Hat "(" uu____3375)))


let collect : 'a . 'a Prims.list  ->  ('a * Prims.int) Prims.list = (fun l -> (

let acc = []
in (

let rec add_one1 = (fun acc1 x -> (match (acc1) with
| [] -> begin
(((x), ((Prims.parse_int "1"))))::[]
end
| ((h, n1))::t -> begin
(match ((Prims.op_Equality h x)) with
| true -> begin
(((h), ((n1 + (Prims.parse_int "1")))))::t
end
| uu____3509 -> begin
(

let uu____3511 = (add_one1 t x)
in (((h), (n1)))::uu____3511)
end)
end))
in (FStar_List.fold_left add_one1 acc l))))


let ask_and_report_errors : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  unit = (fun env all_labels prefix1 query suffix -> ((FStar_SMTEncoding_Z3.giveZ3 prefix1);
(

let uu____3567 = (

let uu____3574 = (match (env.FStar_TypeChecker_Env.qtbl_name_and_index) with
| (uu____3587, FStar_Pervasives_Native.None) -> begin
(failwith "No query name set!")
end
| (uu____3613, FStar_Pervasives_Native.Some (q, n1)) -> begin
(

let uu____3636 = (FStar_Ident.text_of_lid q)
in ((uu____3636), (n1)))
end)
in (match (uu____3574) with
| (qname, index1) -> begin
(

let rlimit = (

let uu____3654 = (FStar_Options.z3_rlimit_factor ())
in (

let uu____3656 = (

let uu____3658 = (FStar_Options.z3_rlimit ())
in (uu____3658 * (Prims.parse_int "544656")))
in (uu____3654 * uu____3656)))
in (

let next_hint = (get_hint_for qname index1)
in (

let default_settings = (

let uu____3665 = (FStar_TypeChecker_Env.get_range env)
in (

let uu____3666 = (FStar_Options.initial_fuel ())
in (

let uu____3668 = (FStar_Options.initial_ifuel ())
in {query_env = env; query_decl = query; query_name = qname; query_index = index1; query_range = uu____3665; query_fuel = uu____3666; query_ifuel = uu____3668; query_rlimit = rlimit; query_hint = FStar_Pervasives_Native.None; query_errors = []; query_all_labels = all_labels; query_suffix = suffix; query_hash = (match (next_hint) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ({FStar_Util.hint_name = uu____3677; FStar_Util.hint_index = uu____3678; FStar_Util.fuel = uu____3679; FStar_Util.ifuel = uu____3680; FStar_Util.unsat_core = uu____3681; FStar_Util.query_elapsed_time = uu____3682; FStar_Util.hash = h}) -> begin
h
end)})))
in ((default_settings), (next_hint)))))
end))
in (match (uu____3567) with
| (default_settings, next_hint) -> begin
(

let use_hints_setting = (match (next_hint) with
| FStar_Pervasives_Native.Some ({FStar_Util.hint_name = uu____3710; FStar_Util.hint_index = uu____3711; FStar_Util.fuel = i; FStar_Util.ifuel = j; FStar_Util.unsat_core = FStar_Pervasives_Native.Some (core); FStar_Util.query_elapsed_time = uu____3715; FStar_Util.hash = h}) -> begin
((

let uu___451_3732 = default_settings
in {query_env = uu___451_3732.query_env; query_decl = uu___451_3732.query_decl; query_name = uu___451_3732.query_name; query_index = uu___451_3732.query_index; query_range = uu___451_3732.query_range; query_fuel = i; query_ifuel = j; query_rlimit = uu___451_3732.query_rlimit; query_hint = FStar_Pervasives_Native.Some (core); query_errors = uu___451_3732.query_errors; query_all_labels = uu___451_3732.query_all_labels; query_suffix = uu___451_3732.query_suffix; query_hash = uu___451_3732.query_hash}))::[]
end
| uu____3736 -> begin
[]
end)
in (

let initial_fuel_max_ifuel = (

let uu____3742 = (

let uu____3744 = (FStar_Options.max_ifuel ())
in (

let uu____3746 = (FStar_Options.initial_ifuel ())
in (uu____3744 > uu____3746)))
in (match (uu____3742) with
| true -> begin
(

let uu____3751 = (

let uu___456_3752 = default_settings
in (

let uu____3753 = (FStar_Options.max_ifuel ())
in {query_env = uu___456_3752.query_env; query_decl = uu___456_3752.query_decl; query_name = uu___456_3752.query_name; query_index = uu___456_3752.query_index; query_range = uu___456_3752.query_range; query_fuel = uu___456_3752.query_fuel; query_ifuel = uu____3753; query_rlimit = uu___456_3752.query_rlimit; query_hint = uu___456_3752.query_hint; query_errors = uu___456_3752.query_errors; query_all_labels = uu___456_3752.query_all_labels; query_suffix = uu___456_3752.query_suffix; query_hash = uu___456_3752.query_hash}))
in (uu____3751)::[])
end
| uu____3755 -> begin
[]
end))
in (

let half_max_fuel_max_ifuel = (

let uu____3760 = (

let uu____3762 = (

let uu____3764 = (FStar_Options.max_fuel ())
in (uu____3764 / (Prims.parse_int "2")))
in (

let uu____3767 = (FStar_Options.initial_fuel ())
in (uu____3762 > uu____3767)))
in (match (uu____3760) with
| true -> begin
(

let uu____3772 = (

let uu___460_3773 = default_settings
in (

let uu____3774 = (

let uu____3776 = (FStar_Options.max_fuel ())
in (uu____3776 / (Prims.parse_int "2")))
in (

let uu____3779 = (FStar_Options.max_ifuel ())
in {query_env = uu___460_3773.query_env; query_decl = uu___460_3773.query_decl; query_name = uu___460_3773.query_name; query_index = uu___460_3773.query_index; query_range = uu___460_3773.query_range; query_fuel = uu____3774; query_ifuel = uu____3779; query_rlimit = uu___460_3773.query_rlimit; query_hint = uu___460_3773.query_hint; query_errors = uu___460_3773.query_errors; query_all_labels = uu___460_3773.query_all_labels; query_suffix = uu___460_3773.query_suffix; query_hash = uu___460_3773.query_hash})))
in (uu____3772)::[])
end
| uu____3781 -> begin
[]
end))
in (

let max_fuel_max_ifuel = (

let uu____3786 = ((

let uu____3792 = (FStar_Options.max_fuel ())
in (

let uu____3794 = (FStar_Options.initial_fuel ())
in (uu____3792 > uu____3794))) && (

let uu____3798 = (FStar_Options.max_ifuel ())
in (

let uu____3800 = (FStar_Options.initial_ifuel ())
in (uu____3798 >= uu____3800))))
in (match (uu____3786) with
| true -> begin
(

let uu____3805 = (

let uu___464_3806 = default_settings
in (

let uu____3807 = (FStar_Options.max_fuel ())
in (

let uu____3809 = (FStar_Options.max_ifuel ())
in {query_env = uu___464_3806.query_env; query_decl = uu___464_3806.query_decl; query_name = uu___464_3806.query_name; query_index = uu___464_3806.query_index; query_range = uu___464_3806.query_range; query_fuel = uu____3807; query_ifuel = uu____3809; query_rlimit = uu___464_3806.query_rlimit; query_hint = uu___464_3806.query_hint; query_errors = uu___464_3806.query_errors; query_all_labels = uu___464_3806.query_all_labels; query_suffix = uu___464_3806.query_suffix; query_hash = uu___464_3806.query_hash})))
in (uu____3805)::[])
end
| uu____3811 -> begin
[]
end))
in (

let min_fuel1 = (

let uu____3816 = (

let uu____3818 = (FStar_Options.min_fuel ())
in (

let uu____3820 = (FStar_Options.initial_fuel ())
in (uu____3818 < uu____3820)))
in (match (uu____3816) with
| true -> begin
(

let uu____3825 = (

let uu___468_3826 = default_settings
in (

let uu____3827 = (FStar_Options.min_fuel ())
in {query_env = uu___468_3826.query_env; query_decl = uu___468_3826.query_decl; query_name = uu___468_3826.query_name; query_index = uu___468_3826.query_index; query_range = uu___468_3826.query_range; query_fuel = uu____3827; query_ifuel = (Prims.parse_int "1"); query_rlimit = uu___468_3826.query_rlimit; query_hint = uu___468_3826.query_hint; query_errors = uu___468_3826.query_errors; query_all_labels = uu___468_3826.query_all_labels; query_suffix = uu___468_3826.query_suffix; query_hash = uu___468_3826.query_hash}))
in (uu____3825)::[])
end
| uu____3830 -> begin
[]
end))
in (

let all_configs = (FStar_List.append use_hints_setting (FStar_List.append ((default_settings)::[]) (FStar_List.append initial_fuel_max_ifuel (FStar_List.append half_max_fuel_max_ifuel max_fuel_max_ifuel))))
in (

let check_one_config = (fun config1 -> ((

let uu____3842 = (FStar_Options.z3_refresh ())
in (match (uu____3842) with
| true -> begin
(FStar_SMTEncoding_Z3.refresh ())
end
| uu____3845 -> begin
()
end));
(

let uu____3847 = (with_fuel_and_diagnostics config1 [])
in (

let uu____3850 = (

let uu____3853 = (FStar_SMTEncoding_Z3.mk_fresh_scope ())
in FStar_Pervasives_Native.Some (uu____3853))
in (FStar_SMTEncoding_Z3.ask (settings_to_info config1) (filter_assertions config1.query_env config1.query_hint) config1.query_hash config1.query_all_labels uu____3847 uu____3850 (used_hint config1))));
))
in (

let check_all_configs = (fun configs -> (fold_queries configs check_one_config process_result))
in (

let quake_and_check_all_configs = (fun configs -> (

let lo = (FStar_Options.quake_lo ())
in (

let hi = (FStar_Options.quake_hi ())
in (

let seed = (FStar_Options.z3_seed ())
in (

let name = (full_query_id default_settings)
in (

let quaking = (hi > (Prims.parse_int "1"))
in (

let hi1 = (match ((hi < (Prims.parse_int "1"))) with
| true -> begin
(Prims.parse_int "1")
end
| uu____3903 -> begin
hi
end)
in (

let lo1 = (match ((lo < (Prims.parse_int "1"))) with
| true -> begin
(Prims.parse_int "1")
end
| uu____3911 -> begin
(match ((lo > hi1)) with
| true -> begin
hi1
end
| uu____3915 -> begin
lo
end)
end)
in (

let run_one = (fun seed1 -> (

let uu____3931 = (FStar_Options.z3_refresh ())
in (match (uu____3931) with
| true -> begin
(FStar_Options.with_saved_options (fun uu____3948 -> ((FStar_Options.set_option "z3seed" (FStar_Options.Int (seed1)));
(check_all_configs configs);
)))
end
| uu____3951 -> begin
(check_all_configs configs)
end)))
in (

let rec fold_nat' = (fun f acc lo2 hi2 -> (match ((lo2 > hi2)) with
| true -> begin
acc
end
| uu____4002 -> begin
(

let uu____4004 = (f acc lo2)
in (fold_nat' f uu____4004 (lo2 + (Prims.parse_int "1")) hi2))
end))
in (

let best_fuel = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let best_ifuel = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let maybe_improve = (fun r n1 -> (

let uu____4127 = (FStar_ST.op_Bang r)
in (match (uu____4127) with
| FStar_Pervasives_Native.None -> begin
(FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some (n1)))
end
| FStar_Pervasives_Native.Some (m) -> begin
(match ((n1 < m)) with
| true -> begin
(FStar_ST.op_Colon_Equals r (FStar_Pervasives_Native.Some (n1)))
end
| uu____4213 -> begin
()
end)
end)))
in (

let uu____4215 = (fold_nat' (fun uu____4249 n1 -> (match (uu____4249) with
| (nsucc, rs) -> begin
(

let r = (run_one (seed + n1))
in (

let nsucc1 = (match (r) with
| FStar_Util.Inr (cfg) -> begin
((maybe_improve best_fuel cfg.query_fuel);
(maybe_improve best_ifuel cfg.query_ifuel);
(nsucc + (Prims.parse_int "1"));
)
end
| uu____4314 -> begin
nsucc
end)
in ((

let uu____4322 = ((quaking && ((FStar_Options.interactive ()) || (FStar_Options.debug_any ()))) && (n1 < (hi1 - (Prims.parse_int "1"))))
in (match (uu____4322) with
| true -> begin
(

let uu____4326 = (FStar_Util.string_of_int nsucc1)
in (

let uu____4328 = (FStar_Util.string_of_int ((n1 + (Prims.parse_int "1")) - nsucc1))
in (

let uu____4331 = (FStar_Util.string_of_int ((hi1 - (Prims.parse_int "1")) - n1))
in (FStar_Util.print4 "Quake: so far query %s succeeded %s times and failed %s (%s runs remain)\n" name uu____4326 uu____4328 uu____4331))))
end
| uu____4335 -> begin
()
end));
((nsucc1), ((r)::rs));
)))
end)) (((Prims.parse_int "0")), ([])) (Prims.parse_int "0") (hi1 - (Prims.parse_int "1")))
in (match (uu____4215) with
| (nsuccess, rs) -> begin
((match (quaking) with
| true -> begin
(

let fuel_msg = (

let uu____4394 = (

let uu____4405 = (FStar_ST.op_Bang best_fuel)
in (

let uu____4434 = (FStar_ST.op_Bang best_ifuel)
in ((uu____4405), (uu____4434))))
in (match (uu____4394) with
| (FStar_Pervasives_Native.Some (f), FStar_Pervasives_Native.Some (i)) -> begin
(

let uu____4482 = (FStar_Util.string_of_int f)
in (

let uu____4484 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 " (best fuel=%s, best ifuel=%s)" uu____4482 uu____4484)))
end
| (uu____4487, uu____4488) -> begin
""
end))
in (

let uu____4502 = (FStar_Util.string_of_int nsuccess)
in (

let uu____4504 = (FStar_Util.string_of_int hi1)
in (FStar_Util.print4 "Quake: query %s succeeded %s/%s times%s\n" name uu____4502 uu____4504 fuel_msg))))
end
| uu____4507 -> begin
()
end);
(match ((nsuccess < lo1)) with
| true -> begin
(

let all_errs = (FStar_List.concatMap (fun uu___4_4525 -> (match (uu___4_4525) with
| FStar_Util.Inr (uu____4536) -> begin
[]
end
| FStar_Util.Inl (es) -> begin
(es)::[]
end)) rs)
in (

let uu____4550 = (quaking && (

let uu____4553 = (FStar_Options.query_stats ())
in (not (uu____4553))))
in (match (uu____4550) with
| true -> begin
(

let errors_to_report1 = (fun errs -> (errors_to_report (

let uu___548_4570 = default_settings
in {query_env = uu___548_4570.query_env; query_decl = uu___548_4570.query_decl; query_name = uu___548_4570.query_name; query_index = uu___548_4570.query_index; query_range = uu___548_4570.query_range; query_fuel = uu___548_4570.query_fuel; query_ifuel = uu___548_4570.query_ifuel; query_rlimit = uu___548_4570.query_rlimit; query_hint = uu___548_4570.query_hint; query_errors = errs; query_all_labels = uu___548_4570.query_all_labels; query_suffix = uu___548_4570.query_suffix; query_hash = uu___548_4570.query_hash})))
in (

let errs = (FStar_List.map errors_to_report1 all_errs)
in (

let errs1 = (

let uu____4595 = (FStar_All.pipe_right errs FStar_List.flatten)
in (FStar_All.pipe_right uu____4595 collect))
in (

let errs2 = (FStar_All.pipe_right errs1 (FStar_List.map (fun uu____4678 -> (match (uu____4678) with
| ((e, m, r), n1) -> begin
(match ((n1 > (Prims.parse_int "1"))) with
| true -> begin
(

let uu____4722 = (

let uu____4724 = (

let uu____4726 = (FStar_Util.string_of_int n1)
in (FStar_Util.format1 " (%s times)" uu____4726))
in (Prims.op_Hat m uu____4724))
in ((e), (uu____4722), (r)))
end
| uu____4730 -> begin
((e), (m), (r))
end)
end))))
in ((FStar_Errors.add_errors errs2);
(

let rng = (match ((FStar_Pervasives_Native.snd env.FStar_TypeChecker_Env.qtbl_name_and_index)) with
| FStar_Pervasives_Native.Some (l, uu____4746) -> begin
(FStar_Ident.range_of_lid l)
end
| uu____4754 -> begin
FStar_Range.dummyRange
end)
in (

let uu____4762 = (

let uu____4772 = (

let uu____4780 = (

let uu____4782 = (FStar_Util.string_of_int nsuccess)
in (

let uu____4784 = (FStar_Util.string_of_int hi1)
in (

let uu____4786 = (FStar_Util.string_of_int lo1)
in (FStar_Util.format4 "Query %s failed the quake test, %s out of %s attempts succeded, but the threshold was %s" name uu____4782 uu____4784 uu____4786))))
in ((FStar_Errors.Error_QuakeFailed), (uu____4780), (rng)))
in (uu____4772)::[])
in (FStar_TypeChecker_Err.add_errors env uu____4762)));
)))))
end
| uu____4804 -> begin
(

let report1 = (fun errs -> (report_errors (

let uu___569_4818 = default_settings
in {query_env = uu___569_4818.query_env; query_decl = uu___569_4818.query_decl; query_name = uu___569_4818.query_name; query_index = uu___569_4818.query_index; query_range = uu___569_4818.query_range; query_fuel = uu___569_4818.query_fuel; query_ifuel = uu___569_4818.query_ifuel; query_rlimit = uu___569_4818.query_rlimit; query_hint = uu___569_4818.query_hint; query_errors = errs; query_all_labels = uu___569_4818.query_all_labels; query_suffix = uu___569_4818.query_suffix; query_hash = uu___569_4818.query_hash})))
in (FStar_List.iter report1 all_errs))
end)))
end
| uu____4821 -> begin
()
end);
)
end)))))))))))))))
in (

let uu____4823 = (

let uu____4832 = (FStar_Options.admit_smt_queries ())
in (

let uu____4834 = (FStar_Options.admit_except ())
in ((uu____4832), (uu____4834))))
in (match (uu____4823) with
| (true, uu____4842) -> begin
()
end
| (false, FStar_Pervasives_Native.None) -> begin
(quake_and_check_all_configs all_configs)
end
| (false, FStar_Pervasives_Native.Some (id1)) -> begin
(

let skip = (match ((FStar_Util.starts_with id1 "(")) with
| true -> begin
(

let uu____4870 = (full_query_id default_settings)
in (Prims.op_disEquality uu____4870 id1))
end
| uu____4873 -> begin
(Prims.op_disEquality default_settings.query_name id1)
end)
in (match ((not (skip))) with
| true -> begin
(quake_and_check_all_configs all_configs)
end
| uu____4877 -> begin
()
end))
end)))))))))))
end));
))

type solver_cfg =
{seed : Prims.int; cliopt : Prims.string Prims.list; facts : (Prims.string Prims.list * Prims.bool) Prims.list; valid_intro : Prims.bool; valid_elim : Prims.bool}


let __proj__Mksolver_cfg__item__seed : solver_cfg  ->  Prims.int = (fun projectee -> (match (projectee) with
| {seed = seed; cliopt = cliopt; facts = facts; valid_intro = valid_intro; valid_elim = valid_elim} -> begin
seed
end))


let __proj__Mksolver_cfg__item__cliopt : solver_cfg  ->  Prims.string Prims.list = (fun projectee -> (match (projectee) with
| {seed = seed; cliopt = cliopt; facts = facts; valid_intro = valid_intro; valid_elim = valid_elim} -> begin
cliopt
end))


let __proj__Mksolver_cfg__item__facts : solver_cfg  ->  (Prims.string Prims.list * Prims.bool) Prims.list = (fun projectee -> (match (projectee) with
| {seed = seed; cliopt = cliopt; facts = facts; valid_intro = valid_intro; valid_elim = valid_elim} -> begin
facts
end))


let __proj__Mksolver_cfg__item__valid_intro : solver_cfg  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {seed = seed; cliopt = cliopt; facts = facts; valid_intro = valid_intro; valid_elim = valid_elim} -> begin
valid_intro
end))


let __proj__Mksolver_cfg__item__valid_elim : solver_cfg  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {seed = seed; cliopt = cliopt; facts = facts; valid_intro = valid_intro; valid_elim = valid_elim} -> begin
valid_elim
end))


let _last_cfg : solver_cfg FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let get_cfg : FStar_TypeChecker_Env.env  ->  solver_cfg = (fun env -> (

let uu____5100 = (FStar_Options.z3_seed ())
in (

let uu____5102 = (FStar_Options.z3_cliopt ())
in (

let uu____5106 = (FStar_Options.smtencoding_valid_intro ())
in (

let uu____5108 = (FStar_Options.smtencoding_valid_elim ())
in {seed = uu____5100; cliopt = uu____5102; facts = env.FStar_TypeChecker_Env.proof_ns; valid_intro = uu____5106; valid_elim = uu____5108})))))


let save_cfg : FStar_TypeChecker_Env.env  ->  unit = (fun env -> (

let uu____5116 = (

let uu____5119 = (get_cfg env)
in FStar_Pervasives_Native.Some (uu____5119))
in (FStar_ST.op_Colon_Equals _last_cfg uu____5116)))


let should_refresh : FStar_TypeChecker_Env.env  ->  Prims.bool = (fun env -> (

let uu____5150 = (FStar_ST.op_Bang _last_cfg)
in (match (uu____5150) with
| FStar_Pervasives_Native.None -> begin
((save_cfg env);
false;
)
end
| FStar_Pervasives_Native.Some (cfg) -> begin
(

let uu____5180 = (

let uu____5182 = (get_cfg env)
in (Prims.op_Equality cfg uu____5182))
in (not (uu____5180)))
end)))


let do_solve : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  unit = (fun use_env_msg tcenv q -> ((

let uu____5211 = (should_refresh tcenv)
in (match (uu____5211) with
| true -> begin
((save_cfg tcenv);
(FStar_SMTEncoding_Z3.refresh ());
)
end
| uu____5215 -> begin
()
end));
(

let uu____5218 = (

let uu____5220 = (

let uu____5222 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____5222))
in (FStar_Util.format1 "Starting query at %s" uu____5220))
in (FStar_SMTEncoding_Encode.push uu____5218));
(

let pop1 = (fun uu____5230 -> (

let uu____5231 = (

let uu____5233 = (

let uu____5235 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____5235))
in (FStar_Util.format1 "Ending query at %s" uu____5233))
in (FStar_SMTEncoding_Encode.pop uu____5231)))
in (FStar_All.try_with (fun uu___616_5251 -> (match (()) with
| () -> begin
(

let uu____5252 = (FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv q)
in (match (uu____5252) with
| (prefix1, labels, qry, suffix) -> begin
(

let tcenv1 = (FStar_TypeChecker_Env.incr_query_index tcenv)
in (match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.assumption_term = {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.FalseOp, uu____5284); FStar_SMTEncoding_Term.freevars = uu____5285; FStar_SMTEncoding_Term.rng = uu____5286}; FStar_SMTEncoding_Term.assumption_caption = uu____5287; FStar_SMTEncoding_Term.assumption_name = uu____5288; FStar_SMTEncoding_Term.assumption_fact_ids = uu____5289}) -> begin
(pop1 ())
end
| uu____5309 when tcenv1.FStar_TypeChecker_Env.admit -> begin
(pop1 ())
end
| FStar_SMTEncoding_Term.Assume (uu____5310) -> begin
((ask_and_report_errors tcenv1 labels prefix1 qry suffix);
(pop1 ());
)
end
| uu____5312 -> begin
(failwith "Impossible")
end))
end))
end)) (fun uu___615_5318 -> (match (uu___615_5318) with
| FStar_SMTEncoding_Env.Inner_let_rec (names1) -> begin
((pop1 ());
(

let uu____5328 = (

let uu____5338 = (

let uu____5346 = (

let uu____5348 = (

let uu____5350 = (FStar_List.map FStar_Pervasives_Native.fst names1)
in (FStar_String.concat "," uu____5350))
in (FStar_Util.format1 "Could not encode the query since F* does not support precise smtencoding of inner let-recs yet (in this case %s)" uu____5348))
in ((FStar_Errors.Error_NonTopRecFunctionNotFullyEncoded), (uu____5346), (tcenv.FStar_TypeChecker_Env.range)))
in (uu____5338)::[])
in (FStar_TypeChecker_Err.add_errors tcenv uu____5328));
)
end))));
))


let solve : (unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  unit = (fun use_env_msg tcenv q -> (

let uu____5405 = (FStar_Options.no_smt ())
in (match (uu____5405) with
| true -> begin
(

let uu____5408 = (

let uu____5418 = (

let uu____5426 = (

let uu____5428 = (FStar_Syntax_Print.term_to_string q)
in (FStar_Util.format1 "Q = %s\nA query could not be solved internally, and --no_smt was given" uu____5428))
in ((FStar_Errors.Error_NoSMTButNeeded), (uu____5426), (tcenv.FStar_TypeChecker_Env.range)))
in (uu____5418)::[])
in (FStar_TypeChecker_Err.add_errors tcenv uu____5408))
end
| uu____5446 -> begin
(do_solve use_env_msg tcenv q)
end)))


let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun e -> ((save_cfg e);
(FStar_SMTEncoding_Encode.init e);
)); FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push; FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop; FStar_TypeChecker_Env.snapshot = FStar_SMTEncoding_Encode.snapshot; FStar_TypeChecker_Env.rollback = FStar_SMTEncoding_Encode.rollback; FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig; FStar_TypeChecker_Env.preprocess = (fun e g -> (

let uu____5460 = (

let uu____5467 = (FStar_Options.peek ())
in ((e), (g), (uu____5467)))
in (uu____5460)::[])); FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}


let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun uu____5483 -> ()); FStar_TypeChecker_Env.push = (fun uu____5485 -> ()); FStar_TypeChecker_Env.pop = (fun uu____5488 -> ()); FStar_TypeChecker_Env.snapshot = (fun uu____5491 -> (((((Prims.parse_int "0")), ((Prims.parse_int "0")), ((Prims.parse_int "0")))), (()))); FStar_TypeChecker_Env.rollback = (fun uu____5510 uu____5511 -> ()); FStar_TypeChecker_Env.encode_sig = (fun uu____5526 uu____5527 -> ()); FStar_TypeChecker_Env.preprocess = (fun e g -> (

let uu____5533 = (

let uu____5540 = (FStar_Options.peek ())
in ((e), (g), (uu____5540)))
in (uu____5533)::[])); FStar_TypeChecker_Env.solve = (fun uu____5556 uu____5557 uu____5558 -> ()); FStar_TypeChecker_Env.finish = (fun uu____5565 -> ()); FStar_TypeChecker_Env.refresh = (fun uu____5567 -> ())}




