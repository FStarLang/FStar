
open Prims
open FStar_Pervasives

type z3_err =
(FStar_SMTEncoding_Term.error_labels * FStar_SMTEncoding_Z3.error_kind)


type z3_result =
(FStar_SMTEncoding_Z3.unsat_core, z3_err) FStar_Util.either


type z3_replay_result =
(FStar_SMTEncoding_Z3.unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either


let z3_result_as_replay_result = (fun uu___84_27 -> (match (uu___84_27) with
| FStar_Util.Inl (l) -> begin
FStar_Util.Inl (l)
end
| FStar_Util.Inr (r, uu____36) -> begin
FStar_Util.Inr (r)
end))

type hint_stat =
{hint : FStar_Util.hint FStar_Pervasives_Native.option; replay_result : z3_replay_result; elapsed_time : Prims.int; source_location : FStar_Range.range}


let __proj__Mkhint_stat__item__hint : hint_stat  ->  FStar_Util.hint FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {hint = __fname__hint; replay_result = __fname__replay_result; elapsed_time = __fname__elapsed_time; source_location = __fname__source_location} -> begin
__fname__hint
end))


let __proj__Mkhint_stat__item__replay_result : hint_stat  ->  z3_replay_result = (fun projectee -> (match (projectee) with
| {hint = __fname__hint; replay_result = __fname__replay_result; elapsed_time = __fname__elapsed_time; source_location = __fname__source_location} -> begin
__fname__replay_result
end))


let __proj__Mkhint_stat__item__elapsed_time : hint_stat  ->  Prims.int = (fun projectee -> (match (projectee) with
| {hint = __fname__hint; replay_result = __fname__replay_result; elapsed_time = __fname__elapsed_time; source_location = __fname__source_location} -> begin
__fname__elapsed_time
end))


let __proj__Mkhint_stat__item__source_location : hint_stat  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {hint = __fname__hint; replay_result = __fname__replay_result; elapsed_time = __fname__elapsed_time; source_location = __fname__source_location} -> begin
__fname__source_location
end))


type hint_stats_t =
hint_stat Prims.list


let recorded_hints : FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let replaying_hints : FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let hint_stats : hint_stat Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let format_hints_file_name : Prims.string  ->  Prims.string = (fun src_filename -> (FStar_Util.format1 "%s.hints" src_filename))


let initialize_hints_db = (fun src_filename format_filename -> ((FStar_ST.write hint_stats []);
(

let uu____134 = (FStar_Options.record_hints ())
in (match (uu____134) with
| true -> begin
(FStar_ST.write recorded_hints (FStar_Pervasives_Native.Some ([])))
end
| uu____141 -> begin
()
end));
(

let uu____142 = (FStar_Options.use_hints ())
in (match (uu____142) with
| true -> begin
(

let norm_src_filename = (FStar_Util.normalize_file_path src_filename)
in (

let val_filename = (

let uu____145 = (FStar_Options.hint_file ())
in (match (uu____145) with
| FStar_Pervasives_Native.Some (fn) -> begin
fn
end
| FStar_Pervasives_Native.None -> begin
(format_hints_file_name norm_src_filename)
end))
in (

let uu____148 = (FStar_Util.read_hints val_filename)
in (match (uu____148) with
| FStar_Pervasives_Native.Some (hints) -> begin
(

let expected_digest = (FStar_Util.digest_of_file norm_src_filename)
in ((

let uu____153 = (FStar_Options.hint_info ())
in (match (uu____153) with
| true -> begin
(

let uu____154 = (

let uu____155 = (FStar_Options.hint_file ())
in (match (uu____155) with
| FStar_Pervasives_Native.Some (fn) -> begin
(Prims.strcat " from \'" (Prims.strcat val_filename "\'"))
end
| uu____158 -> begin
""
end))
in (FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename (match ((hints.FStar_Util.module_digest = expected_digest)) with
| true -> begin
"valid; using hints"
end
| uu____160 -> begin
"invalid; using potentially stale hints"
end) uu____154))
end
| uu____161 -> begin
()
end));
(FStar_ST.write replaying_hints (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)));
))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____165 = (FStar_Options.hint_info ())
in (match (uu____165) with
| true -> begin
(FStar_Util.print1 "(%s) Unable to read hint file.\n" norm_src_filename)
end
| uu____166 -> begin
()
end))
end))))
end
| uu____167 -> begin
()
end));
))


let finalize_hints_db : Prims.string  ->  Prims.unit = (fun src_filename -> ((

let uu____173 = (FStar_Options.record_hints ())
in (match (uu____173) with
| true -> begin
(

let hints = (

let uu____175 = (FStar_ST.read recorded_hints)
in (FStar_Option.get uu____175))
in (

let hints_db = (

let uu____181 = (FStar_Util.digest_of_file src_filename)
in {FStar_Util.module_digest = uu____181; FStar_Util.hints = hints})
in (

let norm_src_filename = (FStar_Util.normalize_file_path src_filename)
in (

let val_filename = (

let uu____184 = (FStar_Options.hint_file ())
in (match (uu____184) with
| FStar_Pervasives_Native.Some (fn) -> begin
fn
end
| FStar_Pervasives_Native.None -> begin
(format_hints_file_name norm_src_filename)
end))
in (FStar_Util.write_hints val_filename hints_db)))))
end
| uu____187 -> begin
()
end));
(

let uu____189 = (FStar_Options.hint_info ())
in (match (uu____189) with
| true -> begin
(

let stats = (

let uu____192 = (FStar_ST.read hint_stats)
in (FStar_All.pipe_right uu____192 FStar_List.rev))
in (FStar_All.pipe_right stats (FStar_List.iter (fun s -> (

let uu____204 = (FStar_Range.string_of_range s.source_location)
in (

let uu____205 = (FStar_Util.string_of_int s.elapsed_time)
in (FStar_Util.print3 "Hint-info (%s): Replay %s in %s milliseconds.\n" uu____204 (match (s.replay_result) with
| FStar_Util.Inl (uu____207) -> begin
"succeeded"
end
| FStar_Util.Inr (uu____208) -> begin
"failed"
end) uu____205)))))))
end
| uu____209 -> begin
()
end));
(FStar_ST.write recorded_hints FStar_Pervasives_Native.None);
(FStar_ST.write replaying_hints FStar_Pervasives_Native.None);
(FStar_ST.write hint_stats []);
))


let with_hints_db = (fun fname f -> ((initialize_hints_db fname false);
(

let result = (f ())
in ((finalize_hints_db fname);
result;
));
))


let next_hint : Prims.string  ->  Prims.int  ->  FStar_Util.hint FStar_Pervasives_Native.option = (fun qname qindex -> (

let uu____253 = (FStar_ST.read replaying_hints)
in (match (uu____253) with
| FStar_Pervasives_Native.Some (hints) -> begin
(FStar_Util.find_map hints (fun uu___85_263 -> (match (uu___85_263) with
| FStar_Pervasives_Native.Some (hint) when ((hint.FStar_Util.hint_name = qname) && (hint.FStar_Util.hint_index = qindex)) -> begin
FStar_Pervasives_Native.Some (hint)
end
| uu____267 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____269 -> begin
FStar_Pervasives_Native.None
end)))


let record_hint : FStar_Util.hint FStar_Pervasives_Native.option  ->  Prims.unit = (fun hint -> (

let hint1 = (match (hint) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (h) -> begin
FStar_Pervasives_Native.Some ((

let uu___89_282 = h
in {FStar_Util.hint_name = uu___89_282.FStar_Util.hint_name; FStar_Util.hint_index = uu___89_282.FStar_Util.hint_index; FStar_Util.fuel = uu___89_282.FStar_Util.fuel; FStar_Util.ifuel = uu___89_282.FStar_Util.ifuel; FStar_Util.unsat_core = uu___89_282.FStar_Util.unsat_core; FStar_Util.query_elapsed_time = (Prims.parse_int "0")}))
end)
in (

let uu____283 = (FStar_ST.read recorded_hints)
in (match (uu____283) with
| FStar_Pervasives_Native.Some (l) -> begin
(FStar_ST.write recorded_hints (FStar_Pervasives_Native.Some ((FStar_List.append l ((hint1)::[])))))
end
| uu____297 -> begin
()
end))))


let record_hint_stat : FStar_Util.hint FStar_Pervasives_Native.option  ->  z3_result  ->  Prims.int  ->  FStar_Range.range  ->  Prims.unit = (fun h res time r -> (

let s = {hint = h; replay_result = (z3_result_as_replay_result res); elapsed_time = time; source_location = r}
in (

let uu____318 = (

let uu____320 = (FStar_ST.read hint_stats)
in (s)::uu____320)
in (FStar_ST.write hint_stats uu____318))))


let filter_using_facts_from : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Term.decls_t  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun e theory -> (

let should_enc_fid = (fun fid -> (match (fid) with
| FStar_SMTEncoding_Term.Namespace (lid) -> begin
(FStar_TypeChecker_Env.should_enc_lid e lid)
end
| uu____342 -> begin
false
end))
in (

let matches_fact_ids = (fun include_assumption_names a -> (match (a.FStar_SMTEncoding_Term.assumption_fact_ids) with
| [] -> begin
true
end
| uu____352 -> begin
((FStar_List.contains a.FStar_SMTEncoding_Term.assumption_name include_assumption_names) || (FStar_All.pipe_right a.FStar_SMTEncoding_Term.assumption_fact_ids (FStar_Util.for_some (fun fid -> (should_enc_fid fid)))))
end))
in (

let theory_rev = (FStar_List.rev theory)
in (

let uu____359 = (FStar_List.fold_left (fun uu____374 d -> (match (uu____374) with
| (out, include_assumption_names) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(

let uu____395 = (matches_fact_ids include_assumption_names a)
in (match (uu____395) with
| true -> begin
(((d)::out), (include_assumption_names))
end
| uu____402 -> begin
((out), (include_assumption_names))
end))
end
| FStar_SMTEncoding_Term.RetainAssumptions (names1) -> begin
(((d)::out), ((FStar_List.append names1 include_assumption_names)))
end
| uu____409 -> begin
(((d)::out), (include_assumption_names))
end)
end)) (([]), ([])) theory_rev)
in (match (uu____359) with
| (pruned_theory, uu____416) -> begin
pruned_theory
end))))))


let filter_assertions : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Z3.unsat_core  ->  FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool) = (fun e core theory -> (match (core) with
| FStar_Pervasives_Native.None -> begin
(

let uu____440 = (filter_using_facts_from e theory)
in ((uu____440), (false)))
end
| FStar_Pervasives_Native.Some (core1) -> begin
(

let uu____446 = (FStar_List.fold_right (fun d uu____462 -> (match (uu____462) with
| (theory1, n_retained, n_pruned) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(match ((FStar_List.contains a.FStar_SMTEncoding_Term.assumption_name core1)) with
| true -> begin
(((d)::theory1), ((n_retained + (Prims.parse_int "1"))), (n_pruned))
end
| uu____486 -> begin
(match ((FStar_Util.starts_with a.FStar_SMTEncoding_Term.assumption_name "@")) with
| true -> begin
(((d)::theory1), (n_retained), (n_pruned))
end
| uu____492 -> begin
((theory1), (n_retained), ((n_pruned + (Prims.parse_int "1"))))
end)
end)
end
| uu____494 -> begin
(((d)::theory1), (n_retained), (n_pruned))
end)
end)) theory (([]), ((Prims.parse_int "0")), ((Prims.parse_int "0"))))
in (match (uu____446) with
| (theory', n_retained, n_pruned) -> begin
(

let missed_assertions = (fun th core2 -> (

let missed = (

let uu____517 = (FStar_All.pipe_right core2 (FStar_List.filter (fun nm -> (

let uu____524 = (FStar_All.pipe_right th (FStar_Util.for_some (fun uu___86_528 -> (match (uu___86_528) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(nm = a.FStar_SMTEncoding_Term.assumption_name)
end
| uu____530 -> begin
false
end))))
in (FStar_All.pipe_right uu____524 Prims.op_Negation)))))
in (FStar_All.pipe_right uu____517 (FStar_String.concat ", ")))
in (

let included = (

let uu____533 = (FStar_All.pipe_right th (FStar_List.collect (fun uu___87_539 -> (match (uu___87_539) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(a.FStar_SMTEncoding_Term.assumption_name)::[]
end
| uu____542 -> begin
[]
end))))
in (FStar_All.pipe_right uu____533 (FStar_String.concat ", ")))
in (FStar_Util.format2 "missed={%s}; included={%s}" missed included))))
in ((

let uu____545 = ((FStar_Options.hint_info ()) && (FStar_Options.debug_any ()))
in (match (uu____545) with
| true -> begin
(

let n1 = (FStar_List.length core1)
in (

let missed = (match ((n1 <> n_retained)) with
| true -> begin
(missed_assertions theory' core1)
end
| uu____554 -> begin
""
end)
in (

let uu____555 = (FStar_Util.string_of_int n_retained)
in (

let uu____556 = (match ((n1 <> n_retained)) with
| true -> begin
(

let uu____561 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 " (expected %s (%s); replay may be inaccurate)" uu____561 missed))
end
| uu____568 -> begin
""
end)
in (

let uu____569 = (FStar_Util.string_of_int n_pruned)
in (FStar_Util.print3 "\tHint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n" uu____555 uu____556 uu____569))))))
end
| uu____570 -> begin
()
end));
(

let uu____571 = (

let uu____573 = (

let uu____575 = (

let uu____576 = (

let uu____577 = (FStar_All.pipe_right core1 (FStar_String.concat ", "))
in (Prims.strcat "UNSAT CORE: " uu____577))
in FStar_SMTEncoding_Term.Caption (uu____576))
in (uu____575)::[])
in (FStar_List.append theory' uu____573))
in ((uu____571), (true)));
))
end))
end))


let filter_facts_without_core : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decl Prims.list * Prims.bool) = (fun e x -> (

let uu____591 = (filter_using_facts_from e x)
in ((uu____591), (false))))


let ask_and_report_errors : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun env all_labels prefix1 query suffix -> ((FStar_SMTEncoding_Z3.giveZ3 prefix1);
(

let uu____619 = (match (env.FStar_TypeChecker_Env.qname_and_index) with
| FStar_Pervasives_Native.None -> begin
(failwith "No query name set!")
end
| FStar_Pervasives_Native.Some (q, n1) -> begin
(((FStar_Ident.text_of_lid q)), (n1))
end)
in (match (uu____619) with
| (query_name, query_index) -> begin
(

let minimum_workable_fuel = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let set_minimum_workable_fuel = (fun f uu___88_675 -> (match (uu___88_675) with
| ([], uu____682) -> begin
()
end
| errs -> begin
(

let uu____688 = (FStar_ST.read minimum_workable_fuel)
in (match (uu____688) with
| FStar_Pervasives_Native.Some (uu____709) -> begin
()
end
| FStar_Pervasives_Native.None -> begin
(FStar_ST.write minimum_workable_fuel (FStar_Pervasives_Native.Some (((f), (errs)))))
end))
end))
in (

let with_fuel = (fun label_assumptions p uu____773 -> (match (uu____773) with
| (n1, i, rlimit) -> begin
(

let uu____782 = (

let uu____784 = (

let uu____785 = (

let uu____786 = (FStar_Util.string_of_int n1)
in (

let uu____787 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" uu____786 uu____787)))
in FStar_SMTEncoding_Term.Caption (uu____785))
in (

let uu____788 = (

let uu____790 = (

let uu____791 = (

let uu____795 = (

let uu____796 = (

let uu____799 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (

let uu____801 = (FStar_SMTEncoding_Term.n_fuel n1)
in ((uu____799), (uu____801))))
in (FStar_SMTEncoding_Util.mkEq uu____796))
in ((uu____795), (FStar_Pervasives_Native.None), ("@MaxFuel_assumption")))
in (FStar_SMTEncoding_Util.mkAssume uu____791))
in (

let uu____803 = (

let uu____805 = (

let uu____806 = (

let uu____810 = (

let uu____811 = (

let uu____814 = (FStar_SMTEncoding_Util.mkApp (("MaxIFuel"), ([])))
in (

let uu____816 = (FStar_SMTEncoding_Term.n_fuel i)
in ((uu____814), (uu____816))))
in (FStar_SMTEncoding_Util.mkEq uu____811))
in ((uu____810), (FStar_Pervasives_Native.None), ("@MaxIFuel_assumption")))
in (FStar_SMTEncoding_Util.mkAssume uu____806))
in (uu____805)::(p)::[])
in (uu____790)::uu____803))
in (uu____784)::uu____788))
in (

let uu____818 = (

let uu____820 = (

let uu____822 = (

let uu____824 = (

let uu____825 = (

let uu____828 = (FStar_Util.string_of_int rlimit)
in (("rlimit"), (uu____828)))
in FStar_SMTEncoding_Term.SetOption (uu____825))
in (uu____824)::[])
in (

let uu____829 = (

let uu____831 = (

let uu____833 = (

let uu____835 = (FStar_Options.record_hints ())
in (match (uu____835) with
| true -> begin
(FStar_SMTEncoding_Term.GetUnsatCore)::[]
end
| uu____837 -> begin
[]
end))
in (

let uu____838 = (

let uu____840 = (

let uu____842 = ((FStar_Options.print_z3_statistics ()) || (FStar_Options.check_hints ()))
in (match (uu____842) with
| true -> begin
(FStar_SMTEncoding_Term.GetStatistics)::(FStar_SMTEncoding_Term.GetReasonUnknown)::[]
end
| uu____844 -> begin
[]
end))
in (FStar_List.append uu____840 suffix))
in (FStar_List.append uu____833 uu____838)))
in (FStar_List.append ((FStar_SMTEncoding_Term.CheckSat)::[]) uu____831))
in (FStar_List.append uu____822 uu____829)))
in (FStar_List.append label_assumptions uu____820))
in (FStar_List.append uu____782 uu____818)))
end))
in (

let check = (fun p -> (

let rlimit = (

let uu____850 = (FStar_Options.z3_rlimit_factor ())
in (

let uu____851 = (

let uu____852 = (FStar_Options.z3_rlimit ())
in (uu____852 * (Prims.parse_int "544656")))
in (uu____850 * uu____851)))
in (

let default_initial_config = (

let uu____857 = (FStar_Options.initial_fuel ())
in (

let uu____858 = (FStar_Options.initial_ifuel ())
in ((uu____857), (uu____858), (rlimit))))
in (

let hint_opt = (next_hint query_name query_index)
in (

let uu____861 = (match (hint_opt) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (default_initial_config))
end
| FStar_Pervasives_Native.Some (hint) -> begin
(

let uu____883 = (match ((FStar_Option.isSome hint.FStar_Util.unsat_core)) with
| true -> begin
((hint.FStar_Util.unsat_core), (rlimit))
end
| uu____895 -> begin
((FStar_Pervasives_Native.None), (((Prims.parse_int "60") * (Prims.parse_int "544656"))))
end)
in (match (uu____883) with
| (core, timeout) -> begin
((core), (((hint.FStar_Util.fuel), (hint.FStar_Util.ifuel), (timeout))))
end))
end)
in (match (uu____861) with
| (unsat_core, initial_config) -> begin
(

let alt_configs = (

let uu____934 = (

let uu____940 = (

let uu____946 = (

let uu____951 = (

let uu____952 = (FStar_Options.max_ifuel ())
in (

let uu____953 = (FStar_Options.initial_ifuel ())
in (uu____952 > uu____953)))
in (match (uu____951) with
| true -> begin
(

let uu____958 = (

let uu____962 = (FStar_Options.initial_fuel ())
in (

let uu____963 = (FStar_Options.max_ifuel ())
in ((uu____962), (uu____963), (rlimit))))
in (uu____958)::[])
end
| uu____970 -> begin
[]
end))
in (

let uu____974 = (

let uu____980 = (

let uu____985 = (

let uu____986 = (

let uu____987 = (FStar_Options.max_fuel ())
in (uu____987 / (Prims.parse_int "2")))
in (

let uu____994 = (FStar_Options.initial_fuel ())
in (uu____986 > uu____994)))
in (match (uu____985) with
| true -> begin
(

let uu____999 = (

let uu____1003 = (

let uu____1004 = (FStar_Options.max_fuel ())
in (uu____1004 / (Prims.parse_int "2")))
in (

let uu____1011 = (FStar_Options.max_ifuel ())
in ((uu____1003), (uu____1011), (rlimit))))
in (uu____999)::[])
end
| uu____1018 -> begin
[]
end))
in (

let uu____1022 = (

let uu____1028 = (

let uu____1033 = ((

let uu____1038 = (FStar_Options.max_fuel ())
in (

let uu____1039 = (FStar_Options.initial_fuel ())
in (uu____1038 > uu____1039))) && (

let uu____1042 = (FStar_Options.max_ifuel ())
in (

let uu____1043 = (FStar_Options.initial_ifuel ())
in (uu____1042 >= uu____1043))))
in (match (uu____1033) with
| true -> begin
(

let uu____1048 = (

let uu____1052 = (FStar_Options.max_fuel ())
in (

let uu____1053 = (FStar_Options.max_ifuel ())
in ((uu____1052), (uu____1053), (rlimit))))
in (uu____1048)::[])
end
| uu____1060 -> begin
[]
end))
in (

let uu____1064 = (

let uu____1070 = (

let uu____1075 = (

let uu____1076 = (FStar_Options.min_fuel ())
in (

let uu____1077 = (FStar_Options.initial_fuel ())
in (uu____1076 < uu____1077)))
in (match (uu____1075) with
| true -> begin
(

let uu____1082 = (

let uu____1086 = (FStar_Options.min_fuel ())
in ((uu____1086), ((Prims.parse_int "1")), (rlimit)))
in (uu____1082)::[])
end
| uu____1093 -> begin
[]
end))
in (uu____1070)::[])
in (uu____1028)::uu____1064))
in (uu____980)::uu____1022))
in (uu____946)::uu____974))
in ((match (((default_initial_config <> initial_config) || (FStar_Option.isSome unsat_core))) with
| true -> begin
(default_initial_config)::[]
end
| uu____1135 -> begin
[]
end))::uu____940)
in (FStar_List.flatten uu____934))
in (

let report1 = (fun p1 errs -> (

let errs1 = (

let uu____1150 = ((FStar_Options.detail_errors ()) && (

let uu____1152 = (FStar_Options.n_cores ())
in (uu____1152 = (Prims.parse_int "1"))))
in (match (uu____1150) with
| true -> begin
(

let uu____1153 = (

let uu____1162 = (FStar_ST.read minimum_workable_fuel)
in (match (uu____1162) with
| FStar_Pervasives_Native.Some (f, errs1) -> begin
((f), (errs1))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1227 = (

let uu____1231 = (FStar_Options.min_fuel ())
in ((uu____1231), ((Prims.parse_int "1")), (rlimit)))
in ((uu____1227), (errs)))
end))
in (match (uu____1153) with
| (min_fuel1, potential_errors) -> begin
(

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((

let uu____1261 = (with_fuel label_assumptions p1 min_fuel1)
in (FStar_SMTEncoding_Z3.ask (filter_facts_without_core env) all_labels uu____1261 FStar_Pervasives_Native.None (fun r -> (FStar_ST.write res (FStar_Pervasives_Native.Some (r))))));
(

let uu____1268 = (FStar_ST.read res)
in (FStar_Option.get uu____1268));
)))
in (

let uu____1273 = (FStar_SMTEncoding_ErrorReporting.detail_errors env all_labels ask_z3)
in ((uu____1273), (FStar_SMTEncoding_Z3.Default))))
end))
end
| uu____1274 -> begin
(match (errs) with
| ([], FStar_SMTEncoding_Z3.Timeout) -> begin
(((((((""), (FStar_SMTEncoding_Term.Term_sort))), ("Timeout: Unknown assertion failed"), (FStar_Range.dummyRange)))::[]), ((FStar_Pervasives_Native.snd errs)))
end
| ([], FStar_SMTEncoding_Z3.Default) -> begin
(((((((""), (FStar_SMTEncoding_Term.Term_sort))), ("Unknown assertion failed"), (FStar_Range.dummyRange)))::[]), ((FStar_Pervasives_Native.snd errs)))
end
| (uu____1313, FStar_SMTEncoding_Z3.Kill) -> begin
(((((((""), (FStar_SMTEncoding_Term.Term_sort))), ("Killed: Unknown assertion failed"), (FStar_Range.dummyRange)))::[]), ((FStar_Pervasives_Native.snd errs)))
end
| uu____1332 -> begin
errs
end)
end))
in ((record_hint FStar_Pervasives_Native.None);
(

let uu____1335 = (FStar_Options.print_fuels ())
in (match (uu____1335) with
| true -> begin
(

let uu____1336 = (

let uu____1337 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range uu____1337))
in (

let uu____1338 = (

let uu____1339 = (FStar_Options.max_fuel ())
in (FStar_All.pipe_right uu____1339 FStar_Util.string_of_int))
in (

let uu____1340 = (

let uu____1341 = (FStar_Options.max_ifuel ())
in (FStar_All.pipe_right uu____1341 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" uu____1336 uu____1338 uu____1340))))
end
| uu____1342 -> begin
()
end));
(

let uu____1343 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst errs1) (FStar_List.map (fun uu____1359 -> (match (uu____1359) with
| (uu____1365, x, y) -> begin
((x), (y))
end))))
in (FStar_TypeChecker_Err.add_errors env uu____1343));
)))
in (

let use_errors = (fun errs result -> (match (((errs), (result))) with
| (([], uu____1381), uu____1382) -> begin
result
end
| (uu____1387, FStar_Util.Inl (uu____1388)) -> begin
result
end
| (uu____1395, FStar_Util.Inr (uu____1396)) -> begin
FStar_Util.Inr (errs)
end))
in (

let rec try_alt_configs = (fun prev_f p1 errs cfgs scope -> ((set_minimum_workable_fuel prev_f errs);
(match (((cfgs), ((FStar_Pervasives_Native.snd errs)))) with
| ([], uu____1463) -> begin
(report1 p1 errs)
end
| (uu____1471, FStar_SMTEncoding_Z3.Kill) -> begin
(report1 p1 errs)
end
| ((mi)::tl1, uu____1482) -> begin
(

let uu____1497 = (with_fuel [] p1 mi)
in (FStar_SMTEncoding_Z3.ask (filter_facts_without_core env) all_labels uu____1497 (FStar_Pervasives_Native.Some (scope)) (fun uu____1504 -> (match (uu____1504) with
| (result, elapsed_time, statistics) -> begin
(

let uu____1516 = (

let uu____1520 = (use_errors errs result)
in ((uu____1520), (elapsed_time), (statistics)))
in (cb false mi p1 tl1 scope uu____1516))
end))))
end);
))
and cb = (fun used_hint uu____1522 p1 alt scope uu____1526 -> (match (((uu____1522), (uu____1526))) with
| ((prev_fuel, prev_ifuel, timeout), (result, elapsed_time, statistics)) -> begin
((match (used_hint) with
| true -> begin
((FStar_SMTEncoding_Z3.refresh ());
(

let uu____1557 = (FStar_TypeChecker_Env.get_range env)
in (record_hint_stat hint_opt result elapsed_time uu____1557));
)
end
| uu____1558 -> begin
()
end);
(

let uu____1560 = ((FStar_Options.z3_refresh ()) || (FStar_Options.check_hints ()))
in (match (uu____1560) with
| true -> begin
(FStar_SMTEncoding_Z3.refresh ())
end
| uu____1561 -> begin
()
end));
(

let query_info = (fun env1 name tag statistics1 -> (

let uu____1579 = (((FStar_Options.print_fuels ()) || (FStar_Options.hint_info ())) || (FStar_Options.print_z3_statistics ()))
in (match (uu____1579) with
| true -> begin
(

let uu____1580 = (

let uu____1582 = (

let uu____1584 = (match (env1) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____1586 = (

let uu____1587 = (

let uu____1588 = (FStar_TypeChecker_Env.get_range e)
in (FStar_Range.string_of_range uu____1588))
in (

let uu____1589 = (

let uu____1590 = (FStar_SMTEncoding_Z3.at_log_file ())
in (Prims.strcat uu____1590 ")"))
in (Prims.strcat uu____1587 uu____1589)))
in (Prims.strcat "(" uu____1586))
end
| FStar_Pervasives_Native.None -> begin
""
end)
in (

let uu____1591 = (

let uu____1593 = (

let uu____1595 = (

let uu____1597 = (FStar_Util.string_of_int query_index)
in (

let uu____1598 = (

let uu____1600 = (

let uu____1602 = (

let uu____1604 = (FStar_Util.string_of_int elapsed_time)
in (

let uu____1605 = (

let uu____1607 = (FStar_Util.string_of_int prev_fuel)
in (

let uu____1608 = (

let uu____1610 = (FStar_Util.string_of_int prev_ifuel)
in (

let uu____1611 = (

let uu____1613 = (FStar_Util.string_of_int rlimit)
in (uu____1613)::[])
in (uu____1610)::uu____1611))
in (uu____1607)::uu____1608))
in (uu____1604)::uu____1605))
in ((match (env1) with
| FStar_Pervasives_Native.Some (e) -> begin
(match (used_hint) with
| true -> begin
" (with hint)"
end
| uu____1616 -> begin
""
end)
end
| FStar_Pervasives_Native.None -> begin
""
end))::uu____1602)
in (tag)::uu____1600)
in (uu____1597)::uu____1598))
in (query_name)::uu____1595)
in (name)::uu____1593)
in (uu____1584)::uu____1591))
in (

let uu____1617 = (

let uu____1619 = (

let uu____1620 = (FStar_Options.print_z3_statistics ())
in (match (uu____1620) with
| true -> begin
(

let f = (fun k v1 a -> (Prims.strcat a (Prims.strcat k (Prims.strcat "=" (Prims.strcat v1 " ")))))
in (

let str = (FStar_Util.smap_fold statistics1 f "statistics={")
in (

let uu____1632 = (FStar_Util.substring str (Prims.parse_int "0") ((FStar_String.length str) - (Prims.parse_int "1")))
in (Prims.strcat uu____1632 "}"))))
end
| uu____1639 -> begin
(

let uu____1640 = (FStar_Util.smap_try_find statistics1 "reason-unknown")
in (match (uu____1640) with
| FStar_Pervasives_Native.Some (v1) -> begin
(Prims.strcat "(reason-unknown=" (Prims.strcat v1 ")"))
end
| uu____1643 -> begin
""
end))
end))
in (uu____1619)::[])
in (FStar_List.append uu____1582 uu____1617)))
in (FStar_Util.print "%s\t%s (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n" uu____1580))
end
| uu____1645 -> begin
()
end)))
in (

let refine_hint = (fun unsat_core1 scope1 -> (

let current_core = (FStar_Util.mk_ref unsat_core1)
in (

let hint_worked = (FStar_Util.mk_ref false)
in (

let rec refine_hint = (fun core_ext_max_dist -> (

let uu____1663 = (

let uu____1664 = (FStar_ST.read hint_worked)
in (not (uu____1664)))
in (match (uu____1663) with
| true -> begin
(

let hint_check_cb = (fun uu____1678 -> (match (uu____1678) with
| (result1, elapsed_time1, statistics1) -> begin
(

let tag = (match (result1) with
| FStar_Util.Inl (uu____1701) -> begin
((FStar_ST.write hint_worked true);
"succeeded";
)
end
| FStar_Util.Inr (uu____1707) -> begin
"failed"
end)
in (

let uu____1712 = (FStar_Options.hint_info ())
in (match (uu____1712) with
| true -> begin
(query_info FStar_Pervasives_Native.None "Hint-check" tag statistics1)
end
| uu____1713 -> begin
()
end)))
end))
in ((FStar_SMTEncoding_Z3.refresh ());
(

let uu____1716 = (

let uu____1721 = (FStar_ST.read current_core)
in (filter_assertions env uu____1721))
in (

let uu____1724 = (with_fuel [] p1 ((prev_fuel), (prev_ifuel), (rlimit)))
in (FStar_SMTEncoding_Z3.ask uu____1716 all_labels uu____1724 (FStar_Pervasives_Native.Some (scope1)) hint_check_cb)));
(

let uu____1726 = (

let uu____1727 = (FStar_ST.read hint_worked)
in (not (uu____1727)))
in (match (uu____1726) with
| true -> begin
(

let refinement_ok = (FStar_Util.mk_ref false)
in ((

let uu____1734 = (

let uu____1735 = (

let uu____1737 = (

let uu____1739 = (

let uu____1740 = (

let uu____1741 = (

let uu____1743 = (FStar_Util.string_of_int core_ext_max_dist)
in (uu____1743)::[])
in (FStar_Util.format "smt.core.extend_patterns.max_distance=%s" uu____1741))
in FStar_Options.String (uu____1740))
in (uu____1739)::[])
in (FStar_Options.String ("smt.core.extend_patterns=true"))::uu____1737)
in FStar_Options.List (uu____1735))
in (FStar_Options.set_option "z3cliopt" uu____1734));
(

let hint_refinement_cb = (fun uu____1755 -> (match (uu____1755) with
| (result1, elapsed_time1, statistics1) -> begin
(

let uu____1777 = (FStar_Options.hint_info ())
in (match (uu____1777) with
| true -> begin
(

let tag = (match (result1) with
| FStar_Util.Inl (uc) -> begin
((FStar_ST.write refinement_ok true);
(FStar_ST.write current_core uc);
(

let uu____1788 = (FStar_Util.string_of_int core_ext_max_dist)
in (FStar_Util.format1 "succeeded (with smt.core.extend_patterns.max_distance=%s)" uu____1788));
)
end
| FStar_Util.Inr (errs) -> begin
"failed"
end)
in (query_info FStar_Pervasives_Native.None "Hint-refinement" tag statistics1))
end
| uu____1794 -> begin
()
end))
end))
in ((FStar_SMTEncoding_Z3.refresh ());
(

let uu____1797 = (with_fuel [] p1 ((prev_fuel), (prev_ifuel), (rlimit)))
in (FStar_SMTEncoding_Z3.ask (filter_facts_without_core env) all_labels uu____1797 (FStar_Pervasives_Native.Some (scope1)) hint_refinement_cb));
(

let uu____1799 = (FStar_ST.read refinement_ok)
in (match (uu____1799) with
| true -> begin
(

let cutoff = (Prims.parse_int "10")
in (match ((core_ext_max_dist >= cutoff)) with
| true -> begin
((

let uu____1804 = (

let uu____1806 = (FStar_Util.string_of_int cutoff)
in (uu____1806)::[])
in (FStar_Util.print "\tHint-fallback smt.core.extend_patterns.max_distance=%s reached, aborting refinement." uu____1804));
(FStar_ST.write current_core FStar_Pervasives_Native.None);
)
end
| uu____1810 -> begin
(refine_hint (core_ext_max_dist + (Prims.parse_int "1")))
end))
end
| uu____1811 -> begin
()
end));
));
))
end
| uu____1812 -> begin
()
end));
))
end
| uu____1813 -> begin
()
end)))
in ((

let z3cliopts_before = (FStar_Options.z3_cliopt ())
in (

let log_queries_before = (FStar_Options.log_queries ())
in ((FStar_Options.set_option "log_queries" (FStar_Options.Bool (false)));
(refine_hint (Prims.parse_int "1"));
(

let uu____1821 = (

let uu____1822 = (FStar_List.map (fun x -> FStar_Options.String (x)) z3cliopts_before)
in FStar_Options.List (uu____1822))
in (FStar_Options.set_option "z3cliopt" uu____1821));
(FStar_Options.set_option "log_queries" (FStar_Options.Bool (log_queries_before)));
)));
(

let uu____1826 = (FStar_ST.read current_core)
in {FStar_Util.hint_name = query_name; FStar_Util.hint_index = query_index; FStar_Util.fuel = prev_fuel; FStar_Util.ifuel = prev_ifuel; FStar_Util.unsat_core = uu____1826; FStar_Util.query_elapsed_time = elapsed_time});
)))))
in (match (result) with
| FStar_Util.Inl (unsat_core1) -> begin
((query_info (FStar_Pervasives_Native.Some (env)) "Query-stats" "succeeded" statistics);
(

let uu____1833 = (

let uu____1835 = ((not (used_hint)) && (FStar_Options.record_hints ()))
in (match (uu____1835) with
| true -> begin
(

let uu____1837 = (

let uu____1838 = (FStar_Options.check_hints ())
in (match (uu____1838) with
| true -> begin
(refine_hint unsat_core1 scope)
end
| uu____1839 -> begin
{FStar_Util.hint_name = query_name; FStar_Util.hint_index = query_index; FStar_Util.fuel = prev_fuel; FStar_Util.ifuel = prev_ifuel; FStar_Util.unsat_core = unsat_core1; FStar_Util.query_elapsed_time = elapsed_time}
end))
in FStar_Pervasives_Native.Some (uu____1837))
end
| uu____1840 -> begin
hint_opt
end))
in (record_hint uu____1833));
)
end
| FStar_Util.Inr (errs) -> begin
((query_info (FStar_Pervasives_Native.Some (env)) "Query-stats" "failed" statistics);
(

let uu____1844 = (used_hint && (FStar_Options.hint_info ()))
in (match (uu____1844) with
| true -> begin
((FStar_Util.print_string "Failed hint:\n");
(match (unsat_core) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.print_string "<empty>")
end
| FStar_Pervasives_Native.Some (core) -> begin
((

let uu____1851 = (FStar_List.map (fun x -> (FStar_Util.print_string (Prims.strcat " " x))) core)
in ());
(FStar_Util.print_string "\n");
)
end);
)
end
| uu____1856 -> begin
()
end));
(try_alt_configs ((prev_fuel), (prev_ifuel), (timeout)) p1 errs alt scope);
)
end)));
)
end))
in ((

let uu____1858 = ((FStar_Option.isSome unsat_core) || (FStar_Options.z3_refresh ()))
in (match (uu____1858) with
| true -> begin
(FStar_SMTEncoding_Z3.refresh ())
end
| uu____1860 -> begin
()
end));
(

let wf = (with_fuel [] p initial_config)
in (

let uu____1863 = (

let uu____1864 = (FStar_SMTEncoding_Z3.mk_fresh_scope ())
in (cb (FStar_Option.isSome unsat_core) initial_config p alt_configs uu____1864))
in (FStar_SMTEncoding_Z3.ask (filter_assertions env unsat_core) all_labels wf FStar_Pervasives_Native.None uu____1863)));
)))))
end))))))
in (

let process_query = (fun q -> (check q))
in (

let uu____1872 = (FStar_Options.admit_smt_queries ())
in (match (uu____1872) with
| true -> begin
()
end
| uu____1873 -> begin
(process_query query)
end)))))))
end));
))


let solve : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun use_env_msg tcenv q -> ((

let uu____1894 = (

let uu____1895 = (

let uu____1896 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____1896))
in (FStar_Util.format1 "Starting query at %s" uu____1895))
in (FStar_SMTEncoding_Encode.push uu____1894));
(

let tcenv1 = (FStar_TypeChecker_Env.incr_query_index tcenv)
in (

let uu____1898 = (FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q)
in (match (uu____1898) with
| (prefix1, labels, qry, suffix) -> begin
(

let pop1 = (fun uu____1919 -> (

let uu____1920 = (

let uu____1921 = (

let uu____1922 = (FStar_TypeChecker_Env.get_range tcenv1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____1922))
in (FStar_Util.format1 "Ending query at %s" uu____1921))
in (FStar_SMTEncoding_Encode.pop uu____1920)))
in (match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.assumption_term = {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.FalseOp, uu____1923); FStar_SMTEncoding_Term.freevars = uu____1924; FStar_SMTEncoding_Term.rng = uu____1925}; FStar_SMTEncoding_Term.assumption_caption = uu____1926; FStar_SMTEncoding_Term.assumption_name = uu____1927; FStar_SMTEncoding_Term.assumption_fact_ids = uu____1928}) -> begin
(pop1 ())
end
| uu____1936 when tcenv1.FStar_TypeChecker_Env.admit -> begin
(pop1 ())
end
| FStar_SMTEncoding_Term.Assume (uu____1937) -> begin
((ask_and_report_errors tcenv1 labels prefix1 qry suffix);
(pop1 ());
)
end
| uu____1939 -> begin
(failwith "Impossible")
end))
end)));
))


let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init; FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push; FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop; FStar_TypeChecker_Env.mark = FStar_SMTEncoding_Encode.mark; FStar_TypeChecker_Env.reset_mark = FStar_SMTEncoding_Encode.reset_mark; FStar_TypeChecker_Env.commit_mark = FStar_SMTEncoding_Encode.commit_mark; FStar_TypeChecker_Env.encode_modul = FStar_SMTEncoding_Encode.encode_modul; FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig; FStar_TypeChecker_Env.preprocess = (fun e g -> (

let uu____1945 = (

let uu____1949 = (FStar_Options.peek ())
in ((e), (g), (uu____1949)))
in (uu____1945)::[])); FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = FStar_SMTEncoding_Encode.is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}


let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun uu____1958 -> ()); FStar_TypeChecker_Env.push = (fun uu____1960 -> ()); FStar_TypeChecker_Env.pop = (fun uu____1962 -> ()); FStar_TypeChecker_Env.mark = (fun uu____1964 -> ()); FStar_TypeChecker_Env.reset_mark = (fun uu____1966 -> ()); FStar_TypeChecker_Env.commit_mark = (fun uu____1968 -> ()); FStar_TypeChecker_Env.encode_modul = (fun uu____1971 uu____1972 -> ()); FStar_TypeChecker_Env.encode_sig = (fun uu____1975 uu____1976 -> ()); FStar_TypeChecker_Env.preprocess = (fun e g -> (

let uu____1982 = (

let uu____1986 = (FStar_Options.peek ())
in ((e), (g), (uu____1986)))
in (uu____1982)::[])); FStar_TypeChecker_Env.solve = (fun uu____1996 uu____1997 uu____1998 -> ()); FStar_TypeChecker_Env.is_trivial = (fun uu____2004 uu____2005 -> false); FStar_TypeChecker_Env.finish = (fun uu____2007 -> ()); FStar_TypeChecker_Env.refresh = (fun uu____2009 -> ())}




