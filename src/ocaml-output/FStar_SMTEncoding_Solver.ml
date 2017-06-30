
open Prims
open FStar_Pervasives

type z3_err =
(FStar_SMTEncoding_Term.error_labels * FStar_SMTEncoding_Z3.error_kind)


type z3_result =
(FStar_SMTEncoding_Z3.unsat_core, z3_err) FStar_Util.either


type z3_replay_result =
(FStar_SMTEncoding_Z3.unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either


let z3_result_as_replay_result = (fun uu___83_23 -> (match (uu___83_23) with
| FStar_Util.Inl (l) -> begin
FStar_Util.Inl (l)
end
| FStar_Util.Inr (r, uu____32) -> begin
FStar_Util.Inr (r)
end))

type hint_stat =
{hint : FStar_Util.hint FStar_Pervasives_Native.option; replay_result : z3_replay_result; elapsed_time : Prims.int; source_location : FStar_Range.range}


type hint_stats_t =
hint_stat Prims.list


let recorded_hints : FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let replaying_hints : FStar_Util.hints FStar_Pervasives_Native.option FStar_ST.ref = (FStar_Util.mk_ref FStar_Pervasives_Native.None)


let hint_stats : hint_stat Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let format_hints_file_name : Prims.string  ->  Prims.string = (fun src_filename -> (FStar_Util.format1 "%s.hints" src_filename))


let initialize_hints_db = (fun src_filename format_filename -> ((FStar_ST.write hint_stats []);
(

let uu____106 = (FStar_Options.record_hints ())
in (match (uu____106) with
| true -> begin
(FStar_ST.write recorded_hints (FStar_Pervasives_Native.Some ([])))
end
| uu____113 -> begin
()
end));
(

let uu____114 = (FStar_Options.use_hints ())
in (match (uu____114) with
| true -> begin
(

let norm_src_filename = (FStar_Util.normalize_file_path src_filename)
in (

let val_filename = (

let uu____117 = (FStar_Options.hint_file ())
in (match (uu____117) with
| FStar_Pervasives_Native.Some (fn) -> begin
fn
end
| FStar_Pervasives_Native.None -> begin
(format_hints_file_name norm_src_filename)
end))
in (

let uu____120 = (FStar_Util.read_hints val_filename)
in (match (uu____120) with
| FStar_Pervasives_Native.Some (hints) -> begin
(

let expected_digest = (FStar_Util.digest_of_file norm_src_filename)
in ((

let uu____125 = (FStar_Options.hint_info ())
in (match (uu____125) with
| true -> begin
(

let uu____126 = (

let uu____127 = (FStar_Options.hint_file ())
in (match (uu____127) with
| FStar_Pervasives_Native.Some (fn) -> begin
(Prims.strcat " from \'" (Prims.strcat val_filename "\'"))
end
| uu____130 -> begin
""
end))
in (FStar_Util.print3 "(%s) digest is %s%s.\n" norm_src_filename (match ((hints.FStar_Util.module_digest = expected_digest)) with
| true -> begin
"valid; using hints"
end
| uu____132 -> begin
"invalid; using potentially stale hints"
end) uu____126))
end
| uu____133 -> begin
()
end));
(FStar_ST.write replaying_hints (FStar_Pervasives_Native.Some (hints.FStar_Util.hints)));
))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____137 = (FStar_Options.hint_info ())
in (match (uu____137) with
| true -> begin
(FStar_Util.print1 "(%s) Unable to read hint file.\n" norm_src_filename)
end
| uu____138 -> begin
()
end))
end))))
end
| uu____139 -> begin
()
end));
))


let finalize_hints_db : Prims.string  ->  Prims.unit = (fun src_filename -> ((

let uu____144 = (FStar_Options.record_hints ())
in (match (uu____144) with
| true -> begin
(

let hints = (

let uu____146 = (FStar_ST.read recorded_hints)
in (FStar_Option.get uu____146))
in (

let hints_db = (

let uu____152 = (FStar_Util.digest_of_file src_filename)
in {FStar_Util.module_digest = uu____152; FStar_Util.hints = hints})
in (

let norm_src_filename = (FStar_Util.normalize_file_path src_filename)
in (

let val_filename = (

let uu____155 = (FStar_Options.hint_file ())
in (match (uu____155) with
| FStar_Pervasives_Native.Some (fn) -> begin
fn
end
| FStar_Pervasives_Native.None -> begin
(format_hints_file_name norm_src_filename)
end))
in (FStar_Util.write_hints val_filename hints_db)))))
end
| uu____158 -> begin
()
end));
(

let uu____160 = (FStar_Options.hint_info ())
in (match (uu____160) with
| true -> begin
(

let stats = (

let uu____163 = (FStar_ST.read hint_stats)
in (FStar_All.pipe_right uu____163 FStar_List.rev))
in (FStar_All.pipe_right stats (FStar_List.iter (fun s -> (

let uu____172 = (FStar_Range.string_of_range s.source_location)
in (

let uu____173 = (FStar_Util.string_of_int s.elapsed_time)
in (FStar_Util.print3 "Hint-info (%s): Replay %s in %s milliseconds.\n" uu____172 (match (s.replay_result) with
| FStar_Util.Inl (uu____174) -> begin
"succeeded"
end
| FStar_Util.Inr (uu____175) -> begin
"failed"
end) uu____173)))))))
end
| uu____176 -> begin
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

let uu____215 = (FStar_ST.read replaying_hints)
in (match (uu____215) with
| FStar_Pervasives_Native.Some (hints) -> begin
(FStar_Util.find_map hints (fun uu___84_223 -> (match (uu___84_223) with
| FStar_Pervasives_Native.Some (hint) when ((hint.FStar_Util.hint_name = qname) && (hint.FStar_Util.hint_index = qindex)) -> begin
FStar_Pervasives_Native.Some (hint)
end
| uu____227 -> begin
FStar_Pervasives_Native.None
end)))
end
| uu____229 -> begin
FStar_Pervasives_Native.None
end)))


let record_hint : FStar_Util.hint FStar_Pervasives_Native.option  ->  Prims.unit = (fun hint -> (

let hint1 = (match (hint) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (h) -> begin
FStar_Pervasives_Native.Some ((

let uu___89_240 = h
in {FStar_Util.hint_name = uu___89_240.FStar_Util.hint_name; FStar_Util.hint_index = uu___89_240.FStar_Util.hint_index; FStar_Util.fuel = uu___89_240.FStar_Util.fuel; FStar_Util.ifuel = uu___89_240.FStar_Util.ifuel; FStar_Util.unsat_core = uu___89_240.FStar_Util.unsat_core; FStar_Util.query_elapsed_time = (Prims.parse_int "0")}))
end)
in (

let uu____241 = (FStar_ST.read recorded_hints)
in (match (uu____241) with
| FStar_Pervasives_Native.Some (l) -> begin
(FStar_ST.write recorded_hints (FStar_Pervasives_Native.Some ((FStar_List.append l ((hint1)::[])))))
end
| uu____255 -> begin
()
end))))


let record_hint_stat : FStar_Util.hint FStar_Pervasives_Native.option  ->  z3_result  ->  Prims.int  ->  FStar_Range.range  ->  Prims.unit = (fun h res time r -> (

let s = {hint = h; replay_result = (z3_result_as_replay_result res); elapsed_time = time; source_location = r}
in (

let uu____272 = (

let uu____274 = (FStar_ST.read hint_stats)
in (s)::uu____274)
in (FStar_ST.write hint_stats uu____272))))


let filter_using_facts_from : FStar_SMTEncoding_Term.decls_t  ->  FStar_SMTEncoding_Term.decls_t = (fun theory -> (

let uu____285 = (FStar_Options.using_facts_from ())
in (match (uu____285) with
| FStar_Pervasives_Native.None -> begin
theory
end
| FStar_Pervasives_Native.Some (namespace_strings) -> begin
(

let fact_id_in_namespace = (fun ns uu___85_298 -> (match (uu___85_298) with
| FStar_SMTEncoding_Term.Namespace (lid) -> begin
(FStar_Util.starts_with (FStar_Ident.text_of_lid lid) ns)
end
| FStar_SMTEncoding_Term.Name (_lid) -> begin
false
end
| FStar_SMTEncoding_Term.Tag (_s) -> begin
false
end))
in (

let matches_fact_ids = (fun include_assumption_names a -> (match (a.FStar_SMTEncoding_Term.assumption_fact_ids) with
| [] -> begin
true
end
| uu____311 -> begin
((FStar_List.contains a.FStar_SMTEncoding_Term.assumption_name include_assumption_names) || (FStar_All.pipe_right a.FStar_SMTEncoding_Term.assumption_fact_ids (FStar_Util.for_some (fun fid -> (FStar_All.pipe_right namespace_strings (FStar_Util.for_some (fun ns -> (fact_id_in_namespace ns fid))))))))
end))
in (

let theory_rev = (FStar_List.rev theory)
in (

let uu____319 = (FStar_List.fold_left (fun uu____328 d -> (match (uu____328) with
| (out, include_assumption_names) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(

let uu____349 = (matches_fact_ids include_assumption_names a)
in (match (uu____349) with
| true -> begin
(((d)::out), (include_assumption_names))
end
| uu____356 -> begin
((out), (include_assumption_names))
end))
end
| FStar_SMTEncoding_Term.RetainAssumptions (names) -> begin
(((d)::out), ((FStar_List.append names include_assumption_names)))
end
| uu____363 -> begin
(((d)::out), (include_assumption_names))
end)
end)) (([]), ([])) theory_rev)
in (match (uu____319) with
| (pruned_theory, uu____369) -> begin
pruned_theory
end)))))
end)))


let filter_assertions : FStar_SMTEncoding_Z3.unsat_core  ->  FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool) = (fun core theory -> (match (core) with
| FStar_Pervasives_Native.None -> begin
(

let uu____385 = (filter_using_facts_from theory)
in ((uu____385), (false)))
end
| FStar_Pervasives_Native.Some (core1) -> begin
(

let uu____389 = (FStar_List.fold_right (fun d uu____399 -> (match (uu____399) with
| (theory1, n_retained, n_pruned) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(match ((FStar_List.contains a.FStar_SMTEncoding_Term.assumption_name core1)) with
| true -> begin
(((d)::theory1), ((n_retained + (Prims.parse_int "1"))), (n_pruned))
end
| uu____423 -> begin
(match ((FStar_Util.starts_with a.FStar_SMTEncoding_Term.assumption_name "@")) with
| true -> begin
(((d)::theory1), (n_retained), (n_pruned))
end
| uu____429 -> begin
((theory1), (n_retained), ((n_pruned + (Prims.parse_int "1"))))
end)
end)
end
| uu____431 -> begin
(((d)::theory1), (n_retained), (n_pruned))
end)
end)) theory (([]), ((Prims.parse_int "0")), ((Prims.parse_int "0"))))
in (match (uu____389) with
| (theory', n_retained, n_pruned) -> begin
(

let missed_assertions = (fun th core2 -> (

let missed = (

let uu____453 = (FStar_All.pipe_right core2 (FStar_List.filter (fun nm -> (

let uu____458 = (FStar_All.pipe_right th (FStar_Util.for_some (fun uu___86_460 -> (match (uu___86_460) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(nm = a.FStar_SMTEncoding_Term.assumption_name)
end
| uu____462 -> begin
false
end))))
in (FStar_All.pipe_right uu____458 Prims.op_Negation)))))
in (FStar_All.pipe_right uu____453 (FStar_String.concat ", ")))
in (

let included = (

let uu____465 = (FStar_All.pipe_right th (FStar_List.collect (fun uu___87_469 -> (match (uu___87_469) with
| FStar_SMTEncoding_Term.Assume (a) -> begin
(a.FStar_SMTEncoding_Term.assumption_name)::[]
end
| uu____472 -> begin
[]
end))))
in (FStar_All.pipe_right uu____465 (FStar_String.concat ", ")))
in (FStar_Util.format2 "missed={%s}; included={%s}" missed included))))
in ((

let uu____475 = ((FStar_Options.hint_info ()) && (FStar_Options.debug_any ()))
in (match (uu____475) with
| true -> begin
(

let n1 = (FStar_List.length core1)
in (

let missed = (match ((n1 <> n_retained)) with
| true -> begin
(missed_assertions theory' core1)
end
| uu____481 -> begin
""
end)
in (

let uu____482 = (FStar_Util.string_of_int n_retained)
in (

let uu____483 = (match ((n1 <> n_retained)) with
| true -> begin
(

let uu____486 = (FStar_Util.string_of_int n1)
in (FStar_Util.format2 " (expected %s (%s); replay may be inaccurate)" uu____486 missed))
end
| uu____490 -> begin
""
end)
in (

let uu____491 = (FStar_Util.string_of_int n_pruned)
in (FStar_Util.print3 "\tHint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n" uu____482 uu____483 uu____491))))))
end
| uu____492 -> begin
()
end));
(

let uu____493 = (

let uu____495 = (

let uu____497 = (

let uu____498 = (

let uu____499 = (FStar_All.pipe_right core1 (FStar_String.concat ", "))
in (Prims.strcat "UNSAT CORE: " uu____499))
in FStar_SMTEncoding_Term.Caption (uu____498))
in (uu____497)::[])
in (FStar_List.append theory' uu____495))
in ((uu____493), (true)));
))
end))
end))


let filter_facts_without_core : FStar_SMTEncoding_Term.decls_t  ->  (FStar_SMTEncoding_Term.decls_t * Prims.bool) = (fun x -> (

let uu____507 = (filter_using_facts_from x)
in ((uu____507), (false))))


let ask_and_report_errors : FStar_TypeChecker_Env.env  ->  FStar_SMTEncoding_Term.error_labels  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun env all_labels prefix1 query suffix -> ((FStar_SMTEncoding_Z3.giveZ3 prefix1);
(

let uu____528 = (match (env.FStar_TypeChecker_Env.qname_and_index) with
| FStar_Pervasives_Native.None -> begin
(failwith "No query name set!")
end
| FStar_Pervasives_Native.Some (q, n1) -> begin
(((FStar_Ident.text_of_lid q)), (n1))
end)
in (match (uu____528) with
| (query_name, query_index) -> begin
(

let minimum_workable_fuel = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in (

let set_minimum_workable_fuel = (fun f uu___88_584 -> (match (uu___88_584) with
| ([], uu____591) -> begin
()
end
| errs -> begin
(

let uu____597 = (FStar_ST.read minimum_workable_fuel)
in (match (uu____597) with
| FStar_Pervasives_Native.Some (uu____618) -> begin
()
end
| FStar_Pervasives_Native.None -> begin
(FStar_ST.write minimum_workable_fuel (FStar_Pervasives_Native.Some (((f), (errs)))))
end))
end))
in (

let with_fuel = (fun label_assumptions p uu____682 -> (match (uu____682) with
| (n1, i, rlimit) -> begin
(

let uu____691 = (

let uu____693 = (

let uu____694 = (

let uu____695 = (FStar_Util.string_of_int n1)
in (

let uu____696 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" uu____695 uu____696)))
in FStar_SMTEncoding_Term.Caption (uu____694))
in (

let uu____697 = (

let uu____699 = (

let uu____700 = (

let uu____704 = (

let uu____705 = (

let uu____708 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (

let uu____710 = (FStar_SMTEncoding_Term.n_fuel n1)
in ((uu____708), (uu____710))))
in (FStar_SMTEncoding_Util.mkEq uu____705))
in ((uu____704), (FStar_Pervasives_Native.None), ("@MaxFuel_assumption")))
in (FStar_SMTEncoding_Util.mkAssume uu____700))
in (

let uu____712 = (

let uu____714 = (

let uu____715 = (

let uu____719 = (

let uu____720 = (

let uu____723 = (FStar_SMTEncoding_Util.mkApp (("MaxIFuel"), ([])))
in (

let uu____725 = (FStar_SMTEncoding_Term.n_fuel i)
in ((uu____723), (uu____725))))
in (FStar_SMTEncoding_Util.mkEq uu____720))
in ((uu____719), (FStar_Pervasives_Native.None), ("@MaxIFuel_assumption")))
in (FStar_SMTEncoding_Util.mkAssume uu____715))
in (uu____714)::(p)::[])
in (uu____699)::uu____712))
in (uu____693)::uu____697))
in (

let uu____727 = (

let uu____729 = (

let uu____731 = (

let uu____733 = (

let uu____734 = (

let uu____737 = (FStar_Util.string_of_int rlimit)
in (("rlimit"), (uu____737)))
in FStar_SMTEncoding_Term.SetOption (uu____734))
in (uu____733)::[])
in (

let uu____738 = (

let uu____740 = (

let uu____742 = (

let uu____744 = (FStar_Options.record_hints ())
in (match (uu____744) with
| true -> begin
(FStar_SMTEncoding_Term.GetUnsatCore)::[]
end
| uu____746 -> begin
[]
end))
in (

let uu____747 = (

let uu____749 = (

let uu____751 = ((FStar_Options.print_z3_statistics ()) || (FStar_Options.check_hints ()))
in (match (uu____751) with
| true -> begin
(FStar_SMTEncoding_Term.GetStatistics)::(FStar_SMTEncoding_Term.GetReasonUnknown)::[]
end
| uu____753 -> begin
[]
end))
in (FStar_List.append uu____749 suffix))
in (FStar_List.append uu____742 uu____747)))
in (FStar_List.append ((FStar_SMTEncoding_Term.CheckSat)::[]) uu____740))
in (FStar_List.append uu____731 uu____738)))
in (FStar_List.append label_assumptions uu____729))
in (FStar_List.append uu____691 uu____727)))
end))
in (

let check = (fun p -> (

let rlimit = (

let uu____759 = (FStar_Options.z3_rlimit_factor ())
in (

let uu____760 = (

let uu____761 = (FStar_Options.z3_rlimit ())
in (uu____761 * (Prims.parse_int "544656")))
in (uu____759 * uu____760)))
in (

let default_initial_config = (

let uu____766 = (FStar_Options.initial_fuel ())
in (

let uu____767 = (FStar_Options.initial_ifuel ())
in ((uu____766), (uu____767), (rlimit))))
in (

let hint_opt = (next_hint query_name query_index)
in (

let uu____770 = (match (hint_opt) with
| FStar_Pervasives_Native.None -> begin
((FStar_Pervasives_Native.None), (default_initial_config))
end
| FStar_Pervasives_Native.Some (hint) -> begin
(

let uu____792 = (match ((FStar_Option.isSome hint.FStar_Util.unsat_core)) with
| true -> begin
((hint.FStar_Util.unsat_core), (rlimit))
end
| uu____804 -> begin
((FStar_Pervasives_Native.None), (((Prims.parse_int "60") * (Prims.parse_int "544656"))))
end)
in (match (uu____792) with
| (core, timeout) -> begin
((core), (((hint.FStar_Util.fuel), (hint.FStar_Util.ifuel), (timeout))))
end))
end)
in (match (uu____770) with
| (unsat_core, initial_config) -> begin
(

let alt_configs = (

let uu____843 = (

let uu____849 = (

let uu____855 = (

let uu____860 = (

let uu____861 = (FStar_Options.max_ifuel ())
in (

let uu____862 = (FStar_Options.initial_ifuel ())
in (uu____861 > uu____862)))
in (match (uu____860) with
| true -> begin
(

let uu____867 = (

let uu____871 = (FStar_Options.initial_fuel ())
in (

let uu____872 = (FStar_Options.max_ifuel ())
in ((uu____871), (uu____872), (rlimit))))
in (uu____867)::[])
end
| uu____879 -> begin
[]
end))
in (

let uu____883 = (

let uu____889 = (

let uu____894 = (

let uu____895 = (

let uu____896 = (FStar_Options.max_fuel ())
in (uu____896 / (Prims.parse_int "2")))
in (

let uu____900 = (FStar_Options.initial_fuel ())
in (uu____895 > uu____900)))
in (match (uu____894) with
| true -> begin
(

let uu____905 = (

let uu____909 = (

let uu____910 = (FStar_Options.max_fuel ())
in (uu____910 / (Prims.parse_int "2")))
in (

let uu____914 = (FStar_Options.max_ifuel ())
in ((uu____909), (uu____914), (rlimit))))
in (uu____905)::[])
end
| uu____921 -> begin
[]
end))
in (

let uu____925 = (

let uu____931 = (

let uu____936 = ((

let uu____937 = (FStar_Options.max_fuel ())
in (

let uu____938 = (FStar_Options.initial_fuel ())
in (uu____937 > uu____938))) && (

let uu____939 = (FStar_Options.max_ifuel ())
in (

let uu____940 = (FStar_Options.initial_ifuel ())
in (uu____939 >= uu____940))))
in (match (uu____936) with
| true -> begin
(

let uu____945 = (

let uu____949 = (FStar_Options.max_fuel ())
in (

let uu____950 = (FStar_Options.max_ifuel ())
in ((uu____949), (uu____950), (rlimit))))
in (uu____945)::[])
end
| uu____957 -> begin
[]
end))
in (

let uu____961 = (

let uu____967 = (

let uu____972 = (

let uu____973 = (FStar_Options.min_fuel ())
in (

let uu____974 = (FStar_Options.initial_fuel ())
in (uu____973 < uu____974)))
in (match (uu____972) with
| true -> begin
(

let uu____979 = (

let uu____983 = (FStar_Options.min_fuel ())
in ((uu____983), ((Prims.parse_int "1")), (rlimit)))
in (uu____979)::[])
end
| uu____990 -> begin
[]
end))
in (uu____967)::[])
in (uu____931)::uu____961))
in (uu____889)::uu____925))
in (uu____855)::uu____883))
in ((match (((default_initial_config <> initial_config) || (FStar_Option.isSome unsat_core))) with
| true -> begin
(default_initial_config)::[]
end
| uu____1032 -> begin
[]
end))::uu____849)
in (FStar_List.flatten uu____843))
in (

let report1 = (fun p1 errs -> (

let errs1 = (

let uu____1047 = ((FStar_Options.detail_errors ()) && (

let uu____1048 = (FStar_Options.n_cores ())
in (uu____1048 = (Prims.parse_int "1"))))
in (match (uu____1047) with
| true -> begin
(

let uu____1049 = (

let uu____1058 = (FStar_ST.read minimum_workable_fuel)
in (match (uu____1058) with
| FStar_Pervasives_Native.Some (f, errs1) -> begin
((f), (errs1))
end
| FStar_Pervasives_Native.None -> begin
(

let uu____1123 = (

let uu____1127 = (FStar_Options.min_fuel ())
in ((uu____1127), ((Prims.parse_int "1")), (rlimit)))
in ((uu____1123), (errs)))
end))
in (match (uu____1049) with
| (min_fuel1, potential_errors) -> begin
(

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref FStar_Pervasives_Native.None)
in ((

let uu____1157 = (with_fuel label_assumptions p1 min_fuel1)
in (FStar_SMTEncoding_Z3.ask filter_facts_without_core all_labels uu____1157 FStar_Pervasives_Native.None (fun r -> (FStar_ST.write res (FStar_Pervasives_Native.Some (r))))));
(

let uu____1163 = (FStar_ST.read res)
in (FStar_Option.get uu____1163));
)))
in (

let uu____1168 = (FStar_SMTEncoding_ErrorReporting.detail_errors env all_labels ask_z3)
in ((uu____1168), (FStar_SMTEncoding_Z3.Default))))
end))
end
| uu____1169 -> begin
(match (errs) with
| ([], FStar_SMTEncoding_Z3.Timeout) -> begin
(((((((""), (FStar_SMTEncoding_Term.Term_sort))), ("Timeout: Unknown assertion failed"), (FStar_Range.dummyRange)))::[]), ((FStar_Pervasives_Native.snd errs)))
end
| ([], FStar_SMTEncoding_Z3.Default) -> begin
(((((((""), (FStar_SMTEncoding_Term.Term_sort))), ("Unknown assertion failed"), (FStar_Range.dummyRange)))::[]), ((FStar_Pervasives_Native.snd errs)))
end
| (uu____1208, FStar_SMTEncoding_Z3.Kill) -> begin
(((((((""), (FStar_SMTEncoding_Term.Term_sort))), ("Killed: Unknown assertion failed"), (FStar_Range.dummyRange)))::[]), ((FStar_Pervasives_Native.snd errs)))
end
| uu____1227 -> begin
errs
end)
end))
in ((record_hint FStar_Pervasives_Native.None);
(

let uu____1230 = (FStar_Options.print_fuels ())
in (match (uu____1230) with
| true -> begin
(

let uu____1231 = (

let uu____1232 = (

let uu____1233 = (FStar_Util.colorize_red " failed ")
in (Prims.strcat uu____1233 " with maximum fuel %s and ifuel %s\n"))
in (Prims.strcat "(%s) Query " uu____1232))
in (

let uu____1234 = (

let uu____1235 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range uu____1235))
in (

let uu____1236 = (

let uu____1237 = (FStar_Options.max_fuel ())
in (FStar_All.pipe_right uu____1237 FStar_Util.string_of_int))
in (

let uu____1238 = (

let uu____1239 = (FStar_Options.max_ifuel ())
in (FStar_All.pipe_right uu____1239 FStar_Util.string_of_int))
in (FStar_Util.print3 uu____1231 uu____1234 uu____1236 uu____1238)))))
end
| uu____1240 -> begin
()
end));
(

let uu____1241 = (FStar_All.pipe_right (FStar_Pervasives_Native.fst errs1) (FStar_List.map (fun uu____1253 -> (match (uu____1253) with
| (uu____1259, x, y) -> begin
((x), (y))
end))))
in (FStar_TypeChecker_Err.add_errors env uu____1241));
)))
in (

let use_errors = (fun errs result -> (match (((errs), (result))) with
| (([], uu____1275), uu____1276) -> begin
result
end
| (uu____1281, FStar_Util.Inl (uu____1282)) -> begin
result
end
| (uu____1289, FStar_Util.Inr (uu____1290)) -> begin
FStar_Util.Inr (errs)
end))
in (

let rec try_alt_configs = (fun prev_f p1 errs cfgs scope -> ((set_minimum_workable_fuel prev_f errs);
(match (((cfgs), ((FStar_Pervasives_Native.snd errs)))) with
| ([], uu____1357) -> begin
(report1 p1 errs)
end
| (uu____1365, FStar_SMTEncoding_Z3.Kill) -> begin
(report1 p1 errs)
end
| ((mi)::tl1, uu____1376) -> begin
(

let uu____1391 = (with_fuel [] p1 mi)
in (FStar_SMTEncoding_Z3.ask filter_facts_without_core all_labels uu____1391 (FStar_Pervasives_Native.Some (scope)) (fun uu____1393 -> (match (uu____1393) with
| (result, elapsed_time, statistics) -> begin
(

let uu____1405 = (

let uu____1409 = (use_errors errs result)
in ((uu____1409), (elapsed_time), (statistics)))
in (cb false mi p1 tl1 scope uu____1405))
end))))
end);
))
and cb = (fun used_hint uu____1411 p1 alt scope uu____1415 -> (match (((uu____1411), (uu____1415))) with
| ((prev_fuel, prev_ifuel, timeout), (result, elapsed_time, statistics)) -> begin
((match (used_hint) with
| true -> begin
((FStar_SMTEncoding_Z3.refresh ());
(

let uu____1446 = (FStar_TypeChecker_Env.get_range env)
in (record_hint_stat hint_opt result elapsed_time uu____1446));
)
end
| uu____1447 -> begin
()
end);
(

let uu____1449 = ((FStar_Options.z3_refresh ()) || (FStar_Options.check_hints ()))
in (match (uu____1449) with
| true -> begin
(FStar_SMTEncoding_Z3.refresh ())
end
| uu____1450 -> begin
()
end));
(

let query_info = (fun env1 name tag statistics1 -> (

let uu____1468 = (((FStar_Options.print_fuels ()) || (FStar_Options.hint_info ())) || (FStar_Options.print_z3_statistics ()))
in (match (uu____1468) with
| true -> begin
(

let uu____1469 = (

let uu____1471 = (

let uu____1473 = (match (env1) with
| FStar_Pervasives_Native.Some (e) -> begin
(

let uu____1475 = (

let uu____1476 = (

let uu____1477 = (FStar_TypeChecker_Env.get_range e)
in (FStar_Range.string_of_range uu____1477))
in (

let uu____1478 = (

let uu____1479 = (FStar_SMTEncoding_Z3.at_log_file ())
in (Prims.strcat uu____1479 ")"))
in (Prims.strcat uu____1476 uu____1478)))
in (Prims.strcat "(" uu____1475))
end
| FStar_Pervasives_Native.None -> begin
""
end)
in (

let uu____1480 = (

let uu____1482 = (

let uu____1484 = (

let uu____1485 = (FStar_Util.colorize_bold "(")
in (

let uu____1486 = (

let uu____1487 = (

let uu____1488 = (

let uu____1489 = (FStar_Util.string_of_int query_index)
in (Prims.strcat uu____1489 ")"))
in (Prims.strcat ", " uu____1488))
in (Prims.strcat query_name uu____1487))
in (Prims.strcat uu____1485 uu____1486)))
in (

let uu____1490 = (

let uu____1492 = (match (tag) with
| "failed" -> begin
(FStar_Util.colorize_red tag)
end
| "succeeded" -> begin
(FStar_Util.colorize_green tag)
end
| uu____1493 -> begin
(FStar_Util.colorize_bold tag)
end)
in (

let uu____1494 = (

let uu____1496 = (

let uu____1498 = (FStar_Util.string_of_int elapsed_time)
in (

let uu____1499 = (

let uu____1501 = (FStar_Util.string_of_int prev_fuel)
in (

let uu____1502 = (

let uu____1504 = (FStar_Util.string_of_int prev_ifuel)
in (

let uu____1505 = (

let uu____1507 = (FStar_Util.string_of_int rlimit)
in (uu____1507)::[])
in (uu____1504)::uu____1505))
in (uu____1501)::uu____1502))
in (uu____1498)::uu____1499))
in ((match (env1) with
| FStar_Pervasives_Native.Some (e) -> begin
(match (used_hint) with
| true -> begin
" (with hint)"
end
| uu____1509 -> begin
""
end)
end
| FStar_Pervasives_Native.None -> begin
""
end))::uu____1496)
in (uu____1492)::uu____1494))
in (uu____1484)::uu____1490))
in (name)::uu____1482)
in (uu____1473)::uu____1480))
in (

let uu____1510 = (

let uu____1512 = (

let uu____1513 = (FStar_Options.print_z3_statistics ())
in (match (uu____1513) with
| true -> begin
(

let f = (fun k v1 a -> (Prims.strcat a (Prims.strcat k (Prims.strcat "=" (Prims.strcat v1 " ")))))
in (

let str = (FStar_Util.smap_fold statistics1 f "statistics={")
in (

let uu____1525 = (FStar_Util.substring str (Prims.parse_int "0") ((FStar_String.length str) - (Prims.parse_int "1")))
in (Prims.strcat uu____1525 "}"))))
end
| uu____1529 -> begin
(

let uu____1530 = (FStar_Util.smap_try_find statistics1 "reason-unknown")
in (match (uu____1530) with
| FStar_Pervasives_Native.Some (v1) -> begin
(Prims.strcat "(reason-unknown=" (Prims.strcat v1 ")"))
end
| uu____1533 -> begin
""
end))
end))
in (uu____1512)::[])
in (FStar_List.append uu____1471 uu____1510)))
in (FStar_Util.print "%s\t%s %s\t%s%s in %s milliseconds with fuel %s and ifuel %s and rlimit %s %s\n" uu____1469))
end
| uu____1535 -> begin
()
end)))
in (

let refine_hint = (fun unsat_core1 scope1 -> (

let current_core = (FStar_Util.mk_ref unsat_core1)
in (

let hint_worked = (FStar_Util.mk_ref false)
in (

let rec refine_hint = (fun core_ext_max_dist -> (

let uu____1553 = (

let uu____1554 = (FStar_ST.read hint_worked)
in (not (uu____1554)))
in (match (uu____1553) with
| true -> begin
(

let hint_check_cb = (fun uu____1568 -> (match (uu____1568) with
| (result1, elapsed_time1, statistics1) -> begin
(

let tag = (match (result1) with
| FStar_Util.Inl (uu____1591) -> begin
((FStar_ST.write hint_worked true);
"succeeded";
)
end
| FStar_Util.Inr (uu____1597) -> begin
"failed"
end)
in (

let uu____1602 = (FStar_Options.hint_info ())
in (match (uu____1602) with
| true -> begin
(query_info FStar_Pervasives_Native.None "Hint-check" tag statistics1)
end
| uu____1603 -> begin
()
end)))
end))
in ((FStar_SMTEncoding_Z3.refresh ());
(

let uu____1606 = (

let uu____1611 = (FStar_ST.read current_core)
in (filter_assertions uu____1611))
in (

let uu____1614 = (with_fuel [] p1 ((prev_fuel), (prev_ifuel), (rlimit)))
in (FStar_SMTEncoding_Z3.ask uu____1606 all_labels uu____1614 (FStar_Pervasives_Native.Some (scope1)) hint_check_cb)));
(

let uu____1616 = (

let uu____1617 = (FStar_ST.read hint_worked)
in (not (uu____1617)))
in (match (uu____1616) with
| true -> begin
(

let refinement_ok = (FStar_Util.mk_ref false)
in ((

let uu____1624 = (

let uu____1625 = (

let uu____1627 = (

let uu____1629 = (

let uu____1630 = (

let uu____1631 = (

let uu____1633 = (FStar_Util.string_of_int core_ext_max_dist)
in (uu____1633)::[])
in (FStar_Util.format "smt.core.extend_patterns.max_distance=%s" uu____1631))
in FStar_Options.String (uu____1630))
in (uu____1629)::[])
in (FStar_Options.String ("smt.core.extend_patterns=true"))::uu____1627)
in FStar_Options.List (uu____1625))
in (FStar_Options.set_option "z3cliopt" uu____1624));
(

let hint_refinement_cb = (fun uu____1645 -> (match (uu____1645) with
| (result1, elapsed_time1, statistics1) -> begin
(

let uu____1667 = (FStar_Options.hint_info ())
in (match (uu____1667) with
| true -> begin
(

let tag = (match (result1) with
| FStar_Util.Inl (uc) -> begin
((FStar_ST.write refinement_ok true);
(FStar_ST.write current_core uc);
(

let uu____1678 = (FStar_Util.string_of_int core_ext_max_dist)
in (FStar_Util.format1 "succeeded (with smt.core.extend_patterns.max_distance=%s)" uu____1678));
)
end
| FStar_Util.Inr (errs) -> begin
"failed"
end)
in (query_info FStar_Pervasives_Native.None "Hint-refinement" tag statistics1))
end
| uu____1684 -> begin
()
end))
end))
in ((FStar_SMTEncoding_Z3.refresh ());
(

let uu____1687 = (with_fuel [] p1 ((prev_fuel), (prev_ifuel), (rlimit)))
in (FStar_SMTEncoding_Z3.ask filter_facts_without_core all_labels uu____1687 (FStar_Pervasives_Native.Some (scope1)) hint_refinement_cb));
(

let uu____1689 = (FStar_ST.read refinement_ok)
in (match (uu____1689) with
| true -> begin
(

let cutoff = (Prims.parse_int "10")
in (match ((core_ext_max_dist >= cutoff)) with
| true -> begin
((

let uu____1694 = (

let uu____1696 = (FStar_Util.string_of_int cutoff)
in (uu____1696)::[])
in (FStar_Util.print "\tHint-fallback smt.core.extend_patterns.max_distance=%s reached, aborting refinement." uu____1694));
(FStar_ST.write current_core FStar_Pervasives_Native.None);
)
end
| uu____1700 -> begin
(refine_hint (core_ext_max_dist + (Prims.parse_int "1")))
end))
end
| uu____1701 -> begin
()
end));
));
))
end
| uu____1702 -> begin
()
end));
))
end
| uu____1703 -> begin
()
end)))
in ((

let z3cliopts_before = (FStar_Options.z3_cliopt ())
in (

let log_queries_before = (FStar_Options.log_queries ())
in ((FStar_Options.set_option "log_queries" (FStar_Options.Bool (false)));
(refine_hint (Prims.parse_int "1"));
(

let uu____1711 = (

let uu____1712 = (FStar_List.map (fun x -> FStar_Options.String (x)) z3cliopts_before)
in FStar_Options.List (uu____1712))
in (FStar_Options.set_option "z3cliopt" uu____1711));
(FStar_Options.set_option "log_queries" (FStar_Options.Bool (log_queries_before)));
)));
(

let uu____1715 = (FStar_ST.read current_core)
in {FStar_Util.hint_name = query_name; FStar_Util.hint_index = query_index; FStar_Util.fuel = prev_fuel; FStar_Util.ifuel = prev_ifuel; FStar_Util.unsat_core = uu____1715; FStar_Util.query_elapsed_time = elapsed_time});
)))))
in (match (result) with
| FStar_Util.Inl (unsat_core1) -> begin
((query_info (FStar_Pervasives_Native.Some (env)) "Query-stats" "succeeded" statistics);
(

let uu____1722 = (

let uu____1724 = ((not (used_hint)) && (FStar_Options.record_hints ()))
in (match (uu____1724) with
| true -> begin
(

let uu____1726 = (

let uu____1727 = (FStar_Options.check_hints ())
in (match (uu____1727) with
| true -> begin
(refine_hint unsat_core1 scope)
end
| uu____1728 -> begin
{FStar_Util.hint_name = query_name; FStar_Util.hint_index = query_index; FStar_Util.fuel = prev_fuel; FStar_Util.ifuel = prev_ifuel; FStar_Util.unsat_core = unsat_core1; FStar_Util.query_elapsed_time = elapsed_time}
end))
in FStar_Pervasives_Native.Some (uu____1726))
end
| uu____1729 -> begin
hint_opt
end))
in (record_hint uu____1722));
)
end
| FStar_Util.Inr (errs) -> begin
((query_info (FStar_Pervasives_Native.Some (env)) "Query-stats" "failed" statistics);
(

let uu____1733 = (used_hint && (FStar_Options.hint_info ()))
in (match (uu____1733) with
| true -> begin
((FStar_Util.print_string "Failed hint:\n");
(match (unsat_core) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.print_string "<empty>")
end
| FStar_Pervasives_Native.Some (core) -> begin
((

let uu____1740 = (FStar_List.map (fun x -> (FStar_Util.print_string (Prims.strcat " " x))) core)
in ());
(FStar_Util.print_string "\n");
)
end);
)
end
| uu____1744 -> begin
()
end));
(try_alt_configs ((prev_fuel), (prev_ifuel), (timeout)) p1 errs alt scope);
)
end)));
)
end))
in (

let fcore = (filter_assertions unsat_core)
in (

let wf = (with_fuel [] p initial_config)
in ((

let uu____1753 = ((FStar_Option.isSome unsat_core) || (FStar_Options.z3_refresh ()))
in (match (uu____1753) with
| true -> begin
(FStar_SMTEncoding_Z3.refresh ())
end
| uu____1755 -> begin
()
end));
(

let uu____1756 = (FStar_Options.admit_smt_queries ())
in (match (uu____1756) with
| true -> begin
(

let uu____1757 = (FStar_Options.log_queries ())
in (match (uu____1757) with
| true -> begin
(FStar_SMTEncoding_Z3.ask_offline fcore wf)
end
| uu____1758 -> begin
(

let uu____1759 = (

let uu____1760 = (FStar_SMTEncoding_Z3.mk_fresh_scope ())
in (cb (FStar_Option.isSome unsat_core) initial_config p alt_configs uu____1760))
in (FStar_SMTEncoding_Z3.ask fcore all_labels wf FStar_Pervasives_Native.None uu____1759))
end))
end
| uu____1764 -> begin
()
end));
)))))))
end))))))
in (

let uu____1765 = (FStar_Options.lax_except ())
in (match (uu____1765) with
| FStar_Pervasives_Native.None -> begin
(check query)
end
| FStar_Pervasives_Native.Some (id) -> begin
(

let cur_id = (

let uu____1769 = (

let uu____1770 = (

let uu____1771 = (

let uu____1772 = (FStar_Util.string_of_int query_index)
in (Prims.strcat uu____1772 ")"))
in (Prims.strcat ", " uu____1771))
in (Prims.strcat query_name uu____1770))
in (Prims.strcat "(" uu____1769))
in (match ((cur_id = id)) with
| true -> begin
(check query)
end
| uu____1773 -> begin
()
end))
end))))))
end));
))


let solve : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun use_env_msg tcenv q -> ((

let uu____1791 = (

let uu____1792 = (

let uu____1793 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____1793))
in (FStar_Util.format1 "Starting query at %s" uu____1792))
in (FStar_SMTEncoding_Encode.push uu____1791));
(

let tcenv1 = (FStar_TypeChecker_Env.incr_query_index tcenv)
in (

let uu____1795 = (FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q)
in (match (uu____1795) with
| (prefix1, labels, qry, suffix) -> begin
(

let pop1 = (fun uu____1816 -> (

let uu____1817 = (

let uu____1818 = (

let uu____1819 = (FStar_TypeChecker_Env.get_range tcenv1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____1819))
in (FStar_Util.format1 "Ending query at %s" uu____1818))
in (FStar_SMTEncoding_Encode.pop uu____1817)))
in (match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.assumption_term = {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.FalseOp, uu____1820); FStar_SMTEncoding_Term.freevars = uu____1821; FStar_SMTEncoding_Term.rng = uu____1822}; FStar_SMTEncoding_Term.assumption_caption = uu____1823; FStar_SMTEncoding_Term.assumption_name = uu____1824; FStar_SMTEncoding_Term.assumption_fact_ids = uu____1825}) -> begin
(pop1 ())
end
| uu____1833 when tcenv1.FStar_TypeChecker_Env.admit -> begin
(pop1 ())
end
| FStar_SMTEncoding_Term.Assume (uu____1834) -> begin
((ask_and_report_errors tcenv1 labels prefix1 qry suffix);
(pop1 ());
)
end
| uu____1836 -> begin
(failwith "Impossible")
end))
end)));
))


let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init; FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push; FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop; FStar_TypeChecker_Env.mark = FStar_SMTEncoding_Encode.mark; FStar_TypeChecker_Env.reset_mark = FStar_SMTEncoding_Encode.reset_mark; FStar_TypeChecker_Env.commit_mark = FStar_SMTEncoding_Encode.commit_mark; FStar_TypeChecker_Env.encode_modul = FStar_SMTEncoding_Encode.encode_modul; FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig; FStar_TypeChecker_Env.preprocess = (fun e g -> (((e), (g)))::[]); FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = FStar_SMTEncoding_Encode.is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}


let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun uu____1843 -> ()); FStar_TypeChecker_Env.push = (fun uu____1844 -> ()); FStar_TypeChecker_Env.pop = (fun uu____1845 -> ()); FStar_TypeChecker_Env.mark = (fun uu____1846 -> ()); FStar_TypeChecker_Env.reset_mark = (fun uu____1847 -> ()); FStar_TypeChecker_Env.commit_mark = (fun uu____1848 -> ()); FStar_TypeChecker_Env.encode_modul = (fun uu____1849 uu____1850 -> ()); FStar_TypeChecker_Env.encode_sig = (fun uu____1851 uu____1852 -> ()); FStar_TypeChecker_Env.preprocess = (fun e g -> (((e), (g)))::[]); FStar_TypeChecker_Env.solve = (fun uu____1859 uu____1860 uu____1861 -> ()); FStar_TypeChecker_Env.is_trivial = (fun uu____1865 uu____1866 -> false); FStar_TypeChecker_Env.finish = (fun uu____1867 -> ()); FStar_TypeChecker_Env.refresh = (fun uu____1868 -> ())}




