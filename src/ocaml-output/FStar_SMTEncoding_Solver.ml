
open Prims

type z3_err =
(FStar_SMTEncoding_Term.error_labels * FStar_SMTEncoding_Z3.error_kind)


type z3_result =
(FStar_SMTEncoding_Z3.unsat_core, z3_err) FStar_Util.either


type z3_replay_result =
(FStar_SMTEncoding_Z3.unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either


let z3_result_as_replay_result = (fun uu___88_23 -> (match (uu___88_23) with
| FStar_Util.Inl (l) -> begin
FStar_Util.Inl (l)
end
| FStar_Util.Inr (r, uu____32) -> begin
FStar_Util.Inr (r)
end))

type hint_stat =
{hint : FStar_Util.hint Prims.option; replay_result : z3_replay_result; elapsed_time : Prims.int; source_location : FStar_Range.range}


type hint_stats_t =
hint_stat Prims.list


let recorded_hints : FStar_Util.hints Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let replaying_hints : FStar_Util.hints Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let hint_stats : hint_stat Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let format_hints_file_name : Prims.string  ->  Prims.string = (fun src_filename -> (FStar_Util.format1 "%s.hints" src_filename))


let initialize_hints_db = (fun src_filename force_record -> ((FStar_ST.write hint_stats []);
(

let uu____102 = (FStar_Options.record_hints ())
in (match (uu____102) with
| true -> begin
(FStar_ST.write recorded_hints (Some ([])))
end
| uu____109 -> begin
()
end));
(

let uu____110 = (FStar_Options.use_hints ())
in (match (uu____110) with
| true -> begin
(

let norm_src_filename = (FStar_Util.normalize_file_path src_filename)
in (

let val_filename = (format_hints_file_name norm_src_filename)
in (

let uu____113 = (FStar_Util.read_hints val_filename)
in (match (uu____113) with
| Some (hints) -> begin
(

let expected_digest = (FStar_Util.digest_of_file norm_src_filename)
in ((

let uu____118 = (FStar_Options.hint_info ())
in (match (uu____118) with
| true -> begin
(match ((hints.FStar_Util.module_digest = expected_digest)) with
| true -> begin
(FStar_Util.print1 "(%s) digest is valid; using hints db.\n" norm_src_filename)
end
| uu____119 -> begin
(FStar_Util.print1 "(%s) digest is invalid; using potentially stale hints\n" norm_src_filename)
end)
end
| uu____120 -> begin
()
end));
(FStar_ST.write replaying_hints (Some (hints.FStar_Util.hints)));
))
end
| None -> begin
(

let uu____124 = (FStar_Options.hint_info ())
in (match (uu____124) with
| true -> begin
(FStar_Util.print1 "(%s) Unable to read hints db.\n" norm_src_filename)
end
| uu____125 -> begin
()
end))
end))))
end
| uu____126 -> begin
()
end));
))


let finalize_hints_db : Prims.string  ->  Prims.unit = (fun src_filename -> ((

let uu____131 = (FStar_Options.record_hints ())
in (match (uu____131) with
| true -> begin
(

let hints = (

let uu____133 = (FStar_ST.read recorded_hints)
in (FStar_Option.get uu____133))
in (

let hints_db = (

let uu____139 = (FStar_Util.digest_of_file src_filename)
in {FStar_Util.module_digest = uu____139; FStar_Util.hints = hints})
in (

let hints_file_name = (format_hints_file_name src_filename)
in (FStar_Util.write_hints hints_file_name hints_db))))
end
| uu____141 -> begin
()
end));
(

let uu____143 = (FStar_Options.hint_info ())
in (match (uu____143) with
| true -> begin
(

let stats = (

let uu____146 = (FStar_ST.read hint_stats)
in (FStar_All.pipe_right uu____146 FStar_List.rev))
in (FStar_All.pipe_right stats (FStar_List.iter (fun s -> (match (s.replay_result) with
| FStar_Util.Inl (_unsat_core) -> begin
(

let uu____156 = (FStar_Range.string_of_range s.source_location)
in (

let uu____157 = (FStar_Util.string_of_int s.elapsed_time)
in (FStar_Util.print2 "Hint-info (%s): Replay succeeded in %s milliseconds\n" uu____156 uu____157)))
end
| FStar_Util.Inr (_error) -> begin
(

let uu____159 = (FStar_Range.string_of_range s.source_location)
in (

let uu____160 = (FStar_Util.string_of_int s.elapsed_time)
in (FStar_Util.print2 "Hint-info (%s): Replay failed in %s milliseconds\n" uu____159 uu____160)))
end)))))
end
| uu____161 -> begin
()
end));
(FStar_ST.write recorded_hints None);
(FStar_ST.write replaying_hints None);
(FStar_ST.write hint_stats []);
))


let with_hints_db = (fun fname f -> ((initialize_hints_db fname false);
(

let result = (f ())
in ((finalize_hints_db fname);
result;
));
))


let next_hint : Prims.string  ->  Prims.int  ->  FStar_Util.hint Prims.option = (fun qname qindex -> (

let uu____200 = (FStar_ST.read replaying_hints)
in (match (uu____200) with
| Some (hints) -> begin
(FStar_Util.find_map hints (fun uu___89_208 -> (match (uu___89_208) with
| Some (hint) when ((hint.FStar_Util.hint_name = qname) && (hint.FStar_Util.hint_index = qindex)) -> begin
Some (hint)
end
| uu____212 -> begin
None
end)))
end
| uu____214 -> begin
None
end)))


let record_hint : FStar_Util.hint Prims.option  ->  Prims.unit = (fun hint -> (

let hint = (match (hint) with
| None -> begin
None
end
| Some (h) -> begin
Some ((

let uu___91_225 = h
in {FStar_Util.hint_name = uu___91_225.FStar_Util.hint_name; FStar_Util.hint_index = uu___91_225.FStar_Util.hint_index; FStar_Util.fuel = uu___91_225.FStar_Util.fuel; FStar_Util.ifuel = uu___91_225.FStar_Util.ifuel; FStar_Util.unsat_core = uu___91_225.FStar_Util.unsat_core; FStar_Util.query_elapsed_time = (Prims.parse_int "0")}))
end)
in (

let uu____226 = (FStar_ST.read recorded_hints)
in (match (uu____226) with
| Some (l) -> begin
(FStar_ST.write recorded_hints (Some ((FStar_List.append l ((hint)::[])))))
end
| uu____240 -> begin
()
end))))


let record_hint_stat : FStar_Util.hint Prims.option  ->  z3_result  ->  Prims.int  ->  FStar_Range.range  ->  Prims.unit = (fun h res time r -> (

let s = {hint = h; replay_result = (z3_result_as_replay_result res); elapsed_time = time; source_location = r}
in (

let uu____257 = (

let uu____259 = (FStar_ST.read hint_stats)
in (s)::uu____259)
in (FStar_ST.write hint_stats uu____257))))


let ask_and_report_errors : FStar_TypeChecker_Env.env  ->  ((FStar_SMTEncoding_Z3.label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun env all_labels prefix query suffix -> ((FStar_SMTEncoding_Z3.giveZ3 prefix);
(

let uu____299 = (match (env.FStar_TypeChecker_Env.qname_and_index) with
| None -> begin
(failwith "No query name set!")
end
| Some (q, n) -> begin
(((FStar_Ident.text_of_lid q)), (n))
end)
in (match (uu____299) with
| (query_name, query_index) -> begin
(

let minimum_workable_fuel = (FStar_Util.mk_ref None)
in (

let set_minimum_workable_fuel = (fun f uu___90_355 -> (match (uu___90_355) with
| ([], uu____362) -> begin
()
end
| errs -> begin
(

let uu____368 = (FStar_ST.read minimum_workable_fuel)
in (match (uu____368) with
| Some (uu____389) -> begin
()
end
| None -> begin
(FStar_ST.write minimum_workable_fuel (Some (((f), (errs)))))
end))
end))
in (

let with_fuel = (fun label_assumptions p uu____453 -> (match (uu____453) with
| (n, i, rlimit) -> begin
(

let uu____462 = (

let uu____464 = (

let uu____465 = (

let uu____466 = (FStar_Util.string_of_int n)
in (

let uu____467 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" uu____466 uu____467)))
in FStar_SMTEncoding_Term.Caption (uu____465))
in (

let uu____468 = (

let uu____470 = (

let uu____471 = (

let uu____476 = (

let uu____477 = (

let uu____480 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (

let uu____482 = (FStar_SMTEncoding_Term.n_fuel n)
in ((uu____480), (uu____482))))
in (FStar_SMTEncoding_Util.mkEq uu____477))
in ((uu____476), (None), (None)))
in FStar_SMTEncoding_Term.Assume (uu____471))
in (

let uu____485 = (

let uu____487 = (

let uu____488 = (

let uu____493 = (

let uu____494 = (

let uu____497 = (FStar_SMTEncoding_Util.mkApp (("MaxIFuel"), ([])))
in (

let uu____499 = (FStar_SMTEncoding_Term.n_fuel i)
in ((uu____497), (uu____499))))
in (FStar_SMTEncoding_Util.mkEq uu____494))
in ((uu____493), (None), (None)))
in FStar_SMTEncoding_Term.Assume (uu____488))
in (uu____487)::(p)::[])
in (uu____470)::uu____485))
in (uu____464)::uu____468))
in (

let uu____502 = (

let uu____504 = (

let uu____506 = (

let uu____508 = (

let uu____509 = (

let uu____512 = (FStar_Util.string_of_int rlimit)
in (("rlimit"), (uu____512)))
in FStar_SMTEncoding_Term.SetOption (uu____509))
in (uu____508)::[])
in (

let uu____513 = (

let uu____515 = (

let uu____517 = (

let uu____519 = (FStar_Options.record_hints ())
in (match (uu____519) with
| true -> begin
(FStar_SMTEncoding_Term.GetUnsatCore)::[]
end
| uu____521 -> begin
[]
end))
in (FStar_List.append uu____517 suffix))
in (FStar_List.append ((FStar_SMTEncoding_Term.CheckSat)::[]) uu____515))
in (FStar_List.append uu____506 uu____513)))
in (FStar_List.append label_assumptions uu____504))
in (FStar_List.append uu____462 uu____502)))
end))
in (

let check = (fun p -> (

let rlimit = (

let uu____527 = (FStar_Options.z3_rlimit ())
in (uu____527 * (Prims.parse_int "544656")))
in (

let default_initial_config = (

let uu____532 = (FStar_Options.initial_fuel ())
in (

let uu____533 = (FStar_Options.initial_ifuel ())
in ((uu____532), (uu____533), (rlimit))))
in (

let hint_opt = (next_hint query_name query_index)
in (

let uu____536 = (match (hint_opt) with
| None -> begin
((None), (default_initial_config))
end
| Some (hint) -> begin
(

let uu____558 = (match ((FStar_Option.isSome hint.FStar_Util.unsat_core)) with
| true -> begin
((hint.FStar_Util.unsat_core), (rlimit))
end
| uu____570 -> begin
((None), (((Prims.parse_int "60") * (Prims.parse_int "544656"))))
end)
in (match (uu____558) with
| (core, timeout) -> begin
((core), (((hint.FStar_Util.fuel), (hint.FStar_Util.ifuel), (timeout))))
end))
end)
in (match (uu____536) with
| (unsat_core, initial_config) -> begin
(

let alt_configs = (

let uu____609 = (

let uu____615 = (

let uu____621 = (

let uu____626 = (

let uu____627 = (FStar_Options.max_ifuel ())
in (

let uu____628 = (FStar_Options.initial_ifuel ())
in (uu____627 > uu____628)))
in (match (uu____626) with
| true -> begin
(

let uu____633 = (

let uu____637 = (FStar_Options.initial_fuel ())
in (

let uu____638 = (FStar_Options.max_ifuel ())
in ((uu____637), (uu____638), (rlimit))))
in (uu____633)::[])
end
| uu____645 -> begin
[]
end))
in (

let uu____649 = (

let uu____655 = (

let uu____660 = (

let uu____661 = (

let uu____662 = (FStar_Options.max_fuel ())
in (uu____662 / (Prims.parse_int "2")))
in (

let uu____666 = (FStar_Options.initial_fuel ())
in (uu____661 > uu____666)))
in (match (uu____660) with
| true -> begin
(

let uu____671 = (

let uu____675 = (

let uu____676 = (FStar_Options.max_fuel ())
in (uu____676 / (Prims.parse_int "2")))
in (

let uu____680 = (FStar_Options.max_ifuel ())
in ((uu____675), (uu____680), (rlimit))))
in (uu____671)::[])
end
| uu____687 -> begin
[]
end))
in (

let uu____691 = (

let uu____697 = (

let uu____702 = ((

let uu____703 = (FStar_Options.max_fuel ())
in (

let uu____704 = (FStar_Options.initial_fuel ())
in (uu____703 > uu____704))) && (

let uu____705 = (FStar_Options.max_ifuel ())
in (

let uu____706 = (FStar_Options.initial_ifuel ())
in (uu____705 > uu____706))))
in (match (uu____702) with
| true -> begin
(

let uu____711 = (

let uu____715 = (FStar_Options.max_fuel ())
in (

let uu____716 = (FStar_Options.max_ifuel ())
in ((uu____715), (uu____716), (rlimit))))
in (uu____711)::[])
end
| uu____723 -> begin
[]
end))
in (

let uu____727 = (

let uu____733 = (

let uu____738 = (

let uu____739 = (FStar_Options.min_fuel ())
in (

let uu____740 = (FStar_Options.initial_fuel ())
in (uu____739 < uu____740)))
in (match (uu____738) with
| true -> begin
(

let uu____745 = (

let uu____749 = (FStar_Options.min_fuel ())
in ((uu____749), ((Prims.parse_int "1")), (rlimit)))
in (uu____745)::[])
end
| uu____756 -> begin
[]
end))
in (uu____733)::[])
in (uu____697)::uu____727))
in (uu____655)::uu____691))
in (uu____621)::uu____649))
in ((match (((default_initial_config <> initial_config) || (FStar_Option.isSome unsat_core))) with
| true -> begin
(default_initial_config)::[]
end
| uu____798 -> begin
[]
end))::uu____615)
in (FStar_List.flatten uu____609))
in (

let report = (fun p errs -> (

let errs = (

let uu____813 = ((FStar_Options.detail_errors ()) && (

let uu____814 = (FStar_Options.n_cores ())
in (uu____814 = (Prims.parse_int "1"))))
in (match (uu____813) with
| true -> begin
(

let uu____815 = (

let uu____824 = (FStar_ST.read minimum_workable_fuel)
in (match (uu____824) with
| Some (f, errs) -> begin
((f), (errs))
end
| None -> begin
(

let uu____889 = (

let uu____893 = (FStar_Options.min_fuel ())
in ((uu____893), ((Prims.parse_int "1")), (rlimit)))
in ((uu____889), (errs)))
end))
in (match (uu____815) with
| (min_fuel, potential_errors) -> begin
(

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref None)
in ((

let uu____947 = (with_fuel label_assumptions p min_fuel)
in (FStar_SMTEncoding_Z3.ask None all_labels uu____947 (fun r -> (FStar_ST.write res (Some (r))))));
(

let uu____972 = (FStar_ST.read res)
in (FStar_Option.get uu____972));
)))
in (

let uu____995 = (FStar_SMTEncoding_ErrorReporting.detail_errors env all_labels ask_z3)
in ((uu____995), (FStar_SMTEncoding_Z3.Default))))
end))
end
| uu____996 -> begin
(match (errs) with
| ([], FStar_SMTEncoding_Z3.Timeout) -> begin
(((((((""), (FStar_SMTEncoding_Term.Term_sort))), ("Timeout: Unknown assertion failed"), (FStar_Range.dummyRange)))::[]), ((Prims.snd errs)))
end
| ([], FStar_SMTEncoding_Z3.Default) -> begin
(((((((""), (FStar_SMTEncoding_Term.Term_sort))), ("Unknown assertion failed"), (FStar_Range.dummyRange)))::[]), ((Prims.snd errs)))
end
| (uu____1035, FStar_SMTEncoding_Z3.Kill) -> begin
(((((((""), (FStar_SMTEncoding_Term.Term_sort))), ("Killed: Unknown assertion failed"), (FStar_Range.dummyRange)))::[]), ((Prims.snd errs)))
end
| uu____1054 -> begin
errs
end)
end))
in ((record_hint None);
(

let uu____1057 = (FStar_Options.print_fuels ())
in (match (uu____1057) with
| true -> begin
(

let uu____1058 = (

let uu____1059 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range uu____1059))
in (

let uu____1060 = (

let uu____1061 = (FStar_Options.max_fuel ())
in (FStar_All.pipe_right uu____1061 FStar_Util.string_of_int))
in (

let uu____1062 = (

let uu____1063 = (FStar_Options.max_ifuel ())
in (FStar_All.pipe_right uu____1063 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" uu____1058 uu____1060 uu____1062))))
end
| uu____1064 -> begin
()
end));
(

let uu____1065 = (FStar_All.pipe_right (Prims.fst errs) (FStar_List.map (fun uu____1077 -> (match (uu____1077) with
| (uu____1083, x, y) -> begin
((x), (y))
end))))
in (FStar_TypeChecker_Err.add_errors env uu____1065));
)))
in (

let use_errors = (fun errs result -> (match (((errs), (result))) with
| ((([], _), _)) | ((_, FStar_Util.Inl (_))) -> begin
result
end
| (uu____1111, FStar_Util.Inr (uu____1112)) -> begin
FStar_Util.Inr (errs)
end))
in (

let rec try_alt_configs = (fun prev_f p errs cfgs -> ((set_minimum_workable_fuel prev_f errs);
(match (((cfgs), ((Prims.snd errs)))) with
| (([], _)) | ((_, FStar_SMTEncoding_Z3.Kill)) -> begin
(report p errs)
end
| ((mi)::[], uu____1191) -> begin
(match (errs) with
| ([], uu____1205) -> begin
(

let uu____1207 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask None all_labels uu____1207 (cb false mi p [])))
end
| uu____1213 -> begin
((set_minimum_workable_fuel prev_f errs);
(report p errs);
)
end)
end
| ((mi)::tl, uu____1217) -> begin
(

let uu____1232 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask None all_labels uu____1232 (fun uu____1235 -> (match (uu____1235) with
| (result, elapsed_time) -> begin
(

let uu____1252 = (

let uu____1259 = (use_errors errs result)
in ((uu____1259), (elapsed_time)))
in (cb false mi p tl uu____1252))
end))))
end);
))
and cb = (fun used_hint uu____1261 p alt uu____1264 -> (match (((uu____1261), (uu____1264))) with
| ((prev_fuel, prev_ifuel, timeout), (result, elapsed_time)) -> begin
((match (used_hint) with
| true -> begin
((FStar_SMTEncoding_Z3.refresh ());
(

let uu____1311 = (FStar_TypeChecker_Env.get_range env)
in (record_hint_stat hint_opt result elapsed_time uu____1311));
)
end
| uu____1312 -> begin
()
end);
(

let uu____1314 = ((FStar_Options.z3_refresh ()) || (FStar_Options.print_z3_statistics ()))
in (match (uu____1314) with
| true -> begin
(FStar_SMTEncoding_Z3.refresh ())
end
| uu____1315 -> begin
()
end));
(

let query_info = (fun tag -> (

let uu____1320 = (

let uu____1322 = (

let uu____1323 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range uu____1323))
in (

let uu____1324 = (

let uu____1326 = (FStar_SMTEncoding_Z3.at_log_file ())
in (

let uu____1327 = (

let uu____1329 = (

let uu____1331 = (FStar_Util.string_of_int query_index)
in (

let uu____1332 = (

let uu____1334 = (

let uu____1336 = (

let uu____1338 = (FStar_Util.string_of_int elapsed_time)
in (

let uu____1339 = (

let uu____1341 = (FStar_Util.string_of_int prev_fuel)
in (

let uu____1342 = (

let uu____1344 = (FStar_Util.string_of_int prev_ifuel)
in (uu____1344)::[])
in (uu____1341)::uu____1342))
in (uu____1338)::uu____1339))
in ((match (used_hint) with
| true -> begin
" (with hint)"
end
| uu____1345 -> begin
""
end))::uu____1336)
in (tag)::uu____1334)
in (uu____1331)::uu____1332))
in (query_name)::uu____1329)
in (uu____1326)::uu____1327))
in (uu____1322)::uu____1324))
in (FStar_Util.print "(%s%s)\n\tQuery (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s\n" uu____1320)))
in (match (result) with
| FStar_Util.Inl (unsat_core) -> begin
((match ((not (used_hint))) with
| true -> begin
(

let hint = {FStar_Util.hint_name = query_name; FStar_Util.hint_index = query_index; FStar_Util.fuel = prev_fuel; FStar_Util.ifuel = prev_ifuel; FStar_Util.unsat_core = unsat_core; FStar_Util.query_elapsed_time = elapsed_time}
in (record_hint (Some (hint))))
end
| uu____1351 -> begin
(record_hint hint_opt)
end);
(

let uu____1352 = ((FStar_Options.print_fuels ()) || (FStar_Options.hint_info ()))
in (match (uu____1352) with
| true -> begin
(query_info "succeeded")
end
| uu____1353 -> begin
()
end));
)
end
| FStar_Util.Inr (errs) -> begin
((

let uu____1360 = ((FStar_Options.print_fuels ()) || (FStar_Options.hint_info ()))
in (match (uu____1360) with
| true -> begin
(query_info "failed")
end
| uu____1361 -> begin
()
end));
(try_alt_configs ((prev_fuel), (prev_ifuel), (timeout)) p errs alt);
)
end));
)
end))
in ((match ((FStar_Option.isSome unsat_core)) with
| true -> begin
(FStar_SMTEncoding_Z3.refresh ())
end
| uu____1364 -> begin
()
end);
(

let uu____1365 = (with_fuel [] p initial_config)
in (FStar_SMTEncoding_Z3.ask unsat_core all_labels uu____1365 (cb (FStar_Option.isSome unsat_core) initial_config p alt_configs)));
)))))
end))))))
in (

let process_query = (fun q -> (

let uu____1372 = (

let uu____1373 = (FStar_Options.split_cases ())
in (uu____1373 > (Prims.parse_int "0")))
in (match (uu____1372) with
| true -> begin
(

let uu____1374 = (

let uu____1383 = (FStar_Options.split_cases ())
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query uu____1383 q))
in (match (uu____1374) with
| (b, cb) -> begin
(match (b) with
| true -> begin
(FStar_SMTEncoding_SplitQueryCases.handle_query cb check)
end
| uu____1398 -> begin
(check q)
end)
end))
end
| uu____1399 -> begin
(check q)
end)))
in (

let uu____1400 = (FStar_Options.admit_smt_queries ())
in (match (uu____1400) with
| true -> begin
()
end
| uu____1401 -> begin
(process_query query)
end)))))))
end));
))


let solve : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun use_env_msg tcenv q -> ((

let uu____1419 = (

let uu____1420 = (

let uu____1421 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____1421))
in (FStar_Util.format1 "Starting query at %s" uu____1420))
in (FStar_SMTEncoding_Encode.push uu____1419));
(

let tcenv = (FStar_TypeChecker_Env.incr_query_index tcenv)
in (

let uu____1423 = (FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv q)
in (match (uu____1423) with
| (prefix, labels, qry, suffix) -> begin
(

let pop = (fun uu____1444 -> (

let uu____1445 = (

let uu____1446 = (

let uu____1447 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____1447))
in (FStar_Util.format1 "Ending query at %s" uu____1446))
in (FStar_SMTEncoding_Encode.pop uu____1445)))
in (match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.FalseOp, uu____1448); FStar_SMTEncoding_Term.freevars = uu____1449; FStar_SMTEncoding_Term.rng = uu____1450}, uu____1451, uu____1452) -> begin
(pop ())
end
| uu____1462 when tcenv.FStar_TypeChecker_Env.admit -> begin
(pop ())
end
| FStar_SMTEncoding_Term.Assume (q, uu____1465, uu____1466) -> begin
((ask_and_report_errors tcenv labels prefix qry suffix);
(pop ());
)
end
| uu____1470 -> begin
(failwith "Impossible")
end))
end)));
))


let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init; FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push; FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop; FStar_TypeChecker_Env.mark = FStar_SMTEncoding_Encode.mark; FStar_TypeChecker_Env.reset_mark = FStar_SMTEncoding_Encode.reset_mark; FStar_TypeChecker_Env.commit_mark = FStar_SMTEncoding_Encode.commit_mark; FStar_TypeChecker_Env.encode_modul = FStar_SMTEncoding_Encode.encode_modul; FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig; FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = FStar_SMTEncoding_Encode.is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}


let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun uu____1471 -> ()); FStar_TypeChecker_Env.push = (fun uu____1472 -> ()); FStar_TypeChecker_Env.pop = (fun uu____1473 -> ()); FStar_TypeChecker_Env.mark = (fun uu____1474 -> ()); FStar_TypeChecker_Env.reset_mark = (fun uu____1475 -> ()); FStar_TypeChecker_Env.commit_mark = (fun uu____1476 -> ()); FStar_TypeChecker_Env.encode_modul = (fun uu____1477 uu____1478 -> ()); FStar_TypeChecker_Env.encode_sig = (fun uu____1479 uu____1480 -> ()); FStar_TypeChecker_Env.solve = (fun uu____1481 uu____1482 uu____1483 -> ()); FStar_TypeChecker_Env.is_trivial = (fun uu____1487 uu____1488 -> false); FStar_TypeChecker_Env.finish = (fun uu____1489 -> ()); FStar_TypeChecker_Env.refresh = (fun uu____1490 -> ())}




