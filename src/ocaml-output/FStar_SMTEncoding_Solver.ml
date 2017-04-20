
open Prims

type z3_err =
(FStar_SMTEncoding_Term.error_labels * FStar_SMTEncoding_Z3.error_kind)


type z3_result =
(FStar_SMTEncoding_Z3.unsat_core, z3_err) FStar_Util.either


type z3_replay_result =
(FStar_SMTEncoding_Z3.unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either


let z3_result_as_replay_result = (fun uu___93_23 -> (match (uu___93_23) with
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
(FStar_Util.find_map hints (fun uu___94_208 -> (match (uu___94_208) with
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

let hint1 = (match (hint) with
| None -> begin
None
end
| Some (h) -> begin
Some ((

let uu___96_225 = h
in {FStar_Util.hint_name = uu___96_225.FStar_Util.hint_name; FStar_Util.hint_index = uu___96_225.FStar_Util.hint_index; FStar_Util.fuel = uu___96_225.FStar_Util.fuel; FStar_Util.ifuel = uu___96_225.FStar_Util.ifuel; FStar_Util.unsat_core = uu___96_225.FStar_Util.unsat_core; FStar_Util.query_elapsed_time = (Prims.parse_int "0")}))
end)
in (

let uu____226 = (FStar_ST.read recorded_hints)
in (match (uu____226) with
| Some (l) -> begin
(FStar_ST.write recorded_hints (Some ((FStar_List.append l ((hint1)::[])))))
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


let ask_and_report_errors : FStar_TypeChecker_Env.env  ->  ((FStar_SMTEncoding_Z3.label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun env all_labels prefix1 query suffix -> ((FStar_SMTEncoding_Z3.giveZ3 prefix1);
(

let uu____299 = (match (env.FStar_TypeChecker_Env.qname_and_index) with
| None -> begin
(failwith "No query name set!")
end
| Some (q, n1) -> begin
(((FStar_Ident.text_of_lid q)), (n1))
end)
in (match (uu____299) with
| (query_name, query_index) -> begin
(

let minimum_workable_fuel = (FStar_Util.mk_ref None)
in (

let set_minimum_workable_fuel = (fun f uu___95_355 -> (match (uu___95_355) with
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
| (n1, i, rlimit) -> begin
(

let uu____462 = (

let uu____464 = (

let uu____465 = (

let uu____466 = (FStar_Util.string_of_int n1)
in (

let uu____467 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" uu____466 uu____467)))
in FStar_SMTEncoding_Term.Caption (uu____465))
in (

let uu____468 = (

let uu____470 = (

let uu____471 = (

let uu____475 = (

let uu____476 = (

let uu____479 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (

let uu____481 = (FStar_SMTEncoding_Term.n_fuel n1)
in ((uu____479), (uu____481))))
in (FStar_SMTEncoding_Util.mkEq uu____476))
in ((uu____475), (None), ("@MaxFuel_assumption")))
in FStar_SMTEncoding_Term.Assume (uu____471))
in (

let uu____483 = (

let uu____485 = (

let uu____486 = (

let uu____490 = (

let uu____491 = (

let uu____494 = (FStar_SMTEncoding_Util.mkApp (("MaxIFuel"), ([])))
in (

let uu____496 = (FStar_SMTEncoding_Term.n_fuel i)
in ((uu____494), (uu____496))))
in (FStar_SMTEncoding_Util.mkEq uu____491))
in ((uu____490), (None), ("@MaxIFuel_assumption")))
in FStar_SMTEncoding_Term.Assume (uu____486))
in (uu____485)::(p)::[])
in (uu____470)::uu____483))
in (uu____464)::uu____468))
in (

let uu____498 = (

let uu____500 = (

let uu____502 = (

let uu____504 = (

let uu____505 = (

let uu____508 = (FStar_Util.string_of_int rlimit)
in (("rlimit"), (uu____508)))
in FStar_SMTEncoding_Term.SetOption (uu____505))
in (uu____504)::[])
in (

let uu____509 = (

let uu____511 = (

let uu____513 = (

let uu____515 = (FStar_Options.record_hints ())
in (match (uu____515) with
| true -> begin
(FStar_SMTEncoding_Term.GetUnsatCore)::[]
end
| uu____517 -> begin
[]
end))
in (FStar_List.append uu____513 suffix))
in (FStar_List.append ((FStar_SMTEncoding_Term.CheckSat)::[]) uu____511))
in (FStar_List.append uu____502 uu____509)))
in (FStar_List.append label_assumptions uu____500))
in (FStar_List.append uu____462 uu____498)))
end))
in (

let check = (fun p -> (

let rlimit = (

let uu____523 = (FStar_Options.z3_rlimit_factor ())
in (

let uu____524 = (

let uu____525 = (FStar_Options.z3_rlimit ())
in (uu____525 * (Prims.parse_int "544656")))
in (uu____523 * uu____524)))
in (

let default_initial_config = (

let uu____530 = (FStar_Options.initial_fuel ())
in (

let uu____531 = (FStar_Options.initial_ifuel ())
in ((uu____530), (uu____531), (rlimit))))
in (

let hint_opt = (next_hint query_name query_index)
in (

let uu____534 = (match (hint_opt) with
| None -> begin
((None), (default_initial_config))
end
| Some (hint) -> begin
(

let uu____556 = (match ((FStar_Option.isSome hint.FStar_Util.unsat_core)) with
| true -> begin
((hint.FStar_Util.unsat_core), (rlimit))
end
| uu____568 -> begin
((None), (((Prims.parse_int "60") * (Prims.parse_int "544656"))))
end)
in (match (uu____556) with
| (core, timeout) -> begin
((core), (((hint.FStar_Util.fuel), (hint.FStar_Util.ifuel), (timeout))))
end))
end)
in (match (uu____534) with
| (unsat_core, initial_config) -> begin
(

let alt_configs = (

let uu____607 = (

let uu____613 = (

let uu____619 = (

let uu____624 = (

let uu____625 = (FStar_Options.max_ifuel ())
in (

let uu____626 = (FStar_Options.initial_ifuel ())
in (uu____625 > uu____626)))
in (match (uu____624) with
| true -> begin
(

let uu____631 = (

let uu____635 = (FStar_Options.initial_fuel ())
in (

let uu____636 = (FStar_Options.max_ifuel ())
in ((uu____635), (uu____636), (rlimit))))
in (uu____631)::[])
end
| uu____643 -> begin
[]
end))
in (

let uu____647 = (

let uu____653 = (

let uu____658 = (

let uu____659 = (

let uu____660 = (FStar_Options.max_fuel ())
in (uu____660 / (Prims.parse_int "2")))
in (

let uu____664 = (FStar_Options.initial_fuel ())
in (uu____659 > uu____664)))
in (match (uu____658) with
| true -> begin
(

let uu____669 = (

let uu____673 = (

let uu____674 = (FStar_Options.max_fuel ())
in (uu____674 / (Prims.parse_int "2")))
in (

let uu____678 = (FStar_Options.max_ifuel ())
in ((uu____673), (uu____678), (rlimit))))
in (uu____669)::[])
end
| uu____685 -> begin
[]
end))
in (

let uu____689 = (

let uu____695 = (

let uu____700 = ((

let uu____701 = (FStar_Options.max_fuel ())
in (

let uu____702 = (FStar_Options.initial_fuel ())
in (uu____701 > uu____702))) && (

let uu____703 = (FStar_Options.max_ifuel ())
in (

let uu____704 = (FStar_Options.initial_ifuel ())
in (uu____703 > uu____704))))
in (match (uu____700) with
| true -> begin
(

let uu____709 = (

let uu____713 = (FStar_Options.max_fuel ())
in (

let uu____714 = (FStar_Options.max_ifuel ())
in ((uu____713), (uu____714), (rlimit))))
in (uu____709)::[])
end
| uu____721 -> begin
[]
end))
in (

let uu____725 = (

let uu____731 = (

let uu____736 = (

let uu____737 = (FStar_Options.min_fuel ())
in (

let uu____738 = (FStar_Options.initial_fuel ())
in (uu____737 < uu____738)))
in (match (uu____736) with
| true -> begin
(

let uu____743 = (

let uu____747 = (FStar_Options.min_fuel ())
in ((uu____747), ((Prims.parse_int "1")), (rlimit)))
in (uu____743)::[])
end
| uu____754 -> begin
[]
end))
in (uu____731)::[])
in (uu____695)::uu____725))
in (uu____653)::uu____689))
in (uu____619)::uu____647))
in ((match (((default_initial_config <> initial_config) || (FStar_Option.isSome unsat_core))) with
| true -> begin
(default_initial_config)::[]
end
| uu____796 -> begin
[]
end))::uu____613)
in (FStar_List.flatten uu____607))
in (

let report1 = (fun p1 errs -> (

let errs1 = (

let uu____811 = ((FStar_Options.detail_errors ()) && (

let uu____812 = (FStar_Options.n_cores ())
in (uu____812 = (Prims.parse_int "1"))))
in (match (uu____811) with
| true -> begin
(

let uu____813 = (

let uu____822 = (FStar_ST.read minimum_workable_fuel)
in (match (uu____822) with
| Some (f, errs1) -> begin
((f), (errs1))
end
| None -> begin
(

let uu____887 = (

let uu____891 = (FStar_Options.min_fuel ())
in ((uu____891), ((Prims.parse_int "1")), (rlimit)))
in ((uu____887), (errs)))
end))
in (match (uu____813) with
| (min_fuel1, potential_errors) -> begin
(

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref None)
in ((

let uu____945 = (with_fuel label_assumptions p1 min_fuel1)
in (FStar_SMTEncoding_Z3.ask None all_labels uu____945 None (fun r -> (FStar_ST.write res (Some (r))))));
(

let uu____970 = (FStar_ST.read res)
in (FStar_Option.get uu____970));
)))
in (

let uu____993 = (FStar_SMTEncoding_ErrorReporting.detail_errors env all_labels ask_z3)
in ((uu____993), (FStar_SMTEncoding_Z3.Default))))
end))
end
| uu____994 -> begin
(match (errs) with
| ([], FStar_SMTEncoding_Z3.Timeout) -> begin
(((((((""), (FStar_SMTEncoding_Term.Term_sort))), ("Timeout: Unknown assertion failed"), (FStar_Range.dummyRange)))::[]), ((Prims.snd errs)))
end
| ([], FStar_SMTEncoding_Z3.Default) -> begin
(((((((""), (FStar_SMTEncoding_Term.Term_sort))), ("Unknown assertion failed"), (FStar_Range.dummyRange)))::[]), ((Prims.snd errs)))
end
| (uu____1033, FStar_SMTEncoding_Z3.Kill) -> begin
(((((((""), (FStar_SMTEncoding_Term.Term_sort))), ("Killed: Unknown assertion failed"), (FStar_Range.dummyRange)))::[]), ((Prims.snd errs)))
end
| uu____1052 -> begin
errs
end)
end))
in ((record_hint None);
(

let uu____1055 = (FStar_Options.print_fuels ())
in (match (uu____1055) with
| true -> begin
(

let uu____1056 = (

let uu____1057 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range uu____1057))
in (

let uu____1058 = (

let uu____1059 = (FStar_Options.max_fuel ())
in (FStar_All.pipe_right uu____1059 FStar_Util.string_of_int))
in (

let uu____1060 = (

let uu____1061 = (FStar_Options.max_ifuel ())
in (FStar_All.pipe_right uu____1061 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" uu____1056 uu____1058 uu____1060))))
end
| uu____1062 -> begin
()
end));
(

let uu____1063 = (FStar_All.pipe_right (Prims.fst errs1) (FStar_List.map (fun uu____1075 -> (match (uu____1075) with
| (uu____1081, x, y) -> begin
((x), (y))
end))))
in (FStar_TypeChecker_Err.add_errors env uu____1063));
)))
in (

let use_errors = (fun errs result -> (match (((errs), (result))) with
| ((([], _), _)) | ((_, FStar_Util.Inl (_))) -> begin
result
end
| (uu____1109, FStar_Util.Inr (uu____1110)) -> begin
FStar_Util.Inr (errs)
end))
in (

let rec try_alt_configs = (fun prev_f p1 errs cfgs scope -> ((set_minimum_workable_fuel prev_f errs);
(match (((cfgs), ((Prims.snd errs)))) with
| (([], _)) | ((_, FStar_SMTEncoding_Z3.Kill)) -> begin
(report1 p1 errs)
end
| ((mi)::[], uu____1194) -> begin
(match (errs) with
| ([], uu____1208) -> begin
(

let uu____1210 = (with_fuel [] p1 mi)
in (FStar_SMTEncoding_Z3.ask None all_labels uu____1210 (Some (scope)) (cb false mi p1 [] scope)))
end
| uu____1216 -> begin
((set_minimum_workable_fuel prev_f errs);
(report1 p1 errs);
)
end)
end
| ((mi)::tl1, uu____1220) -> begin
(

let uu____1235 = (with_fuel [] p1 mi)
in (FStar_SMTEncoding_Z3.ask None all_labels uu____1235 (Some (scope)) (fun uu____1238 -> (match (uu____1238) with
| (result, elapsed_time) -> begin
(

let uu____1255 = (

let uu____1262 = (use_errors errs result)
in ((uu____1262), (elapsed_time)))
in (cb false mi p1 tl1 scope uu____1255))
end))))
end);
))
and cb = (fun used_hint uu____1264 p1 alt scope uu____1268 -> (match (((uu____1264), (uu____1268))) with
| ((prev_fuel, prev_ifuel, timeout), (result, elapsed_time)) -> begin
((match (used_hint) with
| true -> begin
((FStar_SMTEncoding_Z3.refresh ());
(

let uu____1315 = (FStar_TypeChecker_Env.get_range env)
in (record_hint_stat hint_opt result elapsed_time uu____1315));
)
end
| uu____1316 -> begin
()
end);
(

let uu____1318 = ((FStar_Options.z3_refresh ()) || (FStar_Options.print_z3_statistics ()))
in (match (uu____1318) with
| true -> begin
(FStar_SMTEncoding_Z3.refresh ())
end
| uu____1319 -> begin
()
end));
(

let query_info = (fun tag -> (

let uu____1324 = (

let uu____1326 = (

let uu____1327 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range uu____1327))
in (

let uu____1328 = (

let uu____1330 = (FStar_SMTEncoding_Z3.at_log_file ())
in (

let uu____1331 = (

let uu____1333 = (

let uu____1335 = (FStar_Util.string_of_int query_index)
in (

let uu____1336 = (

let uu____1338 = (

let uu____1340 = (

let uu____1342 = (FStar_Util.string_of_int elapsed_time)
in (

let uu____1343 = (

let uu____1345 = (FStar_Util.string_of_int prev_fuel)
in (

let uu____1346 = (

let uu____1348 = (FStar_Util.string_of_int prev_ifuel)
in (uu____1348)::[])
in (uu____1345)::uu____1346))
in (uu____1342)::uu____1343))
in ((match (used_hint) with
| true -> begin
" (with hint)"
end
| uu____1349 -> begin
""
end))::uu____1340)
in (tag)::uu____1338)
in (uu____1335)::uu____1336))
in (query_name)::uu____1333)
in (uu____1330)::uu____1331))
in (uu____1326)::uu____1328))
in (FStar_Util.print "(%s%s)\n\tQuery (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s\n" uu____1324)))
in (match (result) with
| FStar_Util.Inl (unsat_core1) -> begin
((match ((not (used_hint))) with
| true -> begin
(

let hint = {FStar_Util.hint_name = query_name; FStar_Util.hint_index = query_index; FStar_Util.fuel = prev_fuel; FStar_Util.ifuel = prev_ifuel; FStar_Util.unsat_core = unsat_core1; FStar_Util.query_elapsed_time = elapsed_time}
in (record_hint (Some (hint))))
end
| uu____1355 -> begin
(record_hint hint_opt)
end);
(

let uu____1356 = ((FStar_Options.print_fuels ()) || (FStar_Options.hint_info ()))
in (match (uu____1356) with
| true -> begin
(query_info "succeeded")
end
| uu____1357 -> begin
()
end));
)
end
| FStar_Util.Inr (errs) -> begin
((

let uu____1364 = ((FStar_Options.print_fuels ()) || (FStar_Options.hint_info ()))
in (match (uu____1364) with
| true -> begin
(query_info "failed")
end
| uu____1365 -> begin
()
end));
(try_alt_configs ((prev_fuel), (prev_ifuel), (timeout)) p1 errs alt scope);
)
end));
)
end))
in ((

let uu____1367 = ((FStar_Option.isSome unsat_core) || (FStar_Options.z3_refresh ()))
in (match (uu____1367) with
| true -> begin
(FStar_SMTEncoding_Z3.refresh ())
end
| uu____1369 -> begin
()
end));
(

let uu____1370 = (with_fuel [] p initial_config)
in (

let uu____1372 = (

let uu____1381 = (FStar_ST.read FStar_SMTEncoding_Z3.fresh_scope)
in (cb (FStar_Option.isSome unsat_core) initial_config p alt_configs uu____1381))
in (FStar_SMTEncoding_Z3.ask unsat_core all_labels uu____1370 None uu____1372)));
)))))
end))))))
in (

let process_query = (fun q -> (check q))
in (

let uu____1391 = (FStar_Options.admit_smt_queries ())
in (match (uu____1391) with
| true -> begin
()
end
| uu____1392 -> begin
(process_query query)
end)))))))
end));
))


let solve : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun use_env_msg tcenv q -> ((

let uu____1410 = (

let uu____1411 = (

let uu____1412 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____1412))
in (FStar_Util.format1 "Starting query at %s" uu____1411))
in (FStar_SMTEncoding_Encode.push uu____1410));
(

let tcenv1 = (FStar_TypeChecker_Env.incr_query_index tcenv)
in (

let uu____1414 = (FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv1 q)
in (match (uu____1414) with
| (prefix1, labels, qry, suffix) -> begin
(

let pop1 = (fun uu____1435 -> (

let uu____1436 = (

let uu____1437 = (

let uu____1438 = (FStar_TypeChecker_Env.get_range tcenv1)
in (FStar_All.pipe_left FStar_Range.string_of_range uu____1438))
in (FStar_Util.format1 "Ending query at %s" uu____1437))
in (FStar_SMTEncoding_Encode.pop uu____1436)))
in (match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.FalseOp, uu____1439); FStar_SMTEncoding_Term.freevars = uu____1440; FStar_SMTEncoding_Term.rng = uu____1441}, uu____1442, uu____1443) -> begin
(pop1 ())
end
| uu____1451 when tcenv1.FStar_TypeChecker_Env.admit -> begin
(pop1 ())
end
| FStar_SMTEncoding_Term.Assume (q1, uu____1454, uu____1455) -> begin
((ask_and_report_errors tcenv1 labels prefix1 qry suffix);
(pop1 ());
)
end
| uu____1457 -> begin
(failwith "Impossible")
end))
end)));
))


let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init; FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push; FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop; FStar_TypeChecker_Env.mark = FStar_SMTEncoding_Encode.mark; FStar_TypeChecker_Env.reset_mark = FStar_SMTEncoding_Encode.reset_mark; FStar_TypeChecker_Env.commit_mark = FStar_SMTEncoding_Encode.commit_mark; FStar_TypeChecker_Env.encode_modul = FStar_SMTEncoding_Encode.encode_modul; FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig; FStar_TypeChecker_Env.preprocess = (fun e g -> (((e), (g)))::[]); FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = FStar_SMTEncoding_Encode.is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}


let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun uu____1464 -> ()); FStar_TypeChecker_Env.push = (fun uu____1465 -> ()); FStar_TypeChecker_Env.pop = (fun uu____1466 -> ()); FStar_TypeChecker_Env.mark = (fun uu____1467 -> ()); FStar_TypeChecker_Env.reset_mark = (fun uu____1468 -> ()); FStar_TypeChecker_Env.commit_mark = (fun uu____1469 -> ()); FStar_TypeChecker_Env.encode_modul = (fun uu____1470 uu____1471 -> ()); FStar_TypeChecker_Env.encode_sig = (fun uu____1472 uu____1473 -> ()); FStar_TypeChecker_Env.preprocess = (fun e g -> (((e), (g)))::[]); FStar_TypeChecker_Env.solve = (fun uu____1480 uu____1481 uu____1482 -> ()); FStar_TypeChecker_Env.is_trivial = (fun uu____1486 uu____1487 -> false); FStar_TypeChecker_Env.finish = (fun uu____1488 -> ()); FStar_TypeChecker_Env.refresh = (fun uu____1489 -> ())}




