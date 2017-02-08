
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

let hints = (FStar_Option.get (FStar_ST.read recorded_hints))
in (

let hints_db = (let _0_330 = (FStar_Util.digest_of_file src_filename)
in {FStar_Util.module_digest = _0_330; FStar_Util.hints = hints})
in (

let hints_file_name = (format_hints_file_name src_filename)
in (FStar_Util.write_hints hints_file_name hints_db))))
end
| uu____138 -> begin
()
end));
(

let uu____140 = (FStar_Options.hint_info ())
in (match (uu____140) with
| true -> begin
(

let stats = (let _0_331 = (FStar_ST.read hint_stats)
in (FStar_All.pipe_right _0_331 FStar_List.rev))
in (FStar_All.pipe_right stats (FStar_List.iter (fun s -> (match (s.replay_result) with
| FStar_Util.Inl (_unsat_core) -> begin
(let _0_333 = (FStar_Range.string_of_range s.source_location)
in (let _0_332 = (FStar_Util.string_of_int s.elapsed_time)
in (FStar_Util.print2 "Hint-info (%s): Replay succeeded in %s milliseconds\n" _0_333 _0_332)))
end
| FStar_Util.Inr (_error) -> begin
(let _0_335 = (FStar_Range.string_of_range s.source_location)
in (let _0_334 = (FStar_Util.string_of_int s.elapsed_time)
in (FStar_Util.print2 "Hint-info (%s): Replay failed in %s milliseconds\n" _0_335 _0_334)))
end)))))
end
| uu____152 -> begin
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

let uu____191 = (FStar_ST.read replaying_hints)
in (match (uu____191) with
| Some (hints) -> begin
(FStar_Util.find_map hints (fun uu___89_199 -> (match (uu___89_199) with
| Some (hint) when ((hint.FStar_Util.hint_name = qname) && (hint.FStar_Util.hint_index = qindex)) -> begin
Some (hint)
end
| uu____203 -> begin
None
end)))
end
| uu____205 -> begin
None
end)))


let record_hint : FStar_Util.hint Prims.option  ->  Prims.unit = (fun hint -> (

let hint = (match (hint) with
| None -> begin
None
end
| Some (h) -> begin
Some ((

let uu___91_216 = h
in {FStar_Util.hint_name = uu___91_216.FStar_Util.hint_name; FStar_Util.hint_index = uu___91_216.FStar_Util.hint_index; FStar_Util.fuel = uu___91_216.FStar_Util.fuel; FStar_Util.ifuel = uu___91_216.FStar_Util.ifuel; FStar_Util.unsat_core = uu___91_216.FStar_Util.unsat_core; FStar_Util.query_elapsed_time = (Prims.parse_int "0")}))
end)
in (

let uu____217 = (FStar_ST.read recorded_hints)
in (match (uu____217) with
| Some (l) -> begin
(FStar_ST.write recorded_hints (Some ((FStar_List.append l ((hint)::[])))))
end
| uu____231 -> begin
()
end))))


let record_hint_stat : FStar_Util.hint Prims.option  ->  z3_result  ->  Prims.int  ->  FStar_Range.range  ->  Prims.unit = (fun h res time r -> (

let s = {hint = h; replay_result = (z3_result_as_replay_result res); elapsed_time = time; source_location = r}
in (let _0_337 = (let _0_336 = (FStar_ST.read hint_stats)
in (s)::_0_336)
in (FStar_ST.write hint_stats _0_337))))


let ask_and_report_errors : FStar_TypeChecker_Env.env  ->  ((FStar_SMTEncoding_Z3.label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun env all_labels prefix query suffix -> ((FStar_SMTEncoding_Z3.giveZ3 prefix);
(

let uu____286 = (match (env.FStar_TypeChecker_Env.qname_and_index) with
| None -> begin
(failwith "No query name set!")
end
| Some (q, n) -> begin
(((FStar_Ident.text_of_lid q)), (n))
end)
in (match (uu____286) with
| (query_name, query_index) -> begin
(

let minimum_workable_fuel = (FStar_Util.mk_ref None)
in (

let set_minimum_workable_fuel = (fun f uu___90_342 -> (match (uu___90_342) with
| ([], uu____349) -> begin
()
end
| errs -> begin
(

let uu____355 = (FStar_ST.read minimum_workable_fuel)
in (match (uu____355) with
| Some (uu____376) -> begin
()
end
| None -> begin
(FStar_ST.write minimum_workable_fuel (Some (((f), (errs)))))
end))
end))
in (

let with_fuel = (fun label_assumptions p uu____440 -> (match (uu____440) with
| (n, i, rlimit) -> begin
(let _0_359 = (let _0_350 = FStar_SMTEncoding_Term.Caption ((let _0_339 = (FStar_Util.string_of_int n)
in (let _0_338 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _0_339 _0_338))))
in (let _0_349 = (let _0_348 = FStar_SMTEncoding_Term.Assume ((let _0_342 = (FStar_SMTEncoding_Util.mkEq (let _0_341 = (FStar_SMTEncoding_Util.mkApp (("MaxFuel"), ([])))
in (let _0_340 = (FStar_SMTEncoding_Term.n_fuel n)
in ((_0_341), (_0_340)))))
in ((_0_342), (None), (None))))
in (let _0_347 = (let _0_346 = FStar_SMTEncoding_Term.Assume ((let _0_345 = (FStar_SMTEncoding_Util.mkEq (let _0_344 = (FStar_SMTEncoding_Util.mkApp (("MaxIFuel"), ([])))
in (let _0_343 = (FStar_SMTEncoding_Term.n_fuel i)
in ((_0_344), (_0_343)))))
in ((_0_345), (None), (None))))
in (_0_346)::(p)::[])
in (_0_348)::_0_347))
in (_0_350)::_0_349))
in (let _0_358 = (let _0_357 = (let _0_356 = (let _0_352 = FStar_SMTEncoding_Term.SetOption ((let _0_351 = (FStar_Util.string_of_int rlimit)
in (("rlimit"), (_0_351))))
in (_0_352)::[])
in (let _0_355 = (let _0_354 = (let _0_353 = (

let uu____455 = (FStar_Options.record_hints ())
in (match (uu____455) with
| true -> begin
(FStar_SMTEncoding_Term.GetUnsatCore)::[]
end
| uu____457 -> begin
[]
end))
in (FStar_List.append _0_353 suffix))
in (FStar_List.append ((FStar_SMTEncoding_Term.CheckSat)::[]) _0_354))
in (FStar_List.append _0_356 _0_355)))
in (FStar_List.append label_assumptions _0_357))
in (FStar_List.append _0_359 _0_358)))
end))
in (

let check = (fun p -> (

let rlimit = (let _0_360 = (FStar_Options.z3_rlimit ())
in (_0_360 * (Prims.parse_int "544656")))
in (

let default_initial_config = (let _0_362 = (FStar_Options.initial_fuel ())
in (let _0_361 = (FStar_Options.initial_ifuel ())
in ((_0_362), (_0_361), (rlimit))))
in (

let hint_opt = (next_hint query_name query_index)
in (

let uu____469 = (match (hint_opt) with
| None -> begin
((None), (default_initial_config))
end
| Some (hint) -> begin
(

let uu____491 = (match ((FStar_Option.isSome hint.FStar_Util.unsat_core)) with
| true -> begin
((hint.FStar_Util.unsat_core), (rlimit))
end
| uu____503 -> begin
((None), (((Prims.parse_int "60") * (Prims.parse_int "544656"))))
end)
in (match (uu____491) with
| (core, timeout) -> begin
((core), (((hint.FStar_Util.fuel), (hint.FStar_Util.ifuel), (timeout))))
end))
end)
in (match (uu____469) with
| (unsat_core, initial_config) -> begin
(

let alt_configs = (FStar_List.flatten (let _0_393 = (let _0_392 = (

let uu____571 = (let _0_364 = (FStar_Options.max_ifuel ())
in (let _0_363 = (FStar_Options.initial_ifuel ())
in (_0_364 > _0_363)))
in (match (uu____571) with
| true -> begin
(let _0_367 = (let _0_366 = (FStar_Options.initial_fuel ())
in (let _0_365 = (FStar_Options.max_ifuel ())
in ((_0_366), (_0_365), (rlimit))))
in (_0_367)::[])
end
| uu____582 -> begin
[]
end))
in (let _0_391 = (let _0_390 = (

let uu____590 = (let _0_370 = (let _0_368 = (FStar_Options.max_fuel ())
in (_0_368 / (Prims.parse_int "2")))
in (let _0_369 = (FStar_Options.initial_fuel ())
in (_0_370 > _0_369)))
in (match (uu____590) with
| true -> begin
(let _0_374 = (let _0_373 = (let _0_371 = (FStar_Options.max_fuel ())
in (_0_371 / (Prims.parse_int "2")))
in (let _0_372 = (FStar_Options.max_ifuel ())
in ((_0_373), (_0_372), (rlimit))))
in (_0_374)::[])
end
| uu____601 -> begin
[]
end))
in (let _0_389 = (let _0_388 = (

let uu____609 = ((let _0_376 = (FStar_Options.max_fuel ())
in (let _0_375 = (FStar_Options.initial_fuel ())
in (_0_376 > _0_375))) && (let _0_378 = (FStar_Options.max_ifuel ())
in (let _0_377 = (FStar_Options.initial_ifuel ())
in (_0_378 > _0_377))))
in (match (uu____609) with
| true -> begin
(let _0_381 = (let _0_380 = (FStar_Options.max_fuel ())
in (let _0_379 = (FStar_Options.max_ifuel ())
in ((_0_380), (_0_379), (rlimit))))
in (_0_381)::[])
end
| uu____620 -> begin
[]
end))
in (let _0_387 = (let _0_386 = (

let uu____628 = (let _0_383 = (FStar_Options.min_fuel ())
in (let _0_382 = (FStar_Options.initial_fuel ())
in (_0_383 < _0_382)))
in (match (uu____628) with
| true -> begin
(let _0_385 = (let _0_384 = (FStar_Options.min_fuel ())
in ((_0_384), ((Prims.parse_int "1")), (rlimit)))
in (_0_385)::[])
end
| uu____639 -> begin
[]
end))
in (_0_386)::[])
in (_0_388)::_0_387))
in (_0_390)::_0_389))
in (_0_392)::_0_391))
in ((match (((default_initial_config <> initial_config) || (FStar_Option.isSome unsat_core))) with
| true -> begin
(default_initial_config)::[]
end
| uu____563 -> begin
[]
end))::_0_393))
in (

let report = (fun p errs -> (

let errs = (

let uu____655 = ((FStar_Options.detail_errors ()) && (let _0_394 = (FStar_Options.n_cores ())
in (_0_394 = (Prims.parse_int "1"))))
in (match (uu____655) with
| true -> begin
(

let uu____656 = (

let uu____665 = (FStar_ST.read minimum_workable_fuel)
in (match (uu____665) with
| Some (f, errs) -> begin
((f), (errs))
end
| None -> begin
(let _0_396 = (let _0_395 = (FStar_Options.min_fuel ())
in ((_0_395), ((Prims.parse_int "1")), (rlimit)))
in ((_0_396), (errs)))
end))
in (match (uu____656) with
| (min_fuel, potential_errors) -> begin
(

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref None)
in ((let _0_397 = (with_fuel label_assumptions p min_fuel)
in (FStar_SMTEncoding_Z3.ask None all_labels _0_397 (fun r -> (FStar_ST.write res (Some (r))))));
(FStar_Option.get (FStar_ST.read res));
)))
in (let _0_398 = (FStar_SMTEncoding_ErrorReporting.detail_errors env all_labels ask_z3)
in ((_0_398), (FStar_SMTEncoding_Z3.Default))))
end))
end
| uu____821 -> begin
(match (errs) with
| ([], FStar_SMTEncoding_Z3.Timeout) -> begin
(((((((""), (FStar_SMTEncoding_Term.Term_sort))), ("Timeout: Unknown assertion failed"), (FStar_Range.dummyRange)))::[]), ((Prims.snd errs)))
end
| ([], FStar_SMTEncoding_Z3.Default) -> begin
(((((((""), (FStar_SMTEncoding_Term.Term_sort))), ("Unknown assertion failed"), (FStar_Range.dummyRange)))::[]), ((Prims.snd errs)))
end
| (uu____860, FStar_SMTEncoding_Z3.Kill) -> begin
(((((((""), (FStar_SMTEncoding_Term.Term_sort))), ("Killed: Unknown assertion failed"), (FStar_Range.dummyRange)))::[]), ((Prims.snd errs)))
end
| uu____879 -> begin
errs
end)
end))
in ((record_hint None);
(

let uu____882 = (FStar_Options.print_fuels ())
in (match (uu____882) with
| true -> begin
(let _0_403 = (FStar_Range.string_of_range (FStar_TypeChecker_Env.get_range env))
in (let _0_402 = (let _0_399 = (FStar_Options.max_fuel ())
in (FStar_All.pipe_right _0_399 FStar_Util.string_of_int))
in (let _0_401 = (let _0_400 = (FStar_Options.max_ifuel ())
in (FStar_All.pipe_right _0_400 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _0_403 _0_402 _0_401))))
end
| uu____883 -> begin
()
end));
(let _0_404 = (FStar_All.pipe_right (Prims.fst errs) (FStar_List.map (fun uu____892 -> (match (uu____892) with
| (uu____898, x, y) -> begin
((x), (y))
end))))
in (FStar_TypeChecker_Err.add_errors env _0_404));
)))
in (

let use_errors = (fun errs result -> (match (((errs), (result))) with
| ((([], _), _)) | ((_, FStar_Util.Inl (_))) -> begin
result
end
| (uu____926, FStar_Util.Inr (uu____927)) -> begin
FStar_Util.Inr (errs)
end))
in (

let rec try_alt_configs = (fun prev_f p errs cfgs -> ((set_minimum_workable_fuel prev_f errs);
(match (((cfgs), ((Prims.snd errs)))) with
| (([], _)) | ((_, FStar_SMTEncoding_Z3.Kill)) -> begin
(report p errs)
end
| ((mi)::[], uu____1006) -> begin
(match (errs) with
| ([], uu____1020) -> begin
(let _0_405 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask None all_labels _0_405 (cb false mi p [])))
end
| uu____1026 -> begin
((set_minimum_workable_fuel prev_f errs);
(report p errs);
)
end)
end
| ((mi)::tl, uu____1030) -> begin
(let _0_408 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask None all_labels _0_408 (fun uu____1046 -> (match (uu____1046) with
| (result, elapsed_time) -> begin
(let _0_407 = (let _0_406 = (use_errors errs result)
in ((_0_406), (elapsed_time)))
in (cb false mi p tl _0_407))
end))))
end);
))
and cb = (fun used_hint uu____1064 p alt uu____1067 -> (match (((uu____1064), (uu____1067))) with
| ((prev_fuel, prev_ifuel, timeout), (result, elapsed_time)) -> begin
((match (used_hint) with
| true -> begin
((FStar_SMTEncoding_Z3.refresh ());
(let _0_409 = (FStar_TypeChecker_Env.get_range env)
in (record_hint_stat hint_opt result elapsed_time _0_409));
)
end
| uu____1114 -> begin
()
end);
(

let uu____1116 = ((FStar_Options.z3_refresh ()) || (FStar_Options.print_z3_statistics ()))
in (match (uu____1116) with
| true -> begin
(FStar_SMTEncoding_Z3.refresh ())
end
| uu____1117 -> begin
()
end));
(

let query_info = (fun tag -> (let _0_424 = (let _0_423 = (FStar_Range.string_of_range (FStar_TypeChecker_Env.get_range env))
in (let _0_422 = (let _0_421 = (FStar_SMTEncoding_Z3.at_log_file ())
in (let _0_420 = (let _0_419 = (let _0_418 = (FStar_Util.string_of_int query_index)
in (let _0_417 = (let _0_416 = (let _0_415 = (let _0_414 = (FStar_Util.string_of_int elapsed_time)
in (let _0_413 = (let _0_412 = (FStar_Util.string_of_int prev_fuel)
in (let _0_411 = (let _0_410 = (FStar_Util.string_of_int prev_ifuel)
in (_0_410)::[])
in (_0_412)::_0_411))
in (_0_414)::_0_413))
in ((match (used_hint) with
| true -> begin
" (with hint)"
end
| uu____1122 -> begin
""
end))::_0_415)
in (tag)::_0_416)
in (_0_418)::_0_417))
in (query_name)::_0_419)
in (_0_421)::_0_420))
in (_0_423)::_0_422))
in (FStar_Util.print "(%s%s)\n\tQuery (%s, %s)\t%s%s in %s milliseconds with fuel %s and ifuel %s\n" _0_424)))
in (match (result) with
| FStar_Util.Inl (unsat_core) -> begin
((match ((not (used_hint))) with
| true -> begin
(

let hint = {FStar_Util.hint_name = query_name; FStar_Util.hint_index = query_index; FStar_Util.fuel = prev_fuel; FStar_Util.ifuel = prev_ifuel; FStar_Util.unsat_core = unsat_core; FStar_Util.query_elapsed_time = elapsed_time}
in (record_hint (Some (hint))))
end
| uu____1128 -> begin
(record_hint hint_opt)
end);
(

let uu____1129 = ((FStar_Options.print_fuels ()) || (FStar_Options.hint_info ()))
in (match (uu____1129) with
| true -> begin
(query_info "succeeded")
end
| uu____1130 -> begin
()
end));
)
end
| FStar_Util.Inr (errs) -> begin
((

let uu____1137 = ((FStar_Options.print_fuels ()) || (FStar_Options.hint_info ()))
in (match (uu____1137) with
| true -> begin
(query_info "failed")
end
| uu____1138 -> begin
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
| uu____1141 -> begin
()
end);
(let _0_425 = (with_fuel [] p initial_config)
in (FStar_SMTEncoding_Z3.ask unsat_core all_labels _0_425 (cb (FStar_Option.isSome unsat_core) initial_config p alt_configs)));
)))))
end))))))
in (

let process_query = (fun q -> (

let uu____1147 = (let _0_426 = (FStar_Options.split_cases ())
in (_0_426 > (Prims.parse_int "0")))
in (match (uu____1147) with
| true -> begin
(

let uu____1148 = (let _0_427 = (FStar_Options.split_cases ())
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _0_427 q))
in (match (uu____1148) with
| (b, cb) -> begin
(match (b) with
| true -> begin
(FStar_SMTEncoding_SplitQueryCases.handle_query cb check)
end
| uu____1171 -> begin
(check q)
end)
end))
end
| uu____1172 -> begin
(check q)
end)))
in (

let uu____1173 = (FStar_Options.admit_smt_queries ())
in (match (uu____1173) with
| true -> begin
()
end
| uu____1174 -> begin
(process_query query)
end)))))))
end));
))


let solve : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  Prims.unit = (fun use_env_msg tcenv q -> ((FStar_SMTEncoding_Encode.push (let _0_429 = (let _0_428 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _0_428))
in (FStar_Util.format1 "Starting query at %s" _0_429)));
(

let tcenv = (FStar_TypeChecker_Env.incr_query_index tcenv)
in (

let uu____1193 = (FStar_SMTEncoding_Encode.encode_query use_env_msg tcenv q)
in (match (uu____1193) with
| (prefix, labels, qry, suffix) -> begin
(

let pop = (fun uu____1214 -> (FStar_SMTEncoding_Encode.pop (let _0_431 = (let _0_430 = (FStar_TypeChecker_Env.get_range tcenv)
in (FStar_All.pipe_left FStar_Range.string_of_range _0_430))
in (FStar_Util.format1 "Ending query at %s" _0_431))))
in (match (qry) with
| FStar_SMTEncoding_Term.Assume ({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.FalseOp, uu____1215); FStar_SMTEncoding_Term.freevars = uu____1216; FStar_SMTEncoding_Term.rng = uu____1217}, uu____1218, uu____1219) -> begin
(pop ())
end
| uu____1229 when tcenv.FStar_TypeChecker_Env.admit -> begin
(pop ())
end
| FStar_SMTEncoding_Term.Assume (q, uu____1232, uu____1233) -> begin
((ask_and_report_errors tcenv labels prefix qry suffix);
(pop ());
)
end
| uu____1237 -> begin
(failwith "Impossible")
end))
end)));
))


let solver : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = FStar_SMTEncoding_Encode.init; FStar_TypeChecker_Env.push = FStar_SMTEncoding_Encode.push; FStar_TypeChecker_Env.pop = FStar_SMTEncoding_Encode.pop; FStar_TypeChecker_Env.mark = FStar_SMTEncoding_Encode.mark; FStar_TypeChecker_Env.reset_mark = FStar_SMTEncoding_Encode.reset_mark; FStar_TypeChecker_Env.commit_mark = FStar_SMTEncoding_Encode.commit_mark; FStar_TypeChecker_Env.encode_modul = FStar_SMTEncoding_Encode.encode_modul; FStar_TypeChecker_Env.encode_sig = FStar_SMTEncoding_Encode.encode_sig; FStar_TypeChecker_Env.solve = solve; FStar_TypeChecker_Env.is_trivial = FStar_SMTEncoding_Encode.is_trivial; FStar_TypeChecker_Env.finish = FStar_SMTEncoding_Z3.finish; FStar_TypeChecker_Env.refresh = FStar_SMTEncoding_Z3.refresh}


let dummy : FStar_TypeChecker_Env.solver_t = {FStar_TypeChecker_Env.init = (fun uu____1238 -> ()); FStar_TypeChecker_Env.push = (fun uu____1239 -> ()); FStar_TypeChecker_Env.pop = (fun uu____1240 -> ()); FStar_TypeChecker_Env.mark = (fun uu____1241 -> ()); FStar_TypeChecker_Env.reset_mark = (fun uu____1242 -> ()); FStar_TypeChecker_Env.commit_mark = (fun uu____1243 -> ()); FStar_TypeChecker_Env.encode_modul = (fun uu____1244 uu____1245 -> ()); FStar_TypeChecker_Env.encode_sig = (fun uu____1246 uu____1247 -> ()); FStar_TypeChecker_Env.solve = (fun uu____1248 uu____1249 uu____1250 -> ()); FStar_TypeChecker_Env.is_trivial = (fun uu____1254 uu____1255 -> false); FStar_TypeChecker_Env.finish = (fun uu____1256 -> ()); FStar_TypeChecker_Env.refresh = (fun uu____1257 -> ())}




