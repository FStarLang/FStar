
open Prims
type ('env, 'modul) interactive_tc =
{pop : 'env  ->  Prims.string  ->  Prims.unit; push : 'env  ->  Prims.bool  ->  Prims.bool  ->  Prims.string  ->  'env; mark : 'env  ->  'env; reset_mark : 'env  ->  'env; commit_mark : 'env  ->  'env; check_frag : 'env  ->  'modul  ->  FStar_Parser_ParseIt.input_frag  ->  ('modul * 'env * Prims.int) Prims.option; report_fail : Prims.unit  ->  Prims.unit; tc_prims : Prims.unit  ->  'env; tc_one_file : Prims.string Prims.list  ->  'env  ->  ((Prims.string Prims.option * Prims.string) * 'env * 'modul * Prims.string Prims.list); cleanup : 'env  ->  Prims.unit}

type input_chunks =
| Push of (Prims.bool * Prims.int * Prims.int)
| Pop of Prims.string
| Code of (Prims.string * (Prims.string * Prims.string))


let uu___is_Push : input_chunks  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Push (_0) -> begin
true
end
| uu____395 -> begin
false
end))


let __proj__Push__item___0 : input_chunks  ->  (Prims.bool * Prims.int * Prims.int) = (fun projectee -> (match (projectee) with
| Push (_0) -> begin
_0
end))


let uu___is_Pop : input_chunks  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Pop (_0) -> begin
true
end
| uu____416 -> begin
false
end))


let __proj__Pop__item___0 : input_chunks  ->  Prims.string = (fun projectee -> (match (projectee) with
| Pop (_0) -> begin
_0
end))


let uu___is_Code : input_chunks  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Code (_0) -> begin
true
end
| uu____432 -> begin
false
end))


let __proj__Code__item___0 : input_chunks  ->  (Prims.string * (Prims.string * Prims.string)) = (fun projectee -> (match (projectee) with
| Code (_0) -> begin
_0
end))


type ('env, 'modul) stack =
('env * 'modul) Prims.list

type interactive_state =
{chunk : FStar_Util.string_builder; stdin : FStar_Util.stream_reader Prims.option FStar_ST.ref; buffer : input_chunks Prims.list FStar_ST.ref; log : FStar_Util.file_handle Prims.option FStar_ST.ref}


let the_interactive_state : interactive_state = (let _0_678 = (FStar_Util.new_string_builder ())
in (let _0_677 = (FStar_Util.mk_ref None)
in (let _0_676 = (FStar_Util.mk_ref [])
in (let _0_675 = (FStar_Util.mk_ref None)
in {chunk = _0_678; stdin = _0_677; buffer = _0_676; log = _0_675}))))


let rec read_chunk : Prims.unit  ->  input_chunks = (fun uu____523 -> (

let s = the_interactive_state
in (

let log = (

let uu____528 = (FStar_Options.debug_any ())
in (match (uu____528) with
| true -> begin
(

let transcript = (

let uu____532 = (FStar_ST.read s.log)
in (match (uu____532) with
| Some (transcript) -> begin
transcript
end
| None -> begin
(

let transcript = (FStar_Util.open_file_for_writing "transcript")
in ((FStar_ST.write s.log (Some (transcript)));
transcript;
))
end))
in (fun line -> ((FStar_Util.append_to_file transcript line);
(FStar_Util.flush_file transcript);
)))
end
| uu____545 -> begin
(fun uu____546 -> ())
end))
in (

let stdin = (

let uu____548 = (FStar_ST.read s.stdin)
in (match (uu____548) with
| Some (i) -> begin
i
end
| None -> begin
(

let i = (FStar_Util.open_stdin ())
in ((FStar_ST.write s.stdin (Some (i)));
i;
))
end))
in (

let line = (

let uu____560 = (FStar_Util.read_line stdin)
in (match (uu____560) with
| None -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| Some (l) -> begin
l
end))
in ((log line);
(

let l = (FStar_Util.trim_string line)
in (match ((FStar_Util.starts_with l "#end")) with
| true -> begin
(

let responses = (match ((FStar_Util.split l " ")) with
| (uu____570)::(ok)::(fail)::[] -> begin
((ok), (fail))
end
| uu____573 -> begin
(("ok"), ("fail"))
end)
in (

let str = (FStar_Util.string_of_string_builder s.chunk)
in ((FStar_Util.clear_string_builder s.chunk);
Code (((str), (responses)));
)))
end
| uu____579 -> begin
(match ((FStar_Util.starts_with l "#pop")) with
| true -> begin
((FStar_Util.clear_string_builder s.chunk);
Pop (l);
)
end
| uu____581 -> begin
(match ((FStar_Util.starts_with l "#push")) with
| true -> begin
((FStar_Util.clear_string_builder s.chunk);
(

let lc_lax = (FStar_Util.trim_string (FStar_Util.substring_from l (FStar_String.length "#push")))
in (

let lc = (match ((FStar_Util.split lc_lax " ")) with
| (l)::(c)::("#lax")::[] -> begin
(let _0_680 = (FStar_Util.int_of_string l)
in (let _0_679 = (FStar_Util.int_of_string c)
in ((true), (_0_680), (_0_679))))
end
| (l)::(c)::[] -> begin
(let _0_682 = (FStar_Util.int_of_string l)
in (let _0_681 = (FStar_Util.int_of_string c)
in ((false), (_0_682), (_0_681))))
end
| uu____597 -> begin
((FStar_Util.print_warning (Prims.strcat "Error locations may be wrong, unrecognized string after #push: " lc_lax));
((false), ((Prims.parse_int "1")), ((Prims.parse_int "0")));
)
end)
in Push (lc)));
)
end
| uu____600 -> begin
(match ((l = "#finish")) with
| true -> begin
(FStar_All.exit (Prims.parse_int "0"))
end
| uu____601 -> begin
((FStar_Util.string_builder_append s.chunk line);
(FStar_Util.string_builder_append s.chunk "\n");
(read_chunk ());
)
end)
end)
end)
end));
))))))


let shift_chunk : Prims.unit  ->  input_chunks = (fun uu____606 -> (

let s = the_interactive_state
in (

let uu____608 = (FStar_ST.read s.buffer)
in (match (uu____608) with
| [] -> begin
(read_chunk ())
end
| (chunk)::chunks -> begin
((FStar_ST.write s.buffer chunks);
chunk;
)
end))))


let fill_buffer : Prims.unit  ->  Prims.unit = (fun uu____622 -> (

let s = the_interactive_state
in (let _0_686 = (let _0_685 = (FStar_ST.read s.buffer)
in (let _0_684 = (let _0_683 = (read_chunk ())
in (_0_683)::[])
in (FStar_List.append _0_685 _0_684)))
in (FStar_ST.write s.buffer _0_686))))


let deps_of_our_file : Prims.string  ->  (Prims.string Prims.list * Prims.string Prims.option) = (fun filename -> (

let deps = (FStar_Dependencies.find_deps_if_needed FStar_Parser_Dep.VerifyFigureItOut ((filename)::[]))
in (

let uu____639 = (FStar_List.partition (fun x -> (let _0_688 = (FStar_Parser_Dep.lowercase_module_name x)
in (let _0_687 = (FStar_Parser_Dep.lowercase_module_name filename)
in (_0_688 <> _0_687)))) deps)
in (match (uu____639) with
| (deps, same_name) -> begin
(

let maybe_intf = (match (same_name) with
| (intf)::(impl)::[] -> begin
((

let uu____661 = ((not ((FStar_Parser_Dep.is_interface intf))) || (not ((FStar_Parser_Dep.is_implementation impl))))
in (match (uu____661) with
| true -> begin
(FStar_Util.print_warning (FStar_Util.format2 "Found %s and %s but not an interface + implementation" intf impl))
end
| uu____662 -> begin
()
end));
Some (intf);
)
end
| (impl)::[] -> begin
None
end
| uu____664 -> begin
((FStar_Util.print_warning (FStar_Util.format1 "Unexpected: ended up with %s" (FStar_String.concat " " same_name)));
None;
)
end)
in ((deps), (maybe_intf)))
end))))


type m_timestamps =
(Prims.string Prims.option * Prims.string * FStar_Util.time Prims.option * FStar_Util.time) Prims.list


let rec tc_deps = (fun tc m stack env remaining ts -> (match (remaining) with
| [] -> begin
((stack), (env), (ts))
end
| uu____735 -> begin
(

let stack = (((env), (m)))::stack
in (

let env = (let _0_689 = (FStar_Options.lax ())
in (tc.push env _0_689 true "typecheck_modul"))
in (

let uu____748 = (tc.tc_one_file remaining env)
in (match (uu____748) with
| ((intf, impl), env, modl, remaining) -> begin
(

let uu____774 = (

let intf_t = (match (intf) with
| Some (intf) -> begin
Some ((FStar_Util.get_file_last_modification_time intf))
end
| None -> begin
None
end)
in (

let impl_t = (FStar_Util.get_file_last_modification_time impl)
in ((intf_t), (impl_t))))
in (match (uu____774) with
| (intf_t, impl_t) -> begin
(tc_deps tc m stack env remaining ((((intf), (impl), (intf_t), (impl_t)))::ts))
end))
end))))
end))


let update_deps = (fun filename tc m stk env ts -> (

let is_stale = (fun intf impl intf_t impl_t -> (

let impl_mt = (FStar_Util.get_file_last_modification_time impl)
in ((FStar_Util.is_before impl_t impl_mt) || (match (((intf), (intf_t))) with
| (Some (intf), Some (intf_t)) -> begin
(

let intf_mt = (FStar_Util.get_file_last_modification_time intf)
in (FStar_Util.is_before intf_t intf_mt))
end
| (None, None) -> begin
false
end
| (uu____879, uu____880) -> begin
(failwith "Impossible, if the interface is None, the timestamp entry should also be None")
end))))
in (

let rec iterate = (fun depnames st env' ts good_stack good_ts -> (

let match_dep = (fun depnames intf impl -> (match (intf) with
| None -> begin
(match (depnames) with
| (dep)::depnames' -> begin
(match ((dep = impl)) with
| true -> begin
((true), (depnames'))
end
| uu____960 -> begin
((false), (depnames))
end)
end
| uu____962 -> begin
((false), (depnames))
end)
end
| Some (intf) -> begin
(match (depnames) with
| (depintf)::(dep)::depnames' -> begin
(match (((depintf = intf) && (dep = impl))) with
| true -> begin
((true), (depnames'))
end
| uu____977 -> begin
((false), (depnames))
end)
end
| uu____979 -> begin
((false), (depnames))
end)
end))
in (

let rec pop_tc_and_stack = (fun env stack ts -> (match (ts) with
| [] -> begin
env
end
| (uu____1018)::ts -> begin
((tc.pop env "");
(

let uu____1040 = (let _0_691 = (FStar_List.hd stack)
in (let _0_690 = (FStar_List.tl stack)
in ((_0_691), (_0_690))))
in (match (uu____1040) with
| ((env, uu____1058), stack) -> begin
(pop_tc_and_stack env stack ts)
end));
)
end))
in (match (ts) with
| (ts_elt)::ts' -> begin
(

let uu____1094 = ts_elt
in (match (uu____1094) with
| (intf, impl, intf_t, impl_t) -> begin
(

let uu____1114 = (match_dep depnames intf impl)
in (match (uu____1114) with
| (b, depnames') -> begin
(

let uu____1127 = ((not (b)) || (is_stale intf impl intf_t impl_t))
in (match (uu____1127) with
| true -> begin
(

let env = (pop_tc_and_stack env' (FStar_List.rev_append st []) ts)
in (tc_deps tc m good_stack env depnames good_ts))
end
| uu____1146 -> begin
(

let uu____1147 = (let _0_693 = (FStar_List.hd st)
in (let _0_692 = (FStar_List.tl st)
in ((_0_693), (_0_692))))
in (match (uu____1147) with
| (stack_elt, st') -> begin
(iterate depnames' st' env' ts' ((stack_elt)::good_stack) ((ts_elt)::good_ts))
end))
end))
end))
end))
end
| [] -> begin
(tc_deps tc m good_stack env' depnames good_ts)
end))))
in (

let uu____1211 = (deps_of_our_file filename)
in (match (uu____1211) with
| (filenames, uu____1222) -> begin
(iterate filenames (FStar_List.rev_append stk []) env (FStar_List.rev_append ts []) [] [])
end)))))


let rec go = (fun line_col filename tc stack curmod env ts -> (

let uu____1310 = (shift_chunk ())
in (match (uu____1310) with
| Pop (msg) -> begin
((FStar_Util.print_string "Pop\n");
(tc.pop env msg);
(

let uu____1314 = (match (stack) with
| [] -> begin
((FStar_Util.print_error "too many pops");
(FStar_All.exit (Prims.parse_int "1"));
)
end
| (hd)::tl -> begin
((hd), (tl))
end)
in (match (uu____1314) with
| ((env, curmod), stack) -> begin
((match (((FStar_List.length stack) = (FStar_List.length ts))) with
| true -> begin
(tc.cleanup env)
end
| uu____1379 -> begin
()
end);
(go line_col filename tc stack curmod env ts);
)
end));
)
end
| Push (lax, l, c) -> begin
((FStar_Util.print_string "Push\n");
(

let uu____1384 = (match (((FStar_List.length stack) = (FStar_List.length ts))) with
| true -> begin
(let _0_694 = (update_deps filename tc curmod stack env ts)
in ((true), (_0_694)))
end
| uu____1424 -> begin
((false), (((stack), (env), (ts))))
end)
in (match (uu____1384) with
| (restore_cmd_line_options, (stack, env, ts)) -> begin
(

let stack = (((env), (curmod)))::stack
in (

let env = (tc.push env lax restore_cmd_line_options "#push")
in (go ((l), (c)) filename tc stack curmod env ts)))
end));
)
end
| Code (text, (ok, fail)) -> begin
((FStar_Util.print_string "Code\n");
(

let fail = (fun curmod env_mark -> ((tc.report_fail ());
(FStar_Util.print1 "%s\n" fail);
(

let env = (tc.reset_mark env_mark)
in (

let env = (tc.reset_mark env_mark)
in (

let env = (tc.reset_mark env_mark)
in (

let uu____1478 = (tc.mark env)
in (go line_col filename tc stack curmod env ts)))));
))
in (

let env_mark = (tc.mark env)
in (

let frag = {FStar_Parser_ParseIt.frag_text = text; FStar_Parser_ParseIt.frag_line = (Prims.fst line_col); FStar_Parser_ParseIt.frag_col = (Prims.snd line_col)}
in (

let res = (tc.check_frag env_mark curmod frag)
in (match (res) with
| Some (curmod, env, n_errs) -> begin
(match ((n_errs = (Prims.parse_int "0"))) with
| true -> begin
((FStar_Util.print1 "\n%s\n" ok);
(

let env = (tc.commit_mark env)
in (go line_col filename tc stack curmod env ts));
)
end
| uu____1502 -> begin
(fail curmod env_mark)
end)
end
| uu____1503 -> begin
(fail curmod env_mark)
end)))));
)
end)))


let interactive_mode = (fun filename initial_mod tc -> ((

let uu____1532 = (FStar_Option.isSome (FStar_Options.codegen ()))
in (match (uu____1532) with
| true -> begin
(FStar_Util.print_warning "code-generation is not supported in interactive mode, ignoring the codegen flag")
end
| uu____1533 -> begin
()
end));
(

let uu____1534 = (deps_of_our_file filename)
in (match (uu____1534) with
| (filenames, maybe_intf) -> begin
(

let env = (tc.tc_prims ())
in (

let uu____1546 = (tc_deps tc initial_mod [] env filenames [])
in (match (uu____1546) with
| (stack, env, ts) -> begin
(

let uu____1567 = (match (maybe_intf) with
| Some (intf) -> begin
(

let frag = (let _0_695 = (FStar_Util.file_get_contents intf)
in {FStar_Parser_ParseIt.frag_text = _0_695; FStar_Parser_ParseIt.frag_line = (Prims.parse_int "0"); FStar_Parser_ParseIt.frag_col = (Prims.parse_int "0")})
in (

let uu____1574 = (tc.check_frag env initial_mod frag)
in (match (uu____1574) with
| Some (curmod, env, n_errs) -> begin
((match ((n_errs <> (Prims.parse_int "0"))) with
| true -> begin
((FStar_Util.print_warning (FStar_Util.format1 "Found the interface %s but it has errors!" intf));
(FStar_All.exit (Prims.parse_int "1"));
)
end
| uu____1589 -> begin
()
end);
(FStar_Util.print_string "Reminder: fst+fsti in interactive mode is unsound.\n");
((curmod), (env));
)
end
| None -> begin
((FStar_Util.print_warning (FStar_Util.format1 "Found the interface %s but could not parse it first!" intf));
(FStar_All.exit (Prims.parse_int "1"));
)
end)))
end
| None -> begin
((initial_mod), (env))
end)
in (match (uu____1567) with
| (initial_mod, env) -> begin
(

let uu____1599 = ((FStar_Options.record_hints ()) || (FStar_Options.use_hints ()))
in (match (uu____1599) with
| true -> begin
(let _0_696 = (FStar_List.hd (FStar_Options.file_list ()))
in (FStar_SMTEncoding_Solver.with_hints_db _0_696 (fun uu____1600 -> (go (((Prims.parse_int "1")), ((Prims.parse_int "0"))) filename tc stack initial_mod env ts))))
end
| uu____1605 -> begin
(go (((Prims.parse_int "1")), ((Prims.parse_int "0"))) filename tc stack initial_mod env ts)
end))
end))
end)))
end));
))




