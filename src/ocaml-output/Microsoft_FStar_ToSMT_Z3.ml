
type z3version =
| Z3V_Unknown
| Z3V of (int * int * int)

let is_Z3V_Unknown = (fun ( _discr_ ) -> (match (_discr_) with
| Z3V_Unknown -> begin
true
end
| _ -> begin
false
end))

let is_Z3V = (fun ( _discr_ ) -> (match (_discr_) with
| Z3V (_) -> begin
true
end
| _ -> begin
false
end))

let z3v_compare = (fun ( known ) ( _48_8 ) -> (match (_48_8) with
| (w1, w2, w3) -> begin
(match (known) with
| Z3V_Unknown -> begin
None
end
| Z3V ((k1, k2, k3)) -> begin
Some ((match ((k1 <> w1)) with
| true -> begin
(w1 - k1)
end
| false -> begin
(match ((k2 <> w2)) with
| true -> begin
(w2 - k2)
end
| false -> begin
(w3 - k3)
end)
end))
end)
end))

let z3v_le = (fun ( known ) ( wanted ) -> (match ((z3v_compare known wanted)) with
| None -> begin
false
end
| Some (i) -> begin
(i >= 0)
end))

let _z3version = (Support.Microsoft.FStar.Util.mk_ref None)

let get_z3version = (fun ( _48_20 ) -> (match (()) with
| () -> begin
(let prefix = "Z3 version "
in (match ((Support.ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(let _48_30 = (let _68_20881 = (Support.ST.read Microsoft_FStar_Options.z3_exe)
in (Support.Microsoft.FStar.Util.run_proc _68_20881 "-version" ""))
in (match (_48_30) with
| (_48_26, out, _48_29) -> begin
(let out = (match ((Support.Microsoft.FStar.Util.splitlines out)) with
| x::_48_32 when (Support.Microsoft.FStar.Util.starts_with x prefix) -> begin
(let x = (let _68_20882 = (Support.Microsoft.FStar.Util.substring_from x (Support.String.length prefix))
in (Support.Microsoft.FStar.Util.trim_string _68_20882))
in (let x = (Support.Prims.try_with (fun ( _48_37 ) -> (match (()) with
| () -> begin
(Support.List.map Support.Microsoft.FStar.Util.int_of_string (Support.Microsoft.FStar.Util.split x "."))
end)) (fun ( _48_36 ) -> (match (_48_36) with
| _48_40 -> begin
[]
end)))
in (match (x) with
| i1::i2::i3::[] -> begin
Z3V ((i1, i2, i3))
end
| _48_49 -> begin
Z3V_Unknown
end)))
end
| _48_51 -> begin
Z3V_Unknown
end)
in (let _48_53 = (Support.ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))

let ini_params = (fun ( _48_55 ) -> (match (()) with
| () -> begin
(let t = (match ((let _68_20887 = (get_z3version ())
in (z3v_le _68_20887 (4, 3, 1)))) with
| true -> begin
(Support.ST.read Microsoft_FStar_Options.z3timeout)
end
| false -> begin
((Support.ST.read Microsoft_FStar_Options.z3timeout) * 1000)
end)
in (let timeout = (let _68_20888 = (Support.Microsoft.FStar.Util.string_of_int t)
in (Support.Microsoft.FStar.Util.format1 "-t:%s" _68_20888))
in (let relevancy = (match ((let _68_20889 = (get_z3version ())
in (z3v_le _68_20889 (4, 3, 1)))) with
| true -> begin
"RELEVANCY"
end
| false -> begin
"SMT.RELEVANCY"
end)
in (Support.Microsoft.FStar.Util.format2 "-smt2 -in %s AUTO_CONFIG=false MODEL=true %s=2" timeout relevancy))))
end))

type z3status =
| SAT
| UNSAT
| UNKNOWN
| TIMEOUT

let is_SAT = (fun ( _discr_ ) -> (match (_discr_) with
| SAT -> begin
true
end
| _ -> begin
false
end))

let is_UNSAT = (fun ( _discr_ ) -> (match (_discr_) with
| UNSAT -> begin
true
end
| _ -> begin
false
end))

let is_UNKNOWN = (fun ( _discr_ ) -> (match (_discr_) with
| UNKNOWN -> begin
true
end
| _ -> begin
false
end))

let is_TIMEOUT = (fun ( _discr_ ) -> (match (_discr_) with
| TIMEOUT -> begin
true
end
| _ -> begin
false
end))

let status_to_string = (fun ( _48_1 ) -> (match (_48_1) with
| SAT -> begin
"sat"
end
| UNSAT -> begin
"unsat"
end
| UNKNOWN -> begin
"unknown"
end
| TIMEOUT -> begin
"timeout"
end))

let tid = (fun ( _48_64 ) -> (match (()) with
| () -> begin
(let _68_20898 = (Support.Microsoft.FStar.Util.current_tid ())
in (Support.Prims.pipe_right _68_20898 Support.Microsoft.FStar.Util.string_of_int))
end))

let new_z3proc = (fun ( id ) -> (let cond = (fun ( pid ) ( s ) -> (let x = ((Support.Microsoft.FStar.Util.trim_string s) = "Done!")
in x))
in (let _68_20906 = (Support.ST.read Microsoft_FStar_Options.z3_exe)
in (let _68_20905 = (ini_params ())
in (Support.Microsoft.FStar.Util.start_process id _68_20906 _68_20905 cond)))))

type bgproc =
{grab : unit  ->  Support.Microsoft.FStar.Util.proc; release : unit  ->  unit; refresh : unit  ->  unit}

let is_Mkbgproc = (fun ( _ ) -> (failwith ("Not yet implemented:is_Mkbgproc")))

let queries_dot_smt2 = (Support.Microsoft.FStar.Util.mk_ref None)

let get_qfile = (let ctr = (Support.Microsoft.FStar.Util.mk_ref 0)
in (fun ( fresh ) -> (match (fresh) with
| true -> begin
(let _48_76 = (Support.Microsoft.FStar.Util.incr ctr)
in (let _68_20939 = (let _68_20938 = (let _68_20937 = (Support.ST.read ctr)
in (Support.Microsoft.FStar.Util.string_of_int _68_20937))
in (Support.Microsoft.FStar.Util.format1 "queries-%s.smt2" _68_20938))
in (Support.Microsoft.FStar.Util.open_file_for_writing _68_20939)))
end
| false -> begin
(match ((Support.ST.read queries_dot_smt2)) with
| None -> begin
(let fh = (Support.Microsoft.FStar.Util.open_file_for_writing "queries-bg-0.smt2")
in (let _48_80 = (Support.ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
in fh))
end
| Some (fh) -> begin
fh
end)
end)))

let log_query = (fun ( fresh ) ( i ) -> (let fh = (get_qfile fresh)
in (let _48_87 = (Support.Microsoft.FStar.Util.append_to_file fh i)
in (match (fresh) with
| true -> begin
(Support.Microsoft.FStar.Util.close_file fh)
end
| false -> begin
()
end))))

let bg_z3_proc = (let ctr = (Support.Microsoft.FStar.Util.mk_ref (- (1)))
in (let new_proc = (fun ( _48_91 ) -> (match (()) with
| () -> begin
(let _68_20948 = (let _68_20947 = (let _48_92 = (Support.Microsoft.FStar.Util.incr ctr)
in (let _68_20946 = (Support.ST.read ctr)
in (Support.Prims.pipe_right _68_20946 Support.Microsoft.FStar.Util.string_of_int)))
in (Support.Microsoft.FStar.Util.format1 "bg-%s" _68_20947))
in (new_z3proc _68_20948))
end))
in (let z3proc = (let _68_20949 = (new_proc ())
in (Support.Microsoft.FStar.Util.mk_ref _68_20949))
in (let x = []
in (let grab = (fun ( _48_97 ) -> (match (()) with
| () -> begin
(let _48_98 = (Support.Microsoft.FStar.Util.monitor_enter x)
in (Support.ST.read z3proc))
end))
in (let release = (fun ( _48_101 ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.monitor_exit x)
end))
in (let refresh = (fun ( _48_103 ) -> (match (()) with
| () -> begin
(let proc = (grab ())
in (let _48_105 = (Support.Microsoft.FStar.Util.kill_process proc)
in (let _48_107 = (let _68_20956 = (new_proc ())
in (Support.ST.op_Colon_Equals z3proc _68_20956))
in (let _48_115 = (match ((Support.ST.read queries_dot_smt2)) with
| None -> begin
()
end
| Some (fh) -> begin
(let _48_112 = (Support.Microsoft.FStar.Util.close_file fh)
in (let fh = (let _68_20959 = (let _68_20958 = (let _68_20957 = (Support.ST.read ctr)
in (Support.Prims.pipe_right _68_20957 Support.Microsoft.FStar.Util.string_of_int))
in (Support.Microsoft.FStar.Util.format1 "queries-bg-%s.smt2" _68_20958))
in (Support.Microsoft.FStar.Util.open_file_for_writing _68_20959))
in (Support.ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))))
end)
in (release ())))))
end))
in {grab = grab; release = release; refresh = refresh})))))))

let doZ3Exe' = (fun ( input ) ( z3proc ) -> (let parse = (fun ( z3out ) -> (let lines = (Support.Prims.pipe_right (Support.String.split (('\n')::[]) z3out) (Support.List.map Support.Microsoft.FStar.Util.trim_string))
in (let rec lblnegs = (fun ( lines ) -> (match (lines) with
| lname::"false"::rest -> begin
(let _68_20968 = (lblnegs rest)
in (lname)::_68_20968)
end
| lname::_48_131::rest -> begin
(lblnegs rest)
end
| _48_136 -> begin
[]
end))
in (let rec result = (fun ( x ) -> (match (x) with
| "timeout"::tl -> begin
(TIMEOUT, [])
end
| "unknown"::tl -> begin
(let _68_20971 = (lblnegs tl)
in (UNKNOWN, _68_20971))
end
| "sat"::tl -> begin
(let _68_20972 = (lblnegs tl)
in (SAT, _68_20972))
end
| "unsat"::tl -> begin
(UNSAT, [])
end
| _48_153::tl -> begin
(result tl)
end
| _48_156 -> begin
(let _68_20976 = (let _68_20975 = (let _68_20974 = (Support.List.map (fun ( l ) -> (Support.Microsoft.FStar.Util.format1 "<%s>" (Support.Microsoft.FStar.Util.trim_string l))) lines)
in (Support.String.concat "\n" _68_20974))
in (Support.Microsoft.FStar.Util.format1 "Got output lines: %s\n" _68_20975))
in (Support.Prims.pipe_left failwith _68_20976))
end))
in (result lines)))))
in (let stdout = (Support.Microsoft.FStar.Util.ask_process z3proc input)
in (parse (Support.Microsoft.FStar.Util.trim_string stdout)))))

let doZ3Exe = (let ctr = (Support.Microsoft.FStar.Util.mk_ref 0)
in (fun ( fresh ) ( input ) -> (let z3proc = (match (fresh) with
| true -> begin
(let _48_162 = (Support.Microsoft.FStar.Util.incr ctr)
in (let _68_20982 = (let _68_20981 = (Support.ST.read ctr)
in (Support.Microsoft.FStar.Util.string_of_int _68_20981))
in (new_z3proc _68_20982)))
end
| false -> begin
(bg_z3_proc.grab ())
end)
in (let res = (doZ3Exe' input z3proc)
in (let _48_166 = (match (fresh) with
| true -> begin
(Support.Microsoft.FStar.Util.kill_process z3proc)
end
| false -> begin
(bg_z3_proc.release ())
end)
in res)))))

let z3_options = (fun ( _48_168 ) -> (match (()) with
| () -> begin
(let mbqi = (match ((let _68_20985 = (get_z3version ())
in (z3v_le _68_20985 (4, 3, 1)))) with
| true -> begin
"mbqi"
end
| false -> begin
"smt.mbqi"
end)
in (let model_on_timeout = (match ((let _68_20986 = (get_z3version ())
in (z3v_le _68_20986 (4, 3, 1)))) with
| true -> begin
"(set-option :model-on-timeout true)\n"
end
| false -> begin
""
end)
in (Support.String.strcat (Support.String.strcat (Support.String.strcat (Support.String.strcat "(set-option :global-decls false)\n" "(set-option :") mbqi) " false)\n") model_on_timeout)))
end))

type 'a job =
{job : unit  ->  'a; callback : 'a  ->  unit}

let is_Mkjob = (fun ( _ ) -> (failwith ("Not yet implemented:is_Mkjob")))

type z3job =
(bool * (string * Support.Microsoft.FStar.Range.range) list) job

let job_queue = (let x = (Support.Microsoft.FStar.Util.mk_ref (({job = (fun ( _48_175 ) -> (match (()) with
| () -> begin
(let _68_21010 = (let _68_21009 = (let _68_21008 = (Support.Microsoft.FStar.Range.mk_range "" 0 0)
in ("", _68_21008))
in (_68_21009)::[])
in (false, _68_21010))
end)); callback = (fun ( a ) -> ())})::[]))
in (let _48_178 = (Support.ST.op_Colon_Equals x [])
in x))

let pending_jobs = (Support.Microsoft.FStar.Util.mk_ref 0)

let with_monitor = (fun ( m ) ( f ) -> (let _48_182 = (Support.Microsoft.FStar.Util.monitor_enter m)
in (let res = (f ())
in (let _48_185 = (Support.Microsoft.FStar.Util.monitor_exit m)
in res))))

let z3_job = (fun ( fresh ) ( label_messages ) ( input ) ( _48_190 ) -> (match (()) with
| () -> begin
(let _48_193 = (doZ3Exe fresh input)
in (match (_48_193) with
| (status, lblnegs) -> begin
(let result = (match (status) with
| UNSAT -> begin
(true, [])
end
| _48_196 -> begin
(let _48_197 = (match (((Support.ST.read Microsoft_FStar_Options.debug) <> [])) with
| true -> begin
(let _68_21021 = (Support.Microsoft.FStar.Util.format1 "Z3 says: %s\n" (status_to_string status))
in (Support.Prims.pipe_left Support.Microsoft.FStar.Util.print_string _68_21021))
end
| false -> begin
()
end)
in (let failing_assertions = (Support.Prims.pipe_right lblnegs (Support.List.collect (fun ( l ) -> (match ((Support.Prims.pipe_right label_messages (Support.List.tryFind (fun ( _48_205 ) -> (match (_48_205) with
| (m, _48_202, _48_204) -> begin
((Support.Prims.fst m) = l)
end))))) with
| None -> begin
[]
end
| Some ((_48_208, msg, r)) -> begin
((msg, r))::[]
end))))
in (false, failing_assertions)))
end)
in result)
end))
end))

let rec dequeue' = (fun ( _48_215 ) -> (match (()) with
| () -> begin
(let j = (match ((Support.ST.read job_queue)) with
| [] -> begin
(failwith ("Impossible"))
end
| hd::tl -> begin
(let _48_220 = (Support.ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (let _48_223 = (Support.Microsoft.FStar.Util.incr pending_jobs)
in (let _48_225 = (Support.Microsoft.FStar.Util.monitor_exit job_queue)
in (let _48_227 = (run_job j)
in (let _48_230 = (with_monitor job_queue (fun ( _48_229 ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.decr pending_jobs)
end)))
in (let _48_232 = (dequeue ())
in ()))))))
end))
and dequeue = (fun ( _48_234 ) -> (match (()) with
| () -> begin
(let _48_235 = (Support.Microsoft.FStar.Util.monitor_enter job_queue)
in (let rec aux = (fun ( _48_238 ) -> (match (()) with
| () -> begin
(match ((Support.ST.read job_queue)) with
| [] -> begin
(let _48_240 = (Support.Microsoft.FStar.Util.monitor_wait job_queue)
in (aux ()))
end
| _48_243 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job = (fun ( j ) -> (let _68_21033 = (j.job ())
in (Support.Prims.pipe_left j.callback _68_21033)))

let init = (fun ( _48_245 ) -> (match (()) with
| () -> begin
(let n_runners = ((Support.ST.read Microsoft_FStar_Options.n_cores) - 1)
in (let rec aux = (fun ( n ) -> (match ((n = 0)) with
| true -> begin
()
end
| false -> begin
(let _48_249 = (Support.Microsoft.FStar.Util.spawn dequeue)
in (aux (n - 1)))
end))
in (aux n_runners)))
end))

let enqueue = (fun ( fresh ) ( j ) -> (match ((not (fresh))) with
| true -> begin
(run_job j)
end
| false -> begin
(let _48_253 = (Support.Microsoft.FStar.Util.monitor_enter job_queue)
in (let _48_255 = (let _68_21043 = (let _68_21042 = (Support.ST.read job_queue)
in (Support.List.append _68_21042 ((j)::[])))
in (Support.ST.op_Colon_Equals job_queue _68_21043))
in (let _48_257 = (Support.Microsoft.FStar.Util.monitor_pulse job_queue)
in (Support.Microsoft.FStar.Util.monitor_exit job_queue))))
end))

let finish = (fun ( _48_259 ) -> (match (()) with
| () -> begin
(let bg = (bg_z3_proc.grab ())
in (let _48_261 = (Support.Microsoft.FStar.Util.kill_process bg)
in (let _48_263 = (bg_z3_proc.release ())
in (let rec aux = (fun ( _48_266 ) -> (match (()) with
| () -> begin
(let _48_270 = (with_monitor job_queue (fun ( _48_267 ) -> (match (()) with
| () -> begin
(let _68_21051 = (Support.ST.read pending_jobs)
in (let _68_21050 = (let _68_21049 = (Support.ST.read job_queue)
in (Support.List.length _68_21049))
in (_68_21051, _68_21050)))
end)))
in (match (_48_270) with
| (n, m) -> begin
(match (((n + m) = 0)) with
| true -> begin
(let _68_21052 = (Microsoft_FStar_Tc_Errors.report_all ())
in (Support.Prims.pipe_right _68_21052 Support.Prims.ignore))
end
| false -> begin
(let _48_271 = (Support.Microsoft.FStar.Util.sleep 500)
in (aux ()))
end)
end))
end))
in (aux ())))))
end))

type scope_t =
Microsoft_FStar_ToSMT_Term.decl list list

let fresh_scope = (Support.Microsoft.FStar.Util.mk_ref (([])::[]))

let bg_scope = (Support.Microsoft.FStar.Util.mk_ref [])

let push = (fun ( msg ) -> (let _48_274 = (let _68_21056 = (let _68_21055 = (Support.ST.read fresh_scope)
in ((Microsoft_FStar_ToSMT_Term.Caption (msg))::[])::_68_21055)
in (Support.ST.op_Colon_Equals fresh_scope _68_21056))
in (let _68_21058 = (let _68_21057 = (Support.ST.read bg_scope)
in (Support.List.append ((Microsoft_FStar_ToSMT_Term.Caption (msg))::(Microsoft_FStar_ToSMT_Term.Push)::[]) _68_21057))
in (Support.ST.op_Colon_Equals bg_scope _68_21058))))

let pop = (fun ( msg ) -> (let _48_277 = (let _68_21062 = (let _68_21061 = (Support.ST.read fresh_scope)
in (Support.List.tl _68_21061))
in (Support.ST.op_Colon_Equals fresh_scope _68_21062))
in (let _68_21064 = (let _68_21063 = (Support.ST.read bg_scope)
in (Support.List.append ((Microsoft_FStar_ToSMT_Term.Caption (msg))::(Microsoft_FStar_ToSMT_Term.Pop)::[]) _68_21063))
in (Support.ST.op_Colon_Equals bg_scope _68_21064))))

let giveZ3 = (fun ( decls ) -> (let _48_285 = (match ((Support.ST.read fresh_scope)) with
| hd::tl -> begin
(Support.ST.op_Colon_Equals fresh_scope (((Support.List.append hd decls))::tl))
end
| _48_284 -> begin
(failwith ("Impossible"))
end)
in (let _68_21068 = (let _68_21067 = (Support.ST.read bg_scope)
in (Support.List.append (Support.List.rev decls) _68_21067))
in (Support.ST.op_Colon_Equals bg_scope _68_21068))))

let bgtheory = (fun ( fresh ) -> (match (fresh) with
| true -> begin
(let _68_21072 = (let _68_21071 = (Support.ST.read fresh_scope)
in (Support.List.rev _68_21071))
in (Support.Prims.pipe_right _68_21072 Support.List.flatten))
end
| false -> begin
(let bg = (Support.ST.read bg_scope)
in (let _48_289 = (Support.ST.op_Colon_Equals bg_scope [])
in (Support.List.rev bg)))
end))

let refresh = (fun ( _48_291 ) -> (match (()) with
| () -> begin
(let _48_292 = (bg_z3_proc.refresh ())
in (let theory = (bgtheory true)
in (Support.ST.op_Colon_Equals bg_scope (Support.List.rev theory))))
end))

let mark = (fun ( msg ) -> (push msg))

let reset_mark = (fun ( msg ) -> (let _48_297 = (pop msg)
in (refresh ())))

let commit_mark = (fun ( msg ) -> (match ((Support.ST.read fresh_scope)) with
| hd::s::tl -> begin
(Support.ST.op_Colon_Equals fresh_scope (((Support.List.append hd s))::tl))
end
| _48_306 -> begin
(failwith ("Impossible"))
end))

let ask = (fun ( fresh ) ( label_messages ) ( qry ) ( cb ) -> (let fresh = (fresh && ((Support.ST.read Microsoft_FStar_Options.n_cores) > 1))
in (let theory = (bgtheory fresh)
in (let theory = (match (fresh) with
| true -> begin
(Support.List.append theory qry)
end
| false -> begin
(Support.List.append (Support.List.append (Support.List.append theory ((Microsoft_FStar_ToSMT_Term.Push)::[])) qry) ((Microsoft_FStar_ToSMT_Term.Pop)::[]))
end)
in (let input = (let _68_21089 = (let _68_21088 = (let _68_21087 = (z3_options ())
in (Microsoft_FStar_ToSMT_Term.declToSmt _68_21087))
in (Support.List.map _68_21088 theory))
in (Support.Prims.pipe_right _68_21089 (Support.String.concat "\n")))
in (let _48_315 = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(log_query fresh input)
end
| false -> begin
()
end)
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb})))))))




