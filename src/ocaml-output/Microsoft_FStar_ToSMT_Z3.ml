
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

let z3v_compare = (fun ( known ) ( _50_8 ) -> (match (_50_8) with
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

let get_z3version = (fun ( _50_20 ) -> (match (()) with
| () -> begin
(let prefix = "Z3 version "
in (match ((Support.ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(let _50_30 = (let _70_21003 = (Support.ST.read Microsoft_FStar_Options.z3_exe)
in (Support.Microsoft.FStar.Util.run_proc _70_21003 "-version" ""))
in (match (_50_30) with
| (_50_26, out, _50_29) -> begin
(let out = (match ((Support.Microsoft.FStar.Util.splitlines out)) with
| x::_50_32 when (Support.Microsoft.FStar.Util.starts_with x prefix) -> begin
(let x = (let _70_21004 = (Support.Microsoft.FStar.Util.substring_from x (Support.String.length prefix))
in (Support.Microsoft.FStar.Util.trim_string _70_21004))
in (let x = (Support.All.try_with (fun ( _50_37 ) -> (match (()) with
| () -> begin
(Support.List.map Support.Microsoft.FStar.Util.int_of_string (Support.Microsoft.FStar.Util.split x "."))
end)) (fun ( _50_36 ) -> (match (_50_36) with
| _50_40 -> begin
[]
end)))
in (match (x) with
| i1::i2::i3::[] -> begin
Z3V ((i1, i2, i3))
end
| _50_49 -> begin
Z3V_Unknown
end)))
end
| _50_51 -> begin
Z3V_Unknown
end)
in (let _50_53 = (Support.ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))

let ini_params = (fun ( _50_55 ) -> (match (()) with
| () -> begin
(let t = (match ((let _70_21009 = (get_z3version ())
in (z3v_le _70_21009 (4, 3, 1)))) with
| true -> begin
(Support.ST.read Microsoft_FStar_Options.z3timeout)
end
| false -> begin
((Support.ST.read Microsoft_FStar_Options.z3timeout) * 1000)
end)
in (let timeout = (let _70_21010 = (Support.Microsoft.FStar.Util.string_of_int t)
in (Support.Microsoft.FStar.Util.format1 "-t:%s" _70_21010))
in (let relevancy = (match ((let _70_21011 = (get_z3version ())
in (z3v_le _70_21011 (4, 3, 1)))) with
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

let status_to_string = (fun ( _50_1 ) -> (match (_50_1) with
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

let tid = (fun ( _50_64 ) -> (match (()) with
| () -> begin
(let _70_21020 = (Support.Microsoft.FStar.Util.current_tid ())
in (Support.All.pipe_right _70_21020 Support.Microsoft.FStar.Util.string_of_int))
end))

let new_z3proc = (fun ( id ) -> (let cond = (fun ( pid ) ( s ) -> (let x = ((Support.Microsoft.FStar.Util.trim_string s) = "Done!")
in x))
in (let _70_21028 = (Support.ST.read Microsoft_FStar_Options.z3_exe)
in (let _70_21027 = (ini_params ())
in (Support.Microsoft.FStar.Util.start_process id _70_21028 _70_21027 cond)))))

type bgproc =
{grab : unit  ->  Support.Microsoft.FStar.Util.proc; release : unit  ->  unit; refresh : unit  ->  unit}

let is_Mkbgproc = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkbgproc"))

let queries_dot_smt2 = (Support.Microsoft.FStar.Util.mk_ref None)

let get_qfile = (let ctr = (Support.Microsoft.FStar.Util.mk_ref 0)
in (fun ( fresh ) -> (match (fresh) with
| true -> begin
(let _50_76 = (Support.Microsoft.FStar.Util.incr ctr)
in (let _70_21061 = (let _70_21060 = (let _70_21059 = (Support.ST.read ctr)
in (Support.Microsoft.FStar.Util.string_of_int _70_21059))
in (Support.Microsoft.FStar.Util.format1 "queries-%s.smt2" _70_21060))
in (Support.Microsoft.FStar.Util.open_file_for_writing _70_21061)))
end
| false -> begin
(match ((Support.ST.read queries_dot_smt2)) with
| None -> begin
(let fh = (Support.Microsoft.FStar.Util.open_file_for_writing "queries-bg-0.smt2")
in (let _50_80 = (Support.ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
in fh))
end
| Some (fh) -> begin
fh
end)
end)))

let log_query = (fun ( fresh ) ( i ) -> (let fh = (get_qfile fresh)
in (let _50_87 = (Support.Microsoft.FStar.Util.append_to_file fh i)
in (match (fresh) with
| true -> begin
(Support.Microsoft.FStar.Util.close_file fh)
end
| false -> begin
()
end))))

let bg_z3_proc = (let ctr = (Support.Microsoft.FStar.Util.mk_ref (- (1)))
in (let new_proc = (fun ( _50_91 ) -> (match (()) with
| () -> begin
(let _70_21070 = (let _70_21069 = (let _50_92 = (Support.Microsoft.FStar.Util.incr ctr)
in (let _70_21068 = (Support.ST.read ctr)
in (Support.All.pipe_right _70_21068 Support.Microsoft.FStar.Util.string_of_int)))
in (Support.Microsoft.FStar.Util.format1 "bg-%s" _70_21069))
in (new_z3proc _70_21070))
end))
in (let z3proc = (let _70_21071 = (new_proc ())
in (Support.Microsoft.FStar.Util.mk_ref _70_21071))
in (let x = []
in (let grab = (fun ( _50_97 ) -> (match (()) with
| () -> begin
(let _50_98 = (Support.Microsoft.FStar.Util.monitor_enter x)
in (Support.ST.read z3proc))
end))
in (let release = (fun ( _50_101 ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.monitor_exit x)
end))
in (let refresh = (fun ( _50_103 ) -> (match (()) with
| () -> begin
(let proc = (grab ())
in (let _50_105 = (Support.Microsoft.FStar.Util.kill_process proc)
in (let _50_107 = (let _70_21078 = (new_proc ())
in (Support.ST.op_Colon_Equals z3proc _70_21078))
in (let _50_115 = (match ((Support.ST.read queries_dot_smt2)) with
| None -> begin
()
end
| Some (fh) -> begin
(let _50_112 = (Support.Microsoft.FStar.Util.close_file fh)
in (let fh = (let _70_21081 = (let _70_21080 = (let _70_21079 = (Support.ST.read ctr)
in (Support.All.pipe_right _70_21079 Support.Microsoft.FStar.Util.string_of_int))
in (Support.Microsoft.FStar.Util.format1 "queries-bg-%s.smt2" _70_21080))
in (Support.Microsoft.FStar.Util.open_file_for_writing _70_21081))
in (Support.ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))))
end)
in (release ())))))
end))
in {grab = grab; release = release; refresh = refresh})))))))

let doZ3Exe' = (fun ( input ) ( z3proc ) -> (let parse = (fun ( z3out ) -> (let lines = (Support.All.pipe_right (Support.String.split (('\n')::[]) z3out) (Support.List.map Support.Microsoft.FStar.Util.trim_string))
in (let rec lblnegs = (fun ( lines ) -> (match (lines) with
| lname::"false"::rest -> begin
(let _70_21090 = (lblnegs rest)
in (lname)::_70_21090)
end
| lname::_50_131::rest -> begin
(lblnegs rest)
end
| _50_136 -> begin
[]
end))
in (let rec result = (fun ( x ) -> (match (x) with
| "timeout"::tl -> begin
(TIMEOUT, [])
end
| "unknown"::tl -> begin
(let _70_21093 = (lblnegs tl)
in (UNKNOWN, _70_21093))
end
| "sat"::tl -> begin
(let _70_21094 = (lblnegs tl)
in (SAT, _70_21094))
end
| "unsat"::tl -> begin
(UNSAT, [])
end
| _50_153::tl -> begin
(result tl)
end
| _50_156 -> begin
(let _70_21098 = (let _70_21097 = (let _70_21096 = (Support.List.map (fun ( l ) -> (Support.Microsoft.FStar.Util.format1 "<%s>" (Support.Microsoft.FStar.Util.trim_string l))) lines)
in (Support.String.concat "\n" _70_21096))
in (Support.Microsoft.FStar.Util.format1 "Got output lines: %s\n" _70_21097))
in (Support.All.pipe_left Support.All.failwith _70_21098))
end))
in (result lines)))))
in (let stdout = (Support.Microsoft.FStar.Util.ask_process z3proc input)
in (parse (Support.Microsoft.FStar.Util.trim_string stdout)))))

let doZ3Exe = (let ctr = (Support.Microsoft.FStar.Util.mk_ref 0)
in (fun ( fresh ) ( input ) -> (let z3proc = (match (fresh) with
| true -> begin
(let _50_162 = (Support.Microsoft.FStar.Util.incr ctr)
in (let _70_21104 = (let _70_21103 = (Support.ST.read ctr)
in (Support.Microsoft.FStar.Util.string_of_int _70_21103))
in (new_z3proc _70_21104)))
end
| false -> begin
(bg_z3_proc.grab ())
end)
in (let res = (doZ3Exe' input z3proc)
in (let _50_166 = (match (fresh) with
| true -> begin
(Support.Microsoft.FStar.Util.kill_process z3proc)
end
| false -> begin
(bg_z3_proc.release ())
end)
in res)))))

let z3_options = (fun ( _50_168 ) -> (match (()) with
| () -> begin
(let mbqi = (match ((let _70_21107 = (get_z3version ())
in (z3v_le _70_21107 (4, 3, 1)))) with
| true -> begin
"mbqi"
end
| false -> begin
"smt.mbqi"
end)
in (let model_on_timeout = (match ((let _70_21108 = (get_z3version ())
in (z3v_le _70_21108 (4, 3, 1)))) with
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

let is_Mkjob = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkjob"))

type z3job =
(bool * (string * Support.Microsoft.FStar.Range.range) list) job

let job_queue = (let x = (Support.Microsoft.FStar.Util.mk_ref (({job = (fun ( _50_175 ) -> (match (()) with
| () -> begin
(let _70_21132 = (let _70_21131 = (let _70_21130 = (Support.Microsoft.FStar.Range.mk_range "" 0 0)
in ("", _70_21130))
in (_70_21131)::[])
in (false, _70_21132))
end)); callback = (fun ( a ) -> ())})::[]))
in (let _50_178 = (Support.ST.op_Colon_Equals x [])
in x))

let pending_jobs = (Support.Microsoft.FStar.Util.mk_ref 0)

let with_monitor = (fun ( m ) ( f ) -> (let _50_182 = (Support.Microsoft.FStar.Util.monitor_enter m)
in (let res = (f ())
in (let _50_185 = (Support.Microsoft.FStar.Util.monitor_exit m)
in res))))

let z3_job = (fun ( fresh ) ( label_messages ) ( input ) ( _50_190 ) -> (match (()) with
| () -> begin
(let _50_193 = (doZ3Exe fresh input)
in (match (_50_193) with
| (status, lblnegs) -> begin
(let result = (match (status) with
| UNSAT -> begin
(true, [])
end
| _50_196 -> begin
(let _50_197 = (match (((Support.ST.read Microsoft_FStar_Options.debug) <> [])) with
| true -> begin
(let _70_21143 = (Support.Microsoft.FStar.Util.format1 "Z3 says: %s\n" (status_to_string status))
in (Support.All.pipe_left Support.Microsoft.FStar.Util.print_string _70_21143))
end
| false -> begin
()
end)
in (let failing_assertions = (Support.All.pipe_right lblnegs (Support.List.collect (fun ( l ) -> (match ((Support.All.pipe_right label_messages (Support.List.tryFind (fun ( _50_205 ) -> (match (_50_205) with
| (m, _50_202, _50_204) -> begin
((Support.Prims.fst m) = l)
end))))) with
| None -> begin
[]
end
| Some ((_50_208, msg, r)) -> begin
((msg, r))::[]
end))))
in (false, failing_assertions)))
end)
in result)
end))
end))

let rec dequeue' = (fun ( _50_215 ) -> (match (()) with
| () -> begin
(let j = (match ((Support.ST.read job_queue)) with
| [] -> begin
(Support.All.failwith "Impossible")
end
| hd::tl -> begin
(let _50_220 = (Support.ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (let _50_223 = (Support.Microsoft.FStar.Util.incr pending_jobs)
in (let _50_225 = (Support.Microsoft.FStar.Util.monitor_exit job_queue)
in (let _50_227 = (run_job j)
in (let _50_230 = (with_monitor job_queue (fun ( _50_229 ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.decr pending_jobs)
end)))
in (let _50_232 = (dequeue ())
in ()))))))
end))
and dequeue = (fun ( _50_234 ) -> (match (()) with
| () -> begin
(let _50_235 = (Support.Microsoft.FStar.Util.monitor_enter job_queue)
in (let rec aux = (fun ( _50_238 ) -> (match (()) with
| () -> begin
(match ((Support.ST.read job_queue)) with
| [] -> begin
(let _50_240 = (Support.Microsoft.FStar.Util.monitor_wait job_queue)
in (aux ()))
end
| _50_243 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job = (fun ( j ) -> (let _70_21155 = (j.job ())
in (Support.All.pipe_left j.callback _70_21155)))

let init = (fun ( _50_245 ) -> (match (()) with
| () -> begin
(let n_runners = ((Support.ST.read Microsoft_FStar_Options.n_cores) - 1)
in (let rec aux = (fun ( n ) -> (match ((n = 0)) with
| true -> begin
()
end
| false -> begin
(let _50_249 = (Support.Microsoft.FStar.Util.spawn dequeue)
in (aux (n - 1)))
end))
in (aux n_runners)))
end))

let enqueue = (fun ( fresh ) ( j ) -> (match ((not (fresh))) with
| true -> begin
(run_job j)
end
| false -> begin
(let _50_253 = (Support.Microsoft.FStar.Util.monitor_enter job_queue)
in (let _50_255 = (let _70_21165 = (let _70_21164 = (Support.ST.read job_queue)
in (Support.List.append _70_21164 ((j)::[])))
in (Support.ST.op_Colon_Equals job_queue _70_21165))
in (let _50_257 = (Support.Microsoft.FStar.Util.monitor_pulse job_queue)
in (Support.Microsoft.FStar.Util.monitor_exit job_queue))))
end))

let finish = (fun ( _50_259 ) -> (match (()) with
| () -> begin
(let bg = (bg_z3_proc.grab ())
in (let _50_261 = (Support.Microsoft.FStar.Util.kill_process bg)
in (let _50_263 = (bg_z3_proc.release ())
in (let rec aux = (fun ( _50_266 ) -> (match (()) with
| () -> begin
(let _50_270 = (with_monitor job_queue (fun ( _50_267 ) -> (match (()) with
| () -> begin
(let _70_21173 = (Support.ST.read pending_jobs)
in (let _70_21172 = (let _70_21171 = (Support.ST.read job_queue)
in (Support.List.length _70_21171))
in (_70_21173, _70_21172)))
end)))
in (match (_50_270) with
| (n, m) -> begin
(match (((n + m) = 0)) with
| true -> begin
(let _70_21174 = (Microsoft_FStar_Tc_Errors.report_all ())
in (Support.All.pipe_right _70_21174 Support.Prims.ignore))
end
| false -> begin
(let _50_271 = (Support.Microsoft.FStar.Util.sleep 500)
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

let push = (fun ( msg ) -> (let _50_274 = (let _70_21178 = (let _70_21177 = (Support.ST.read fresh_scope)
in ((Microsoft_FStar_ToSMT_Term.Caption (msg))::[])::_70_21177)
in (Support.ST.op_Colon_Equals fresh_scope _70_21178))
in (let _70_21180 = (let _70_21179 = (Support.ST.read bg_scope)
in (Support.List.append ((Microsoft_FStar_ToSMT_Term.Caption (msg))::(Microsoft_FStar_ToSMT_Term.Push)::[]) _70_21179))
in (Support.ST.op_Colon_Equals bg_scope _70_21180))))

let pop = (fun ( msg ) -> (let _50_277 = (let _70_21184 = (let _70_21183 = (Support.ST.read fresh_scope)
in (Support.List.tl _70_21183))
in (Support.ST.op_Colon_Equals fresh_scope _70_21184))
in (let _70_21186 = (let _70_21185 = (Support.ST.read bg_scope)
in (Support.List.append ((Microsoft_FStar_ToSMT_Term.Caption (msg))::(Microsoft_FStar_ToSMT_Term.Pop)::[]) _70_21185))
in (Support.ST.op_Colon_Equals bg_scope _70_21186))))

let giveZ3 = (fun ( decls ) -> (let _50_285 = (match ((Support.ST.read fresh_scope)) with
| hd::tl -> begin
(Support.ST.op_Colon_Equals fresh_scope (((Support.List.append hd decls))::tl))
end
| _50_284 -> begin
(Support.All.failwith "Impossible")
end)
in (let _70_21190 = (let _70_21189 = (Support.ST.read bg_scope)
in (Support.List.append (Support.List.rev decls) _70_21189))
in (Support.ST.op_Colon_Equals bg_scope _70_21190))))

let bgtheory = (fun ( fresh ) -> (match (fresh) with
| true -> begin
(let _70_21194 = (let _70_21193 = (Support.ST.read fresh_scope)
in (Support.List.rev _70_21193))
in (Support.All.pipe_right _70_21194 Support.List.flatten))
end
| false -> begin
(let bg = (Support.ST.read bg_scope)
in (let _50_289 = (Support.ST.op_Colon_Equals bg_scope [])
in (Support.List.rev bg)))
end))

let refresh = (fun ( _50_291 ) -> (match (()) with
| () -> begin
(let _50_292 = (bg_z3_proc.refresh ())
in (let theory = (bgtheory true)
in (Support.ST.op_Colon_Equals bg_scope (Support.List.rev theory))))
end))

let mark = (fun ( msg ) -> (push msg))

let reset_mark = (fun ( msg ) -> (let _50_297 = (pop msg)
in (refresh ())))

let commit_mark = (fun ( msg ) -> (match ((Support.ST.read fresh_scope)) with
| hd::s::tl -> begin
(Support.ST.op_Colon_Equals fresh_scope (((Support.List.append hd s))::tl))
end
| _50_306 -> begin
(Support.All.failwith "Impossible")
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
in (let input = (let _70_21211 = (let _70_21210 = (let _70_21209 = (z3_options ())
in (Microsoft_FStar_ToSMT_Term.declToSmt _70_21209))
in (Support.List.map _70_21210 theory))
in (Support.All.pipe_right _70_21211 (Support.String.concat "\n")))
in (let _50_315 = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(log_query fresh input)
end
| false -> begin
()
end)
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb})))))))




