
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

let ___Z3V____0 = (fun ( projectee ) -> (match (projectee) with
| Z3V (_50_4) -> begin
_50_4
end))

let z3v_compare = (fun ( known ) ( _50_9 ) -> (match (_50_9) with
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

let get_z3version = (fun ( _50_21 ) -> (match (()) with
| () -> begin
(let prefix = "Z3 version "
in (match ((Support.ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(let _50_31 = (let _121_26 = (Support.ST.read Microsoft_FStar_Options.z3_exe)
in (Support.Microsoft.FStar.Util.run_proc _121_26 "-version" ""))
in (match (_50_31) with
| (_50_27, out, _50_30) -> begin
(let out = (match ((Support.Microsoft.FStar.Util.splitlines out)) with
| x::_50_33 when (Support.Microsoft.FStar.Util.starts_with x prefix) -> begin
(let x = (let _121_27 = (Support.Microsoft.FStar.Util.substring_from x (Support.String.length prefix))
in (Support.Microsoft.FStar.Util.trim_string _121_27))
in (let x = (Support.All.try_with (fun ( _50_38 ) -> (match (()) with
| () -> begin
(Support.List.map Support.Microsoft.FStar.Util.int_of_string (Support.Microsoft.FStar.Util.split x "."))
end)) (fun ( _50_37 ) -> (match (_50_37) with
| _50_41 -> begin
[]
end)))
in (match (x) with
| i1::i2::i3::[] -> begin
Z3V ((i1, i2, i3))
end
| _50_50 -> begin
Z3V_Unknown
end)))
end
| _50_52 -> begin
Z3V_Unknown
end)
in (let _50_54 = (Support.ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))

let ini_params = (fun ( _50_56 ) -> (match (()) with
| () -> begin
(let t = (match ((let _121_32 = (get_z3version ())
in (z3v_le _121_32 (4, 3, 1)))) with
| true -> begin
(Support.ST.read Microsoft_FStar_Options.z3timeout)
end
| false -> begin
((Support.ST.read Microsoft_FStar_Options.z3timeout) * 1000)
end)
in (let timeout = (let _121_33 = (Support.Microsoft.FStar.Util.string_of_int t)
in (Support.Microsoft.FStar.Util.format1 "-t:%s" _121_33))
in (let relevancy = (match ((let _121_34 = (get_z3version ())
in (z3v_le _121_34 (4, 3, 1)))) with
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

let tid = (fun ( _50_65 ) -> (match (()) with
| () -> begin
(let _121_43 = (Support.Microsoft.FStar.Util.current_tid ())
in (Support.All.pipe_right _121_43 Support.Microsoft.FStar.Util.string_of_int))
end))

let new_z3proc = (fun ( id ) -> (let cond = (fun ( pid ) ( s ) -> (let x = ((Support.Microsoft.FStar.Util.trim_string s) = "Done!")
in x))
in (let _121_51 = (Support.ST.read Microsoft_FStar_Options.z3_exe)
in (let _121_50 = (ini_params ())
in (Support.Microsoft.FStar.Util.start_process id _121_51 _121_50 cond)))))

type bgproc =
{grab : unit  ->  Support.Microsoft.FStar.Util.proc; release : unit  ->  unit; refresh : unit  ->  unit}

let is_Mkbgproc = (fun ( _ ) -> (Support.All.failwith "Not yet implemented:is_Mkbgproc"))

let queries_dot_smt2 = (Support.Microsoft.FStar.Util.mk_ref None)

let get_qfile = (let ctr = (Support.Microsoft.FStar.Util.mk_ref 0)
in (fun ( fresh ) -> (match (fresh) with
| true -> begin
(let _50_77 = (Support.Microsoft.FStar.Util.incr ctr)
in (let _121_84 = (let _121_83 = (let _121_82 = (Support.ST.read ctr)
in (Support.Microsoft.FStar.Util.string_of_int _121_82))
in (Support.Microsoft.FStar.Util.format1 "queries-%s.smt2" _121_83))
in (Support.Microsoft.FStar.Util.open_file_for_writing _121_84)))
end
| false -> begin
(match ((Support.ST.read queries_dot_smt2)) with
| None -> begin
(let fh = (Support.Microsoft.FStar.Util.open_file_for_writing "queries-bg-0.smt2")
in (let _50_81 = (Support.ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
in fh))
end
| Some (fh) -> begin
fh
end)
end)))

let log_query = (fun ( fresh ) ( i ) -> (let fh = (get_qfile fresh)
in (let _50_88 = (Support.Microsoft.FStar.Util.append_to_file fh i)
in (match (fresh) with
| true -> begin
(Support.Microsoft.FStar.Util.close_file fh)
end
| false -> begin
()
end))))

let bg_z3_proc = (let ctr = (Support.Microsoft.FStar.Util.mk_ref (- (1)))
in (let new_proc = (fun ( _50_92 ) -> (match (()) with
| () -> begin
(let _121_93 = (let _121_92 = (let _50_93 = (Support.Microsoft.FStar.Util.incr ctr)
in (let _121_91 = (Support.ST.read ctr)
in (Support.All.pipe_right _121_91 Support.Microsoft.FStar.Util.string_of_int)))
in (Support.Microsoft.FStar.Util.format1 "bg-%s" _121_92))
in (new_z3proc _121_93))
end))
in (let z3proc = (let _121_94 = (new_proc ())
in (Support.Microsoft.FStar.Util.mk_ref _121_94))
in (let x = []
in (let grab = (fun ( _50_98 ) -> (match (()) with
| () -> begin
(let _50_99 = (Support.Microsoft.FStar.Util.monitor_enter x)
in (Support.ST.read z3proc))
end))
in (let release = (fun ( _50_102 ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.monitor_exit x)
end))
in (let refresh = (fun ( _50_104 ) -> (match (()) with
| () -> begin
(let proc = (grab ())
in (let _50_106 = (Support.Microsoft.FStar.Util.kill_process proc)
in (let _50_108 = (let _121_101 = (new_proc ())
in (Support.ST.op_Colon_Equals z3proc _121_101))
in (let _50_116 = (match ((Support.ST.read queries_dot_smt2)) with
| None -> begin
()
end
| Some (fh) -> begin
(let _50_113 = (Support.Microsoft.FStar.Util.close_file fh)
in (let fh = (let _121_104 = (let _121_103 = (let _121_102 = (Support.ST.read ctr)
in (Support.All.pipe_right _121_102 Support.Microsoft.FStar.Util.string_of_int))
in (Support.Microsoft.FStar.Util.format1 "queries-bg-%s.smt2" _121_103))
in (Support.Microsoft.FStar.Util.open_file_for_writing _121_104))
in (Support.ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))))
end)
in (release ())))))
end))
in {grab = grab; release = release; refresh = refresh})))))))

let doZ3Exe' = (fun ( input ) ( z3proc ) -> (let parse = (fun ( z3out ) -> (let lines = (Support.All.pipe_right (Support.String.split (('\n')::[]) z3out) (Support.List.map Support.Microsoft.FStar.Util.trim_string))
in (let rec lblnegs = (fun ( lines ) -> (match (lines) with
| lname::"false"::rest -> begin
(let _121_113 = (lblnegs rest)
in (lname)::_121_113)
end
| lname::_50_132::rest -> begin
(lblnegs rest)
end
| _50_137 -> begin
[]
end))
in (let rec result = (fun ( x ) -> (match (x) with
| "timeout"::tl -> begin
(TIMEOUT, [])
end
| "unknown"::tl -> begin
(let _121_116 = (lblnegs tl)
in (UNKNOWN, _121_116))
end
| "sat"::tl -> begin
(let _121_117 = (lblnegs tl)
in (SAT, _121_117))
end
| "unsat"::tl -> begin
(UNSAT, [])
end
| _50_154::tl -> begin
(result tl)
end
| _50_157 -> begin
(let _121_121 = (let _121_120 = (let _121_119 = (Support.List.map (fun ( l ) -> (Support.Microsoft.FStar.Util.format1 "<%s>" (Support.Microsoft.FStar.Util.trim_string l))) lines)
in (Support.String.concat "\n" _121_119))
in (Support.Microsoft.FStar.Util.format1 "Got output lines: %s\n" _121_120))
in (Support.All.pipe_left Support.All.failwith _121_121))
end))
in (result lines)))))
in (let stdout = (Support.Microsoft.FStar.Util.ask_process z3proc input)
in (parse (Support.Microsoft.FStar.Util.trim_string stdout)))))

let doZ3Exe = (let ctr = (Support.Microsoft.FStar.Util.mk_ref 0)
in (fun ( fresh ) ( input ) -> (let z3proc = (match (fresh) with
| true -> begin
(let _50_163 = (Support.Microsoft.FStar.Util.incr ctr)
in (let _121_127 = (let _121_126 = (Support.ST.read ctr)
in (Support.Microsoft.FStar.Util.string_of_int _121_126))
in (new_z3proc _121_127)))
end
| false -> begin
(bg_z3_proc.grab ())
end)
in (let res = (doZ3Exe' input z3proc)
in (let _50_167 = (match (fresh) with
| true -> begin
(Support.Microsoft.FStar.Util.kill_process z3proc)
end
| false -> begin
(bg_z3_proc.release ())
end)
in res)))))

let z3_options = (fun ( _50_169 ) -> (match (()) with
| () -> begin
(let mbqi = (match ((let _121_130 = (get_z3version ())
in (z3v_le _121_130 (4, 3, 1)))) with
| true -> begin
"mbqi"
end
| false -> begin
"smt.mbqi"
end)
in (let model_on_timeout = (match ((let _121_131 = (get_z3version ())
in (z3v_le _121_131 (4, 3, 1)))) with
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

let job_queue = (let x = (Support.Microsoft.FStar.Util.mk_ref (({job = (fun ( _50_176 ) -> (match (()) with
| () -> begin
(let _121_155 = (let _121_154 = (let _121_153 = (Support.Microsoft.FStar.Range.mk_range "" 0 0)
in ("", _121_153))
in (_121_154)::[])
in (false, _121_155))
end)); callback = (fun ( a ) -> ())})::[]))
in (let _50_179 = (Support.ST.op_Colon_Equals x [])
in x))

let pending_jobs = (Support.Microsoft.FStar.Util.mk_ref 0)

let with_monitor = (fun ( m ) ( f ) -> (let _50_183 = (Support.Microsoft.FStar.Util.monitor_enter m)
in (let res = (f ())
in (let _50_186 = (Support.Microsoft.FStar.Util.monitor_exit m)
in res))))

let z3_job = (fun ( fresh ) ( label_messages ) ( input ) ( _50_191 ) -> (match (()) with
| () -> begin
(let _50_194 = (doZ3Exe fresh input)
in (match (_50_194) with
| (status, lblnegs) -> begin
(let result = (match (status) with
| UNSAT -> begin
(true, [])
end
| _50_197 -> begin
(let _50_198 = (match (((Support.ST.read Microsoft_FStar_Options.debug) <> [])) with
| true -> begin
(let _121_166 = (Support.Microsoft.FStar.Util.format1 "Z3 says: %s\n" (status_to_string status))
in (Support.All.pipe_left Support.Microsoft.FStar.Util.print_string _121_166))
end
| false -> begin
()
end)
in (let failing_assertions = (Support.All.pipe_right lblnegs (Support.List.collect (fun ( l ) -> (match ((Support.All.pipe_right label_messages (Support.List.tryFind (fun ( _50_206 ) -> (match (_50_206) with
| (m, _50_203, _50_205) -> begin
((Support.Prims.fst m) = l)
end))))) with
| None -> begin
[]
end
| Some ((_50_209, msg, r)) -> begin
((msg, r))::[]
end))))
in (false, failing_assertions)))
end)
in result)
end))
end))

let rec dequeue' = (fun ( _50_216 ) -> (match (()) with
| () -> begin
(let j = (match ((Support.ST.read job_queue)) with
| [] -> begin
(Support.All.failwith "Impossible")
end
| hd::tl -> begin
(let _50_221 = (Support.ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (let _50_224 = (Support.Microsoft.FStar.Util.incr pending_jobs)
in (let _50_226 = (Support.Microsoft.FStar.Util.monitor_exit job_queue)
in (let _50_228 = (run_job j)
in (let _50_231 = (with_monitor job_queue (fun ( _50_230 ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.decr pending_jobs)
end)))
in (let _50_233 = (dequeue ())
in ()))))))
end))
and dequeue = (fun ( _50_235 ) -> (match (()) with
| () -> begin
(let _50_236 = (Support.Microsoft.FStar.Util.monitor_enter job_queue)
in (let rec aux = (fun ( _50_239 ) -> (match (()) with
| () -> begin
(match ((Support.ST.read job_queue)) with
| [] -> begin
(let _50_241 = (Support.Microsoft.FStar.Util.monitor_wait job_queue)
in (aux ()))
end
| _50_244 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job = (fun ( j ) -> (let _121_178 = (j.job ())
in (Support.All.pipe_left j.callback _121_178)))

let init = (fun ( _50_246 ) -> (match (()) with
| () -> begin
(let n_runners = ((Support.ST.read Microsoft_FStar_Options.n_cores) - 1)
in (let rec aux = (fun ( n ) -> (match ((n = 0)) with
| true -> begin
()
end
| false -> begin
(let _50_250 = (Support.Microsoft.FStar.Util.spawn dequeue)
in (aux (n - 1)))
end))
in (aux n_runners)))
end))

let enqueue = (fun ( fresh ) ( j ) -> (match ((not (fresh))) with
| true -> begin
(run_job j)
end
| false -> begin
(let _50_254 = (Support.Microsoft.FStar.Util.monitor_enter job_queue)
in (let _50_256 = (let _121_188 = (let _121_187 = (Support.ST.read job_queue)
in (Support.List.append _121_187 ((j)::[])))
in (Support.ST.op_Colon_Equals job_queue _121_188))
in (let _50_258 = (Support.Microsoft.FStar.Util.monitor_pulse job_queue)
in (Support.Microsoft.FStar.Util.monitor_exit job_queue))))
end))

let finish = (fun ( _50_260 ) -> (match (()) with
| () -> begin
(let bg = (bg_z3_proc.grab ())
in (let _50_262 = (Support.Microsoft.FStar.Util.kill_process bg)
in (let _50_264 = (bg_z3_proc.release ())
in (let rec aux = (fun ( _50_267 ) -> (match (()) with
| () -> begin
(let _50_271 = (with_monitor job_queue (fun ( _50_268 ) -> (match (()) with
| () -> begin
(let _121_196 = (Support.ST.read pending_jobs)
in (let _121_195 = (let _121_194 = (Support.ST.read job_queue)
in (Support.List.length _121_194))
in (_121_196, _121_195)))
end)))
in (match (_50_271) with
| (n, m) -> begin
(match (((n + m) = 0)) with
| true -> begin
(let _121_197 = (Microsoft_FStar_Tc_Errors.report_all ())
in (Support.All.pipe_right _121_197 Support.Prims.ignore))
end
| false -> begin
(let _50_272 = (Support.Microsoft.FStar.Util.sleep 500)
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

let push = (fun ( msg ) -> (let _50_275 = (let _121_201 = (let _121_200 = (Support.ST.read fresh_scope)
in ((Microsoft_FStar_ToSMT_Term.Caption (msg))::[])::_121_200)
in (Support.ST.op_Colon_Equals fresh_scope _121_201))
in (let _121_203 = (let _121_202 = (Support.ST.read bg_scope)
in (Support.List.append ((Microsoft_FStar_ToSMT_Term.Caption (msg))::(Microsoft_FStar_ToSMT_Term.Push)::[]) _121_202))
in (Support.ST.op_Colon_Equals bg_scope _121_203))))

let pop = (fun ( msg ) -> (let _50_278 = (let _121_207 = (let _121_206 = (Support.ST.read fresh_scope)
in (Support.List.tl _121_206))
in (Support.ST.op_Colon_Equals fresh_scope _121_207))
in (let _121_209 = (let _121_208 = (Support.ST.read bg_scope)
in (Support.List.append ((Microsoft_FStar_ToSMT_Term.Caption (msg))::(Microsoft_FStar_ToSMT_Term.Pop)::[]) _121_208))
in (Support.ST.op_Colon_Equals bg_scope _121_209))))

let giveZ3 = (fun ( decls ) -> (let _50_286 = (match ((Support.ST.read fresh_scope)) with
| hd::tl -> begin
(Support.ST.op_Colon_Equals fresh_scope (((Support.List.append hd decls))::tl))
end
| _50_285 -> begin
(Support.All.failwith "Impossible")
end)
in (let _121_213 = (let _121_212 = (Support.ST.read bg_scope)
in (Support.List.append (Support.List.rev decls) _121_212))
in (Support.ST.op_Colon_Equals bg_scope _121_213))))

let bgtheory = (fun ( fresh ) -> (match (fresh) with
| true -> begin
(let _121_217 = (let _121_216 = (Support.ST.read fresh_scope)
in (Support.List.rev _121_216))
in (Support.All.pipe_right _121_217 Support.List.flatten))
end
| false -> begin
(let bg = (Support.ST.read bg_scope)
in (let _50_290 = (Support.ST.op_Colon_Equals bg_scope [])
in (Support.List.rev bg)))
end))

let refresh = (fun ( _50_292 ) -> (match (()) with
| () -> begin
(let _50_293 = (bg_z3_proc.refresh ())
in (let theory = (bgtheory true)
in (Support.ST.op_Colon_Equals bg_scope (Support.List.rev theory))))
end))

let mark = (fun ( msg ) -> (push msg))

let reset_mark = (fun ( msg ) -> (let _50_298 = (pop msg)
in (refresh ())))

let commit_mark = (fun ( msg ) -> (match ((Support.ST.read fresh_scope)) with
| hd::s::tl -> begin
(Support.ST.op_Colon_Equals fresh_scope (((Support.List.append hd s))::tl))
end
| _50_307 -> begin
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
in (let input = (let _121_234 = (let _121_233 = (let _121_232 = (z3_options ())
in (Microsoft_FStar_ToSMT_Term.declToSmt _121_232))
in (Support.List.map _121_233 theory))
in (Support.All.pipe_right _121_234 (Support.String.concat "\n")))
in (let _50_316 = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(log_query fresh input)
end
| false -> begin
()
end)
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb})))))))




