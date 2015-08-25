
type z3version =
| Z3V_Unknown
| Z3V of (Prims.int * Prims.int * Prims.int)

let is_Z3V_Unknown = (fun _discr_ -> (match (_discr_) with
| Z3V_Unknown -> begin
true
end
| _ -> begin
false
end))

let is_Z3V = (fun _discr_ -> (match (_discr_) with
| Z3V (_) -> begin
true
end
| _ -> begin
false
end))

let ___Z3V____0 = (fun projectee -> (match (projectee) with
| Z3V (_50_4) -> begin
_50_4
end))

let z3v_compare = (fun known _50_9 -> (match (_50_9) with
| (w1, w2, w3) -> begin
(match (known) with
| Z3V_Unknown -> begin
None
end
| Z3V (k1, k2, k3) -> begin
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

let z3v_le = (fun known wanted -> (match ((z3v_compare known wanted)) with
| None -> begin
false
end
| Some (i) -> begin
(i >= 0)
end))

let _z3version = (FStar_Util.mk_ref None)

let get_z3version = (fun _50_21 -> (match (()) with
| () -> begin
(let prefix = "Z3 version "
in (match ((FStar_ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(let _50_31 = (let _116_26 = (FStar_ST.read FStar_Options.z3_exe)
in (FStar_Util.run_proc _116_26 "-version" ""))
in (match (_50_31) with
| (_50_27, out, _50_30) -> begin
(let out = (match ((FStar_Util.splitlines out)) with
| x::_50_33 when (FStar_Util.starts_with x prefix) -> begin
(let x = (let _116_27 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _116_27))
in (let x = (FStar_All.try_with (fun _50_38 -> (match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)) (fun _50_37 -> (match (_50_37) with
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
in (let _50_54 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))

let ini_params = (fun _50_56 -> (match (()) with
| () -> begin
(let t = (match ((let _116_32 = (get_z3version ())
in (z3v_le _116_32 (4, 3, 1)))) with
| true -> begin
(FStar_ST.read FStar_Options.z3timeout)
end
| false -> begin
((FStar_ST.read FStar_Options.z3timeout) * 1000)
end)
in (let timeout = (let _116_33 = (FStar_Util.string_of_int t)
in (FStar_Util.format1 "-t:%s" _116_33))
in (let relevancy = (match ((let _116_34 = (get_z3version ())
in (z3v_le _116_34 (4, 3, 1)))) with
| true -> begin
"RELEVANCY"
end
| false -> begin
"SMT.RELEVANCY"
end)
in (FStar_Util.format2 "-smt2 -in %s AUTO_CONFIG=false MODEL=true %s=2" timeout relevancy))))
end))

type z3status =
| SAT
| UNSAT
| UNKNOWN
| TIMEOUT

let is_SAT = (fun _discr_ -> (match (_discr_) with
| SAT -> begin
true
end
| _ -> begin
false
end))

let is_UNSAT = (fun _discr_ -> (match (_discr_) with
| UNSAT -> begin
true
end
| _ -> begin
false
end))

let is_UNKNOWN = (fun _discr_ -> (match (_discr_) with
| UNKNOWN -> begin
true
end
| _ -> begin
false
end))

let is_TIMEOUT = (fun _discr_ -> (match (_discr_) with
| TIMEOUT -> begin
true
end
| _ -> begin
false
end))

let status_to_string = (fun _50_1 -> (match (_50_1) with
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

let tid = (fun _50_65 -> (match (()) with
| () -> begin
(let _116_43 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _116_43 FStar_Util.string_of_int))
end))

let new_z3proc = (fun id -> (let cond = (fun pid s -> (let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (let _116_51 = (FStar_ST.read FStar_Options.z3_exe)
in (let _116_50 = (ini_params ())
in (FStar_Util.start_process id _116_51 _116_50 cond)))))

type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}

let is_Mkbgproc = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbgproc"))

let queries_dot_smt2 = (FStar_Util.mk_ref None)

let get_qfile = (let ctr = (FStar_Util.mk_ref 0)
in (fun fresh -> (match (fresh) with
| true -> begin
(let _50_77 = (FStar_Util.incr ctr)
in (let _116_84 = (let _116_83 = (let _116_82 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _116_82))
in (FStar_Util.format1 "queries-%s.smt2" _116_83))
in (FStar_Util.open_file_for_writing _116_84)))
end
| false -> begin
(match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
(let fh = (FStar_Util.open_file_for_writing "queries-bg-0.smt2")
in (let _50_81 = (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
in fh))
end
| Some (fh) -> begin
fh
end)
end)))

let log_query = (fun fresh i -> (let fh = (get_qfile fresh)
in (let _50_88 = (FStar_Util.append_to_file fh i)
in (match (fresh) with
| true -> begin
(FStar_Util.close_file fh)
end
| false -> begin
()
end))))

let bg_z3_proc = (let ctr = (FStar_Util.mk_ref (- (1)))
in (let new_proc = (fun _50_92 -> (match (()) with
| () -> begin
(let _116_93 = (let _116_92 = (let _50_93 = (FStar_Util.incr ctr)
in (let _116_91 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _116_91 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _116_92))
in (new_z3proc _116_93))
end))
in (let z3proc = (let _116_94 = (new_proc ())
in (FStar_Util.mk_ref _116_94))
in (let x = []
in (let grab = (fun _50_98 -> (match (()) with
| () -> begin
(let _50_99 = (FStar_Util.monitor_enter x)
in (FStar_ST.read z3proc))
end))
in (let release = (fun _50_102 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (let refresh = (fun _50_104 -> (match (()) with
| () -> begin
(let proc = (grab ())
in (let _50_106 = (FStar_Util.kill_process proc)
in (let _50_108 = (let _116_101 = (new_proc ())
in (FStar_ST.op_Colon_Equals z3proc _116_101))
in (let _50_116 = (match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
()
end
| Some (fh) -> begin
(let _50_113 = (FStar_Util.close_file fh)
in (let fh = (let _116_104 = (let _116_103 = (let _116_102 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _116_102 FStar_Util.string_of_int))
in (FStar_Util.format1 "queries-bg-%s.smt2" _116_103))
in (FStar_Util.open_file_for_writing _116_104))
in (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))))
end)
in (release ())))))
end))
in {grab = grab; release = release; refresh = refresh})))))))

let doZ3Exe' = (fun input z3proc -> (let parse = (fun z3out -> (let lines = (FStar_All.pipe_right (FStar_String.split (('\n')::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (let rec lblnegs = (fun lines -> (match (lines) with
| lname::"false"::rest -> begin
(let _116_113 = (lblnegs rest)
in (lname)::_116_113)
end
| lname::_50_132::rest -> begin
(lblnegs rest)
end
| _50_137 -> begin
[]
end))
in (let rec result = (fun x -> (match (x) with
| "timeout"::tl -> begin
(TIMEOUT, [])
end
| "unknown"::tl -> begin
(let _116_116 = (lblnegs tl)
in (UNKNOWN, _116_116))
end
| "sat"::tl -> begin
(let _116_117 = (lblnegs tl)
in (SAT, _116_117))
end
| "unsat"::tl -> begin
(UNSAT, [])
end
| _50_154::tl -> begin
(result tl)
end
| _50_157 -> begin
(let _116_121 = (let _116_120 = (let _116_119 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _116_119))
in (FStar_Util.format1 "Got output lines: %s\n" _116_120))
in (FStar_All.pipe_left FStar_All.failwith _116_121))
end))
in (result lines)))))
in (let stdout = (FStar_Util.ask_process z3proc input)
in (parse (FStar_Util.trim_string stdout)))))

let doZ3Exe = (let ctr = (FStar_Util.mk_ref 0)
in (fun fresh input -> (let z3proc = (match (fresh) with
| true -> begin
(let _50_163 = (FStar_Util.incr ctr)
in (let _116_127 = (let _116_126 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _116_126))
in (new_z3proc _116_127)))
end
| false -> begin
(bg_z3_proc.grab ())
end)
in (let res = (doZ3Exe' input z3proc)
in (let _50_167 = (match (fresh) with
| true -> begin
(FStar_Util.kill_process z3proc)
end
| false -> begin
(bg_z3_proc.release ())
end)
in res)))))

let z3_options = (fun _50_169 -> (match (()) with
| () -> begin
(let mbqi = (match ((let _116_130 = (get_z3version ())
in (z3v_le _116_130 (4, 3, 1)))) with
| true -> begin
"mbqi"
end
| false -> begin
"smt.mbqi"
end)
in (let model_on_timeout = (match ((let _116_131 = (get_z3version ())
in (z3v_le _116_131 (4, 3, 1)))) with
| true -> begin
"(set-option :model-on-timeout true)\n"
end
| false -> begin
""
end)
in (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "(set-option :global-decls false)\n" "(set-option :") mbqi) " false)\n") model_on_timeout)))
end))

type 'a job =
{job : Prims.unit  ->  'a; callback : 'a  ->  Prims.unit}

let is_Mkjob = (fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkjob"))

type z3job =
(Prims.bool * (Prims.string * FStar_Range.range) Prims.list) job

let job_queue = (let x = (FStar_Util.mk_ref (({job = (fun _50_176 -> (match (()) with
| () -> begin
(let _116_155 = (let _116_154 = (let _116_153 = (FStar_Range.mk_range "" 0 0)
in ("", _116_153))
in (_116_154)::[])
in (false, _116_155))
end)); callback = (fun a -> ())})::[]))
in (let _50_179 = (FStar_ST.op_Colon_Equals x [])
in x))

let pending_jobs = (FStar_Util.mk_ref 0)

let with_monitor = (fun m f -> (let _50_183 = (FStar_Util.monitor_enter m)
in (let res = (f ())
in (let _50_186 = (FStar_Util.monitor_exit m)
in res))))

let z3_job = (fun fresh label_messages input _50_191 -> (match (()) with
| () -> begin
(let _50_194 = (doZ3Exe fresh input)
in (match (_50_194) with
| (status, lblnegs) -> begin
(let result = (match (status) with
| UNSAT -> begin
(true, [])
end
| _50_197 -> begin
(let _50_198 = (match (((FStar_ST.read FStar_Options.debug) <> [])) with
| true -> begin
(let _116_166 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _116_166))
end
| false -> begin
()
end)
in (let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _50_206 -> (match (_50_206) with
| (m, _50_203, _50_205) -> begin
((Prims.fst m) = l)
end))))) with
| None -> begin
[]
end
| Some (_50_209, msg, r) -> begin
((msg, r))::[]
end))))
in (false, failing_assertions)))
end)
in result)
end))
end))

let rec dequeue' = (fun _50_216 -> (match (()) with
| () -> begin
(let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| hd::tl -> begin
(let _50_221 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (let _50_224 = (FStar_Util.incr pending_jobs)
in (let _50_226 = (FStar_Util.monitor_exit job_queue)
in (let _50_228 = (run_job j)
in (let _50_231 = (with_monitor job_queue (fun _50_230 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (let _50_233 = (dequeue ())
in ()))))))
end))
and dequeue = (fun _50_235 -> (match (()) with
| () -> begin
(let _50_236 = (FStar_Util.monitor_enter job_queue)
in (let rec aux = (fun _50_239 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(let _50_241 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _50_244 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job = (fun j -> (let _116_178 = (j.job ())
in (FStar_All.pipe_left j.callback _116_178)))

let init = (fun _50_246 -> (match (()) with
| () -> begin
(let n_runners = ((FStar_ST.read FStar_Options.n_cores) - 1)
in (let rec aux = (fun n -> (match ((n = 0)) with
| true -> begin
()
end
| false -> begin
(let _50_250 = (FStar_Util.spawn dequeue)
in (aux (n - 1)))
end))
in (aux n_runners)))
end))

let enqueue = (fun fresh j -> (match ((not (fresh))) with
| true -> begin
(run_job j)
end
| false -> begin
(let _50_254 = (FStar_Util.monitor_enter job_queue)
in (let _50_256 = (let _116_188 = (let _116_187 = (FStar_ST.read job_queue)
in (FStar_List.append _116_187 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _116_188))
in (let _50_258 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end))

let finish = (fun _50_260 -> (match (()) with
| () -> begin
(let bg = (bg_z3_proc.grab ())
in (let _50_262 = (FStar_Util.kill_process bg)
in (let _50_264 = (bg_z3_proc.release ())
in (let rec aux = (fun _50_267 -> (match (()) with
| () -> begin
(let _50_271 = (with_monitor job_queue (fun _50_268 -> (match (()) with
| () -> begin
(let _116_196 = (FStar_ST.read pending_jobs)
in (let _116_195 = (let _116_194 = (FStar_ST.read job_queue)
in (FStar_List.length _116_194))
in (_116_196, _116_195)))
end)))
in (match (_50_271) with
| (n, m) -> begin
(match (((n + m) = 0)) with
| true -> begin
(let _116_197 = (FStar_Tc_Errors.report_all ())
in (FStar_All.pipe_right _116_197 Prims.ignore))
end
| false -> begin
(let _50_272 = (FStar_Util.sleep 500)
in (aux ()))
end)
end))
end))
in (aux ())))))
end))

type scope_t =
FStar_ToSMT_Term.decl Prims.list Prims.list

let fresh_scope = (FStar_Util.mk_ref (([])::[]))

let bg_scope = (FStar_Util.mk_ref [])

let push = (fun msg -> (let _50_275 = (let _116_201 = (let _116_200 = (FStar_ST.read fresh_scope)
in ((FStar_ToSMT_Term.Caption (msg))::[])::_116_200)
in (FStar_ST.op_Colon_Equals fresh_scope _116_201))
in (let _116_203 = (let _116_202 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::(FStar_ToSMT_Term.Push)::[]) _116_202))
in (FStar_ST.op_Colon_Equals bg_scope _116_203))))

let pop = (fun msg -> (let _50_278 = (let _116_207 = (let _116_206 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _116_206))
in (FStar_ST.op_Colon_Equals fresh_scope _116_207))
in (let _116_209 = (let _116_208 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::(FStar_ToSMT_Term.Pop)::[]) _116_208))
in (FStar_ST.op_Colon_Equals bg_scope _116_209))))

let giveZ3 = (fun decls -> (let _50_286 = (match ((FStar_ST.read fresh_scope)) with
| hd::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _50_285 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _116_213 = (let _116_212 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _116_212))
in (FStar_ST.op_Colon_Equals bg_scope _116_213))))

let bgtheory = (fun fresh -> (match (fresh) with
| true -> begin
(let _116_217 = (let _116_216 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _116_216))
in (FStar_All.pipe_right _116_217 FStar_List.flatten))
end
| false -> begin
(let bg = (FStar_ST.read bg_scope)
in (let _50_290 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end))

let refresh = (fun _50_292 -> (match (()) with
| () -> begin
(let _50_293 = (bg_z3_proc.refresh ())
in (let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))

let mark = (fun msg -> (push msg))

let reset_mark = (fun msg -> (let _50_298 = (pop msg)
in (refresh ())))

let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| hd::s::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _50_307 -> begin
(FStar_All.failwith "Impossible")
end))

let ask = (fun fresh label_messages qry cb -> (let fresh = (fresh && ((FStar_ST.read FStar_Options.n_cores) > 1))
in (let theory = (bgtheory fresh)
in (let theory = (match (fresh) with
| true -> begin
(FStar_List.append theory qry)
end
| false -> begin
(FStar_List.append (FStar_List.append (FStar_List.append theory ((FStar_ToSMT_Term.Push)::[])) qry) ((FStar_ToSMT_Term.Pop)::[]))
end)
in (let input = (let _116_234 = (let _116_233 = (let _116_232 = (z3_options ())
in (FStar_ToSMT_Term.declToSmt _116_232))
in (FStar_List.map _116_233 theory))
in (FStar_All.pipe_right _116_234 (FStar_String.concat "\n")))
in (let _50_316 = (match ((FStar_ST.read FStar_Options.logQueries)) with
| true -> begin
(log_query fresh input)
end
| false -> begin
()
end)
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb})))))))




