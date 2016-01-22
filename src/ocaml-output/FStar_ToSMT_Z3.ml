
open Prims
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
| Z3V (_52_4) -> begin
_52_4
end))

let z3v_compare = (fun known _52_9 -> (match (_52_9) with
| (w1, w2, w3) -> begin
(match (known) with
| Z3V_Unknown -> begin
None
end
| Z3V (k1, k2, k3) -> begin
Some (if (k1 <> w1) then begin
(w1 - k1)
end else begin
if (k2 <> w2) then begin
(w2 - k2)
end else begin
(w3 - k3)
end
end)
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

let get_z3version = (fun _52_21 -> (match (()) with
| () -> begin
(let prefix = "Z3 version "
in (match ((FStar_ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(let _52_31 = (let _119_26 = (FStar_ST.read FStar_Options.z3_exe)
in (FStar_Util.run_proc _119_26 "-version" ""))
in (match (_52_31) with
| (_52_27, out, _52_30) -> begin
(let out = (match ((FStar_Util.splitlines out)) with
| x::_52_33 when (FStar_Util.starts_with x prefix) -> begin
(let x = (let _119_27 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _119_27))
in (let x = (FStar_All.try_with (fun _52_38 -> (match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)) (fun _52_37 -> (match (_52_37) with
| _52_41 -> begin
[]
end)))
in (match (x) with
| i1::i2::i3::[] -> begin
Z3V ((i1, i2, i3))
end
| _52_50 -> begin
Z3V_Unknown
end)))
end
| _52_52 -> begin
Z3V_Unknown
end)
in (let _52_54 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))

let ini_params = (fun _52_56 -> (match (()) with
| () -> begin
(let t = if (let _119_32 = (get_z3version ())
in (z3v_le _119_32 (4, 3, 1))) then begin
(FStar_ST.read FStar_Options.z3timeout)
end else begin
((FStar_ST.read FStar_Options.z3timeout) * 1000)
end
in (let timeout = (let _119_33 = (FStar_Util.string_of_int t)
in (FStar_Util.format1 "-t:%s" _119_33))
in (let relevancy = if (let _119_34 = (get_z3version ())
in (z3v_le _119_34 (4, 3, 1))) then begin
"RELEVANCY"
end else begin
"SMT.RELEVANCY"
end
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

let status_to_string = (fun _52_1 -> (match (_52_1) with
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

let tid = (fun _52_65 -> (match (()) with
| () -> begin
(let _119_43 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _119_43 FStar_Util.string_of_int))
end))

let new_z3proc = (fun id -> (let cond = (fun pid s -> (let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (let _119_51 = (FStar_ST.read FStar_Options.z3_exe)
in (let _119_50 = (ini_params ())
in (FStar_Util.start_process id _119_51 _119_50 cond)))))

type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}

let is_Mkbgproc = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbgproc"))))

let queries_dot_smt2 = (FStar_Util.mk_ref None)

let get_qfile = (let ctr = (FStar_Util.mk_ref 0)
in (fun fresh -> if fresh then begin
(let _52_77 = (FStar_Util.incr ctr)
in (let _119_84 = (let _119_83 = (let _119_82 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _119_82))
in (FStar_Util.format1 "queries-%s.smt2" _119_83))
in (FStar_Util.open_file_for_writing _119_84)))
end else begin
(match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
(let fh = (FStar_Util.open_file_for_writing "queries-bg-0.smt2")
in (let _52_81 = (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
in fh))
end
| Some (fh) -> begin
fh
end)
end))

let log_query = (fun fresh i -> (let fh = (get_qfile fresh)
in (let _52_88 = (FStar_Util.append_to_file fh i)
in if fresh then begin
(FStar_Util.close_file fh)
end else begin
()
end)))

let bg_z3_proc = (let ctr = (FStar_Util.mk_ref (- (1)))
in (let new_proc = (fun _52_92 -> (match (()) with
| () -> begin
(let _119_93 = (let _119_92 = (let _52_93 = (FStar_Util.incr ctr)
in (let _119_91 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _119_91 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _119_92))
in (new_z3proc _119_93))
end))
in (let z3proc = (let _119_94 = (new_proc ())
in (FStar_Util.mk_ref _119_94))
in (let x = []
in (let grab = (fun _52_98 -> (match (()) with
| () -> begin
(let _52_99 = (FStar_Util.monitor_enter x)
in (FStar_ST.read z3proc))
end))
in (let release = (fun _52_102 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (let refresh = (fun _52_104 -> (match (()) with
| () -> begin
(let proc = (grab ())
in (let _52_106 = (FStar_Util.kill_process proc)
in (let _52_108 = (let _119_101 = (new_proc ())
in (FStar_ST.op_Colon_Equals z3proc _119_101))
in (let _52_116 = (match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
()
end
| Some (fh) -> begin
(let _52_113 = (FStar_Util.close_file fh)
in (let fh = (let _119_104 = (let _119_103 = (let _119_102 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _119_102 FStar_Util.string_of_int))
in (FStar_Util.format1 "queries-bg-%s.smt2" _119_103))
in (FStar_Util.open_file_for_writing _119_104))
in (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))))
end)
in (release ())))))
end))
in {grab = grab; release = release; refresh = refresh})))))))

let doZ3Exe' = (fun input z3proc -> (let parse = (fun z3out -> (let lines = (FStar_All.pipe_right (FStar_String.split (('\n')::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (let rec lblnegs = (fun lines -> (match (lines) with
| lname::"false"::rest -> begin
(let _119_113 = (lblnegs rest)
in (lname)::_119_113)
end
| lname::_52_132::rest -> begin
(lblnegs rest)
end
| _52_137 -> begin
[]
end))
in (let rec result = (fun x -> (match (x) with
| "timeout"::tl -> begin
(TIMEOUT, [])
end
| "unknown"::tl -> begin
(let _119_116 = (lblnegs tl)
in (UNKNOWN, _119_116))
end
| "sat"::tl -> begin
(let _119_117 = (lblnegs tl)
in (SAT, _119_117))
end
| "unsat"::tl -> begin
(UNSAT, [])
end
| _52_154::tl -> begin
(result tl)
end
| _52_157 -> begin
(let _119_121 = (let _119_120 = (let _119_119 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _119_119))
in (FStar_Util.format1 "Got output lines: %s\n" _119_120))
in (FStar_All.pipe_left FStar_All.failwith _119_121))
end))
in (result lines)))))
in (let stdout = (FStar_Util.ask_process z3proc input)
in (parse (FStar_Util.trim_string stdout)))))

let doZ3Exe = (let ctr = (FStar_Util.mk_ref 0)
in (fun fresh input -> (let z3proc = if fresh then begin
(let _52_163 = (FStar_Util.incr ctr)
in (let _119_127 = (let _119_126 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _119_126))
in (new_z3proc _119_127)))
end else begin
(bg_z3_proc.grab ())
end
in (let res = (doZ3Exe' input z3proc)
in (let _52_167 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))

let z3_options = (fun _52_169 -> (match (()) with
| () -> begin
(let mbqi = if (let _119_130 = (get_z3version ())
in (z3v_le _119_130 (4, 3, 1))) then begin
"mbqi"
end else begin
"smt.mbqi"
end
in (let model_on_timeout = if (let _119_131 = (get_z3version ())
in (z3v_le _119_131 (4, 3, 1))) then begin
"(set-option :model-on-timeout true)\n"
end else begin
""
end
in (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "(set-option :global-decls false)\n" "(set-option :") mbqi) " false)\n") model_on_timeout)))
end))

type 'a job =
{job : Prims.unit  ->  'a; callback : 'a  ->  Prims.unit}

let is_Mkjob = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkjob"))))

type z3job =
(Prims.bool * (Prims.string * FStar_Range.range) Prims.list) job

let job_queue = (let x = (FStar_Util.mk_ref (({job = (fun _52_176 -> (match (()) with
| () -> begin
(let _119_155 = (let _119_154 = (let _119_153 = (FStar_Range.mk_range "" 0 0)
in ("", _119_153))
in (_119_154)::[])
in (false, _119_155))
end)); callback = (fun a -> ())})::[]))
in (let _52_179 = (FStar_ST.op_Colon_Equals x [])
in x))

let pending_jobs = (FStar_Util.mk_ref 0)

let with_monitor = (fun m f -> (let _52_183 = (FStar_Util.monitor_enter m)
in (let res = (f ())
in (let _52_186 = (FStar_Util.monitor_exit m)
in res))))

let z3_job = (fun fresh label_messages input _52_191 -> (match (()) with
| () -> begin
(let _52_194 = (doZ3Exe fresh input)
in (match (_52_194) with
| (status, lblnegs) -> begin
(let result = (match (status) with
| UNSAT -> begin
(true, [])
end
| _52_197 -> begin
(let _52_198 = if ((FStar_ST.read FStar_Options.debug) <> []) then begin
(let _119_166 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _119_166))
end else begin
()
end
in (let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _52_206 -> (match (_52_206) with
| (m, _52_203, _52_205) -> begin
((Prims.fst m) = l)
end))))) with
| None -> begin
[]
end
| Some (_52_209, msg, r) -> begin
((msg, r))::[]
end))))
in (false, failing_assertions)))
end)
in result)
end))
end))

let rec dequeue' = (fun _52_216 -> (match (()) with
| () -> begin
(let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| hd::tl -> begin
(let _52_221 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (let _52_224 = (FStar_Util.incr pending_jobs)
in (let _52_226 = (FStar_Util.monitor_exit job_queue)
in (let _52_228 = (run_job j)
in (let _52_231 = (with_monitor job_queue (fun _52_230 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (let _52_233 = (dequeue ())
in ()))))))
end))
and dequeue = (fun _52_235 -> (match (()) with
| () -> begin
(let _52_236 = (FStar_Util.monitor_enter job_queue)
in (let rec aux = (fun _52_239 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(let _52_241 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _52_244 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job = (fun j -> (let _119_178 = (j.job ())
in (FStar_All.pipe_left j.callback _119_178)))

let init = (fun _52_246 -> (match (()) with
| () -> begin
(let n_runners = ((FStar_ST.read FStar_Options.n_cores) - 1)
in (let rec aux = (fun n -> if (n = 0) then begin
()
end else begin
(let _52_250 = (FStar_Util.spawn dequeue)
in (aux (n - 1)))
end)
in (aux n_runners)))
end))

let enqueue = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(let _52_254 = (FStar_Util.monitor_enter job_queue)
in (let _52_256 = (let _119_188 = (let _119_187 = (FStar_ST.read job_queue)
in (FStar_List.append _119_187 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _119_188))
in (let _52_258 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)

let finish = (fun _52_260 -> (match (()) with
| () -> begin
(let bg = (bg_z3_proc.grab ())
in (let _52_262 = (FStar_Util.kill_process bg)
in (let _52_264 = (bg_z3_proc.release ())
in (let rec aux = (fun _52_267 -> (match (()) with
| () -> begin
(let _52_271 = (with_monitor job_queue (fun _52_268 -> (match (()) with
| () -> begin
(let _119_196 = (FStar_ST.read pending_jobs)
in (let _119_195 = (let _119_194 = (FStar_ST.read job_queue)
in (FStar_List.length _119_194))
in (_119_196, _119_195)))
end)))
in (match (_52_271) with
| (n, m) -> begin
if ((n + m) = 0) then begin
(let _119_197 = (FStar_Tc_Errors.report_all ())
in (FStar_All.pipe_right _119_197 Prims.ignore))
end else begin
(let _52_272 = (FStar_Util.sleep 500)
in (aux ()))
end
end))
end))
in (aux ())))))
end))

type scope_t =
FStar_ToSMT_Term.decl Prims.list Prims.list

let fresh_scope = (FStar_Util.mk_ref (([])::[]))

let bg_scope = (FStar_Util.mk_ref [])

let push = (fun msg -> (let _52_275 = (let _119_201 = (let _119_200 = (FStar_ST.read fresh_scope)
in ((FStar_ToSMT_Term.Caption (msg))::[])::_119_200)
in (FStar_ST.op_Colon_Equals fresh_scope _119_201))
in (let _119_203 = (let _119_202 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::(FStar_ToSMT_Term.Push)::[]) _119_202))
in (FStar_ST.op_Colon_Equals bg_scope _119_203))))

let pop = (fun msg -> (let _52_278 = (let _119_207 = (let _119_206 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _119_206))
in (FStar_ST.op_Colon_Equals fresh_scope _119_207))
in (let _119_209 = (let _119_208 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::(FStar_ToSMT_Term.Pop)::[]) _119_208))
in (FStar_ST.op_Colon_Equals bg_scope _119_209))))

let giveZ3 = (fun decls -> (let _52_286 = (match ((FStar_ST.read fresh_scope)) with
| hd::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _52_285 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _119_213 = (let _119_212 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _119_212))
in (FStar_ST.op_Colon_Equals bg_scope _119_213))))

let bgtheory = (fun fresh -> if fresh then begin
(let _119_217 = (let _119_216 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _119_216))
in (FStar_All.pipe_right _119_217 FStar_List.flatten))
end else begin
(let bg = (FStar_ST.read bg_scope)
in (let _52_290 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)

let refresh = (fun _52_292 -> (match (()) with
| () -> begin
(let _52_293 = (bg_z3_proc.refresh ())
in (let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))

let mark = (fun msg -> (push msg))

let reset_mark = (fun msg -> (let _52_298 = (pop msg)
in (refresh ())))

let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| hd::s::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _52_307 -> begin
(FStar_All.failwith "Impossible")
end))

let ask = (fun fresh label_messages qry cb -> (let fresh = (fresh && ((FStar_ST.read FStar_Options.n_cores) > 1))
in (let theory = (bgtheory fresh)
in (let theory = if fresh then begin
(FStar_List.append theory qry)
end else begin
(FStar_List.append (FStar_List.append (FStar_List.append theory ((FStar_ToSMT_Term.Push)::[])) qry) ((FStar_ToSMT_Term.Pop)::[]))
end
in (let input = (let _119_234 = (let _119_233 = (let _119_232 = (z3_options ())
in (FStar_ToSMT_Term.declToSmt _119_232))
in (FStar_List.map _119_233 theory))
in (FStar_All.pipe_right _119_234 (FStar_String.concat "\n")))
in (let _52_316 = if (FStar_ST.read FStar_Options.logQueries) then begin
(log_query fresh input)
end else begin
()
end
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb})))))))




