
open Prims
type z3version =
| Z3V_Unknown
| Z3V of (Prims.int * Prims.int * Prims.int)

let is_Z3V_Unknown : z3version  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Z3V_Unknown -> begin
true
end
| _ -> begin
false
end))

let is_Z3V : z3version  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Z3V (_) -> begin
true
end
| _ -> begin
false
end))

let ___Z3V____0 : z3version  ->  (Prims.int * Prims.int * Prims.int) = (fun projectee -> (match (projectee) with
| Z3V (_99_4) -> begin
_99_4
end))

let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _99_9 -> (match (_99_9) with
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

let z3v_le : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.bool = (fun known wanted -> (match ((z3v_compare known wanted)) with
| None -> begin
false
end
| Some (i) -> begin
(i >= 0)
end))

let _z3version : z3version Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

let get_z3version : Prims.unit  ->  z3version = (fun _99_21 -> (match (()) with
| () -> begin
(let prefix = "Z3 version "
in (match ((FStar_ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(let _99_31 = (let _201_26 = (FStar_ST.read FStar_Options.z3_exe)
in (FStar_Util.run_proc _201_26 "-version" ""))
in (match (_99_31) with
| (_99_27, out, _99_30) -> begin
(let out = (match ((FStar_Util.splitlines out)) with
| x::_99_33 when (FStar_Util.starts_with x prefix) -> begin
(let x = (let _201_27 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _201_27))
in (let x = (FStar_All.try_with (fun _99_38 -> (match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)) (fun _99_37 -> (match (_99_37) with
| _99_41 -> begin
[]
end)))
in (match (x) with
| i1::i2::i3::[] -> begin
Z3V ((i1, i2, i3))
end
| _99_50 -> begin
Z3V_Unknown
end)))
end
| _99_52 -> begin
Z3V_Unknown
end)
in (let _99_54 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))

let ini_params : Prims.unit  ->  Prims.string = (fun _99_56 -> (match (()) with
| () -> begin
(let t = if (let _201_32 = (get_z3version ())
in (z3v_le _201_32 (4, 3, 1))) then begin
(FStar_ST.read FStar_Options.z3timeout)
end else begin
((FStar_ST.read FStar_Options.z3timeout) * 1000)
end
in (let timeout = (let _201_33 = (FStar_Util.string_of_int t)
in (FStar_Util.format1 "-t:%s" _201_33))
in (let relevancy = if (let _201_34 = (get_z3version ())
in (z3v_le _201_34 (4, 3, 1))) then begin
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

let is_SAT : z3status  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| SAT -> begin
true
end
| _ -> begin
false
end))

let is_UNSAT : z3status  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| UNSAT -> begin
true
end
| _ -> begin
false
end))

let is_UNKNOWN : z3status  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| UNKNOWN -> begin
true
end
| _ -> begin
false
end))

let is_TIMEOUT : z3status  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| TIMEOUT -> begin
true
end
| _ -> begin
false
end))

let status_to_string : z3status  ->  Prims.string = (fun _99_1 -> (match (_99_1) with
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

let tid : Prims.unit  ->  Prims.string = (fun _99_65 -> (match (()) with
| () -> begin
(let _201_43 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _201_43 FStar_Util.string_of_int))
end))

let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (let cond = (fun pid s -> (let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (let _201_51 = (FStar_ST.read FStar_Options.z3_exe)
in (let _201_50 = (ini_params ())
in (FStar_Util.start_process id _201_51 _201_50 cond)))))

type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}

let is_Mkbgproc : bgproc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbgproc"))))

let queries_dot_smt2 : FStar_Util.file_handle Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

let get_qfile : Prims.bool  ->  FStar_Util.file_handle = (let ctr = (FStar_Util.mk_ref 0)
in (fun fresh -> if fresh then begin
(let _99_77 = (FStar_Util.incr ctr)
in (let _201_84 = (let _201_83 = (let _201_82 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _201_82))
in (FStar_Util.format1 "queries-%s.smt2" _201_83))
in (FStar_Util.open_file_for_writing _201_84)))
end else begin
(match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
(let fh = (FStar_Util.open_file_for_writing "queries-bg-0.smt2")
in (let _99_81 = (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
in fh))
end
| Some (fh) -> begin
fh
end)
end))

let log_query : Prims.bool  ->  Prims.string  ->  Prims.unit = (fun fresh i -> (let fh = (get_qfile fresh)
in (let _99_88 = (FStar_Util.append_to_file fh i)
in if fresh then begin
(FStar_Util.close_file fh)
end else begin
()
end)))

let bg_z3_proc : bgproc = (let ctr = (FStar_Util.mk_ref (- (1)))
in (let new_proc = (fun _99_92 -> (match (()) with
| () -> begin
(let _201_93 = (let _201_92 = (let _99_93 = (FStar_Util.incr ctr)
in (let _201_91 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _201_91 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _201_92))
in (new_z3proc _201_93))
end))
in (let z3proc = (let _201_94 = (new_proc ())
in (FStar_Util.mk_ref _201_94))
in (let x = []
in (let grab = (fun _99_98 -> (match (()) with
| () -> begin
(let _99_99 = (FStar_Util.monitor_enter x)
in (FStar_ST.read z3proc))
end))
in (let release = (fun _99_102 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (let refresh = (fun _99_104 -> (match (()) with
| () -> begin
(let proc = (grab ())
in (let _99_106 = (FStar_Util.kill_process proc)
in (let _99_108 = (let _201_101 = (new_proc ())
in (FStar_ST.op_Colon_Equals z3proc _201_101))
in (let _99_116 = (match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
()
end
| Some (fh) -> begin
(let _99_113 = (FStar_Util.close_file fh)
in (let fh = (let _201_104 = (let _201_103 = (let _201_102 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _201_102 FStar_Util.string_of_int))
in (FStar_Util.format1 "queries-bg-%s.smt2" _201_103))
in (FStar_Util.open_file_for_writing _201_104))
in (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))))
end)
in (release ())))))
end))
in {grab = grab; release = release; refresh = refresh})))))))

let doZ3Exe' : Prims.string  ->  FStar_Util.proc  ->  (z3status * Prims.string Prims.list) = (fun input z3proc -> (let parse = (fun z3out -> (let lines = (FStar_All.pipe_right (FStar_String.split (('\n')::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (let rec lblnegs = (fun lines -> (match (lines) with
| lname::"false"::rest -> begin
(let _201_113 = (lblnegs rest)
in (lname)::_201_113)
end
| lname::_99_132::rest -> begin
(lblnegs rest)
end
| _99_137 -> begin
[]
end))
in (let rec result = (fun x -> (match (x) with
| "timeout"::tl -> begin
(TIMEOUT, [])
end
| "unknown"::tl -> begin
(let _201_116 = (lblnegs tl)
in (UNKNOWN, _201_116))
end
| "sat"::tl -> begin
(let _201_117 = (lblnegs tl)
in (SAT, _201_117))
end
| "unsat"::tl -> begin
(UNSAT, [])
end
| _99_154::tl -> begin
(result tl)
end
| _99_157 -> begin
(let _201_121 = (let _201_120 = (let _201_119 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _201_119))
in (FStar_Util.format1 "Got output lines: %s\n" _201_120))
in (FStar_All.pipe_left FStar_All.failwith _201_121))
end))
in (result lines)))))
in (let stdout = (FStar_Util.ask_process z3proc input)
in (parse (FStar_Util.trim_string stdout)))))

let doZ3Exe : Prims.bool  ->  Prims.string  ->  (z3status * Prims.string Prims.list) = (let ctr = (FStar_Util.mk_ref 0)
in (fun fresh input -> (let z3proc = if fresh then begin
(let _99_163 = (FStar_Util.incr ctr)
in (let _201_127 = (let _201_126 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _201_126))
in (new_z3proc _201_127)))
end else begin
(bg_z3_proc.grab ())
end
in (let res = (doZ3Exe' input z3proc)
in (let _99_167 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))

let z3_options : Prims.unit  ->  Prims.string = (fun _99_169 -> (match (()) with
| () -> begin
(let mbqi = if (let _201_130 = (get_z3version ())
in (z3v_le _201_130 (4, 3, 1))) then begin
"mbqi"
end else begin
"smt.mbqi"
end
in (let model_on_timeout = if (let _201_131 = (get_z3version ())
in (z3v_le _201_131 (4, 3, 1))) then begin
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

let job_queue : z3job Prims.list FStar_ST.ref = (let x = (FStar_Util.mk_ref (({job = (fun _99_176 -> (match (()) with
| () -> begin
(let _201_155 = (let _201_154 = (let _201_153 = (FStar_Range.mk_range "" 0 0)
in ("", _201_153))
in (_201_154)::[])
in (false, _201_155))
end)); callback = (fun a -> ())})::[]))
in (let _99_179 = (FStar_ST.op_Colon_Equals x [])
in x))

let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 0)

let with_monitor = (fun m f -> (let _99_183 = (FStar_Util.monitor_enter m)
in (let res = (f ())
in (let _99_186 = (FStar_Util.monitor_exit m)
in res))))

let z3_job = (fun fresh label_messages input _99_191 -> (match (()) with
| () -> begin
(let _99_194 = (doZ3Exe fresh input)
in (match (_99_194) with
| (status, lblnegs) -> begin
(let result = (match (status) with
| UNSAT -> begin
(true, [])
end
| _99_197 -> begin
(let _99_198 = if ((FStar_ST.read FStar_Options.debug) <> []) then begin
(let _201_166 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _201_166))
end else begin
()
end
in (let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _99_206 -> (match (_99_206) with
| (m, _99_203, _99_205) -> begin
((Prims.fst m) = l)
end))))) with
| None -> begin
[]
end
| Some (_99_209, msg, r) -> begin
((msg, r))::[]
end))))
in (false, failing_assertions)))
end)
in result)
end))
end))

let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _99_216 -> (match (()) with
| () -> begin
(let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| hd::tl -> begin
(let _99_221 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (let _99_224 = (FStar_Util.incr pending_jobs)
in (let _99_226 = (FStar_Util.monitor_exit job_queue)
in (let _99_228 = (run_job j)
in (let _99_231 = (with_monitor job_queue (fun _99_230 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (let _99_233 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _99_235 -> (match (()) with
| () -> begin
(let _99_236 = (FStar_Util.monitor_enter job_queue)
in (let rec aux = (fun _99_239 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(let _99_241 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _99_244 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _201_178 = (j.job ())
in (FStar_All.pipe_left j.callback _201_178)))

let init : Prims.unit  ->  Prims.unit = (fun _99_246 -> (match (()) with
| () -> begin
(let n_runners = ((FStar_ST.read FStar_Options.n_cores) - 1)
in (let rec aux = (fun n -> if (n = 0) then begin
()
end else begin
(let _99_250 = (FStar_Util.spawn dequeue)
in (aux (n - 1)))
end)
in (aux n_runners)))
end))

let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(let _99_254 = (FStar_Util.monitor_enter job_queue)
in (let _99_256 = (let _201_188 = (let _201_187 = (FStar_ST.read job_queue)
in (FStar_List.append _201_187 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _201_188))
in (let _99_258 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)

let finish : Prims.unit  ->  Prims.unit = (fun _99_260 -> (match (()) with
| () -> begin
(let bg = (bg_z3_proc.grab ())
in (let _99_262 = (FStar_Util.kill_process bg)
in (let _99_264 = (bg_z3_proc.release ())
in (let rec aux = (fun _99_267 -> (match (()) with
| () -> begin
(let _99_271 = (with_monitor job_queue (fun _99_268 -> (match (()) with
| () -> begin
(let _201_196 = (FStar_ST.read pending_jobs)
in (let _201_195 = (let _201_194 = (FStar_ST.read job_queue)
in (FStar_List.length _201_194))
in (_201_196, _201_195)))
end)))
in (match (_99_271) with
| (n, m) -> begin
if ((n + m) = 0) then begin
(let _201_197 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _201_197 Prims.ignore))
end else begin
(let _99_272 = (FStar_Util.sleep 500)
in (aux ()))
end
end))
end))
in (aux ())))))
end))

type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list

let fresh_scope : FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))

let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

let push : Prims.string  ->  Prims.unit = (fun msg -> (let _99_275 = (let _201_201 = (let _201_200 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::[])::_201_200)
in (FStar_ST.op_Colon_Equals fresh_scope _201_201))
in (let _201_203 = (let _201_202 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[]) _201_202))
in (FStar_ST.op_Colon_Equals bg_scope _201_203))))

let pop : Prims.string  ->  Prims.unit = (fun msg -> (let _99_278 = (let _201_207 = (let _201_206 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _201_206))
in (FStar_ST.op_Colon_Equals fresh_scope _201_207))
in (let _201_209 = (let _201_208 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[]) _201_208))
in (FStar_ST.op_Colon_Equals bg_scope _201_209))))

let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (let _99_286 = (match ((FStar_ST.read fresh_scope)) with
| hd::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _99_285 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _201_213 = (let _201_212 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _201_212))
in (FStar_ST.op_Colon_Equals bg_scope _201_213))))

let bgtheory : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun fresh -> if fresh then begin
(let _201_217 = (let _201_216 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _201_216))
in (FStar_All.pipe_right _201_217 FStar_List.flatten))
end else begin
(let bg = (FStar_ST.read bg_scope)
in (let _99_290 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)

let refresh : Prims.unit  ->  Prims.unit = (fun _99_292 -> (match (()) with
| () -> begin
(let _99_293 = (bg_z3_proc.refresh ())
in (let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))

let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))

let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (let _99_298 = (pop msg)
in (refresh ())))

let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| hd::s::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _99_307 -> begin
(FStar_All.failwith "Impossible")
end))

let ask = (fun fresh label_messages qry cb -> (let fresh = (fresh && ((FStar_ST.read FStar_Options.n_cores) > 1))
in (let theory = (bgtheory fresh)
in (let theory = if fresh then begin
(FStar_List.append theory qry)
end else begin
(FStar_List.append (FStar_List.append (FStar_List.append theory ((FStar_SMTEncoding_Term.Push)::[])) qry) ((FStar_SMTEncoding_Term.Pop)::[]))
end
in (let input = (let _201_234 = (let _201_233 = (let _201_232 = (z3_options ())
in (FStar_SMTEncoding_Term.declToSmt _201_232))
in (FStar_List.map _201_233 theory))
in (FStar_All.pipe_right _201_234 (FStar_String.concat "\n")))
in (let _99_316 = if (FStar_ST.read FStar_Options.logQueries) then begin
(log_query fresh input)
end else begin
()
end
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb})))))))




