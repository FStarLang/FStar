
open Prims

type z3version =
| Z3V_Unknown
| Z3V of (Prims.int * Prims.int * Prims.int)


let is_Z3V_Unknown = (fun _discr_ -> (match (_discr_) with
| Z3V_Unknown (_) -> begin
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
| Z3V (_80_4) -> begin
_80_4
end))


let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _80_9 -> (match (_80_9) with
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


let get_z3version : Prims.unit  ->  z3version = (fun _80_21 -> (match (()) with
| () -> begin
(

let prefix = "Z3 version "
in (match ((FStar_ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(

let _80_31 = (let _169_26 = (FStar_ST.read FStar_Options.z3_exe)
in (FStar_Util.run_proc _169_26 "-version" ""))
in (match (_80_31) with
| (_80_27, out, _80_30) -> begin
(

let out = (match ((FStar_Util.splitlines out)) with
| x::_80_33 when (FStar_Util.starts_with x prefix) -> begin
(

let x = (let _169_27 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _169_27))
in (

let x = try
(match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)
with
| _80_41 -> begin
[]
end
in (match (x) with
| i1::i2::i3::[] -> begin
Z3V ((i1, i2, i3))
end
| _80_50 -> begin
Z3V_Unknown
end)))
end
| _80_52 -> begin
Z3V_Unknown
end)
in (

let _80_54 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))


let ini_params : Prims.unit  ->  Prims.string = (fun _80_56 -> (match (()) with
| () -> begin
(

let t = if (let _169_32 = (get_z3version ())
in (z3v_le _169_32 (4, 3, 1))) then begin
(FStar_ST.read FStar_Options.z3timeout)
end else begin
((FStar_ST.read FStar_Options.z3timeout) * 1000)
end
in (

let timeout = (let _169_33 = (FStar_Util.string_of_int t)
in (FStar_Util.format1 "-t:%s" _169_33))
in (

let relevancy = if (let _169_34 = (get_z3version ())
in (z3v_le _169_34 (4, 3, 1))) then begin
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
| SAT (_) -> begin
true
end
| _ -> begin
false
end))


let is_UNSAT = (fun _discr_ -> (match (_discr_) with
| UNSAT (_) -> begin
true
end
| _ -> begin
false
end))


let is_UNKNOWN = (fun _discr_ -> (match (_discr_) with
| UNKNOWN (_) -> begin
true
end
| _ -> begin
false
end))


let is_TIMEOUT = (fun _discr_ -> (match (_discr_) with
| TIMEOUT (_) -> begin
true
end
| _ -> begin
false
end))


let status_to_string : z3status  ->  Prims.string = (fun _80_1 -> (match (_80_1) with
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


let tid : Prims.unit  ->  Prims.string = (fun _80_65 -> (match (()) with
| () -> begin
(let _169_43 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _169_43 FStar_Util.string_of_int))
end))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (let _169_51 = (FStar_ST.read FStar_Options.z3_exe)
in (let _169_50 = (ini_params ())
in (FStar_Util.start_process id _169_51 _169_50 cond)))))


type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}


let is_Mkbgproc : bgproc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbgproc"))))


let queries_dot_smt2 : FStar_Util.file_handle Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let get_qfile : Prims.bool  ->  FStar_Util.file_handle = (

let ctr = (FStar_Util.mk_ref 0)
in (fun fresh -> if fresh then begin
(

let _80_77 = (FStar_Util.incr ctr)
in (let _169_84 = (let _169_83 = (let _169_82 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _169_82))
in (FStar_Util.format1 "queries-%s.smt2" _169_83))
in (FStar_Util.open_file_for_writing _169_84)))
end else begin
(match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
(

let fh = (FStar_Util.open_file_for_writing "queries-bg-0.smt2")
in (

let _80_81 = (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
in fh))
end
| Some (fh) -> begin
fh
end)
end))


let log_query : Prims.bool  ->  Prims.string  ->  Prims.unit = (fun fresh i -> (

let fh = (get_qfile fresh)
in (

let _80_88 = (FStar_Util.append_to_file fh i)
in if fresh then begin
(FStar_Util.close_file fh)
end else begin
()
end)))


let bg_z3_proc : bgproc = (

let ctr = (FStar_Util.mk_ref (- (1)))
in (

let new_proc = (fun _80_92 -> (match (()) with
| () -> begin
(let _169_93 = (let _169_92 = (

let _80_93 = (FStar_Util.incr ctr)
in (let _169_91 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _169_91 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _169_92))
in (new_z3proc _169_93))
end))
in (

let z3proc = (let _169_94 = (new_proc ())
in (FStar_Util.mk_ref _169_94))
in (

let x = []
in (

let grab = (fun _80_98 -> (match (()) with
| () -> begin
(

let _80_99 = (FStar_Util.monitor_enter x)
in (FStar_ST.read z3proc))
end))
in (

let release = (fun _80_102 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (

let refresh = (fun _80_104 -> (match (()) with
| () -> begin
(

let proc = (grab ())
in (

let _80_106 = (FStar_Util.kill_process proc)
in (

let _80_108 = (let _169_101 = (new_proc ())
in (FStar_ST.op_Colon_Equals z3proc _169_101))
in (

let _80_116 = (match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
()
end
| Some (fh) -> begin
(

let _80_113 = (FStar_Util.close_file fh)
in (

let fh = (let _169_104 = (let _169_103 = (let _169_102 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _169_102 FStar_Util.string_of_int))
in (FStar_Util.format1 "queries-bg-%s.smt2" _169_103))
in (FStar_Util.open_file_for_writing _169_104))
in (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))))
end)
in (release ())))))
end))
in {grab = grab; release = release; refresh = refresh})))))))


let doZ3Exe' : Prims.string  ->  FStar_Util.proc  ->  (z3status * Prims.string Prims.list) = (fun input z3proc -> (

let parse = (fun z3out -> (

let lines = (FStar_All.pipe_right (FStar_String.split (('\n')::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (

let rec lblnegs = (fun lines -> (match (lines) with
| lname::"false"::rest -> begin
(let _169_113 = (lblnegs rest)
in (lname)::_169_113)
end
| lname::_80_132::rest -> begin
(lblnegs rest)
end
| _80_137 -> begin
[]
end))
in (

let rec result = (fun x -> (match (x) with
| "timeout"::tl -> begin
(TIMEOUT, [])
end
| "unknown"::tl -> begin
(let _169_116 = (lblnegs tl)
in (UNKNOWN, _169_116))
end
| "sat"::tl -> begin
(let _169_117 = (lblnegs tl)
in (SAT, _169_117))
end
| "unsat"::tl -> begin
(UNSAT, [])
end
| _80_154::tl -> begin
(result tl)
end
| _80_157 -> begin
(let _169_121 = (let _169_120 = (let _169_119 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _169_119))
in (FStar_Util.format1 "Got output lines: %s\n" _169_120))
in (FStar_All.pipe_left FStar_All.failwith _169_121))
end))
in (result lines)))))
in (

let stdout = (FStar_Util.ask_process z3proc input)
in (parse (FStar_Util.trim_string stdout)))))


let doZ3Exe : Prims.bool  ->  Prims.string  ->  (z3status * Prims.string Prims.list) = (

let ctr = (FStar_Util.mk_ref 0)
in (fun fresh input -> (

let z3proc = if fresh then begin
(

let _80_163 = (FStar_Util.incr ctr)
in (let _169_127 = (let _169_126 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _169_126))
in (new_z3proc _169_127)))
end else begin
(bg_z3_proc.grab ())
end
in (

let res = (doZ3Exe' input z3proc)
in (

let _80_167 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))


let z3_options : Prims.unit  ->  Prims.string = (fun _80_169 -> (match (()) with
| () -> begin
(

let mbqi = if (let _169_130 = (get_z3version ())
in (z3v_le _169_130 (4, 3, 1))) then begin
"mbqi"
end else begin
"smt.mbqi"
end
in (

let model_on_timeout = if (let _169_131 = (get_z3version ())
in (z3v_le _169_131 (4, 3, 1))) then begin
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
(Prims.bool * FStar_SMTEncoding_Term.error_label Prims.list) job


let job_queue : z3job Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 0)


let with_monitor = (fun m f -> (

let _80_178 = (FStar_Util.monitor_enter m)
in (

let res = (f ())
in (

let _80_181 = (FStar_Util.monitor_exit m)
in res))))


let z3_job = (fun fresh label_messages input _80_186 -> (match (()) with
| () -> begin
(

let _80_189 = (doZ3Exe fresh input)
in (match (_80_189) with
| (status, lblnegs) -> begin
(

let result = (match (status) with
| UNSAT -> begin
(true, [])
end
| _80_192 -> begin
(

let _80_193 = if ((FStar_ST.read FStar_Options.debug) <> []) then begin
(let _169_161 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _169_161))
end else begin
()
end
in (

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _80_201 -> (match (_80_201) with
| (m, _80_198, _80_200) -> begin
((Prims.fst m) = l)
end))))) with
| None -> begin
[]
end
| Some (lbl, msg, r) -> begin
((lbl, msg, r))::[]
end))))
in (false, failing_assertions)))
end)
in result)
end))
end))


let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _80_210 -> (match (()) with
| () -> begin
(

let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| hd::tl -> begin
(

let _80_215 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (

let _80_218 = (FStar_Util.incr pending_jobs)
in (

let _80_220 = (FStar_Util.monitor_exit job_queue)
in (

let _80_222 = (run_job j)
in (

let _80_225 = (with_monitor job_queue (fun _80_224 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (

let _80_227 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _80_229 -> (match (()) with
| () -> begin
(

let _80_230 = (FStar_Util.monitor_enter job_queue)
in (

let rec aux = (fun _80_233 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(

let _80_235 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _80_238 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _169_173 = (j.job ())
in (FStar_All.pipe_left j.callback _169_173)))


let init : Prims.unit  ->  Prims.unit = (fun _80_240 -> (match (()) with
| () -> begin
(

let n_runners = ((FStar_ST.read FStar_Options.n_cores) - 1)
in (

let rec aux = (fun n -> if (n = 0) then begin
()
end else begin
(

let _80_244 = (FStar_Util.spawn dequeue)
in (aux (n - 1)))
end)
in (aux n_runners)))
end))


let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(

let _80_248 = (FStar_Util.monitor_enter job_queue)
in (

let _80_250 = (let _169_183 = (let _169_182 = (FStar_ST.read job_queue)
in (FStar_List.append _169_182 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _169_183))
in (

let _80_252 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)


let finish : Prims.unit  ->  Prims.unit = (fun _80_254 -> (match (()) with
| () -> begin
(

let bg = (bg_z3_proc.grab ())
in (

let _80_256 = (FStar_Util.kill_process bg)
in (

let _80_258 = (bg_z3_proc.release ())
in (

let rec aux = (fun _80_261 -> (match (()) with
| () -> begin
(

let _80_265 = (with_monitor job_queue (fun _80_262 -> (match (()) with
| () -> begin
(let _169_191 = (FStar_ST.read pending_jobs)
in (let _169_190 = (let _169_189 = (FStar_ST.read job_queue)
in (FStar_List.length _169_189))
in (_169_191, _169_190)))
end)))
in (match (_80_265) with
| (n, m) -> begin
if ((n + m) = 0) then begin
(let _169_192 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _169_192 Prims.ignore))
end else begin
(

let _80_266 = (FStar_Util.sleep 500)
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


let push : Prims.string  ->  Prims.unit = (fun msg -> (

let _80_269 = (let _169_196 = (let _169_195 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::[])::_169_195)
in (FStar_ST.op_Colon_Equals fresh_scope _169_196))
in (let _169_198 = (let _169_197 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[]) _169_197))
in (FStar_ST.op_Colon_Equals bg_scope _169_198))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _80_272 = (let _169_202 = (let _169_201 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _169_201))
in (FStar_ST.op_Colon_Equals fresh_scope _169_202))
in (let _169_204 = (let _169_203 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[]) _169_203))
in (FStar_ST.op_Colon_Equals bg_scope _169_204))))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (

let _80_280 = (match ((FStar_ST.read fresh_scope)) with
| hd::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _80_279 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _169_208 = (let _169_207 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _169_207))
in (FStar_ST.op_Colon_Equals bg_scope _169_208))))


let bgtheory : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun fresh -> if fresh then begin
(let _169_212 = (let _169_211 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _169_211))
in (FStar_All.pipe_right _169_212 FStar_List.flatten))
end else begin
(

let bg = (FStar_ST.read bg_scope)
in (

let _80_284 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)


let refresh : Prims.unit  ->  Prims.unit = (fun _80_286 -> (match (()) with
| () -> begin
(

let _80_287 = (bg_z3_proc.refresh ())
in (

let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _80_292 = (pop msg)
in (refresh ())))


let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| hd::s::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _80_301 -> begin
(FStar_All.failwith "Impossible")
end))


let ask : Prims.bool  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  ((Prims.bool * FStar_SMTEncoding_Term.error_labels)  ->  Prims.unit)  ->  Prims.unit = (fun fresh label_messages qry cb -> (

let fresh = (fresh && ((FStar_ST.read FStar_Options.n_cores) > 1))
in (

let theory = (bgtheory fresh)
in (

let theory = if fresh then begin
(FStar_List.append theory qry)
end else begin
(FStar_List.append (FStar_List.append (FStar_List.append theory ((FStar_SMTEncoding_Term.Push)::[])) qry) ((FStar_SMTEncoding_Term.Pop)::[]))
end
in (

let input = (let _169_235 = (let _169_234 = (let _169_233 = (z3_options ())
in (FStar_SMTEncoding_Term.declToSmt _169_233))
in (FStar_List.map _169_234 theory))
in (FStar_All.pipe_right _169_235 (FStar_String.concat "\n")))
in (

let _80_310 = if (FStar_ST.read FStar_Options.logQueries) then begin
(log_query fresh input)
end else begin
()
end
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb})))))))




