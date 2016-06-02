
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
| Z3V (_81_4) -> begin
_81_4
end))


let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _81_9 -> (match (_81_9) with
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


let get_z3version : Prims.unit  ->  z3version = (fun _81_21 -> (match (()) with
| () -> begin
(

let prefix = "Z3 version "
in (match ((FStar_ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(

let _81_31 = (let _171_26 = (FStar_Options.z3_exe ())
in (FStar_Util.run_proc _171_26 "-version" ""))
in (match (_81_31) with
| (_81_27, out, _81_30) -> begin
(

let out = (match ((FStar_Util.splitlines out)) with
| x::_81_33 when (FStar_Util.starts_with x prefix) -> begin
(

let x = (let _171_27 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _171_27))
in (

let x = try
(match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)
with
| _81_41 -> begin
[]
end
in (match (x) with
| i1::i2::i3::[] -> begin
Z3V ((i1, i2, i3))
end
| _81_50 -> begin
Z3V_Unknown
end)))
end
| _81_52 -> begin
Z3V_Unknown
end)
in (

let _81_54 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))


let ini_params : Prims.unit  ->  Prims.string = (fun _81_56 -> (match (()) with
| () -> begin
(

let _81_57 = if (let _171_32 = (get_z3version ())
in (z3v_le _171_32 (4, 3, 1))) then begin
(FStar_All.pipe_left Prims.raise (FStar_Util.Failure ("Z3 v4.3.1 is required.")))
end else begin
()
end
in "-smt2 -in AUTO_CONFIG=false MODEL=true SMT.RELEVANCY=2")
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


let status_to_string : z3status  ->  Prims.string = (fun _81_1 -> (match (_81_1) with
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


let tid : Prims.unit  ->  Prims.string = (fun _81_64 -> (match (()) with
| () -> begin
(let _171_41 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _171_41 FStar_Util.string_of_int))
end))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (let _171_49 = (FStar_Options.z3_exe ())
in (let _171_48 = (ini_params ())
in (FStar_Util.start_process id _171_49 _171_48 cond)))))


type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}


let is_Mkbgproc : bgproc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbgproc"))))


let queries_dot_smt2 : FStar_Util.file_handle Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let get_qfile : Prims.bool  ->  FStar_Util.file_handle = (

let ctr = (FStar_Util.mk_ref 0)
in (fun fresh -> if fresh then begin
(

let _81_76 = (FStar_Util.incr ctr)
in (let _171_82 = (let _171_81 = (let _171_80 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _171_80))
in (FStar_Util.format1 "queries-%s.smt2" _171_81))
in (FStar_Util.open_file_for_writing _171_82)))
end else begin
(match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
(

let fh = (FStar_Util.open_file_for_writing "queries-bg-0.smt2")
in (

let _81_80 = (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
in fh))
end
| Some (fh) -> begin
fh
end)
end))


let log_query : Prims.bool  ->  Prims.string  ->  Prims.unit = (fun fresh i -> (

let fh = (get_qfile fresh)
in (

let _81_87 = (FStar_Util.append_to_file fh i)
in if fresh then begin
(FStar_Util.close_file fh)
end else begin
()
end)))


let the_z3proc : FStar_Util.proc Prims.option FStar_ST.ref = (FStar_ST.alloc None)


let ctr : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (- (1)))


let new_proc : Prims.unit  ->  FStar_Util.proc = (fun _81_89 -> (match (()) with
| () -> begin
(let _171_91 = (let _171_90 = (

let _81_90 = (FStar_Util.incr ctr)
in (let _171_89 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _171_89 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _171_90))
in (new_z3proc _171_91))
end))


let z3proc : Prims.unit  ->  FStar_Util.proc = (fun _81_92 -> (match (()) with
| () -> begin
(

let _81_93 = if ((FStar_ST.read the_z3proc) = None) then begin
(let _171_95 = (let _171_94 = (new_proc ())
in Some (_171_94))
in (FStar_ST.op_Colon_Equals the_z3proc _171_95))
end else begin
()
end
in (let _171_96 = (FStar_ST.read the_z3proc)
in (FStar_Util.must _171_96)))
end))


let bg_z3_proc : bgproc = (

let x = []
in (

let grab = (fun _81_97 -> (match (()) with
| () -> begin
(

let _81_98 = (FStar_Util.monitor_enter x)
in (z3proc ()))
end))
in (

let release = (fun _81_101 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (

let refresh = (fun _81_103 -> (match (()) with
| () -> begin
(

let proc = (grab ())
in (

let _81_105 = (FStar_Util.kill_process proc)
in (

let _81_107 = (let _171_104 = (let _171_103 = (new_proc ())
in Some (_171_103))
in (FStar_ST.op_Colon_Equals the_z3proc _171_104))
in (

let _81_115 = (match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
()
end
| Some (fh) -> begin
(

let _81_112 = (FStar_Util.close_file fh)
in (

let fh = (let _171_107 = (let _171_106 = (let _171_105 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _171_105 FStar_Util.string_of_int))
in (FStar_Util.format1 "queries-bg-%s.smt2" _171_106))
in (FStar_Util.open_file_for_writing _171_107))
in (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))))
end)
in (release ())))))
end))
in {grab = grab; release = release; refresh = refresh}))))


let doZ3Exe' : Prims.string  ->  FStar_Util.proc  ->  (z3status * Prims.string Prims.list) = (fun input z3proc -> (

let parse = (fun z3out -> (

let lines = (FStar_All.pipe_right (FStar_String.split (('\n')::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (

let rec lblnegs = (fun lines -> (match (lines) with
| lname::"false"::rest -> begin
(let _171_116 = (lblnegs rest)
in (lname)::_171_116)
end
| lname::_81_131::rest -> begin
(lblnegs rest)
end
| _81_136 -> begin
[]
end))
in (

let rec result = (fun x -> (match (x) with
| "timeout"::tl -> begin
(TIMEOUT, [])
end
| "unknown"::tl -> begin
(let _171_119 = (lblnegs tl)
in (UNKNOWN, _171_119))
end
| "sat"::tl -> begin
(let _171_120 = (lblnegs tl)
in (SAT, _171_120))
end
| "unsat"::tl -> begin
(UNSAT, [])
end
| _81_153::tl -> begin
(result tl)
end
| _81_156 -> begin
(let _171_124 = (let _171_123 = (let _171_122 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _171_122))
in (FStar_Util.format1 "Got output lines: %s\n" _171_123))
in (FStar_All.pipe_left FStar_All.failwith _171_124))
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

let _81_162 = (FStar_Util.incr ctr)
in (let _171_130 = (let _171_129 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _171_129))
in (new_z3proc _171_130)))
end else begin
(bg_z3_proc.grab ())
end
in (

let res = (doZ3Exe' input z3proc)
in (

let _81_166 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))


let z3_options : Prims.unit  ->  Prims.string = (fun _81_168 -> (match (()) with
| () -> begin
(

let mbqi = if (let _171_133 = (get_z3version ())
in (z3v_le _171_133 (4, 3, 1))) then begin
"mbqi"
end else begin
"smt.mbqi"
end
in (

let model_on_timeout = if (let _171_134 = (get_z3version ())
in (z3v_le _171_134 (4, 3, 1))) then begin
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

let _81_177 = (FStar_Util.monitor_enter m)
in (

let res = (f ())
in (

let _81_180 = (FStar_Util.monitor_exit m)
in res))))


let z3_job = (fun fresh label_messages input _81_185 -> (match (()) with
| () -> begin
(

let _81_188 = (doZ3Exe fresh input)
in (match (_81_188) with
| (status, lblnegs) -> begin
(

let result = (match (status) with
| UNSAT -> begin
(true, [])
end
| _81_191 -> begin
(

let _81_192 = if (FStar_Options.debug_any ()) then begin
(let _171_164 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _171_164))
end else begin
()
end
in (

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _81_200 -> (match (_81_200) with
| (m, _81_197, _81_199) -> begin
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


let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _81_209 -> (match (()) with
| () -> begin
(

let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| hd::tl -> begin
(

let _81_214 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (

let _81_217 = (FStar_Util.incr pending_jobs)
in (

let _81_219 = (FStar_Util.monitor_exit job_queue)
in (

let _81_221 = (run_job j)
in (

let _81_224 = (with_monitor job_queue (fun _81_223 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (

let _81_226 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _81_228 -> (match (()) with
| () -> begin
(

let _81_229 = (FStar_Util.monitor_enter job_queue)
in (

let rec aux = (fun _81_232 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(

let _81_234 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _81_237 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _171_176 = (j.job ())
in (FStar_All.pipe_left j.callback _171_176)))


let init : Prims.unit  ->  Prims.unit = (fun _81_239 -> (match (()) with
| () -> begin
(

let n_runners = ((FStar_Options.n_cores ()) - 1)
in (

let rec aux = (fun n -> if (n = 0) then begin
()
end else begin
(

let _81_243 = (FStar_Util.spawn dequeue)
in (aux (n - 1)))
end)
in (aux n_runners)))
end))


let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(

let _81_247 = (FStar_Util.monitor_enter job_queue)
in (

let _81_249 = (let _171_186 = (let _171_185 = (FStar_ST.read job_queue)
in (FStar_List.append _171_185 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _171_186))
in (

let _81_251 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)


let finish : Prims.unit  ->  Prims.unit = (fun _81_253 -> (match (()) with
| () -> begin
(

let bg = (bg_z3_proc.grab ())
in (

let _81_255 = (FStar_Util.kill_process bg)
in (

let _81_257 = (bg_z3_proc.release ())
in (

let rec aux = (fun _81_260 -> (match (()) with
| () -> begin
(

let _81_264 = (with_monitor job_queue (fun _81_261 -> (match (()) with
| () -> begin
(let _171_194 = (FStar_ST.read pending_jobs)
in (let _171_193 = (let _171_192 = (FStar_ST.read job_queue)
in (FStar_List.length _171_192))
in (_171_194, _171_193)))
end)))
in (match (_81_264) with
| (n, m) -> begin
if ((n + m) = 0) then begin
(let _171_195 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _171_195 Prims.ignore))
end else begin
(

let _81_265 = (FStar_Util.sleep 500)
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

let _81_268 = (let _171_199 = (let _171_198 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::[])::_171_198)
in (FStar_ST.op_Colon_Equals fresh_scope _171_199))
in (let _171_201 = (let _171_200 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[]) _171_200))
in (FStar_ST.op_Colon_Equals bg_scope _171_201))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _81_271 = (let _171_205 = (let _171_204 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _171_204))
in (FStar_ST.op_Colon_Equals fresh_scope _171_205))
in (let _171_207 = (let _171_206 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[]) _171_206))
in (FStar_ST.op_Colon_Equals bg_scope _171_207))))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (

let _81_279 = (match ((FStar_ST.read fresh_scope)) with
| hd::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _81_278 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _171_211 = (let _171_210 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _171_210))
in (FStar_ST.op_Colon_Equals bg_scope _171_211))))


let bgtheory : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun fresh -> if fresh then begin
(let _171_215 = (let _171_214 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _171_214))
in (FStar_All.pipe_right _171_215 FStar_List.flatten))
end else begin
(

let bg = (FStar_ST.read bg_scope)
in (

let _81_283 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)


let refresh : Prims.unit  ->  Prims.unit = (fun _81_285 -> (match (()) with
| () -> begin
(

let _81_286 = (bg_z3_proc.refresh ())
in (

let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _81_291 = (pop msg)
in (refresh ())))


let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| hd::s::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _81_300 -> begin
(FStar_All.failwith "Impossible")
end))


let ask : Prims.bool  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  ((Prims.bool * FStar_SMTEncoding_Term.error_labels)  ->  Prims.unit)  ->  Prims.unit = (fun fresh label_messages qry cb -> (

let fresh = (fresh && ((FStar_Options.n_cores ()) > 1))
in (

let theory = (bgtheory fresh)
in (

let theory = if fresh then begin
(FStar_List.append theory qry)
end else begin
(FStar_List.append (FStar_List.append (FStar_List.append theory ((FStar_SMTEncoding_Term.Push)::[])) qry) ((FStar_SMTEncoding_Term.Pop)::[]))
end
in (

let input = (let _171_238 = (let _171_237 = (let _171_236 = (z3_options ())
in (FStar_SMTEncoding_Term.declToSmt _171_236))
in (FStar_List.map _171_237 theory))
in (FStar_All.pipe_right _171_238 (FStar_String.concat "\n")))
in (

let _81_309 = if (FStar_Options.log_queries ()) then begin
(log_query fresh input)
end else begin
()
end
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb})))))))




