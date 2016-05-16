
open Prims

type fuel_trace_identity =
{module_digest : Prims.string; transitive_digest : Prims.string Prims.option}


let is_Mkfuel_trace_identity : fuel_trace_identity  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkfuel_trace_identity"))))


type fuel_trace_state =
{identity : fuel_trace_identity; fuels : (Prims.int * Prims.int) Prims.list}


let is_Mkfuel_trace_state : fuel_trace_state  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkfuel_trace_state"))))


type fuel_trace_status =
| FuelTraceUnavailable
| RecordFuelTrace of (Prims.int * Prims.int) Prims.list
| ReplayFuelTrace of (Prims.string * (Prims.int * Prims.int) Prims.list)


let is_FuelTraceUnavailable = (fun _discr_ -> (match (_discr_) with
| FuelTraceUnavailable (_) -> begin
true
end
| _ -> begin
false
end))


let is_RecordFuelTrace = (fun _discr_ -> (match (_discr_) with
| RecordFuelTrace (_) -> begin
true
end
| _ -> begin
false
end))


let is_ReplayFuelTrace = (fun _discr_ -> (match (_discr_) with
| ReplayFuelTrace (_) -> begin
true
end
| _ -> begin
false
end))


let ___RecordFuelTrace____0 = (fun projectee -> (match (projectee) with
| RecordFuelTrace (_80_10) -> begin
_80_10
end))


let ___ReplayFuelTrace____0 = (fun projectee -> (match (projectee) with
| ReplayFuelTrace (_80_13) -> begin
_80_13
end))


let fuel_trace : fuel_trace_status FStar_ST.ref = (FStar_All.pipe_left FStar_Util.mk_ref FuelTraceUnavailable)


let format_fuel_trace_file_name : Prims.string  ->  Prims.string = (fun src_fn -> (let _169_46 = (FStar_Util.format1 "%s.fuel" src_fn)
in (FStar_All.pipe_left FStar_Util.format_value_file_name _169_46)))


let compute_transitive_digest : Prims.string  ->  Prims.string Prims.list  ->  Prims.string = (fun src_fn deps -> (

let digests = (let _169_51 = (FStar_All.pipe_left (FStar_List.map FStar_Util.digest_of_file) ((src_fn)::[]))
in (FStar_List.append _169_51 deps))
in (

let s = (let _169_52 = (FStar_List.sortWith FStar_String.compare digests)
in (FStar_All.pipe_left (FStar_Util.concat_l ",") _169_52))
in (FStar_Util.digest_of_string s))))


let is_replaying_fuel_trace : Prims.unit  ->  Prims.bool = (fun _80_19 -> (match (()) with
| () -> begin
(match ((FStar_ST.read fuel_trace)) with
| ReplayFuelTrace (_80_21) -> begin
true
end
| _80_24 -> begin
false
end)
end))


exception BadFuelCache of (Prims.unit)


let is_BadFuelCache = (fun _discr_ -> (match (_discr_) with
| BadFuelCache (_) -> begin
true
end
| _ -> begin
false
end))


let ___BadFuelCache____0 = (fun projectee -> ())


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
| Z3V (_80_29) -> begin
_80_29
end))


let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _80_34 -> (match (_80_34) with
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


let get_z3version : Prims.unit  ->  z3version = (fun _80_46 -> (match (()) with
| () -> begin
(

let prefix = "Z3 version "
in (match ((FStar_ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(

let _80_56 = (let _169_85 = (FStar_Options.z3_exe ())
in (FStar_Util.run_proc _169_85 "-version" ""))
in (match (_80_56) with
| (_80_52, out, _80_55) -> begin
(

let out = (match ((FStar_Util.splitlines out)) with
| x::_80_58 when (FStar_Util.starts_with x prefix) -> begin
(

let x = (let _169_86 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _169_86))
in (

let x = try
(match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)
with
| _80_66 -> begin
[]
end
in (match (x) with
| i1::i2::i3::[] -> begin
Z3V ((i1, i2, i3))
end
| _80_75 -> begin
Z3V_Unknown
end)))
end
| _80_77 -> begin
Z3V_Unknown
end)
in (

let _80_79 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))


let ini_params : Prims.int Prims.option  ->  Prims.string = (fun opt_timeout -> (

let timeout = (match (opt_timeout) with
| Some (n) -> begin
(

let t = if (let _169_91 = (get_z3version ())
in (z3v_le _169_91 (4, 3, 1))) then begin
n
end else begin
(n * 1000)
end
in (let _169_92 = (FStar_Util.string_of_int t)
in (FStar_Util.format1 "-t:%s" _169_92)))
end
| None -> begin
""
end)
in (

let relevancy = if (let _169_93 = (get_z3version ())
in (z3v_le _169_93 (4, 3, 1))) then begin
"RELEVANCY"
end else begin
"SMT.RELEVANCY"
end
in (FStar_Util.format2 "-smt2 -in %s AUTO_CONFIG=false MODEL=true %s=2" timeout relevancy))))


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


let tid : Prims.unit  ->  Prims.string = (fun _80_93 -> (match (()) with
| () -> begin
(let _169_102 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _169_102 FStar_Util.string_of_int))
end))


let new_z3proc : Prims.string  ->  Prims.int Prims.option  ->  FStar_Util.proc = (fun id timeout -> (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (

let args = (ini_params timeout)
in (

let _80_104 = if (FStar_Options.print_fuels ()) then begin
(match (timeout) with
| Some (n) -> begin
(let _169_111 = (FStar_Util.string_of_int n)
in (FStar_All.pipe_left (FStar_Util.print2 "Starting z3 process `%s` with a timeout of %s.\n" id) _169_111))
end
| None -> begin
(FStar_Util.print1 "Starting z3 process `%s` without a timeout.\n" id)
end)
end else begin
()
end
in (let _169_112 = (FStar_Options.z3_exe ())
in (FStar_Util.start_process id _169_112 args cond))))))


type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}


let is_Mkbgproc : bgproc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbgproc"))))


let queries_dot_smt2 : FStar_Util.file_handle Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let get_qfile : Prims.bool  ->  FStar_Util.file_handle = (

let ctr = (FStar_Util.mk_ref 0)
in (fun fresh -> if fresh then begin
(

let _80_112 = (FStar_Util.incr ctr)
in (let _169_145 = (let _169_144 = (let _169_143 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _169_143))
in (FStar_Util.format1 "queries-%s.smt2" _169_144))
in (FStar_Util.open_file_for_writing _169_145)))
end else begin
(match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
(

let fh = (FStar_Util.open_file_for_writing "queries-bg-0.smt2")
in (

let _80_116 = (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
in fh))
end
| Some (fh) -> begin
fh
end)
end))


let log_query : Prims.bool  ->  Prims.string  ->  Prims.unit = (fun fresh i -> (

let fh = (get_qfile fresh)
in (

let _80_123 = (FStar_Util.append_to_file fh i)
in if fresh then begin
(FStar_Util.close_file fh)
end else begin
()
end)))


let the_z3proc : FStar_Util.proc Prims.option FStar_ST.ref = (FStar_ST.alloc None)


let ctr : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (- (1)))


let new_proc : Prims.unit  ->  FStar_Util.proc = (fun _80_125 -> (match (()) with
| () -> begin
(

let timeout = if (is_replaying_fuel_trace ()) then begin
None
end else begin
(let _169_152 = (FStar_Options.z3_timeout ())
in Some (_169_152))
end
in (let _169_155 = (let _169_154 = (

let _80_127 = (FStar_Util.incr ctr)
in (let _169_153 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _169_153 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _169_154))
in (new_z3proc _169_155 timeout)))
end))


let z3proc : Prims.unit  ->  FStar_Util.proc = (fun _80_129 -> (match (()) with
| () -> begin
(

let _80_130 = if ((FStar_ST.read the_z3proc) = None) then begin
(let _169_159 = (let _169_158 = (new_proc ())
in Some (_169_158))
in (FStar_ST.op_Colon_Equals the_z3proc _169_159))
end else begin
()
end
in (let _169_160 = (FStar_ST.read the_z3proc)
in (FStar_Util.must _169_160)))
end))


let bg_z3_proc : bgproc = (

let x = []
in (

let grab = (fun _80_134 -> (match (()) with
| () -> begin
(

let _80_135 = (FStar_Util.monitor_enter x)
in (z3proc ()))
end))
in (

let release = (fun _80_138 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (

let refresh = (fun _80_140 -> (match (()) with
| () -> begin
(

let proc = (grab ())
in (

let _80_142 = (FStar_Util.kill_process proc)
in (

let _80_144 = (let _169_168 = (let _169_167 = (new_proc ())
in Some (_169_167))
in (FStar_ST.op_Colon_Equals the_z3proc _169_168))
in (

let _80_152 = (match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
()
end
| Some (fh) -> begin
(

let _80_149 = (FStar_Util.close_file fh)
in (

let fh = (let _169_171 = (let _169_170 = (let _169_169 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _169_169 FStar_Util.string_of_int))
in (FStar_Util.format1 "queries-bg-%s.smt2" _169_170))
in (FStar_Util.open_file_for_writing _169_171))
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
(let _169_180 = (lblnegs rest)
in (lname)::_169_180)
end
| lname::_80_168::rest -> begin
(lblnegs rest)
end
| _80_173 -> begin
[]
end))
in (

let rec result = (fun x -> (match (x) with
| "timeout"::tl -> begin
(TIMEOUT, [])
end
| "unknown"::tl -> begin
(let _169_183 = (lblnegs tl)
in (UNKNOWN, _169_183))
end
| "sat"::tl -> begin
(let _169_184 = (lblnegs tl)
in (SAT, _169_184))
end
| "unsat"::tl -> begin
(UNSAT, [])
end
| _80_190::tl -> begin
(result tl)
end
| _80_193 -> begin
(let _169_188 = (let _169_187 = (let _169_186 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _169_186))
in (FStar_Util.format1 "Got output lines: %s\n" _169_187))
in (FStar_All.pipe_left FStar_All.failwith _169_188))
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

let _80_199 = (FStar_Util.incr ctr)
in (let _169_196 = (let _169_193 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _169_193))
in (let _169_195 = (let _169_194 = (FStar_Options.z3_timeout ())
in Some (_169_194))
in (new_z3proc _169_196 _169_195))))
end else begin
(bg_z3_proc.grab ())
end
in (

let res = (doZ3Exe' input z3proc)
in (

let _80_203 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))


let z3_options : Prims.unit  ->  Prims.string = (fun _80_205 -> (match (()) with
| () -> begin
(

let mbqi = if (let _169_199 = (get_z3version ())
in (z3v_le _169_199 (4, 3, 1))) then begin
"mbqi"
end else begin
"smt.mbqi"
end
in (

let model_on_timeout = if (let _169_200 = (get_z3version ())
in (z3v_le _169_200 (4, 3, 1))) then begin
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

let _80_214 = (FStar_Util.monitor_enter m)
in (

let res = (f ())
in (

let _80_217 = (FStar_Util.monitor_exit m)
in res))))


let z3_job = (fun fresh label_messages input _80_222 -> (match (()) with
| () -> begin
(

let _80_225 = (doZ3Exe fresh input)
in (match (_80_225) with
| (status, lblnegs) -> begin
(

let result = (match (status) with
| UNSAT -> begin
(true, [])
end
| _80_228 -> begin
(

let _80_229 = if (FStar_Options.debug_any ()) then begin
(let _169_230 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _169_230))
end else begin
()
end
in (

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _80_237 -> (match (_80_237) with
| (m, _80_234, _80_236) -> begin
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


let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _80_246 -> (match (()) with
| () -> begin
(

let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| hd::tl -> begin
(

let _80_251 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (

let _80_254 = (FStar_Util.incr pending_jobs)
in (

let _80_256 = (FStar_Util.monitor_exit job_queue)
in (

let _80_258 = (run_job j)
in (

let _80_261 = (with_monitor job_queue (fun _80_260 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (

let _80_263 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _80_265 -> (match (()) with
| () -> begin
(

let _80_266 = (FStar_Util.monitor_enter job_queue)
in (

let rec aux = (fun _80_269 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(

let _80_271 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _80_274 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _169_242 = (j.job ())
in (FStar_All.pipe_left j.callback _169_242)))


let init : Prims.unit  ->  Prims.unit = (fun _80_276 -> (match (()) with
| () -> begin
(

let n_runners = ((FStar_Options.n_cores ()) - 1)
in (

let rec aux = (fun n -> if (n = 0) then begin
()
end else begin
(

let _80_280 = (FStar_Util.spawn dequeue)
in (aux (n - 1)))
end)
in (aux n_runners)))
end))


let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(

let _80_284 = (FStar_Util.monitor_enter job_queue)
in (

let _80_286 = (let _169_252 = (let _169_251 = (FStar_ST.read job_queue)
in (FStar_List.append _169_251 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _169_252))
in (

let _80_288 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)


let finish : Prims.unit  ->  Prims.unit = (fun _80_290 -> (match (()) with
| () -> begin
(

let bg = (bg_z3_proc.grab ())
in (

let _80_292 = (FStar_Util.kill_process bg)
in (

let _80_294 = (bg_z3_proc.release ())
in (

let rec aux = (fun _80_297 -> (match (()) with
| () -> begin
(

let _80_301 = (with_monitor job_queue (fun _80_298 -> (match (()) with
| () -> begin
(let _169_260 = (FStar_ST.read pending_jobs)
in (let _169_259 = (let _169_258 = (FStar_ST.read job_queue)
in (FStar_List.length _169_258))
in (_169_260, _169_259)))
end)))
in (match (_80_301) with
| (n, m) -> begin
if ((n + m) = 0) then begin
(let _169_261 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _169_261 Prims.ignore))
end else begin
(

let _80_302 = (FStar_Util.sleep 500)
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

let _80_305 = (let _169_265 = (let _169_264 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::[])::_169_264)
in (FStar_ST.op_Colon_Equals fresh_scope _169_265))
in (let _169_267 = (let _169_266 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[]) _169_266))
in (FStar_ST.op_Colon_Equals bg_scope _169_267))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _80_308 = (let _169_271 = (let _169_270 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _169_270))
in (FStar_ST.op_Colon_Equals fresh_scope _169_271))
in (let _169_273 = (let _169_272 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[]) _169_272))
in (FStar_ST.op_Colon_Equals bg_scope _169_273))))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (

let _80_316 = (match ((FStar_ST.read fresh_scope)) with
| hd::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _80_315 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _169_277 = (let _169_276 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _169_276))
in (FStar_ST.op_Colon_Equals bg_scope _169_277))))


let bgtheory : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun fresh -> if fresh then begin
(let _169_281 = (let _169_280 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _169_280))
in (FStar_All.pipe_right _169_281 FStar_List.flatten))
end else begin
(

let bg = (FStar_ST.read bg_scope)
in (

let _80_320 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)


let refresh : Prims.unit  ->  Prims.unit = (fun _80_322 -> (match (()) with
| () -> begin
(

let _80_323 = (bg_z3_proc.refresh ())
in (

let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _80_328 = (pop msg)
in (refresh ())))


let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| hd::s::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _80_337 -> begin
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

let input = (let _169_304 = (let _169_303 = (let _169_302 = (z3_options ())
in (FStar_SMTEncoding_Term.declToSmt _169_302))
in (FStar_List.map _169_303 theory))
in (FStar_All.pipe_right _169_304 (FStar_String.concat "\n")))
in (

let _80_346 = if (FStar_Options.log_queries ()) then begin
(log_query fresh input)
end else begin
()
end
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb})))))))


let initialize_fuel_trace : Prims.string  ->  Prims.string Prims.list  ->  Prims.bool  ->  Prims.unit = (fun src_fn deps force_invalid_cache -> (

let _80_370 = if force_invalid_cache then begin
(FStar_ST.op_Colon_Equals fuel_trace (RecordFuelTrace ([])))
end else begin
(

let norm_src_fn = (FStar_Util.normalize_file_path src_fn)
in (

let val_fn = (format_fuel_trace_file_name norm_src_fn)
in (match ((FStar_Util.load_value_from_file val_fn)) with
| Some (state) -> begin
(

let _80_362 = if (FStar_Options.explicit_deps ()) then begin
(

let expected = (FStar_Util.digest_of_file norm_src_fn)
in ("Module", (state.identity.module_digest = expected)))
end else begin
(let _169_311 = (match (state.identity.transitive_digest) with
| None -> begin
false
end
| Some (d) -> begin
(

let expected = (compute_transitive_digest norm_src_fn deps)
in (d = expected))
end)
in ("Transitive", _169_311))
end
in (match (_80_362) with
| (means, validated) -> begin
if validated then begin
(

let _80_363 = if (FStar_Options.print_fuels ()) then begin
(FStar_Util.print2 "(%s) %s digest is valid.\n" norm_src_fn means)
end else begin
()
end
in (FStar_ST.op_Colon_Equals fuel_trace (ReplayFuelTrace ((val_fn, state.fuels)))))
end else begin
(

let _80_365 = if (FStar_Options.print_fuels ()) then begin
(FStar_Util.print2 "(%s) %s digest is invalid.\n" norm_src_fn means)
end else begin
()
end
in (FStar_ST.op_Colon_Equals fuel_trace (RecordFuelTrace ([]))))
end
end))
end
| None -> begin
(

let _80_368 = if (FStar_Options.print_fuels ()) then begin
(FStar_Util.print1 "(%s) Unable to read cached fuel trace.\n" norm_src_fn)
end else begin
()
end
in (FStar_ST.op_Colon_Equals fuel_trace (RecordFuelTrace ([]))))
end)))
end
in (refresh ())))


let finalize_fuel_trace : Prims.string  ->  Prims.string Prims.list  ->  Prims.unit = (fun src_fn deps -> (

let _80_385 = (match ((FStar_ST.read fuel_trace)) with
| (ReplayFuelTrace (_)) | (FuelTraceUnavailable) | (RecordFuelTrace ([])) -> begin
()
end
| RecordFuelTrace (l) -> begin
(

let val_fn = (format_fuel_trace_file_name src_fn)
in (

let xd = if (FStar_Options.explicit_deps ()) then begin
None
end else begin
(let _169_317 = (compute_transitive_digest src_fn deps)
in (FStar_All.pipe_left (fun _169_316 -> Some (_169_316)) _169_317))
end
in (

let state = (let _169_319 = (let _169_318 = (FStar_Util.digest_of_file src_fn)
in {module_digest = _169_318; transitive_digest = xd})
in {identity = _169_319; fuels = l})
in (FStar_Util.save_value_to_file val_fn state))))
end)
in (FStar_ST.op_Colon_Equals fuel_trace FuelTraceUnavailable)))




