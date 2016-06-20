
open Prims

type z3version =
| Z3V_Unknown of Prims.string
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


let ___Z3V_Unknown____0 = (fun projectee -> (match (projectee) with
| Z3V_Unknown (_81_7) -> begin
_81_7
end))


let ___Z3V____0 = (fun projectee -> (match (projectee) with
| Z3V (_81_10) -> begin
_81_10
end))


let z3version_as_string : z3version  ->  Prims.string = (fun _81_1 -> (match (_81_1) with
| Z3V_Unknown (s) -> begin
(FStar_Util.format1 "unknown version: %s" s)
end
| Z3V (i, j, k) -> begin
(let _172_33 = (FStar_Util.string_of_int i)
in (let _172_32 = (FStar_Util.string_of_int j)
in (let _172_31 = (FStar_Util.string_of_int k)
in (FStar_Util.format3 "%s.%s.%s" _172_33 _172_32 _172_31))))
end))


let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _81_23 -> (match (_81_23) with
| (w1, w2, w3) -> begin
(match (known) with
| Z3V_Unknown (_81_25) -> begin
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


let get_z3version : Prims.unit  ->  z3version = (fun _81_37 -> (match (()) with
| () -> begin
(

let prefix = "Z3 version "
in (match ((FStar_ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(

let _81_47 = (let _172_44 = (FStar_Options.z3_exe ())
in (FStar_Util.run_proc _172_44 "-version" ""))
in (match (_81_47) with
| (_81_43, out, _81_46) -> begin
(

let out = (match ((FStar_Util.splitlines out)) with
| (x)::_81_49 when (FStar_Util.starts_with x prefix) -> begin
(

let x = (let _172_45 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _172_45))
in (

let x = try
(match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)
with
| _81_57 -> begin
[]
end
in (match (x) with
| (i1)::(i2)::(i3)::[] -> begin
Z3V ((i1, i2, i3))
end
| _81_66 -> begin
Z3V_Unknown (out)
end)))
end
| _81_68 -> begin
Z3V_Unknown (out)
end)
in (

let _81_70 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))


let ini_params : Prims.unit  ->  Prims.string = (fun _81_72 -> (match (()) with
| () -> begin
(

let z3_v = (get_z3version ())
in (

let _81_74 = if (let _172_50 = (get_z3version ())
in (z3v_le _172_50 (4, 4, 0))) then begin
(let _172_53 = (let _172_52 = (let _172_51 = (z3version_as_string z3_v)
in (FStar_Util.format1 "Z3 v4.4.1 is required; got %s\n" _172_51))
in FStar_Util.Failure (_172_52))
in (FStar_All.pipe_left Prims.raise _172_53))
end else begin
()
end
in "-smt2 -in AUTO_CONFIG=false MODEL=true SMT.RELEVANCY=2"))
end))


type label =
Prims.string


type unsat_core =
Prims.string Prims.list Prims.option


type z3status =
| UNSAT of unsat_core
| SAT of label Prims.list
| UNKNOWN of label Prims.list
| TIMEOUT of label Prims.list


let is_UNSAT = (fun _discr_ -> (match (_discr_) with
| UNSAT (_) -> begin
true
end
| _ -> begin
false
end))


let is_SAT = (fun _discr_ -> (match (_discr_) with
| SAT (_) -> begin
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


let ___UNSAT____0 = (fun projectee -> (match (projectee) with
| UNSAT (_81_78) -> begin
_81_78
end))


let ___SAT____0 = (fun projectee -> (match (projectee) with
| SAT (_81_81) -> begin
_81_81
end))


let ___UNKNOWN____0 = (fun projectee -> (match (projectee) with
| UNKNOWN (_81_84) -> begin
_81_84
end))


let ___TIMEOUT____0 = (fun projectee -> (match (projectee) with
| TIMEOUT (_81_87) -> begin
_81_87
end))


let status_to_string : z3status  ->  Prims.string = (fun _81_2 -> (match (_81_2) with
| SAT (_81_90) -> begin
"sat"
end
| UNSAT (_81_93) -> begin
"unsat"
end
| UNKNOWN (_81_96) -> begin
"unknown"
end
| TIMEOUT (_81_99) -> begin
"timeout"
end))


let tid : Prims.unit  ->  Prims.string = (fun _81_101 -> (match (()) with
| () -> begin
(let _172_114 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _172_114 FStar_Util.string_of_int))
end))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (let _172_122 = (FStar_Options.z3_exe ())
in (let _172_121 = (ini_params ())
in (FStar_Util.start_process id _172_122 _172_121 cond)))))


type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}


let is_Mkbgproc : bgproc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbgproc"))))


let queries_dot_smt2 : FStar_Util.file_handle Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let get_qfile : Prims.bool  ->  FStar_Util.file_handle = (

let ctr = (FStar_Util.mk_ref 0)
in (fun fresh -> if fresh then begin
(

let _81_113 = (FStar_Util.incr ctr)
in (let _172_155 = (let _172_154 = (let _172_153 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _172_153))
in (FStar_Util.format1 "queries-%s.smt2" _172_154))
in (FStar_Util.open_file_for_writing _172_155)))
end else begin
(match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
(

let fh = (FStar_Util.open_file_for_writing "queries-bg-0.smt2")
in (

let _81_117 = (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
in fh))
end
| Some (fh) -> begin
fh
end)
end))


let log_query : Prims.bool  ->  Prims.string  ->  Prims.unit = (fun fresh i -> (

let fh = (get_qfile fresh)
in (

let _81_124 = (FStar_Util.append_to_file fh i)
in if fresh then begin
(FStar_Util.close_file fh)
end else begin
()
end)))


let the_z3proc : FStar_Util.proc Prims.option FStar_ST.ref = (FStar_ST.alloc None)


let ctr : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (- (1)))


let new_proc : Prims.unit  ->  FStar_Util.proc = (fun _81_126 -> (match (()) with
| () -> begin
(let _172_164 = (let _172_163 = (

let _81_127 = (FStar_Util.incr ctr)
in (let _172_162 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _172_162 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _172_163))
in (new_z3proc _172_164))
end))


let z3proc : Prims.unit  ->  FStar_Util.proc = (fun _81_129 -> (match (()) with
| () -> begin
(

let _81_130 = if ((FStar_ST.read the_z3proc) = None) then begin
(let _172_168 = (let _172_167 = (new_proc ())
in Some (_172_167))
in (FStar_ST.op_Colon_Equals the_z3proc _172_168))
end else begin
()
end
in (let _172_169 = (FStar_ST.read the_z3proc)
in (FStar_Util.must _172_169)))
end))


let bg_z3_proc : bgproc = (

let x = []
in (

let grab = (fun _81_134 -> (match (()) with
| () -> begin
(

let _81_135 = (FStar_Util.monitor_enter x)
in (z3proc ()))
end))
in (

let release = (fun _81_138 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (

let refresh = (fun _81_140 -> (match (()) with
| () -> begin
(

let proc = (grab ())
in (

let _81_142 = (FStar_Util.kill_process proc)
in (

let _81_144 = (let _172_177 = (let _172_176 = (new_proc ())
in Some (_172_176))
in (FStar_ST.op_Colon_Equals the_z3proc _172_177))
in (

let _81_152 = (match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
()
end
| Some (fh) -> begin
(

let _81_149 = (FStar_Util.close_file fh)
in (

let fh = (let _172_180 = (let _172_179 = (let _172_178 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _172_178 FStar_Util.string_of_int))
in (FStar_Util.format1 "queries-bg-%s.smt2" _172_179))
in (FStar_Util.open_file_for_writing _172_180))
in (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))))
end)
in (release ())))))
end))
in {grab = grab; release = release; refresh = refresh}))))


let doZ3Exe' : Prims.string  ->  FStar_Util.proc  ->  z3status = (fun input z3proc -> (

let parse = (fun z3out -> (

let lines = (FStar_All.pipe_right (FStar_String.split (('\n')::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (

let unsat_core = (fun lines -> (

let parse_core = (fun s -> (

let s = (FStar_Util.trim_string s)
in (

let s = (FStar_Util.substring s 1 ((FStar_String.length s) - 2))
in if (FStar_Util.starts_with s "error") then begin
None
end else begin
(let _172_192 = (FStar_All.pipe_right (FStar_Util.split s " ") (FStar_Util.sort_with FStar_String.compare))
in (FStar_All.pipe_right _172_192 (fun _172_191 -> Some (_172_191))))
end)))
in (match (lines) with
| ("<unsat-core>")::(core)::("</unsat-core>")::rest -> begin
(let _172_193 = (parse_core core)
in (_172_193, lines))
end
| _81_173 -> begin
(None, lines)
end)))
in (

let rec lblnegs = (fun lines -> (match (lines) with
| (lname)::("false")::rest -> begin
(let _172_196 = (lblnegs rest)
in (lname)::_172_196)
end
| (lname)::(_81_183)::rest -> begin
(lblnegs rest)
end
| _81_188 -> begin
[]
end))
in (

let rec unsat_core_and_lblnegs = (fun lines -> (

let _81_193 = (unsat_core lines)
in (match (_81_193) with
| (core_opt, rest) -> begin
(let _172_199 = (lblnegs rest)
in (core_opt, _172_199))
end)))
in (

let rec result = (fun x -> (match (x) with
| ("timeout")::tl -> begin
TIMEOUT ([])
end
| ("unknown")::tl -> begin
(let _172_203 = (let _172_202 = (unsat_core_and_lblnegs tl)
in (Prims.snd _172_202))
in UNKNOWN (_172_203))
end
| ("sat")::tl -> begin
(let _172_205 = (let _172_204 = (unsat_core_and_lblnegs tl)
in (Prims.snd _172_204))
in SAT (_172_205))
end
| ("unsat")::tl -> begin
(let _172_207 = (let _172_206 = (unsat_core tl)
in (Prims.fst _172_206))
in UNSAT (_172_207))
end
| (_81_210)::tl -> begin
(result tl)
end
| _81_213 -> begin
(let _172_211 = (let _172_210 = (let _172_209 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _172_209))
in (FStar_Util.format1 "Got output lines: %s\n" _172_210))
in (FStar_All.pipe_left FStar_All.failwith _172_211))
end))
in (result lines)))))))
in (

let stdout = (FStar_Util.ask_process z3proc input)
in (parse (FStar_Util.trim_string stdout)))))


let doZ3Exe : Prims.bool  ->  Prims.string  ->  z3status = (

let ctr = (FStar_Util.mk_ref 0)
in (fun fresh input -> (

let z3proc = if fresh then begin
(

let _81_219 = (FStar_Util.incr ctr)
in (let _172_217 = (let _172_216 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _172_216))
in (new_z3proc _172_217)))
end else begin
(bg_z3_proc.grab ())
end
in (

let res = (doZ3Exe' input z3proc)
in (

let _81_223 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))


let z3_options : Prims.unit  ->  Prims.string = (fun _81_225 -> (match (()) with
| () -> begin
"(set-option :global-decls false)(set-option :smt.mbqi false)(set-option :produce-unsat-cores true)\n"
end))


type 'a job =
{job : Prims.unit  ->  'a; callback : 'a  ->  Prims.unit}


let is_Mkjob = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkjob"))))


type z3job =
((unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either * Prims.int) job


let job_queue : z3job Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 0)


let with_monitor = (fun m f -> (

let _81_232 = (FStar_Util.monitor_enter m)
in (

let res = (f ())
in (

let _81_235 = (FStar_Util.monitor_exit m)
in res))))


let z3_job : Prims.bool  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  Prims.string  ->  Prims.unit  ->  ((unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either * Prims.int) = (fun fresh label_messages input _81_240 -> (match (()) with
| () -> begin
(

let start = (FStar_Util.now ())
in (

let status = (doZ3Exe fresh input)
in (

let _81_246 = (let _172_253 = (FStar_Util.now ())
in (FStar_Util.time_diff start _172_253))
in (match (_81_246) with
| (_81_244, elapsed_time) -> begin
(

let result = (match (status) with
| UNSAT (core) -> begin
(FStar_Util.Inl (core), elapsed_time)
end
| (TIMEOUT (lblnegs)) | (SAT (lblnegs)) | (UNKNOWN (lblnegs)) -> begin
(

let _81_253 = if (FStar_Options.debug_any ()) then begin
(let _172_254 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _172_254))
end else begin
()
end
in (

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _81_261 -> (match (_81_261) with
| (m, _81_258, _81_260) -> begin
((Prims.fst m) = l)
end))))) with
| None -> begin
[]
end
| Some (lbl, msg, r) -> begin
((lbl, msg, r))::[]
end))))
in (FStar_Util.Inr (failing_assertions), elapsed_time)))
end)
in result)
end))))
end))


let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _81_270 -> (match (()) with
| () -> begin
(

let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (hd)::tl -> begin
(

let _81_275 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (

let _81_278 = (FStar_Util.incr pending_jobs)
in (

let _81_280 = (FStar_Util.monitor_exit job_queue)
in (

let _81_282 = (run_job j)
in (

let _81_285 = (with_monitor job_queue (fun _81_284 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (

let _81_287 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _81_289 -> (match (()) with
| () -> begin
(

let _81_290 = (FStar_Util.monitor_enter job_queue)
in (

let rec aux = (fun _81_293 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(

let _81_295 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _81_298 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _172_266 = (j.job ())
in (FStar_All.pipe_left j.callback _172_266)))


let init : Prims.unit  ->  Prims.unit = (fun _81_300 -> (match (()) with
| () -> begin
(

let n_runners = ((FStar_Options.n_cores ()) - 1)
in (

let rec aux = (fun n -> if (n = 0) then begin
()
end else begin
(

let _81_304 = (FStar_Util.spawn dequeue)
in (aux (n - 1)))
end)
in (aux n_runners)))
end))


let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(

let _81_308 = (FStar_Util.monitor_enter job_queue)
in (

let _81_310 = (let _172_276 = (let _172_275 = (FStar_ST.read job_queue)
in (FStar_List.append _172_275 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _172_276))
in (

let _81_312 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)


let finish : Prims.unit  ->  Prims.unit = (fun _81_314 -> (match (()) with
| () -> begin
(

let bg = (bg_z3_proc.grab ())
in (

let _81_316 = (FStar_Util.kill_process bg)
in (

let _81_318 = (bg_z3_proc.release ())
in (

let rec aux = (fun _81_321 -> (match (()) with
| () -> begin
(

let _81_325 = (with_monitor job_queue (fun _81_322 -> (match (()) with
| () -> begin
(let _172_284 = (FStar_ST.read pending_jobs)
in (let _172_283 = (let _172_282 = (FStar_ST.read job_queue)
in (FStar_List.length _172_282))
in (_172_284, _172_283)))
end)))
in (match (_81_325) with
| (n, m) -> begin
if ((n + m) = 0) then begin
(let _172_285 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _172_285 Prims.ignore))
end else begin
(

let _81_326 = (FStar_Util.sleep 500)
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

let _81_329 = (let _172_289 = (let _172_288 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::[])::_172_288)
in (FStar_ST.op_Colon_Equals fresh_scope _172_289))
in (let _172_291 = (let _172_290 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[]) _172_290))
in (FStar_ST.op_Colon_Equals bg_scope _172_291))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _81_332 = (let _172_295 = (let _172_294 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _172_294))
in (FStar_ST.op_Colon_Equals fresh_scope _172_295))
in (let _172_297 = (let _172_296 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[]) _172_296))
in (FStar_ST.op_Colon_Equals bg_scope _172_297))))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (

let _81_340 = (match ((FStar_ST.read fresh_scope)) with
| (hd)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _81_339 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _172_301 = (let _172_300 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _172_300))
in (FStar_ST.op_Colon_Equals bg_scope _172_301))))


let bgtheory : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun fresh -> if fresh then begin
(let _172_305 = (let _172_304 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _172_304))
in (FStar_All.pipe_right _172_305 FStar_List.flatten))
end else begin
(

let bg = (FStar_ST.read bg_scope)
in (

let _81_344 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)


let refresh : Prims.unit  ->  Prims.unit = (fun _81_346 -> (match (()) with
| () -> begin
(

let _81_347 = (bg_z3_proc.refresh ())
in (

let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _81_352 = (pop msg)
in (refresh ())))


let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| (hd)::(s)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _81_361 -> begin
(FStar_All.failwith "Impossible")
end))


let ask : Prims.bool  ->  unsat_core  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  (((unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either * Prims.int)  ->  Prims.unit)  ->  Prims.unit = (fun fresh core label_messages qry cb -> (

let filter_assertions = (fun theory -> (match (core) with
| None -> begin
(theory, false)
end
| Some (core) -> begin
(

let _81_390 = (FStar_List.fold_right (fun d _81_376 -> (match (_81_376) with
| (theory, n_retained, n_pruned) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (_81_378, _81_380, Some (name)) -> begin
if (FStar_List.contains name core) then begin
((d)::theory, (n_retained + 1), n_pruned)
end else begin
if (FStar_Util.starts_with name "@") then begin
((d)::theory, n_retained, n_pruned)
end else begin
(theory, n_retained, (n_pruned + 1))
end
end
end
| _81_386 -> begin
((d)::theory, n_retained, n_pruned)
end)
end)) theory ([], 0, 0))
in (match (_81_390) with
| (theory', n_retained, n_pruned) -> begin
(

let missed_assertions = (fun th core -> (

let missed = (let _172_339 = (FStar_All.pipe_right core (FStar_List.filter (fun nm -> (let _172_338 = (FStar_All.pipe_right th (FStar_Util.for_some (fun _81_3 -> (match (_81_3) with
| FStar_SMTEncoding_Term.Assume (_81_397, _81_399, Some (nm')) -> begin
(nm = nm')
end
| _81_405 -> begin
false
end))))
in (FStar_All.pipe_right _172_338 Prims.op_Negation)))))
in (FStar_All.pipe_right _172_339 (FStar_String.concat ", ")))
in (

let included = (let _172_341 = (FStar_All.pipe_right th (FStar_List.collect (fun _81_4 -> (match (_81_4) with
| FStar_SMTEncoding_Term.Assume (_81_409, _81_411, Some (nm)) -> begin
(nm)::[]
end
| _81_417 -> begin
[]
end))))
in (FStar_All.pipe_right _172_341 (FStar_String.concat ", ")))
in (FStar_Util.format2 "missed={%s}; included={%s}" missed included))))
in (

let _81_421 = if (FStar_Options.hint_info ()) then begin
(

let n = (FStar_List.length core)
in (

let missed = if (n <> n_retained) then begin
(missed_assertions theory' core)
end else begin
""
end
in (let _172_345 = (FStar_Util.string_of_int n_retained)
in (let _172_344 = if (n <> n_retained) then begin
(let _172_342 = (FStar_Util.string_of_int n)
in (FStar_Util.format2 " (expected %s (%s); replay may be inaccurate)" _172_342 missed))
end else begin
""
end
in (let _172_343 = (FStar_Util.string_of_int n_pruned)
in (FStar_Util.print3 "Hint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n" _172_345 _172_344 _172_343))))))
end else begin
()
end
in (let _172_350 = (let _172_349 = (let _172_348 = (let _172_347 = (let _172_346 = (FStar_All.pipe_right core (FStar_String.concat ", "))
in (Prims.strcat "UNSAT CORE: " _172_346))
in FStar_SMTEncoding_Term.Caption (_172_347))
in (_172_348)::[])
in (FStar_List.append theory' _172_349))
in (_172_350, true))))
end))
end))
in (

let theory = (bgtheory fresh)
in (

let theory = if fresh then begin
(FStar_List.append theory qry)
end else begin
(FStar_List.append (FStar_List.append (FStar_List.append theory ((FStar_SMTEncoding_Term.Push)::[])) qry) ((FStar_SMTEncoding_Term.Pop)::[]))
end
in (

let _81_427 = (filter_assertions theory)
in (match (_81_427) with
| (theory, used_unsat_core) -> begin
(

let cb = (fun _81_431 -> (match (_81_431) with
| (uc_errs, time) -> begin
if used_unsat_core then begin
(match (uc_errs) with
| FStar_Util.Inl (_81_433) -> begin
(cb (uc_errs, time))
end
| FStar_Util.Inr (_81_436) -> begin
(cb (FStar_Util.Inr ([]), time))
end)
end else begin
(cb (uc_errs, time))
end
end))
in (

let input = (let _172_353 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ())) theory)
in (FStar_All.pipe_right _172_353 (FStar_String.concat "\n")))
in (

let _81_439 = if (FStar_Options.log_queries ()) then begin
(log_query fresh input)
end else begin
()
end
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb}))))
end))))))




