
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
| Z3V_Unknown (_81_5) -> begin
_81_5
end))


let ___Z3V____0 = (fun projectee -> (match (projectee) with
| Z3V (_81_8) -> begin
_81_8
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


let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _81_21 -> (match (_81_21) with
| (w1, w2, w3) -> begin
(match (known) with
| Z3V_Unknown (_81_23) -> begin
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


let get_z3version : Prims.unit  ->  z3version = (fun _81_35 -> (match (()) with
| () -> begin
(

let prefix = "Z3 version "
in (match ((FStar_ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(

let _81_45 = (let _172_44 = (FStar_Options.z3_exe ())
in (FStar_Util.run_proc _172_44 "-version" ""))
in (match (_81_45) with
| (_81_41, out, _81_44) -> begin
(

let out = (match ((FStar_Util.splitlines out)) with
| (x)::_81_47 when (FStar_Util.starts_with x prefix) -> begin
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
| _81_55 -> begin
[]
end
in (match (x) with
| (i1)::(i2)::(i3)::[] -> begin
Z3V ((i1, i2, i3))
end
| _81_64 -> begin
Z3V_Unknown (out)
end)))
end
| _81_66 -> begin
Z3V_Unknown (out)
end)
in (

let _81_68 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))


let ini_params : Prims.unit  ->  Prims.string = (fun _81_70 -> (match (()) with
| () -> begin
(

let z3_v = (get_z3version ())
in (

let _81_72 = if (let _172_50 = (get_z3version ())
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
| UNSAT (_81_76) -> begin
_81_76
end))


let ___SAT____0 = (fun projectee -> (match (projectee) with
| SAT (_81_79) -> begin
_81_79
end))


let ___UNKNOWN____0 = (fun projectee -> (match (projectee) with
| UNKNOWN (_81_82) -> begin
_81_82
end))


let ___TIMEOUT____0 = (fun projectee -> (match (projectee) with
| TIMEOUT (_81_85) -> begin
_81_85
end))


let status_to_string : z3status  ->  Prims.string = (fun _81_2 -> (match (_81_2) with
| SAT (_81_88) -> begin
"sat"
end
| UNSAT (_81_91) -> begin
"unsat"
end
| UNKNOWN (_81_94) -> begin
"unknown"
end
| TIMEOUT (_81_97) -> begin
"timeout"
end))


let tid : Prims.unit  ->  Prims.string = (fun _81_99 -> (match (()) with
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

let _81_111 = (FStar_Util.incr ctr)
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

let _81_115 = (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
in fh))
end
| Some (fh) -> begin
fh
end)
end))


let log_query : Prims.bool  ->  Prims.string  ->  Prims.unit = (fun fresh i -> (

let fh = (get_qfile fresh)
in (

let _81_122 = (FStar_Util.append_to_file fh i)
in if fresh then begin
(FStar_Util.close_file fh)
end else begin
()
end)))


let the_z3proc : FStar_Util.proc Prims.option FStar_ST.ref = (FStar_ST.alloc None)


let ctr : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (- (1)))


let new_proc : Prims.unit  ->  FStar_Util.proc = (fun _81_124 -> (match (()) with
| () -> begin
(let _172_164 = (let _172_163 = (

let _81_125 = (FStar_Util.incr ctr)
in (let _172_162 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _172_162 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _172_163))
in (new_z3proc _172_164))
end))


let z3proc : Prims.unit  ->  FStar_Util.proc = (fun _81_127 -> (match (()) with
| () -> begin
(

let _81_128 = if ((FStar_ST.read the_z3proc) = None) then begin
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

let grab = (fun _81_132 -> (match (()) with
| () -> begin
(

let _81_133 = (FStar_Util.monitor_enter x)
in (z3proc ()))
end))
in (

let release = (fun _81_136 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (

let refresh = (fun _81_138 -> (match (()) with
| () -> begin
(

let proc = (grab ())
in (

let _81_140 = (FStar_Util.kill_process proc)
in (

let _81_142 = (let _172_177 = (let _172_176 = (new_proc ())
in Some (_172_176))
in (FStar_ST.op_Colon_Equals the_z3proc _172_177))
in (

let _81_150 = (match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
()
end
| Some (fh) -> begin
(

let _81_147 = (FStar_Util.close_file fh)
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
(FStar_All.pipe_right (FStar_Util.split s " ") (fun _172_191 -> Some (_172_191)))
end)))
in (match (lines) with
| ("<unsat-core>")::(core)::("</unsat-core>")::rest -> begin
(let _172_192 = (parse_core core)
in (_172_192, lines))
end
| _81_171 -> begin
(None, lines)
end)))
in (

let rec lblnegs = (fun lines -> (match (lines) with
| (lname)::("false")::rest -> begin
(let _172_195 = (lblnegs rest)
in (lname)::_172_195)
end
| (lname)::(_81_181)::rest -> begin
(lblnegs rest)
end
| _81_186 -> begin
[]
end))
in (

let rec unsat_core_and_lblnegs = (fun lines -> (

let _81_191 = (unsat_core lines)
in (match (_81_191) with
| (core_opt, rest) -> begin
(let _172_198 = (lblnegs rest)
in (core_opt, _172_198))
end)))
in (

let rec result = (fun x -> (match (x) with
| ("timeout")::tl -> begin
TIMEOUT ([])
end
| ("unknown")::tl -> begin
(let _172_202 = (let _172_201 = (unsat_core_and_lblnegs tl)
in (Prims.snd _172_201))
in UNKNOWN (_172_202))
end
| ("sat")::tl -> begin
(let _172_204 = (let _172_203 = (unsat_core_and_lblnegs tl)
in (Prims.snd _172_203))
in SAT (_172_204))
end
| ("unsat")::tl -> begin
(let _172_206 = (let _172_205 = (unsat_core tl)
in (Prims.fst _172_205))
in UNSAT (_172_206))
end
| (_81_208)::tl -> begin
(result tl)
end
| _81_211 -> begin
(let _172_210 = (let _172_209 = (let _172_208 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _172_208))
in (FStar_Util.format1 "Got output lines: %s\n" _172_209))
in (FStar_All.pipe_left FStar_All.failwith _172_210))
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

let _81_217 = (FStar_Util.incr ctr)
in (let _172_216 = (let _172_215 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _172_215))
in (new_z3proc _172_216)))
end else begin
(bg_z3_proc.grab ())
end
in (

let res = (doZ3Exe' input z3proc)
in (

let _81_221 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))


let z3_options : Prims.unit  ->  Prims.string = (fun _81_223 -> (match (()) with
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

let _81_230 = (FStar_Util.monitor_enter m)
in (

let res = (f ())
in (

let _81_233 = (FStar_Util.monitor_exit m)
in res))))


let z3_job : Prims.bool  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  Prims.string  ->  Prims.unit  ->  ((unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either * Prims.int) = (fun fresh label_messages input _81_238 -> (match (()) with
| () -> begin
(

let start = (FStar_Util.now ())
in (

let status = (doZ3Exe fresh input)
in (

let _81_244 = (let _172_252 = (FStar_Util.now ())
in (FStar_Util.time_diff start _172_252))
in (match (_81_244) with
| (_81_242, elapsed_time) -> begin
(

let result = (match (status) with
| UNSAT (core) -> begin
(FStar_Util.Inl (core), elapsed_time)
end
| (TIMEOUT (lblnegs)) | (SAT (lblnegs)) | (UNKNOWN (lblnegs)) -> begin
(

let _81_251 = if (FStar_Options.debug_any ()) then begin
(let _172_253 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _172_253))
end else begin
()
end
in (

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _81_259 -> (match (_81_259) with
| (m, _81_256, _81_258) -> begin
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


let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _81_268 -> (match (()) with
| () -> begin
(

let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (hd)::tl -> begin
(

let _81_273 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (

let _81_276 = (FStar_Util.incr pending_jobs)
in (

let _81_278 = (FStar_Util.monitor_exit job_queue)
in (

let _81_280 = (run_job j)
in (

let _81_283 = (with_monitor job_queue (fun _81_282 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (

let _81_285 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _81_287 -> (match (()) with
| () -> begin
(

let _81_288 = (FStar_Util.monitor_enter job_queue)
in (

let rec aux = (fun _81_291 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(

let _81_293 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _81_296 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _172_265 = (j.job ())
in (FStar_All.pipe_left j.callback _172_265)))


let init : Prims.unit  ->  Prims.unit = (fun _81_298 -> (match (()) with
| () -> begin
(

let n_runners = ((FStar_Options.n_cores ()) - 1)
in (

let rec aux = (fun n -> if (n = 0) then begin
()
end else begin
(

let _81_302 = (FStar_Util.spawn dequeue)
in (aux (n - 1)))
end)
in (aux n_runners)))
end))


let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(

let _81_306 = (FStar_Util.monitor_enter job_queue)
in (

let _81_308 = (let _172_275 = (let _172_274 = (FStar_ST.read job_queue)
in (FStar_List.append _172_274 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _172_275))
in (

let _81_310 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)


let finish : Prims.unit  ->  Prims.unit = (fun _81_312 -> (match (()) with
| () -> begin
(

let bg = (bg_z3_proc.grab ())
in (

let _81_314 = (FStar_Util.kill_process bg)
in (

let _81_316 = (bg_z3_proc.release ())
in (

let rec aux = (fun _81_319 -> (match (()) with
| () -> begin
(

let _81_323 = (with_monitor job_queue (fun _81_320 -> (match (()) with
| () -> begin
(let _172_283 = (FStar_ST.read pending_jobs)
in (let _172_282 = (let _172_281 = (FStar_ST.read job_queue)
in (FStar_List.length _172_281))
in (_172_283, _172_282)))
end)))
in (match (_81_323) with
| (n, m) -> begin
if ((n + m) = 0) then begin
(let _172_284 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _172_284 Prims.ignore))
end else begin
(

let _81_324 = (FStar_Util.sleep 500)
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

let _81_327 = (let _172_288 = (let _172_287 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::[])::_172_287)
in (FStar_ST.op_Colon_Equals fresh_scope _172_288))
in (let _172_290 = (let _172_289 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[]) _172_289))
in (FStar_ST.op_Colon_Equals bg_scope _172_290))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _81_330 = (let _172_294 = (let _172_293 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _172_293))
in (FStar_ST.op_Colon_Equals fresh_scope _172_294))
in (let _172_296 = (let _172_295 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[]) _172_295))
in (FStar_ST.op_Colon_Equals bg_scope _172_296))))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (

let _81_338 = (match ((FStar_ST.read fresh_scope)) with
| (hd)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _81_337 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _172_300 = (let _172_299 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _172_299))
in (FStar_ST.op_Colon_Equals bg_scope _172_300))))


let bgtheory : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun fresh -> if fresh then begin
(let _172_304 = (let _172_303 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _172_303))
in (FStar_All.pipe_right _172_304 FStar_List.flatten))
end else begin
(

let bg = (FStar_ST.read bg_scope)
in (

let _81_342 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)


let refresh : Prims.unit  ->  Prims.unit = (fun _81_344 -> (match (()) with
| () -> begin
(

let _81_345 = (bg_z3_proc.refresh ())
in (

let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _81_350 = (pop msg)
in (refresh ())))


let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| (hd)::(s)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _81_359 -> begin
(FStar_All.failwith "Impossible")
end))


let ask : Prims.bool  ->  unsat_core  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  (((unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either * Prims.int)  ->  Prims.unit)  ->  Prims.unit = (fun fresh core label_messages qry cb -> (

let filter_assertions = (fun theory -> (match (core) with
| None -> begin
(theory, false)
end
| Some (core) -> begin
(

let _81_388 = (FStar_List.fold_right (fun d _81_374 -> (match (_81_374) with
| (theory, n_retained, n_pruned) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (_81_376, _81_378, Some (name)) -> begin
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
| _81_384 -> begin
((d)::theory, n_retained, n_pruned)
end)
end)) theory ([], 0, 0))
in (match (_81_388) with
| (theory', n_retained, n_pruned) -> begin
(

let _81_390 = if (FStar_Options.hint_info ()) then begin
(

let n = (FStar_List.length core)
in (let _172_334 = (FStar_Util.string_of_int n_retained)
in (let _172_333 = if (n <> n_retained) then begin
(let _172_331 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 " (expected %s; replay may be inaccurate)" _172_331))
end else begin
""
end
in (let _172_332 = (FStar_Util.string_of_int n_pruned)
in (FStar_Util.print3 "Hint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n" _172_334 _172_333 _172_332)))))
end else begin
()
end
in (let _172_339 = (let _172_338 = (let _172_337 = (let _172_336 = (let _172_335 = (FStar_All.pipe_right core (FStar_String.concat ", "))
in (Prims.strcat "UNSAT CORE: " _172_335))
in FStar_SMTEncoding_Term.Caption (_172_336))
in (_172_337)::[])
in (FStar_List.append theory' _172_338))
in (_172_339, true)))
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

let _81_396 = (filter_assertions theory)
in (match (_81_396) with
| (theory, used_unsat_core) -> begin
(

let cb = (fun _81_400 -> (match (_81_400) with
| (uc_errs, time) -> begin
if used_unsat_core then begin
(match (uc_errs) with
| FStar_Util.Inl (_81_402) -> begin
(cb (uc_errs, time))
end
| FStar_Util.Inr (_81_405) -> begin
(cb (FStar_Util.Inr ([]), time))
end)
end else begin
(cb (uc_errs, time))
end
end))
in (

let input = (let _172_342 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ())) theory)
in (FStar_All.pipe_right _172_342 (FStar_String.concat "\n")))
in (

let _81_408 = if (FStar_Options.log_queries ()) then begin
(log_query fresh input)
end else begin
()
end
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb}))))
end))))))




