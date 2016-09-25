
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
| Z3V_Unknown (_84_8) -> begin
_84_8
end))


let ___Z3V____0 = (fun projectee -> (match (projectee) with
| Z3V (_84_11) -> begin
_84_11
end))


let z3version_as_string : z3version  ->  Prims.string = (fun _84_1 -> (match (_84_1) with
| Z3V_Unknown (s) -> begin
(FStar_Util.format1 "unknown version: %s" s)
end
| Z3V (i, j, k) -> begin
(let _178_33 = (FStar_Util.string_of_int i)
in (let _178_32 = (FStar_Util.string_of_int j)
in (let _178_31 = (FStar_Util.string_of_int k)
in (FStar_Util.format3 "%s.%s.%s" _178_33 _178_32 _178_31))))
end))


let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _84_24 -> (match (_84_24) with
| (w1, w2, w3) -> begin
(match (known) with
| Z3V_Unknown (_84_26) -> begin
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
(i >= (Prims.parse_int "0"))
end))


let _z3version : z3version Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let get_z3version : Prims.unit  ->  z3version = (fun _84_38 -> (match (()) with
| () -> begin
(

let prefix = "Z3 version "
in (match ((FStar_ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(

let _84_48 = (let _178_44 = (FStar_Options.z3_exe ())
in (FStar_Util.run_proc _178_44 "-version" ""))
in (match (_84_48) with
| (_84_44, out, _84_47) -> begin
(

let out = (match ((FStar_Util.splitlines out)) with
| (x)::_84_50 when (FStar_Util.starts_with x prefix) -> begin
(

let x = (let _178_45 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _178_45))
in (

let x = try
(match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)
with
| _84_58 -> begin
[]
end
in (match (x) with
| (i1)::(i2)::(i3)::[] -> begin
Z3V (((i1), (i2), (i3)))
end
| _84_67 -> begin
Z3V_Unknown (out)
end)))
end
| _84_69 -> begin
Z3V_Unknown (out)
end)
in (

let _84_71 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))


let ini_params : Prims.unit  ->  Prims.string = (fun _84_73 -> (match (()) with
| () -> begin
(

let z3_v = (get_z3version ())
in (

let _84_75 = if (let _178_50 = (get_z3version ())
in (z3v_le _178_50 (((Prims.parse_int "4")), ((Prims.parse_int "4")), ((Prims.parse_int "0"))))) then begin
(let _178_53 = (let _178_52 = (let _178_51 = (z3version_as_string z3_v)
in (FStar_Util.format1 "Z3 v4.4.1 is required; got %s\n" _178_51))
in FStar_Util.Failure (_178_52))
in (FStar_All.pipe_left Prims.raise _178_53))
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
| UNSAT (_84_79) -> begin
_84_79
end))


let ___SAT____0 = (fun projectee -> (match (projectee) with
| SAT (_84_82) -> begin
_84_82
end))


let ___UNKNOWN____0 = (fun projectee -> (match (projectee) with
| UNKNOWN (_84_85) -> begin
_84_85
end))


let ___TIMEOUT____0 = (fun projectee -> (match (projectee) with
| TIMEOUT (_84_88) -> begin
_84_88
end))


let status_to_string : z3status  ->  Prims.string = (fun _84_2 -> (match (_84_2) with
| SAT (_84_91) -> begin
"sat"
end
| UNSAT (_84_94) -> begin
"unsat"
end
| UNKNOWN (_84_97) -> begin
"unknown"
end
| TIMEOUT (_84_100) -> begin
"timeout"
end))


let tid : Prims.unit  ->  Prims.string = (fun _84_102 -> (match (()) with
| () -> begin
(let _178_114 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _178_114 FStar_Util.string_of_int))
end))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (let _178_122 = (FStar_Options.z3_exe ())
in (let _178_121 = (ini_params ())
in (FStar_Util.start_process id _178_122 _178_121 cond)))))


type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}


let is_Mkbgproc : bgproc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbgproc"))))


type query_log =
{set_module_name : Prims.string  ->  Prims.unit; append_to_log : Prims.string  ->  Prims.unit; close_log : Prims.unit  ->  Prims.unit; log_file_name : Prims.unit  ->  Prims.string}


let is_Mkquery_log : query_log  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkquery_log"))))


let query_logging : query_log = (

let log_file_opt = (FStar_Util.mk_ref None)
in (

let used_file_names = (FStar_Util.mk_ref [])
in (

let current_module_name = (FStar_Util.mk_ref None)
in (

let current_file_name = (FStar_Util.mk_ref None)
in (

let set_module_name = (fun n -> (FStar_ST.op_Colon_Equals current_module_name (Some (n))))
in (

let new_log_file = (fun _84_124 -> (match (()) with
| () -> begin
(match ((FStar_ST.read current_module_name)) with
| None -> begin
(FStar_All.failwith "current module not set")
end
| Some (n) -> begin
(

let file_name = (match ((let _178_193 = (FStar_ST.read used_file_names)
in (FStar_List.tryFind (fun _84_131 -> (match (_84_131) with
| (m, _84_130) -> begin
(n = m)
end)) _178_193))) with
| None -> begin
(

let _84_133 = (let _178_195 = (let _178_194 = (FStar_ST.read used_file_names)
in (((n), ((Prims.parse_int "0"))))::_178_194)
in (FStar_ST.op_Colon_Equals used_file_names _178_195))
in n)
end
| Some (_84_136, k) -> begin
(

let _84_140 = (let _178_197 = (let _178_196 = (FStar_ST.read used_file_names)
in (((n), ((k + (Prims.parse_int "1")))))::_178_196)
in (FStar_ST.op_Colon_Equals used_file_names _178_197))
in (let _178_198 = (FStar_Util.string_of_int (k + (Prims.parse_int "1")))
in (FStar_Util.format2 "%s-%s" n _178_198)))
end)
in (

let file_name = (FStar_Util.format1 "queries-%s.smt2" file_name)
in (

let _84_144 = (FStar_ST.op_Colon_Equals current_file_name (Some (file_name)))
in (

let fh = (FStar_Util.open_file_for_writing file_name)
in (

let _84_147 = (FStar_ST.op_Colon_Equals log_file_opt (Some (fh)))
in fh)))))
end)
end))
in (

let get_log_file = (fun _84_150 -> (match (()) with
| () -> begin
(match ((FStar_ST.read log_file_opt)) with
| None -> begin
(new_log_file ())
end
| Some (fh) -> begin
fh
end)
end))
in (

let append_to_log = (fun str -> (let _178_203 = (get_log_file ())
in (FStar_Util.append_to_file _178_203 str)))
in (

let close_log = (fun _84_157 -> (match (()) with
| () -> begin
(match ((FStar_ST.read log_file_opt)) with
| None -> begin
()
end
| Some (fh) -> begin
(

let _84_161 = (FStar_Util.close_file fh)
in (FStar_ST.op_Colon_Equals log_file_opt None))
end)
end))
in (

let log_file_name = (fun _84_164 -> (match (()) with
| () -> begin
(match ((FStar_ST.read current_file_name)) with
| None -> begin
(FStar_All.failwith "no log file")
end
| Some (n) -> begin
n
end)
end))
in {set_module_name = set_module_name; append_to_log = append_to_log; close_log = close_log; log_file_name = log_file_name}))))))))))


let bg_z3_proc : bgproc = (

let the_z3proc = (FStar_Util.mk_ref None)
in (

let new_proc = (

let ctr = (FStar_Util.mk_ref (~- ((Prims.parse_int "1"))))
in (fun _84_170 -> (match (()) with
| () -> begin
(let _178_212 = (let _178_211 = (

let _84_171 = (FStar_Util.incr ctr)
in (let _178_210 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _178_210 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _178_211))
in (new_z3proc _178_212))
end)))
in (

let z3proc = (fun _84_175 -> (match (()) with
| () -> begin
(

let _84_176 = if ((FStar_ST.read the_z3proc) = None) then begin
(let _178_216 = (let _178_215 = (new_proc ())
in Some (_178_215))
in (FStar_ST.op_Colon_Equals the_z3proc _178_216))
end else begin
()
end
in (let _178_217 = (FStar_ST.read the_z3proc)
in (FStar_Util.must _178_217)))
end))
in (

let x = []
in (

let grab = (fun _84_180 -> (match (()) with
| () -> begin
(

let _84_181 = (FStar_Util.monitor_enter x)
in (z3proc ()))
end))
in (

let release = (fun _84_184 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (

let refresh = (fun _84_186 -> (match (()) with
| () -> begin
(

let proc = (grab ())
in (

let _84_188 = (FStar_Util.kill_process proc)
in (

let _84_190 = (let _178_225 = (let _178_224 = (new_proc ())
in Some (_178_224))
in (FStar_ST.op_Colon_Equals the_z3proc _178_225))
in (

let _84_192 = (query_logging.close_log ())
in (release ())))))
end))
in {grab = grab; release = release; refresh = refresh})))))))


let doZ3Exe' : Prims.string  ->  FStar_Util.proc  ->  z3status = (fun input z3proc -> (

let parse = (fun z3out -> (

let lines = (FStar_All.pipe_right (FStar_String.split (('\n')::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (

let unsat_core = (fun lines -> (

let parse_core = (fun s -> (

let s = (FStar_Util.trim_string s)
in (

let s = (FStar_Util.substring s (Prims.parse_int "1") ((FStar_String.length s) - (Prims.parse_int "2")))
in if (FStar_Util.starts_with s "error") then begin
None
end else begin
(let _178_237 = (FStar_All.pipe_right (FStar_Util.split s " ") (FStar_Util.sort_with FStar_String.compare))
in (FStar_All.pipe_right _178_237 (fun _178_236 -> Some (_178_236))))
end)))
in (match (lines) with
| ("<unsat-core>")::(core)::("</unsat-core>")::rest -> begin
(let _178_238 = (parse_core core)
in ((_178_238), (lines)))
end
| _84_213 -> begin
((None), (lines))
end)))
in (

let rec lblnegs = (fun lines -> (match (lines) with
| (lname)::("false")::rest -> begin
(let _178_241 = (lblnegs rest)
in (lname)::_178_241)
end
| (lname)::(_84_223)::rest -> begin
(lblnegs rest)
end
| _84_228 -> begin
[]
end))
in (

let rec unsat_core_and_lblnegs = (fun lines -> (

let _84_233 = (unsat_core lines)
in (match (_84_233) with
| (core_opt, rest) -> begin
(let _178_244 = (lblnegs rest)
in ((core_opt), (_178_244)))
end)))
in (

let rec result = (fun x -> (match (x) with
| ("timeout")::tl -> begin
TIMEOUT ([])
end
| ("unknown")::tl -> begin
(let _178_248 = (let _178_247 = (unsat_core_and_lblnegs tl)
in (Prims.snd _178_247))
in UNKNOWN (_178_248))
end
| ("sat")::tl -> begin
(let _178_250 = (let _178_249 = (unsat_core_and_lblnegs tl)
in (Prims.snd _178_249))
in SAT (_178_250))
end
| ("unsat")::tl -> begin
(let _178_252 = (let _178_251 = (unsat_core tl)
in (Prims.fst _178_251))
in UNSAT (_178_252))
end
| (hd)::tl -> begin
(

let _84_251 = (let _178_253 = (FStar_Util.format1 "Unexpected output from Z3: %s\n" hd)
in (FStar_TypeChecker_Errors.warn FStar_Range.dummyRange _178_253))
in (result tl))
end
| _84_254 -> begin
(let _178_257 = (let _178_256 = (let _178_255 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _178_255))
in (FStar_Util.format1 "Unexpected output from Z3: got output lines: %s\n" _178_256))
in (FStar_All.pipe_left FStar_All.failwith _178_257))
end))
in (result lines)))))))
in (

let stdout = (FStar_Util.ask_process z3proc input)
in (parse (FStar_Util.trim_string stdout)))))


let doZ3Exe : Prims.bool  ->  Prims.string  ->  z3status = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun fresh input -> (

let z3proc = if fresh then begin
(

let _84_260 = (FStar_Util.incr ctr)
in (let _178_263 = (let _178_262 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _178_262))
in (new_z3proc _178_263)))
end else begin
(bg_z3_proc.grab ())
end
in (

let res = (doZ3Exe' input z3proc)
in (

let _84_264 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))


let z3_options : Prims.unit  ->  Prims.string = (fun _84_266 -> (match (()) with
| () -> begin
"(set-option :global-decls false)(set-option :smt.mbqi false)(set-option :produce-unsat-cores true)\n"
end))


type 'a job =
{job : Prims.unit  ->  'a; callback : 'a  ->  Prims.unit}


let is_Mkjob = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkjob"))))


type z3job =
((unsat_core, (FStar_SMTEncoding_Term.error_labels * Prims.bool)) FStar_Util.either * Prims.int) job


let job_queue : z3job Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let with_monitor = (fun m f -> (

let _84_273 = (FStar_Util.monitor_enter m)
in (

let res = (f ())
in (

let _84_276 = (FStar_Util.monitor_exit m)
in res))))


let z3_job : Prims.bool  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  Prims.string  ->  Prims.unit  ->  ((unsat_core, (FStar_SMTEncoding_Term.error_labels * Prims.bool)) FStar_Util.either * Prims.int) = (fun fresh label_messages input _84_281 -> (match (()) with
| () -> begin
(

let is_timeout = (fun _84_3 -> (match (_84_3) with
| TIMEOUT (_84_284) -> begin
true
end
| _84_287 -> begin
false
end))
in (

let start = (FStar_Util.now ())
in (

let status = (doZ3Exe fresh input)
in (

let _84_294 = (let _178_301 = (FStar_Util.now ())
in (FStar_Util.time_diff start _178_301))
in (match (_84_294) with
| (_84_292, elapsed_time) -> begin
(

let result = (match (status) with
| UNSAT (core) -> begin
((FStar_Util.Inl (core)), (elapsed_time))
end
| (TIMEOUT (lblnegs)) | (SAT (lblnegs)) | (UNKNOWN (lblnegs)) -> begin
(

let _84_301 = if (FStar_Options.debug_any ()) then begin
(let _178_302 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _178_302))
end else begin
()
end
in (

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _84_309 -> (match (_84_309) with
| (m, _84_306, _84_308) -> begin
((Prims.fst m) = l)
end))))) with
| None -> begin
[]
end
| Some (lbl, msg, r) -> begin
(((lbl), (msg), (r)))::[]
end))))
in ((FStar_Util.Inr (((failing_assertions), ((is_timeout status))))), (elapsed_time))))
end)
in result)
end)))))
end))


let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _84_318 -> (match (()) with
| () -> begin
(

let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (hd)::tl -> begin
(

let _84_323 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (

let _84_326 = (FStar_Util.incr pending_jobs)
in (

let _84_328 = (FStar_Util.monitor_exit job_queue)
in (

let _84_330 = (run_job j)
in (

let _84_333 = (with_monitor job_queue (fun _84_332 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (

let _84_335 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _84_337 -> (match (()) with
| () -> begin
(

let _84_338 = (FStar_Util.monitor_enter job_queue)
in (

let rec aux = (fun _84_341 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(

let _84_343 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _84_346 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _178_314 = (j.job ())
in (FStar_All.pipe_left j.callback _178_314)))


let init : Prims.unit  ->  Prims.unit = (fun _84_348 -> (match (()) with
| () -> begin
(

let n_runners = ((FStar_Options.n_cores ()) - (Prims.parse_int "1"))
in (

let rec aux = (fun n -> if (n = (Prims.parse_int "0")) then begin
()
end else begin
(

let _84_352 = (FStar_Util.spawn dequeue)
in (aux (n - (Prims.parse_int "1"))))
end)
in (aux n_runners)))
end))


let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(

let _84_356 = (FStar_Util.monitor_enter job_queue)
in (

let _84_358 = (let _178_324 = (let _178_323 = (FStar_ST.read job_queue)
in (FStar_List.append _178_323 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _178_324))
in (

let _84_360 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)


let finish : Prims.unit  ->  Prims.unit = (fun _84_362 -> (match (()) with
| () -> begin
(

let bg = (bg_z3_proc.grab ())
in (

let _84_364 = (FStar_Util.kill_process bg)
in (

let _84_366 = (bg_z3_proc.release ())
in (

let rec aux = (fun _84_369 -> (match (()) with
| () -> begin
(

let _84_373 = (with_monitor job_queue (fun _84_370 -> (match (()) with
| () -> begin
(let _178_332 = (FStar_ST.read pending_jobs)
in (let _178_331 = (let _178_330 = (FStar_ST.read job_queue)
in (FStar_List.length _178_330))
in ((_178_332), (_178_331))))
end)))
in (match (_84_373) with
| (n, m) -> begin
if ((n + m) = (Prims.parse_int "0")) then begin
(let _178_333 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _178_333 Prims.ignore))
end else begin
(

let _84_374 = (FStar_Util.sleep (Prims.parse_int "500"))
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

let _84_377 = (let _178_337 = (let _178_336 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[])::_178_336)
in (FStar_ST.op_Colon_Equals fresh_scope _178_337))
in (let _178_339 = (let _178_338 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[]) _178_338))
in (FStar_ST.op_Colon_Equals bg_scope _178_339))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _84_380 = (let _178_343 = (let _178_342 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _178_342))
in (FStar_ST.op_Colon_Equals fresh_scope _178_343))
in (let _178_345 = (let _178_344 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Pop)::(FStar_SMTEncoding_Term.Caption (msg))::[]) _178_344))
in (FStar_ST.op_Colon_Equals bg_scope _178_345))))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (

let _84_388 = (match ((FStar_ST.read fresh_scope)) with
| (hd)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _84_387 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _178_349 = (let _178_348 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _178_348))
in (FStar_ST.op_Colon_Equals bg_scope _178_349))))


let bgtheory : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun fresh -> if fresh then begin
(let _178_353 = (let _178_352 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _178_352))
in (FStar_All.pipe_right _178_353 FStar_List.flatten))
end else begin
(

let bg = (FStar_ST.read bg_scope)
in (

let _84_392 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)


let refresh : Prims.unit  ->  Prims.unit = (fun _84_394 -> (match (()) with
| () -> begin
(

let _84_395 = (bg_z3_proc.refresh ())
in (

let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _84_400 = (pop msg)
in (refresh ())))


let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| (hd)::(s)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _84_409 -> begin
(FStar_All.failwith "Impossible")
end))


let ask : unsat_core  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  (((unsat_core, (FStar_SMTEncoding_Term.error_labels * Prims.bool)) FStar_Util.either * Prims.int)  ->  Prims.unit)  ->  Prims.unit = (fun core label_messages qry cb -> (

let filter_assertions = (fun theory -> (match (core) with
| None -> begin
((theory), (false))
end
| Some (core) -> begin
(

let _84_437 = (FStar_List.fold_right (fun d _84_423 -> (match (_84_423) with
| (theory, n_retained, n_pruned) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (_84_425, _84_427, Some (name)) -> begin
if (FStar_List.contains name core) then begin
(((d)::theory), ((n_retained + (Prims.parse_int "1"))), (n_pruned))
end else begin
if (FStar_Util.starts_with name "@") then begin
(((d)::theory), (n_retained), (n_pruned))
end else begin
((theory), (n_retained), ((n_pruned + (Prims.parse_int "1"))))
end
end
end
| _84_433 -> begin
(((d)::theory), (n_retained), (n_pruned))
end)
end)) theory (([]), ((Prims.parse_int "0")), ((Prims.parse_int "0"))))
in (match (_84_437) with
| (theory', n_retained, n_pruned) -> begin
(

let missed_assertions = (fun th core -> (

let missed = (let _178_385 = (FStar_All.pipe_right core (FStar_List.filter (fun nm -> (let _178_384 = (FStar_All.pipe_right th (FStar_Util.for_some (fun _84_4 -> (match (_84_4) with
| FStar_SMTEncoding_Term.Assume (_84_444, _84_446, Some (nm')) -> begin
(nm = nm')
end
| _84_452 -> begin
false
end))))
in (FStar_All.pipe_right _178_384 Prims.op_Negation)))))
in (FStar_All.pipe_right _178_385 (FStar_String.concat ", ")))
in (

let included = (let _178_387 = (FStar_All.pipe_right th (FStar_List.collect (fun _84_5 -> (match (_84_5) with
| FStar_SMTEncoding_Term.Assume (_84_456, _84_458, Some (nm)) -> begin
(nm)::[]
end
| _84_464 -> begin
[]
end))))
in (FStar_All.pipe_right _178_387 (FStar_String.concat ", ")))
in (FStar_Util.format2 "missed={%s}; included={%s}" missed included))))
in (

let _84_468 = if ((FStar_Options.hint_info ()) && (FStar_Options.debug_any ())) then begin
(

let n = (FStar_List.length core)
in (

let missed = if (n <> n_retained) then begin
(missed_assertions theory' core)
end else begin
""
end
in (let _178_391 = (FStar_Util.string_of_int n_retained)
in (let _178_390 = if (n <> n_retained) then begin
(let _178_388 = (FStar_Util.string_of_int n)
in (FStar_Util.format2 " (expected %s (%s); replay may be inaccurate)" _178_388 missed))
end else begin
""
end
in (let _178_389 = (FStar_Util.string_of_int n_pruned)
in (FStar_Util.print3 "Hint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n" _178_391 _178_390 _178_389))))))
end else begin
()
end
in (let _178_396 = (let _178_395 = (let _178_394 = (let _178_393 = (let _178_392 = (FStar_All.pipe_right core (FStar_String.concat ", "))
in (Prims.strcat "UNSAT CORE: " _178_392))
in FStar_SMTEncoding_Term.Caption (_178_393))
in (_178_394)::[])
in (FStar_List.append theory' _178_395))
in ((_178_396), (true)))))
end))
end))
in (

let theory = (bgtheory false)
in (

let theory = (FStar_List.append theory (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[]))))
in (

let _84_474 = (filter_assertions theory)
in (match (_84_474) with
| (theory, used_unsat_core) -> begin
(

let cb = (fun _84_478 -> (match (_84_478) with
| (uc_errs, time) -> begin
if used_unsat_core then begin
(match (uc_errs) with
| FStar_Util.Inl (_84_480) -> begin
(cb ((uc_errs), (time)))
end
| FStar_Util.Inr (_84_483) -> begin
(cb ((FStar_Util.Inr ((([]), (false)))), (time)))
end)
end else begin
(cb ((uc_errs), (time)))
end
end))
in (

let input = (let _178_399 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ())) theory)
in (FStar_All.pipe_right _178_399 (FStar_String.concat "\n")))
in (

let _84_486 = if (FStar_Options.log_queries ()) then begin
(query_logging.append_to_log input)
end else begin
()
end
in (enqueue false {job = (z3_job false label_messages input); callback = cb}))))
end))))))




