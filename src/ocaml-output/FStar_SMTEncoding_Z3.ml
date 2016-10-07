
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
| Z3V_Unknown (_84_9) -> begin
_84_9
end))


let ___Z3V____0 = (fun projectee -> (match (projectee) with
| Z3V (_84_12) -> begin
_84_12
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


let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _84_25 -> (match (_84_25) with
| (w1, w2, w3) -> begin
(match (known) with
| Z3V_Unknown (_84_27) -> begin
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


let get_z3version : Prims.unit  ->  z3version = (fun _84_39 -> (match (()) with
| () -> begin
(

let prefix = "Z3 version "
in (match ((FStar_ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(

let _84_49 = (let _178_44 = (FStar_Options.z3_exe ())
in (FStar_Util.run_proc _178_44 "-version" ""))
in (match (_84_49) with
| (_84_45, out, _84_48) -> begin
(

let out = (match ((FStar_Util.splitlines out)) with
| (x)::_84_51 when (FStar_Util.starts_with x prefix) -> begin
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
| _84_59 -> begin
[]
end
in (match (x) with
| (i1)::(i2)::(i3)::[] -> begin
Z3V (((i1), (i2), (i3)))
end
| _84_68 -> begin
Z3V_Unknown (out)
end)))
end
| _84_70 -> begin
Z3V_Unknown (out)
end)
in (

let _84_72 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))


let ini_params : Prims.unit  ->  Prims.string = (fun _84_74 -> (match (()) with
| () -> begin
(

let z3_v = (get_z3version ())
in (

let _84_76 = if (let _178_50 = (get_z3version ())
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
| UNSAT (_84_80) -> begin
_84_80
end))


let ___SAT____0 = (fun projectee -> (match (projectee) with
| SAT (_84_83) -> begin
_84_83
end))


let ___UNKNOWN____0 = (fun projectee -> (match (projectee) with
| UNKNOWN (_84_86) -> begin
_84_86
end))


let ___TIMEOUT____0 = (fun projectee -> (match (projectee) with
| TIMEOUT (_84_89) -> begin
_84_89
end))


let status_to_string : z3status  ->  Prims.string = (fun _84_2 -> (match (_84_2) with
| SAT (_84_92) -> begin
"sat"
end
| UNSAT (_84_95) -> begin
"unsat"
end
| UNKNOWN (_84_98) -> begin
"unknown"
end
| TIMEOUT (_84_101) -> begin
"timeout"
end))


let tid : Prims.unit  ->  Prims.string = (fun _84_103 -> (match (()) with
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
{get_module_name : Prims.unit  ->  Prims.string; set_module_name : Prims.string  ->  Prims.unit; append_to_log : Prims.string  ->  Prims.unit; close_log : Prims.unit  ->  Prims.unit; log_file_name : Prims.unit  ->  Prims.string}


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

let get_module_name = (fun _84_126 -> (match (()) with
| () -> begin
(match ((FStar_ST.read current_module_name)) with
| None -> begin
(FStar_All.failwith "Module name not set")
end
| Some (n) -> begin
n
end)
end))
in (

let new_log_file = (fun _84_131 -> (match (()) with
| () -> begin
(match ((FStar_ST.read current_module_name)) with
| None -> begin
(FStar_All.failwith "current module not set")
end
| Some (n) -> begin
(

let file_name = (match ((let _178_204 = (FStar_ST.read used_file_names)
in (FStar_List.tryFind (fun _84_138 -> (match (_84_138) with
| (m, _84_137) -> begin
(n = m)
end)) _178_204))) with
| None -> begin
(

let _84_140 = (let _178_206 = (let _178_205 = (FStar_ST.read used_file_names)
in (((n), ((Prims.parse_int "0"))))::_178_205)
in (FStar_ST.op_Colon_Equals used_file_names _178_206))
in n)
end
| Some (_84_143, k) -> begin
(

let _84_147 = (let _178_208 = (let _178_207 = (FStar_ST.read used_file_names)
in (((n), ((k + (Prims.parse_int "1")))))::_178_207)
in (FStar_ST.op_Colon_Equals used_file_names _178_208))
in (let _178_209 = (FStar_Util.string_of_int (k + (Prims.parse_int "1")))
in (FStar_Util.format2 "%s-%s" n _178_209)))
end)
in (

let file_name = (FStar_Util.format1 "queries-%s.smt2" file_name)
in (

let _84_151 = (FStar_ST.op_Colon_Equals current_file_name (Some (file_name)))
in (

let fh = (FStar_Util.open_file_for_writing file_name)
in (

let _84_154 = (FStar_ST.op_Colon_Equals log_file_opt (Some (fh)))
in fh)))))
end)
end))
in (

let get_log_file = (fun _84_157 -> (match (()) with
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

let append_to_log = (fun str -> (let _178_214 = (get_log_file ())
in (FStar_Util.append_to_file _178_214 str)))
in (

let close_log = (fun _84_164 -> (match (()) with
| () -> begin
(match ((FStar_ST.read log_file_opt)) with
| None -> begin
()
end
| Some (fh) -> begin
(

let _84_168 = (FStar_Util.close_file fh)
in (FStar_ST.op_Colon_Equals log_file_opt None))
end)
end))
in (

let log_file_name = (fun _84_171 -> (match (()) with
| () -> begin
(match ((FStar_ST.read current_file_name)) with
| None -> begin
(FStar_All.failwith "no log file")
end
| Some (n) -> begin
n
end)
end))
in {get_module_name = get_module_name; set_module_name = set_module_name; append_to_log = append_to_log; close_log = close_log; log_file_name = log_file_name})))))))))))


let bg_z3_proc : bgproc = (

let the_z3proc = (FStar_Util.mk_ref None)
in (

let new_proc = (

let ctr = (FStar_Util.mk_ref (~- ((Prims.parse_int "1"))))
in (fun _84_177 -> (match (()) with
| () -> begin
(let _178_223 = (let _178_222 = (

let _84_178 = (FStar_Util.incr ctr)
in (let _178_221 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _178_221 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _178_222))
in (new_z3proc _178_223))
end)))
in (

let z3proc = (fun _84_182 -> (match (()) with
| () -> begin
(

let _84_183 = if ((FStar_ST.read the_z3proc) = None) then begin
(let _178_227 = (let _178_226 = (new_proc ())
in Some (_178_226))
in (FStar_ST.op_Colon_Equals the_z3proc _178_227))
end else begin
()
end
in (let _178_228 = (FStar_ST.read the_z3proc)
in (FStar_Util.must _178_228)))
end))
in (

let x = []
in (

let grab = (fun _84_187 -> (match (()) with
| () -> begin
(

let _84_188 = (FStar_Util.monitor_enter x)
in (z3proc ()))
end))
in (

let release = (fun _84_191 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (

let refresh = (fun _84_193 -> (match (()) with
| () -> begin
(

let proc = (grab ())
in (

let _84_195 = (FStar_Util.kill_process proc)
in (

let _84_197 = (let _178_236 = (let _178_235 = (new_proc ())
in Some (_178_235))
in (FStar_ST.op_Colon_Equals the_z3proc _178_236))
in (

let _84_199 = (query_logging.close_log ())
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
(let _178_248 = (FStar_All.pipe_right (FStar_Util.split s " ") (FStar_Util.sort_with FStar_String.compare))
in (FStar_All.pipe_right _178_248 (fun _178_247 -> Some (_178_247))))
end)))
in (match (lines) with
| ("<unsat-core>")::(core)::("</unsat-core>")::rest -> begin
(let _178_249 = (parse_core core)
in ((_178_249), (lines)))
end
| _84_220 -> begin
((None), (lines))
end)))
in (

let rec lblnegs = (fun lines -> (match (lines) with
| (lname)::("false")::rest -> begin
(let _178_252 = (lblnegs rest)
in (lname)::_178_252)
end
| (lname)::(_84_230)::rest -> begin
(lblnegs rest)
end
| _84_235 -> begin
[]
end))
in (

let rec unsat_core_and_lblnegs = (fun lines -> (

let _84_240 = (unsat_core lines)
in (match (_84_240) with
| (core_opt, rest) -> begin
(let _178_255 = (lblnegs rest)
in ((core_opt), (_178_255)))
end)))
in (

let rec result = (fun x -> (match (x) with
| ("timeout")::tl -> begin
TIMEOUT ([])
end
| ("unknown")::tl -> begin
(let _178_259 = (let _178_258 = (unsat_core_and_lblnegs tl)
in (Prims.snd _178_258))
in UNKNOWN (_178_259))
end
| ("sat")::tl -> begin
(let _178_261 = (let _178_260 = (unsat_core_and_lblnegs tl)
in (Prims.snd _178_260))
in SAT (_178_261))
end
| ("unsat")::tl -> begin
(let _178_263 = (let _178_262 = (unsat_core tl)
in (Prims.fst _178_262))
in UNSAT (_178_263))
end
| (hd)::tl -> begin
(

let _84_258 = (let _178_265 = (let _178_264 = (query_logging.get_module_name ())
in (FStar_Util.format2 "%s: Unexpected output from Z3: %s\n" _178_264 hd))
in (FStar_TypeChecker_Errors.warn FStar_Range.dummyRange _178_265))
in (result tl))
end
| _84_261 -> begin
(let _178_269 = (let _178_268 = (let _178_267 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _178_267))
in (FStar_Util.format1 "Unexpected output from Z3: got output lines: %s\n" _178_268))
in (FStar_All.pipe_left FStar_All.failwith _178_269))
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

let _84_267 = (FStar_Util.incr ctr)
in (let _178_275 = (let _178_274 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _178_274))
in (new_z3proc _178_275)))
end else begin
(bg_z3_proc.grab ())
end
in (

let res = (doZ3Exe' input z3proc)
in (

let _84_271 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))


let z3_options : Prims.unit  ->  Prims.string = (fun _84_273 -> (match (()) with
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

let _84_280 = (FStar_Util.monitor_enter m)
in (

let res = (f ())
in (

let _84_283 = (FStar_Util.monitor_exit m)
in res))))


let z3_job : Prims.bool  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list  ->  Prims.string  ->  Prims.unit  ->  ((unsat_core, (FStar_SMTEncoding_Term.error_labels * Prims.bool)) FStar_Util.either * Prims.int) = (fun fresh label_messages input _84_288 -> (match (()) with
| () -> begin
(

let is_timeout = (fun _84_3 -> (match (_84_3) with
| TIMEOUT (_84_291) -> begin
true
end
| _84_294 -> begin
false
end))
in (

let start = (FStar_Util.now ())
in (

let status = (doZ3Exe fresh input)
in (

let _84_301 = (let _178_313 = (FStar_Util.now ())
in (FStar_Util.time_diff start _178_313))
in (match (_84_301) with
| (_84_299, elapsed_time) -> begin
(

let result = (match (status) with
| UNSAT (core) -> begin
((FStar_Util.Inl (core)), (elapsed_time))
end
| (TIMEOUT (lblnegs)) | (SAT (lblnegs)) | (UNKNOWN (lblnegs)) -> begin
(

let _84_308 = if (FStar_Options.debug_any ()) then begin
(let _178_314 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _178_314))
end else begin
()
end
in (

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _84_316 -> (match (_84_316) with
| (m, _84_313, _84_315) -> begin
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


let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _84_325 -> (match (()) with
| () -> begin
(

let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (hd)::tl -> begin
(

let _84_330 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (

let _84_333 = (FStar_Util.incr pending_jobs)
in (

let _84_335 = (FStar_Util.monitor_exit job_queue)
in (

let _84_337 = (run_job j)
in (

let _84_340 = (with_monitor job_queue (fun _84_339 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (

let _84_342 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _84_344 -> (match (()) with
| () -> begin
(

let _84_345 = (FStar_Util.monitor_enter job_queue)
in (

let rec aux = (fun _84_348 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(

let _84_350 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _84_353 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _178_326 = (j.job ())
in (FStar_All.pipe_left j.callback _178_326)))


let init : Prims.unit  ->  Prims.unit = (fun _84_355 -> (match (()) with
| () -> begin
(

let n_runners = ((FStar_Options.n_cores ()) - (Prims.parse_int "1"))
in (

let rec aux = (fun n -> if (n = (Prims.parse_int "0")) then begin
()
end else begin
(

let _84_359 = (FStar_Util.spawn dequeue)
in (aux (n - (Prims.parse_int "1"))))
end)
in (aux n_runners)))
end))


let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(

let _84_363 = (FStar_Util.monitor_enter job_queue)
in (

let _84_365 = (let _178_336 = (let _178_335 = (FStar_ST.read job_queue)
in (FStar_List.append _178_335 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _178_336))
in (

let _84_367 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)


let finish : Prims.unit  ->  Prims.unit = (fun _84_369 -> (match (()) with
| () -> begin
(

let bg = (bg_z3_proc.grab ())
in (

let _84_371 = (FStar_Util.kill_process bg)
in (

let _84_373 = (bg_z3_proc.release ())
in (

let rec aux = (fun _84_376 -> (match (()) with
| () -> begin
(

let _84_380 = (with_monitor job_queue (fun _84_377 -> (match (()) with
| () -> begin
(let _178_344 = (FStar_ST.read pending_jobs)
in (let _178_343 = (let _178_342 = (FStar_ST.read job_queue)
in (FStar_List.length _178_342))
in ((_178_344), (_178_343))))
end)))
in (match (_84_380) with
| (n, m) -> begin
if ((n + m) = (Prims.parse_int "0")) then begin
(let _178_345 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _178_345 Prims.ignore))
end else begin
(

let _84_381 = (FStar_Util.sleep (Prims.parse_int "500"))
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

let _84_384 = (let _178_349 = (let _178_348 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[])::_178_348)
in (FStar_ST.op_Colon_Equals fresh_scope _178_349))
in (let _178_351 = (let _178_350 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[]) _178_350))
in (FStar_ST.op_Colon_Equals bg_scope _178_351))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _84_387 = (let _178_355 = (let _178_354 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _178_354))
in (FStar_ST.op_Colon_Equals fresh_scope _178_355))
in (let _178_357 = (let _178_356 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Pop)::(FStar_SMTEncoding_Term.Caption (msg))::[]) _178_356))
in (FStar_ST.op_Colon_Equals bg_scope _178_357))))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (

let _84_395 = (FStar_All.pipe_right decls (FStar_List.iter (fun _84_4 -> (match (_84_4) with
| (FStar_SMTEncoding_Term.Push) | (FStar_SMTEncoding_Term.Pop) -> begin
(FStar_All.failwith "Unexpected push/pop")
end
| _84_394 -> begin
()
end))))
in (

let _84_402 = (match ((FStar_ST.read fresh_scope)) with
| (hd)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _84_401 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _178_362 = (let _178_361 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _178_361))
in (FStar_ST.op_Colon_Equals bg_scope _178_362)))))


let bgtheory : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun fresh -> if fresh then begin
(

let _84_405 = (FStar_ST.op_Colon_Equals bg_scope [])
in (let _178_366 = (let _178_365 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _178_365))
in (FStar_All.pipe_right _178_366 FStar_List.flatten)))
end else begin
(

let bg = (FStar_ST.read bg_scope)
in (

let _84_408 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)


let refresh : Prims.unit  ->  Prims.unit = (fun _84_410 -> (match (()) with
| () -> begin
(

let _84_411 = (bg_z3_proc.refresh ())
in (

let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _84_416 = (pop msg)
in (refresh ())))


let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| (hd)::(s)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _84_425 -> begin
(FStar_All.failwith "Impossible")
end))


let ask : unsat_core  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  (((unsat_core, (FStar_SMTEncoding_Term.error_labels * Prims.bool)) FStar_Util.either * Prims.int)  ->  Prims.unit)  ->  Prims.unit = (fun core label_messages qry cb -> (

let filter_assertions = (fun theory -> (match (core) with
| None -> begin
((theory), (false))
end
| Some (core) -> begin
(

let _84_453 = (FStar_List.fold_right (fun d _84_439 -> (match (_84_439) with
| (theory, n_retained, n_pruned) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (_84_441, _84_443, Some (name)) -> begin
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
| _84_449 -> begin
(((d)::theory), (n_retained), (n_pruned))
end)
end)) theory (([]), ((Prims.parse_int "0")), ((Prims.parse_int "0"))))
in (match (_84_453) with
| (theory', n_retained, n_pruned) -> begin
(

let missed_assertions = (fun th core -> (

let missed = (let _178_398 = (FStar_All.pipe_right core (FStar_List.filter (fun nm -> (let _178_397 = (FStar_All.pipe_right th (FStar_Util.for_some (fun _84_5 -> (match (_84_5) with
| FStar_SMTEncoding_Term.Assume (_84_460, _84_462, Some (nm')) -> begin
(nm = nm')
end
| _84_468 -> begin
false
end))))
in (FStar_All.pipe_right _178_397 Prims.op_Negation)))))
in (FStar_All.pipe_right _178_398 (FStar_String.concat ", ")))
in (

let included = (let _178_400 = (FStar_All.pipe_right th (FStar_List.collect (fun _84_6 -> (match (_84_6) with
| FStar_SMTEncoding_Term.Assume (_84_472, _84_474, Some (nm)) -> begin
(nm)::[]
end
| _84_480 -> begin
[]
end))))
in (FStar_All.pipe_right _178_400 (FStar_String.concat ", ")))
in (FStar_Util.format2 "missed={%s}; included={%s}" missed included))))
in (

let _84_484 = if ((FStar_Options.hint_info ()) && (FStar_Options.debug_any ())) then begin
(

let n = (FStar_List.length core)
in (

let missed = if (n <> n_retained) then begin
(missed_assertions theory' core)
end else begin
""
end
in (let _178_404 = (FStar_Util.string_of_int n_retained)
in (let _178_403 = if (n <> n_retained) then begin
(let _178_401 = (FStar_Util.string_of_int n)
in (FStar_Util.format2 " (expected %s (%s); replay may be inaccurate)" _178_401 missed))
end else begin
""
end
in (let _178_402 = (FStar_Util.string_of_int n_pruned)
in (FStar_Util.print3 "Hint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n" _178_404 _178_403 _178_402))))))
end else begin
()
end
in (let _178_409 = (let _178_408 = (let _178_407 = (let _178_406 = (let _178_405 = (FStar_All.pipe_right core (FStar_String.concat ", "))
in (Prims.strcat "UNSAT CORE: " _178_405))
in FStar_SMTEncoding_Term.Caption (_178_406))
in (_178_407)::[])
in (FStar_List.append theory' _178_408))
in ((_178_409), (true)))))
end))
end))
in (

let theory = (bgtheory false)
in (

let theory = (FStar_List.append theory (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[]))))
in (

let _84_490 = (filter_assertions theory)
in (match (_84_490) with
| (theory, used_unsat_core) -> begin
(

let cb = (fun _84_494 -> (match (_84_494) with
| (uc_errs, time) -> begin
if used_unsat_core then begin
(match (uc_errs) with
| FStar_Util.Inl (_84_496) -> begin
(cb ((uc_errs), (time)))
end
| FStar_Util.Inr (_84_499) -> begin
(cb ((FStar_Util.Inr ((([]), (false)))), (time)))
end)
end else begin
(cb ((uc_errs), (time)))
end
end))
in (

let input = (let _178_412 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ())) theory)
in (FStar_All.pipe_right _178_412 (FStar_String.concat "\n")))
in (

let _84_502 = if (FStar_Options.log_queries ()) then begin
(query_logging.append_to_log input)
end else begin
()
end
in (enqueue false {job = (z3_job false label_messages input); callback = cb}))))
end))))))




