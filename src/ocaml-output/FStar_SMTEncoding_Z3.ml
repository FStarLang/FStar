
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
| Z3V_Unknown (_85_9) -> begin
_85_9
end))


let ___Z3V____0 = (fun projectee -> (match (projectee) with
| Z3V (_85_12) -> begin
_85_12
end))


let z3version_as_string : z3version  ->  Prims.string = (fun _85_1 -> (match (_85_1) with
| Z3V_Unknown (s) -> begin
(FStar_Util.format1 "unknown version: %s" s)
end
| Z3V (i, j, k) -> begin
(let _180_33 = (FStar_Util.string_of_int i)
in (let _180_32 = (FStar_Util.string_of_int j)
in (let _180_31 = (FStar_Util.string_of_int k)
in (FStar_Util.format3 "%s.%s.%s" _180_33 _180_32 _180_31))))
end))


let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _85_25 -> (match (_85_25) with
| (w1, w2, w3) -> begin
(match (known) with
| Z3V_Unknown (_85_27) -> begin
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


let get_z3version : Prims.unit  ->  z3version = (fun _85_39 -> (match (()) with
| () -> begin
(

let prefix = "Z3 version "
in (match ((FStar_ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(

let _85_49 = (let _180_44 = (FStar_Options.z3_exe ())
in (FStar_Util.run_proc _180_44 "-version" ""))
in (match (_85_49) with
| (_85_45, out, _85_48) -> begin
(

let out = (match ((FStar_Util.splitlines out)) with
| (x)::_85_51 when (FStar_Util.starts_with x prefix) -> begin
(

let x = (let _180_45 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _180_45))
in (

let x = try
(match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)
with
| _85_59 -> begin
[]
end
in (match (x) with
| (i1)::(i2)::(i3)::[] -> begin
Z3V (((i1), (i2), (i3)))
end
| _85_68 -> begin
Z3V_Unknown (out)
end)))
end
| _85_70 -> begin
Z3V_Unknown (out)
end)
in (

let _85_72 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))


let ini_params : Prims.unit  ->  Prims.string = (fun _85_74 -> (match (()) with
| () -> begin
(

let z3_v = (get_z3version ())
in (

let _85_76 = if (let _180_50 = (get_z3version ())
in (z3v_le _180_50 (((Prims.parse_int "4")), ((Prims.parse_int "4")), ((Prims.parse_int "0"))))) then begin
(let _180_53 = (let _180_52 = (let _180_51 = (z3version_as_string z3_v)
in (FStar_Util.format1 "Z3 v4.4.1 is required; got %s\n" _180_51))
in FStar_Util.Failure (_180_52))
in (FStar_All.pipe_left Prims.raise _180_53))
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
| UNSAT (_85_80) -> begin
_85_80
end))


let ___SAT____0 = (fun projectee -> (match (projectee) with
| SAT (_85_83) -> begin
_85_83
end))


let ___UNKNOWN____0 = (fun projectee -> (match (projectee) with
| UNKNOWN (_85_86) -> begin
_85_86
end))


let ___TIMEOUT____0 = (fun projectee -> (match (projectee) with
| TIMEOUT (_85_89) -> begin
_85_89
end))


let status_to_string : z3status  ->  Prims.string = (fun _85_2 -> (match (_85_2) with
| SAT (_85_92) -> begin
"sat"
end
| UNSAT (_85_95) -> begin
"unsat"
end
| UNKNOWN (_85_98) -> begin
"unknown"
end
| TIMEOUT (_85_101) -> begin
"timeout"
end))


let tid : Prims.unit  ->  Prims.string = (fun _85_103 -> (match (()) with
| () -> begin
(let _180_114 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _180_114 FStar_Util.string_of_int))
end))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (let _180_122 = (FStar_Options.z3_exe ())
in (let _180_121 = (ini_params ())
in (FStar_Util.start_process id _180_122 _180_121 cond)))))


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

let get_module_name = (fun _85_126 -> (match (()) with
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

let new_log_file = (fun _85_131 -> (match (()) with
| () -> begin
(match ((FStar_ST.read current_module_name)) with
| None -> begin
(FStar_All.failwith "current module not set")
end
| Some (n) -> begin
(

let file_name = (match ((let _180_204 = (FStar_ST.read used_file_names)
in (FStar_List.tryFind (fun _85_138 -> (match (_85_138) with
| (m, _85_137) -> begin
(n = m)
end)) _180_204))) with
| None -> begin
(

let _85_140 = (let _180_206 = (let _180_205 = (FStar_ST.read used_file_names)
in (((n), ((Prims.parse_int "0"))))::_180_205)
in (FStar_ST.op_Colon_Equals used_file_names _180_206))
in n)
end
| Some (_85_143, k) -> begin
(

let _85_147 = (let _180_208 = (let _180_207 = (FStar_ST.read used_file_names)
in (((n), ((k + (Prims.parse_int "1")))))::_180_207)
in (FStar_ST.op_Colon_Equals used_file_names _180_208))
in (let _180_209 = (FStar_Util.string_of_int (k + (Prims.parse_int "1")))
in (FStar_Util.format2 "%s-%s" n _180_209)))
end)
in (

let file_name = (FStar_Util.format1 "queries-%s.smt2" file_name)
in (

let _85_151 = (FStar_ST.op_Colon_Equals current_file_name (Some (file_name)))
in (

let fh = (FStar_Util.open_file_for_writing file_name)
in (

let _85_154 = (FStar_ST.op_Colon_Equals log_file_opt (Some (fh)))
in fh)))))
end)
end))
in (

let get_log_file = (fun _85_157 -> (match (()) with
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

let append_to_log = (fun str -> (let _180_214 = (get_log_file ())
in (FStar_Util.append_to_file _180_214 str)))
in (

let close_log = (fun _85_164 -> (match (()) with
| () -> begin
(match ((FStar_ST.read log_file_opt)) with
| None -> begin
()
end
| Some (fh) -> begin
(

let _85_168 = (FStar_Util.close_file fh)
in (FStar_ST.op_Colon_Equals log_file_opt None))
end)
end))
in (

let log_file_name = (fun _85_171 -> (match (()) with
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
in (fun _85_177 -> (match (()) with
| () -> begin
(let _180_223 = (let _180_222 = (

let _85_178 = (FStar_Util.incr ctr)
in (let _180_221 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _180_221 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _180_222))
in (new_z3proc _180_223))
end)))
in (

let z3proc = (fun _85_182 -> (match (()) with
| () -> begin
(

let _85_183 = if ((FStar_ST.read the_z3proc) = None) then begin
(let _180_227 = (let _180_226 = (new_proc ())
in Some (_180_226))
in (FStar_ST.op_Colon_Equals the_z3proc _180_227))
end else begin
()
end
in (let _180_228 = (FStar_ST.read the_z3proc)
in (FStar_Util.must _180_228)))
end))
in (

let x = []
in (

let grab = (fun _85_187 -> (match (()) with
| () -> begin
(

let _85_188 = (FStar_Util.monitor_enter x)
in (z3proc ()))
end))
in (

let release = (fun _85_191 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (

let refresh = (fun _85_193 -> (match (()) with
| () -> begin
(

let proc = (grab ())
in (

let _85_195 = (FStar_Util.kill_process proc)
in (

let _85_197 = (let _180_236 = (let _180_235 = (new_proc ())
in Some (_180_235))
in (FStar_ST.op_Colon_Equals the_z3proc _180_236))
in (

let _85_199 = (query_logging.close_log ())
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
(let _180_248 = (FStar_All.pipe_right (FStar_Util.split s " ") (FStar_Util.sort_with FStar_String.compare))
in (FStar_All.pipe_right _180_248 (fun _180_247 -> Some (_180_247))))
end)))
in (match (lines) with
| ("<unsat-core>")::(core)::("</unsat-core>")::rest -> begin
(let _180_249 = (parse_core core)
in ((_180_249), (lines)))
end
| _85_220 -> begin
((None), (lines))
end)))
in (

let rec lblnegs = (fun lines -> (match (lines) with
| (lname)::("false")::rest -> begin
(let _180_252 = (lblnegs rest)
in (lname)::_180_252)
end
| (lname)::(_85_230)::rest -> begin
(lblnegs rest)
end
| _85_235 -> begin
[]
end))
in (

let rec unsat_core_and_lblnegs = (fun lines -> (

let _85_240 = (unsat_core lines)
in (match (_85_240) with
| (core_opt, rest) -> begin
(let _180_255 = (lblnegs rest)
in ((core_opt), (_180_255)))
end)))
in (

let rec result = (fun x -> (match (x) with
| ("timeout")::tl -> begin
TIMEOUT ([])
end
| ("unknown")::tl -> begin
(let _180_259 = (let _180_258 = (unsat_core_and_lblnegs tl)
in (Prims.snd _180_258))
in UNKNOWN (_180_259))
end
| ("sat")::tl -> begin
(let _180_261 = (let _180_260 = (unsat_core_and_lblnegs tl)
in (Prims.snd _180_260))
in SAT (_180_261))
end
| ("unsat")::tl -> begin
(let _180_263 = (let _180_262 = (unsat_core tl)
in (Prims.fst _180_262))
in UNSAT (_180_263))
end
| (hd)::tl -> begin
(

let _85_258 = (let _180_265 = (let _180_264 = (query_logging.get_module_name ())
in (FStar_Util.format2 "%s: Unexpected output from Z3: %s\n" _180_264 hd))
in (FStar_TypeChecker_Errors.warn FStar_Range.dummyRange _180_265))
in (result tl))
end
| _85_261 -> begin
(let _180_269 = (let _180_268 = (let _180_267 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _180_267))
in (FStar_Util.format1 "Unexpected output from Z3: got output lines: %s\n" _180_268))
in (FStar_All.pipe_left FStar_All.failwith _180_269))
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

let _85_267 = (FStar_Util.incr ctr)
in (let _180_275 = (let _180_274 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _180_274))
in (new_z3proc _180_275)))
end else begin
(bg_z3_proc.grab ())
end
in (

let res = (doZ3Exe' input z3proc)
in (

let _85_271 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))


let z3_options : Prims.unit  ->  Prims.string = (fun _85_273 -> (match (()) with
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

let _85_280 = (FStar_Util.monitor_enter m)
in (

let res = (f ())
in (

let _85_283 = (FStar_Util.monitor_exit m)
in res))))


let z3_job : Prims.bool  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list  ->  Prims.string  ->  Prims.unit  ->  ((unsat_core, (FStar_SMTEncoding_Term.error_labels * Prims.bool)) FStar_Util.either * Prims.int) = (fun fresh label_messages input _85_288 -> (match (()) with
| () -> begin
(

let is_timeout = (fun _85_3 -> (match (_85_3) with
| TIMEOUT (_85_291) -> begin
true
end
| _85_294 -> begin
false
end))
in (

let start = (FStar_Util.now ())
in (

let status = (doZ3Exe fresh input)
in (

let _85_301 = (let _180_313 = (FStar_Util.now ())
in (FStar_Util.time_diff start _180_313))
in (match (_85_301) with
| (_85_299, elapsed_time) -> begin
(

let result = (match (status) with
| UNSAT (core) -> begin
((FStar_Util.Inl (core)), (elapsed_time))
end
| (TIMEOUT (lblnegs)) | (SAT (lblnegs)) | (UNKNOWN (lblnegs)) -> begin
(

let _85_308 = if (FStar_Options.debug_any ()) then begin
(let _180_314 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _180_314))
end else begin
()
end
in (

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _85_316 -> (match (_85_316) with
| (m, _85_313, _85_315) -> begin
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


let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _85_325 -> (match (()) with
| () -> begin
(

let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (hd)::tl -> begin
(

let _85_330 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (

let _85_333 = (FStar_Util.incr pending_jobs)
in (

let _85_335 = (FStar_Util.monitor_exit job_queue)
in (

let _85_337 = (run_job j)
in (

let _85_340 = (with_monitor job_queue (fun _85_339 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (

let _85_342 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _85_344 -> (match (()) with
| () -> begin
(

let _85_345 = (FStar_Util.monitor_enter job_queue)
in (

let rec aux = (fun _85_348 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(

let _85_350 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _85_353 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _180_326 = (j.job ())
in (FStar_All.pipe_left j.callback _180_326)))


let init : Prims.unit  ->  Prims.unit = (fun _85_355 -> (match (()) with
| () -> begin
(

let n_runners = ((FStar_Options.n_cores ()) - (Prims.parse_int "1"))
in (

let rec aux = (fun n -> if (n = (Prims.parse_int "0")) then begin
()
end else begin
(

let _85_359 = (FStar_Util.spawn dequeue)
in (aux (n - (Prims.parse_int "1"))))
end)
in (aux n_runners)))
end))


let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(

let _85_363 = (FStar_Util.monitor_enter job_queue)
in (

let _85_365 = (let _180_336 = (let _180_335 = (FStar_ST.read job_queue)
in (FStar_List.append _180_335 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _180_336))
in (

let _85_367 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)


let finish : Prims.unit  ->  Prims.unit = (fun _85_369 -> (match (()) with
| () -> begin
(

let bg = (bg_z3_proc.grab ())
in (

let _85_371 = (FStar_Util.kill_process bg)
in (

let _85_373 = (bg_z3_proc.release ())
in (

let rec aux = (fun _85_376 -> (match (()) with
| () -> begin
(

let _85_380 = (with_monitor job_queue (fun _85_377 -> (match (()) with
| () -> begin
(let _180_344 = (FStar_ST.read pending_jobs)
in (let _180_343 = (let _180_342 = (FStar_ST.read job_queue)
in (FStar_List.length _180_342))
in ((_180_344), (_180_343))))
end)))
in (match (_85_380) with
| (n, m) -> begin
if ((n + m) = (Prims.parse_int "0")) then begin
(let _180_345 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _180_345 Prims.ignore))
end else begin
(

let _85_381 = (FStar_Util.sleep (Prims.parse_int "500"))
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

let _85_384 = (let _180_349 = (let _180_348 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[])::_180_348)
in (FStar_ST.op_Colon_Equals fresh_scope _180_349))
in (let _180_351 = (let _180_350 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[]) _180_350))
in (FStar_ST.op_Colon_Equals bg_scope _180_351))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _85_387 = (let _180_355 = (let _180_354 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _180_354))
in (FStar_ST.op_Colon_Equals fresh_scope _180_355))
in (let _180_357 = (let _180_356 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Pop)::(FStar_SMTEncoding_Term.Caption (msg))::[]) _180_356))
in (FStar_ST.op_Colon_Equals bg_scope _180_357))))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (

let _85_395 = (FStar_All.pipe_right decls (FStar_List.iter (fun _85_4 -> (match (_85_4) with
| (FStar_SMTEncoding_Term.Push) | (FStar_SMTEncoding_Term.Pop) -> begin
(FStar_All.failwith "Unexpected push/pop")
end
| _85_394 -> begin
()
end))))
in (

let _85_402 = (match ((FStar_ST.read fresh_scope)) with
| (hd)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _85_401 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _180_362 = (let _180_361 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _180_361))
in (FStar_ST.op_Colon_Equals bg_scope _180_362)))))


let bgtheory : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun fresh -> if fresh then begin
(

let _85_405 = (FStar_ST.op_Colon_Equals bg_scope [])
in (let _180_366 = (let _180_365 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _180_365))
in (FStar_All.pipe_right _180_366 FStar_List.flatten)))
end else begin
(

let bg = (FStar_ST.read bg_scope)
in (

let _85_408 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)


let refresh : Prims.unit  ->  Prims.unit = (fun _85_410 -> (match (()) with
| () -> begin
(

let _85_411 = (bg_z3_proc.refresh ())
in (

let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _85_416 = (pop msg)
in (refresh ())))


let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| (hd)::(s)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _85_425 -> begin
(FStar_All.failwith "Impossible")
end))


let ask : unsat_core  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  (((unsat_core, (FStar_SMTEncoding_Term.error_labels * Prims.bool)) FStar_Util.either * Prims.int)  ->  Prims.unit)  ->  Prims.unit = (fun core label_messages qry cb -> (

let filter_assertions = (fun theory -> (match (core) with
| None -> begin
((theory), (false))
end
| Some (core) -> begin
(

let _85_453 = (FStar_List.fold_right (fun d _85_439 -> (match (_85_439) with
| (theory, n_retained, n_pruned) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (_85_441, _85_443, Some (name)) -> begin
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
| _85_449 -> begin
(((d)::theory), (n_retained), (n_pruned))
end)
end)) theory (([]), ((Prims.parse_int "0")), ((Prims.parse_int "0"))))
in (match (_85_453) with
| (theory', n_retained, n_pruned) -> begin
(

let missed_assertions = (fun th core -> (

let missed = (let _180_398 = (FStar_All.pipe_right core (FStar_List.filter (fun nm -> (let _180_397 = (FStar_All.pipe_right th (FStar_Util.for_some (fun _85_5 -> (match (_85_5) with
| FStar_SMTEncoding_Term.Assume (_85_460, _85_462, Some (nm')) -> begin
(nm = nm')
end
| _85_468 -> begin
false
end))))
in (FStar_All.pipe_right _180_397 Prims.op_Negation)))))
in (FStar_All.pipe_right _180_398 (FStar_String.concat ", ")))
in (

let included = (let _180_400 = (FStar_All.pipe_right th (FStar_List.collect (fun _85_6 -> (match (_85_6) with
| FStar_SMTEncoding_Term.Assume (_85_472, _85_474, Some (nm)) -> begin
(nm)::[]
end
| _85_480 -> begin
[]
end))))
in (FStar_All.pipe_right _180_400 (FStar_String.concat ", ")))
in (FStar_Util.format2 "missed={%s}; included={%s}" missed included))))
in (

let _85_484 = if ((FStar_Options.hint_info ()) && (FStar_Options.debug_any ())) then begin
(

let n = (FStar_List.length core)
in (

let missed = if (n <> n_retained) then begin
(missed_assertions theory' core)
end else begin
""
end
in (let _180_404 = (FStar_Util.string_of_int n_retained)
in (let _180_403 = if (n <> n_retained) then begin
(let _180_401 = (FStar_Util.string_of_int n)
in (FStar_Util.format2 " (expected %s (%s); replay may be inaccurate)" _180_401 missed))
end else begin
""
end
in (let _180_402 = (FStar_Util.string_of_int n_pruned)
in (FStar_Util.print3 "Hint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n" _180_404 _180_403 _180_402))))))
end else begin
()
end
in (let _180_409 = (let _180_408 = (let _180_407 = (let _180_406 = (let _180_405 = (FStar_All.pipe_right core (FStar_String.concat ", "))
in (Prims.strcat "UNSAT CORE: " _180_405))
in FStar_SMTEncoding_Term.Caption (_180_406))
in (_180_407)::[])
in (FStar_List.append theory' _180_408))
in ((_180_409), (true)))))
end))
end))
in (

let theory = (bgtheory false)
in (

let theory = (FStar_List.append theory (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[]))))
in (

let _85_490 = (filter_assertions theory)
in (match (_85_490) with
| (theory, used_unsat_core) -> begin
(

let cb = (fun _85_494 -> (match (_85_494) with
| (uc_errs, time) -> begin
if used_unsat_core then begin
(match (uc_errs) with
| FStar_Util.Inl (_85_496) -> begin
(cb ((uc_errs), (time)))
end
| FStar_Util.Inr (_85_499) -> begin
(cb ((FStar_Util.Inr ((([]), (false)))), (time)))
end)
end else begin
(cb ((uc_errs), (time)))
end
end))
in (

let input = (let _180_412 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ())) theory)
in (FStar_All.pipe_right _180_412 (FStar_String.concat "\n")))
in (

let _85_502 = if (FStar_Options.log_queries ()) then begin
(query_logging.append_to_log input)
end else begin
()
end
in (enqueue false {job = (z3_job false label_messages input); callback = cb}))))
end))))))




