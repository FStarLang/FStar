
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
| KILLED


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


let is_KILLED = (fun _discr_ -> (match (_discr_) with
| KILLED (_) -> begin
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
end
| KILLED -> begin
"killed"
end))


let tid : Prims.unit  ->  Prims.string = (fun _85_104 -> (match (()) with
| () -> begin
(let _180_115 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _180_115 FStar_Util.string_of_int))
end))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (let _180_123 = (FStar_Options.z3_exe ())
in (let _180_122 = (ini_params ())
in (FStar_Util.start_process id _180_123 _180_122 cond)))))


type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit; restart : Prims.unit  ->  Prims.unit}


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

let get_module_name = (fun _85_128 -> (match (()) with
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

let new_log_file = (fun _85_133 -> (match (()) with
| () -> begin
(match ((FStar_ST.read current_module_name)) with
| None -> begin
(FStar_All.failwith "current module not set")
end
| Some (n) -> begin
(

let file_name = (match ((let _180_214 = (FStar_ST.read used_file_names)
in (FStar_List.tryFind (fun _85_140 -> (match (_85_140) with
| (m, _85_139) -> begin
(n = m)
end)) _180_214))) with
| None -> begin
(

let _85_142 = (let _180_216 = (let _180_215 = (FStar_ST.read used_file_names)
in (((n), ((Prims.parse_int "0"))))::_180_215)
in (FStar_ST.op_Colon_Equals used_file_names _180_216))
in n)
end
| Some (_85_145, k) -> begin
(

let _85_149 = (let _180_218 = (let _180_217 = (FStar_ST.read used_file_names)
in (((n), ((k + (Prims.parse_int "1")))))::_180_217)
in (FStar_ST.op_Colon_Equals used_file_names _180_218))
in (let _180_219 = (FStar_Util.string_of_int (k + (Prims.parse_int "1")))
in (FStar_Util.format2 "%s-%s" n _180_219)))
end)
in (

let file_name = (FStar_Util.format1 "queries-%s.smt2" file_name)
in (

let _85_153 = (FStar_ST.op_Colon_Equals current_file_name (Some (file_name)))
in (

let fh = (FStar_Util.open_file_for_writing file_name)
in (

let _85_156 = (FStar_ST.op_Colon_Equals log_file_opt (Some (fh)))
in fh)))))
end)
end))
in (

let get_log_file = (fun _85_159 -> (match (()) with
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

let append_to_log = (fun str -> (let _180_224 = (get_log_file ())
in (FStar_Util.append_to_file _180_224 str)))
in (

let close_log = (fun _85_166 -> (match (()) with
| () -> begin
(match ((FStar_ST.read log_file_opt)) with
| None -> begin
()
end
| Some (fh) -> begin
(

let _85_170 = (FStar_Util.close_file fh)
in (FStar_ST.op_Colon_Equals log_file_opt None))
end)
end))
in (

let log_file_name = (fun _85_173 -> (match (()) with
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
in (fun _85_179 -> (match (()) with
| () -> begin
(let _180_233 = (let _180_232 = (

let _85_180 = (FStar_Util.incr ctr)
in (let _180_231 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _180_231 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _180_232))
in (new_z3proc _180_233))
end)))
in (

let z3proc = (fun _85_184 -> (match (()) with
| () -> begin
(

let _85_185 = if ((FStar_ST.read the_z3proc) = None) then begin
(let _180_237 = (let _180_236 = (new_proc ())
in Some (_180_236))
in (FStar_ST.op_Colon_Equals the_z3proc _180_237))
end else begin
()
end
in (let _180_238 = (FStar_ST.read the_z3proc)
in (FStar_Util.must _180_238)))
end))
in (

let x = []
in (

let grab = (fun _85_189 -> (match (()) with
| () -> begin
(

let _85_190 = (FStar_Util.monitor_enter x)
in (z3proc ()))
end))
in (

let release = (fun _85_193 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (

let refresh = (fun _85_195 -> (match (()) with
| () -> begin
(

let proc = (grab ())
in (

let _85_197 = (FStar_Util.kill_process proc)
in (

let _85_199 = (let _180_246 = (let _180_245 = (new_proc ())
in Some (_180_245))
in (FStar_ST.op_Colon_Equals the_z3proc _180_246))
in (

let _85_201 = (query_logging.close_log ())
in (release ())))))
end))
in (

let restart = (fun _85_204 -> (match (()) with
| () -> begin
(

let _85_205 = (FStar_Util.monitor_enter ())
in (

let _85_207 = (query_logging.close_log ())
in (

let _85_209 = (FStar_ST.op_Colon_Equals the_z3proc None)
in (

let _85_211 = (let _180_250 = (let _180_249 = (new_proc ())
in Some (_180_249))
in (FStar_ST.op_Colon_Equals the_z3proc _180_250))
in (FStar_Util.monitor_exit ())))))
end))
in {grab = grab; release = release; refresh = refresh; restart = restart}))))))))


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
(let _180_262 = (FStar_All.pipe_right (FStar_Util.split s " ") (FStar_Util.sort_with FStar_String.compare))
in (FStar_All.pipe_right _180_262 (fun _180_261 -> Some (_180_261))))
end)))
in (match (lines) with
| ("<unsat-core>")::(core)::("</unsat-core>")::rest -> begin
(let _180_263 = (parse_core core)
in ((_180_263), (lines)))
end
| _85_232 -> begin
((None), (lines))
end)))
in (

let rec lblnegs = (fun lines -> (match (lines) with
| (lname)::("false")::rest -> begin
(let _180_266 = (lblnegs rest)
in (lname)::_180_266)
end
| (lname)::(_85_242)::rest -> begin
(lblnegs rest)
end
| _85_247 -> begin
[]
end))
in (

let rec unsat_core_and_lblnegs = (fun lines -> (

let _85_252 = (unsat_core lines)
in (match (_85_252) with
| (core_opt, rest) -> begin
(let _180_269 = (lblnegs rest)
in ((core_opt), (_180_269)))
end)))
in (

let rec result = (fun x -> (match (x) with
| ("timeout")::tl -> begin
TIMEOUT ([])
end
| ("unknown")::tl -> begin
(let _180_273 = (let _180_272 = (unsat_core_and_lblnegs tl)
in (Prims.snd _180_272))
in UNKNOWN (_180_273))
end
| ("sat")::tl -> begin
(let _180_275 = (let _180_274 = (unsat_core_and_lblnegs tl)
in (Prims.snd _180_274))
in SAT (_180_275))
end
| ("unsat")::tl -> begin
(let _180_277 = (let _180_276 = (unsat_core tl)
in (Prims.fst _180_276))
in UNSAT (_180_277))
end
| ("killed")::tl -> begin
(

let _85_270 = (bg_z3_proc.restart ())
in KILLED)
end
| (hd)::tl -> begin
(

let _85_275 = (let _180_279 = (let _180_278 = (query_logging.get_module_name ())
in (FStar_Util.format2 "%s: Unexpected output from Z3: %s\n" _180_278 hd))
in (FStar_TypeChecker_Errors.warn FStar_Range.dummyRange _180_279))
in (result tl))
end
| _85_278 -> begin
(let _180_283 = (let _180_282 = (let _180_281 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _180_281))
in (FStar_Util.format1 "Unexpected output from Z3: got output lines: %s\n" _180_282))
in (FStar_All.pipe_left FStar_All.failwith _180_283))
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

let _85_284 = (FStar_Util.incr ctr)
in (let _180_289 = (let _180_288 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _180_288))
in (new_z3proc _180_289)))
end else begin
(bg_z3_proc.grab ())
end
in (

let res = (doZ3Exe' input z3proc)
in (

let _85_288 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))


let z3_options : Prims.unit  ->  Prims.string = (fun _85_290 -> (match (()) with
| () -> begin
"(set-option :global-decls false)(set-option :smt.mbqi false)(set-option :produce-unsat-cores true)\n"
end))


type 'a job =
{job : Prims.unit  ->  'a; callback : 'a  ->  Prims.unit}


let is_Mkjob = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkjob"))))


type error_kind =
| Timeout
| Kill
| Default


let is_Timeout = (fun _discr_ -> (match (_discr_) with
| Timeout (_) -> begin
true
end
| _ -> begin
false
end))


let is_Kill = (fun _discr_ -> (match (_discr_) with
| Kill (_) -> begin
true
end
| _ -> begin
false
end))


let is_Default = (fun _discr_ -> (match (_discr_) with
| Default (_) -> begin
true
end
| _ -> begin
false
end))


type z3job =
((unsat_core, (FStar_SMTEncoding_Term.error_labels * error_kind)) FStar_Util.either * Prims.int) job


let job_queue : z3job Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let with_monitor = (fun m f -> (

let _85_297 = (FStar_Util.monitor_enter m)
in (

let res = (f ())
in (

let _85_300 = (FStar_Util.monitor_exit m)
in res))))


let z3_job : Prims.bool  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list  ->  Prims.string  ->  Prims.unit  ->  ((unsat_core, (FStar_SMTEncoding_Term.error_labels * error_kind)) FStar_Util.either * Prims.int) = (fun fresh label_messages input _85_305 -> (match (()) with
| () -> begin
(

let ekind = (fun _85_3 -> (match (_85_3) with
| TIMEOUT (_85_308) -> begin
Timeout
end
| (SAT (_)) | (UNKNOWN (_)) -> begin
Default
end
| KILLED -> begin
Kill
end
| _85_318 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let start = (FStar_Util.now ())
in (

let status = (doZ3Exe fresh input)
in (

let _85_325 = (let _180_330 = (FStar_Util.now ())
in (FStar_Util.time_diff start _180_330))
in (match (_85_325) with
| (_85_323, elapsed_time) -> begin
(

let result = (match (status) with
| UNSAT (core) -> begin
((FStar_Util.Inl (core)), (elapsed_time))
end
| KILLED -> begin
((FStar_Util.Inr ((([]), (Kill)))), (elapsed_time))
end
| (TIMEOUT (lblnegs)) | (SAT (lblnegs)) | (UNKNOWN (lblnegs)) -> begin
(

let _85_333 = if (FStar_Options.debug_any ()) then begin
(let _180_331 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _180_331))
end else begin
()
end
in (

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _85_341 -> (match (_85_341) with
| (m, _85_338, _85_340) -> begin
((Prims.fst m) = l)
end))))) with
| None -> begin
[]
end
| Some (lbl, msg, r) -> begin
(((lbl), (msg), (r)))::[]
end))))
in (let _180_336 = (let _180_335 = (let _180_334 = (ekind status)
in ((failing_assertions), (_180_334)))
in FStar_Util.Inr (_180_335))
in ((_180_336), (elapsed_time)))))
end)
in result)
end)))))
end))


let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _85_350 -> (match (()) with
| () -> begin
(

let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (hd)::tl -> begin
(

let _85_355 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (

let _85_358 = (FStar_Util.incr pending_jobs)
in (

let _85_360 = (FStar_Util.monitor_exit job_queue)
in (

let _85_362 = (run_job j)
in (

let _85_365 = (with_monitor job_queue (fun _85_364 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (

let _85_367 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _85_369 -> (match (()) with
| () -> begin
(

let _85_370 = (FStar_Util.monitor_enter job_queue)
in (

let rec aux = (fun _85_373 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(

let _85_375 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _85_378 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _180_346 = (j.job ())
in (FStar_All.pipe_left j.callback _180_346)))


let init : Prims.unit  ->  Prims.unit = (fun _85_380 -> (match (()) with
| () -> begin
(

let n_runners = ((FStar_Options.n_cores ()) - (Prims.parse_int "1"))
in (

let rec aux = (fun n -> if (n = (Prims.parse_int "0")) then begin
()
end else begin
(

let _85_384 = (FStar_Util.spawn dequeue)
in (aux (n - (Prims.parse_int "1"))))
end)
in (aux n_runners)))
end))


let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(

let _85_388 = (FStar_Util.monitor_enter job_queue)
in (

let _85_390 = (let _180_356 = (let _180_355 = (FStar_ST.read job_queue)
in (FStar_List.append _180_355 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _180_356))
in (

let _85_392 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)


let finish : Prims.unit  ->  Prims.unit = (fun _85_394 -> (match (()) with
| () -> begin
(

let bg = (bg_z3_proc.grab ())
in (

let _85_396 = (FStar_Util.kill_process bg)
in (

let _85_398 = (bg_z3_proc.release ())
in (

let rec aux = (fun _85_401 -> (match (()) with
| () -> begin
(

let _85_405 = (with_monitor job_queue (fun _85_402 -> (match (()) with
| () -> begin
(let _180_364 = (FStar_ST.read pending_jobs)
in (let _180_363 = (let _180_362 = (FStar_ST.read job_queue)
in (FStar_List.length _180_362))
in ((_180_364), (_180_363))))
end)))
in (match (_85_405) with
| (n, m) -> begin
if ((n + m) = (Prims.parse_int "0")) then begin
(let _180_365 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _180_365 Prims.ignore))
end else begin
(

let _85_406 = (FStar_Util.sleep (Prims.parse_int "500"))
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

let _85_409 = (let _180_369 = (let _180_368 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[])::_180_368)
in (FStar_ST.op_Colon_Equals fresh_scope _180_369))
in (let _180_371 = (let _180_370 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[]) _180_370))
in (FStar_ST.op_Colon_Equals bg_scope _180_371))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _85_412 = (let _180_375 = (let _180_374 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _180_374))
in (FStar_ST.op_Colon_Equals fresh_scope _180_375))
in (let _180_377 = (let _180_376 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Pop)::(FStar_SMTEncoding_Term.Caption (msg))::[]) _180_376))
in (FStar_ST.op_Colon_Equals bg_scope _180_377))))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (

let _85_420 = (FStar_All.pipe_right decls (FStar_List.iter (fun _85_4 -> (match (_85_4) with
| (FStar_SMTEncoding_Term.Push) | (FStar_SMTEncoding_Term.Pop) -> begin
(FStar_All.failwith "Unexpected push/pop")
end
| _85_419 -> begin
()
end))))
in (

let _85_427 = (match ((FStar_ST.read fresh_scope)) with
| (hd)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _85_426 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _180_382 = (let _180_381 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _180_381))
in (FStar_ST.op_Colon_Equals bg_scope _180_382)))))


let bgtheory : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun fresh -> if fresh then begin
(

let _85_430 = (FStar_ST.op_Colon_Equals bg_scope [])
in (let _180_386 = (let _180_385 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _180_385))
in (FStar_All.pipe_right _180_386 FStar_List.flatten)))
end else begin
(

let bg = (FStar_ST.read bg_scope)
in (

let _85_433 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)


let refresh : Prims.unit  ->  Prims.unit = (fun _85_435 -> (match (()) with
| () -> begin
(

let _85_436 = (bg_z3_proc.refresh ())
in (

let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _85_441 = (pop msg)
in (refresh ())))


let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| (hd)::(s)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _85_450 -> begin
(FStar_All.failwith "Impossible")
end))


let ask : unsat_core  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  (((unsat_core, (FStar_SMTEncoding_Term.error_labels * error_kind)) FStar_Util.either * Prims.int)  ->  Prims.unit)  ->  Prims.unit = (fun core label_messages qry cb -> (

let filter_assertions = (fun theory -> (match (core) with
| None -> begin
((theory), (false))
end
| Some (core) -> begin
(

let _85_478 = (FStar_List.fold_right (fun d _85_464 -> (match (_85_464) with
| (theory, n_retained, n_pruned) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (_85_466, _85_468, Some (name)) -> begin
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
| _85_474 -> begin
(((d)::theory), (n_retained), (n_pruned))
end)
end)) theory (([]), ((Prims.parse_int "0")), ((Prims.parse_int "0"))))
in (match (_85_478) with
| (theory', n_retained, n_pruned) -> begin
(

let missed_assertions = (fun th core -> (

let missed = (let _180_418 = (FStar_All.pipe_right core (FStar_List.filter (fun nm -> (let _180_417 = (FStar_All.pipe_right th (FStar_Util.for_some (fun _85_5 -> (match (_85_5) with
| FStar_SMTEncoding_Term.Assume (_85_485, _85_487, Some (nm')) -> begin
(nm = nm')
end
| _85_493 -> begin
false
end))))
in (FStar_All.pipe_right _180_417 Prims.op_Negation)))))
in (FStar_All.pipe_right _180_418 (FStar_String.concat ", ")))
in (

let included = (let _180_420 = (FStar_All.pipe_right th (FStar_List.collect (fun _85_6 -> (match (_85_6) with
| FStar_SMTEncoding_Term.Assume (_85_497, _85_499, Some (nm)) -> begin
(nm)::[]
end
| _85_505 -> begin
[]
end))))
in (FStar_All.pipe_right _180_420 (FStar_String.concat ", ")))
in (FStar_Util.format2 "missed={%s}; included={%s}" missed included))))
in (

let _85_509 = if ((FStar_Options.hint_info ()) && (FStar_Options.debug_any ())) then begin
(

let n = (FStar_List.length core)
in (

let missed = if (n <> n_retained) then begin
(missed_assertions theory' core)
end else begin
""
end
in (let _180_424 = (FStar_Util.string_of_int n_retained)
in (let _180_423 = if (n <> n_retained) then begin
(let _180_421 = (FStar_Util.string_of_int n)
in (FStar_Util.format2 " (expected %s (%s); replay may be inaccurate)" _180_421 missed))
end else begin
""
end
in (let _180_422 = (FStar_Util.string_of_int n_pruned)
in (FStar_Util.print3 "Hint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n" _180_424 _180_423 _180_422))))))
end else begin
()
end
in (let _180_429 = (let _180_428 = (let _180_427 = (let _180_426 = (let _180_425 = (FStar_All.pipe_right core (FStar_String.concat ", "))
in (Prims.strcat "UNSAT CORE: " _180_425))
in FStar_SMTEncoding_Term.Caption (_180_426))
in (_180_427)::[])
in (FStar_List.append theory' _180_428))
in ((_180_429), (true)))))
end))
end))
in (

let theory = (bgtheory false)
in (

let theory = (FStar_List.append theory (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[]))))
in (

let _85_515 = (filter_assertions theory)
in (match (_85_515) with
| (theory, used_unsat_core) -> begin
(

let cb = (fun _85_519 -> (match (_85_519) with
| (uc_errs, time) -> begin
if used_unsat_core then begin
(match (uc_errs) with
| FStar_Util.Inl (_85_521) -> begin
(cb ((uc_errs), (time)))
end
| FStar_Util.Inr (_85_524, ek) -> begin
(cb ((FStar_Util.Inr ((([]), (ek)))), (time)))
end)
end else begin
(cb ((uc_errs), (time)))
end
end))
in (

let input = (let _180_432 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ())) theory)
in (FStar_All.pipe_right _180_432 (FStar_String.concat "\n")))
in (

let _85_529 = if (FStar_Options.log_queries ()) then begin
(query_logging.append_to_log input)
end else begin
()
end
in (enqueue false {job = (z3_job false label_messages input); callback = cb}))))
end))))))




