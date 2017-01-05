
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
| Z3V_Unknown (_88_9) -> begin
_88_9
end))


let ___Z3V____0 = (fun projectee -> (match (projectee) with
| Z3V (_88_12) -> begin
_88_12
end))


let z3version_as_string : z3version  ->  Prims.string = (fun _88_1 -> (match (_88_1) with
| Z3V_Unknown (s) -> begin
(FStar_Util.format1 "unknown version: %s" s)
end
| Z3V (i, j, k) -> begin
(let _187_33 = (FStar_Util.string_of_int i)
in (let _187_32 = (FStar_Util.string_of_int j)
in (let _187_31 = (FStar_Util.string_of_int k)
in (FStar_Util.format3 "%s.%s.%s" _187_33 _187_32 _187_31))))
end))


let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _88_25 -> (match (_88_25) with
| (w1, w2, w3) -> begin
(match (known) with
| Z3V_Unknown (_88_27) -> begin
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


let get_z3version : Prims.unit  ->  z3version = (fun _88_39 -> (match (()) with
| () -> begin
(

let prefix = "Z3 version "
in (match ((FStar_ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(

let _88_49 = (let _187_44 = (FStar_Options.z3_exe ())
in (FStar_Util.run_proc _187_44 "-version" ""))
in (match (_88_49) with
| (_88_45, out, _88_48) -> begin
(

let out = (match ((FStar_Util.splitlines out)) with
| (x)::_88_51 when (FStar_Util.starts_with x prefix) -> begin
(

let x = (let _187_45 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _187_45))
in (

let x = try
(match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)
with
| _88_59 -> begin
[]
end
in (match (x) with
| (i1)::(i2)::(i3)::[] -> begin
Z3V (((i1), (i2), (i3)))
end
| _88_68 -> begin
Z3V_Unknown (out)
end)))
end
| _88_70 -> begin
Z3V_Unknown (out)
end)
in (

let _88_72 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))


let ini_params : Prims.unit  ->  Prims.string = (fun _88_74 -> (match (()) with
| () -> begin
(

let z3_v = (get_z3version ())
in (

let _88_76 = if (let _187_50 = (get_z3version ())
in (z3v_le _187_50 (((Prims.parse_int "4")), ((Prims.parse_int "4")), ((Prims.parse_int "0"))))) then begin
(let _187_53 = (let _187_52 = (let _187_51 = (z3version_as_string z3_v)
in (FStar_Util.format1 "Z3 4.5.0 recommended; at least Z3 v4.4.1 required; got %s\n" _187_51))
in FStar_Util.Failure (_187_52))
in (FStar_All.pipe_left Prims.raise _187_53))
end else begin
()
end
in (let _187_55 = (let _187_54 = (FStar_Options.z3_seed ())
in (FStar_Util.string_of_int _187_54))
in (FStar_Util.format1 "-smt2 -in AUTO_CONFIG=false MODEL=true SMT.RELEVANCY=2 SMT.RANDOM_SEED=%s" _187_55))))
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
| UNSAT (_88_80) -> begin
_88_80
end))


let ___SAT____0 = (fun projectee -> (match (projectee) with
| SAT (_88_83) -> begin
_88_83
end))


let ___UNKNOWN____0 = (fun projectee -> (match (projectee) with
| UNKNOWN (_88_86) -> begin
_88_86
end))


let ___TIMEOUT____0 = (fun projectee -> (match (projectee) with
| TIMEOUT (_88_89) -> begin
_88_89
end))


let status_to_string : z3status  ->  Prims.string = (fun _88_2 -> (match (_88_2) with
| SAT (_88_92) -> begin
"sat"
end
| UNSAT (_88_95) -> begin
"unsat"
end
| UNKNOWN (_88_98) -> begin
"unknown"
end
| TIMEOUT (_88_101) -> begin
"timeout"
end
| KILLED -> begin
"killed"
end))


let tid : Prims.unit  ->  Prims.string = (fun _88_104 -> (match (()) with
| () -> begin
(let _187_117 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _187_117 FStar_Util.string_of_int))
end))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (let _187_125 = (FStar_Options.z3_exe ())
in (let _187_124 = (ini_params ())
in (FStar_Util.start_process id _187_125 _187_124 cond)))))


type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit; restart : Prims.unit  ->  Prims.unit}


let is_Mkbgproc : bgproc  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkbgproc"))))


type query_log =
{get_module_name : Prims.unit  ->  Prims.string; set_module_name : Prims.string  ->  Prims.unit; append_to_log : Prims.string  ->  Prims.unit; close_log : Prims.unit  ->  Prims.unit; log_file_name : Prims.unit  ->  Prims.string}


let is_Mkquery_log : query_log  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkquery_log"))))


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

let get_module_name = (fun _88_128 -> (match (()) with
| () -> begin
(match ((FStar_ST.read current_module_name)) with
| None -> begin
(failwith "Module name not set")
end
| Some (n) -> begin
n
end)
end))
in (

let new_log_file = (fun _88_133 -> (match (()) with
| () -> begin
(match ((FStar_ST.read current_module_name)) with
| None -> begin
(failwith "current module not set")
end
| Some (n) -> begin
(

let file_name = (match ((let _187_216 = (FStar_ST.read used_file_names)
in (FStar_List.tryFind (fun _88_140 -> (match (_88_140) with
| (m, _88_139) -> begin
(n = m)
end)) _187_216))) with
| None -> begin
(

let _88_142 = (let _187_218 = (let _187_217 = (FStar_ST.read used_file_names)
in (((n), ((Prims.parse_int "0"))))::_187_217)
in (FStar_ST.op_Colon_Equals used_file_names _187_218))
in n)
end
| Some (_88_145, k) -> begin
(

let _88_149 = (let _187_220 = (let _187_219 = (FStar_ST.read used_file_names)
in (((n), ((k + (Prims.parse_int "1")))))::_187_219)
in (FStar_ST.op_Colon_Equals used_file_names _187_220))
in (let _187_221 = (FStar_Util.string_of_int (k + (Prims.parse_int "1")))
in (FStar_Util.format2 "%s-%s" n _187_221)))
end)
in (

let file_name = (FStar_Util.format1 "queries-%s.smt2" file_name)
in (

let _88_153 = (FStar_ST.op_Colon_Equals current_file_name (Some (file_name)))
in (

let fh = (FStar_Util.open_file_for_writing file_name)
in (

let _88_156 = (FStar_ST.op_Colon_Equals log_file_opt (Some (fh)))
in fh)))))
end)
end))
in (

let get_log_file = (fun _88_159 -> (match (()) with
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

let append_to_log = (fun str -> (let _187_226 = (get_log_file ())
in (FStar_Util.append_to_file _187_226 str)))
in (

let close_log = (fun _88_166 -> (match (()) with
| () -> begin
(match ((FStar_ST.read log_file_opt)) with
| None -> begin
()
end
| Some (fh) -> begin
(

let _88_170 = (FStar_Util.close_file fh)
in (FStar_ST.op_Colon_Equals log_file_opt None))
end)
end))
in (

let log_file_name = (fun _88_173 -> (match (()) with
| () -> begin
(match ((FStar_ST.read current_file_name)) with
| None -> begin
(failwith "no log file")
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
in (fun _88_179 -> (match (()) with
| () -> begin
(let _187_235 = (let _187_234 = (

let _88_180 = (FStar_Util.incr ctr)
in (let _187_233 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _187_233 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _187_234))
in (new_z3proc _187_235))
end)))
in (

let z3proc = (fun _88_184 -> (match (()) with
| () -> begin
(

let _88_185 = if ((FStar_ST.read the_z3proc) = None) then begin
(let _187_239 = (let _187_238 = (new_proc ())
in Some (_187_238))
in (FStar_ST.op_Colon_Equals the_z3proc _187_239))
end else begin
()
end
in (let _187_240 = (FStar_ST.read the_z3proc)
in (FStar_Util.must _187_240)))
end))
in (

let x = []
in (

let grab = (fun _88_189 -> (match (()) with
| () -> begin
(

let _88_190 = (FStar_Util.monitor_enter x)
in (z3proc ()))
end))
in (

let release = (fun _88_193 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (

let refresh = (fun _88_195 -> (match (()) with
| () -> begin
(

let proc = (grab ())
in (

let _88_197 = (FStar_Util.kill_process proc)
in (

let _88_199 = (let _187_248 = (let _187_247 = (new_proc ())
in Some (_187_247))
in (FStar_ST.op_Colon_Equals the_z3proc _187_248))
in (

let _88_201 = (query_logging.close_log ())
in (release ())))))
end))
in (

let restart = (fun _88_204 -> (match (()) with
| () -> begin
(

let _88_205 = (FStar_Util.monitor_enter ())
in (

let _88_207 = (query_logging.close_log ())
in (

let _88_209 = (FStar_ST.op_Colon_Equals the_z3proc None)
in (

let _88_211 = (let _187_252 = (let _187_251 = (new_proc ())
in Some (_187_251))
in (FStar_ST.op_Colon_Equals the_z3proc _187_252))
in (FStar_Util.monitor_exit ())))))
end))
in {grab = grab; release = release; refresh = refresh; restart = restart}))))))))


let at_log_file : Prims.unit  ->  Prims.string = (fun _88_213 -> (match (()) with
| () -> begin
if (FStar_Options.log_queries ()) then begin
(let _187_255 = (query_logging.log_file_name ())
in (Prims.strcat "@" _187_255))
end else begin
""
end
end))


let doZ3Exe' : Prims.string  ->  FStar_Util.proc  ->  z3status = (fun input z3proc -> (

let parse = (fun z3out -> (

let lines = (FStar_All.pipe_right (FStar_String.split (('\n')::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (

let print_stats = (fun lines -> (

let starts_with = (fun c s -> (((FStar_String.length s) >= (Prims.parse_int "1")) && ((FStar_String.get s (Prims.parse_int "0")) = c)))
in (

let ends_with = (fun c s -> (((FStar_String.length s) >= (Prims.parse_int "1")) && ((FStar_String.get s ((FStar_String.length s) - (Prims.parse_int "1"))) = c)))
in (

let last = (fun l -> (FStar_List.nth l ((FStar_List.length l) - (Prims.parse_int "1"))))
in if (FStar_Options.print_z3_statistics ()) then begin
if ((((FStar_List.length lines) >= (Prims.parse_int "2")) && (let _187_274 = (FStar_List.hd lines)
in (starts_with '(' _187_274))) && (let _187_275 = (last lines)
in (ends_with ')' _187_275))) then begin
(

let _88_229 = (let _187_279 = (let _187_278 = (let _187_276 = (query_logging.get_module_name ())
in (FStar_Util.format1 "BEGIN-STATS %s\n" _187_276))
in (let _187_277 = (at_log_file ())
in (Prims.strcat _187_278 _187_277)))
in (FStar_Util.print_string _187_279))
in (

let _88_232 = (FStar_List.iter (fun s -> (let _187_281 = (FStar_Util.format1 "%s\n" s)
in (FStar_Util.print_string _187_281))) lines)
in (FStar_Util.print_string "END-STATS\n")))
end else begin
(failwith "Unexpected output from Z3: could not find statistics\n")
end
end else begin
()
end))))
in (

let unsat_core = (fun lines -> (

let parse_core = (fun s -> (

let s = (FStar_Util.trim_string s)
in (

let s = (FStar_Util.substring s (Prims.parse_int "1") ((FStar_String.length s) - (Prims.parse_int "2")))
in if (FStar_Util.starts_with s "error") then begin
None
end else begin
(let _187_287 = (FStar_All.pipe_right (FStar_Util.split s " ") (FStar_Util.sort_with FStar_String.compare))
in (FStar_All.pipe_right _187_287 (fun _187_286 -> Some (_187_286))))
end)))
in (match (lines) with
| ("<unsat-core>")::(core)::("</unsat-core>")::rest -> begin
(let _187_288 = (parse_core core)
in ((_187_288), (lines)))
end
| _88_248 -> begin
((None), (lines))
end)))
in (

let rec lblnegs = (fun lines succeeded -> (match (lines) with
| (lname)::("false")::rest when (FStar_Util.starts_with lname "label_") -> begin
(let _187_293 = (lblnegs rest succeeded)
in (lname)::_187_293)
end
| (lname)::(_88_259)::rest when (FStar_Util.starts_with lname "label_") -> begin
(lblnegs rest succeeded)
end
| _88_264 -> begin
(

let _88_265 = if succeeded then begin
(print_stats lines)
end else begin
()
end
in [])
end))
in (

let unsat_core_and_lblnegs = (fun lines succeeded -> (

let _88_272 = (unsat_core lines)
in (match (_88_272) with
| (core_opt, rest) -> begin
(let _187_298 = (lblnegs rest succeeded)
in ((core_opt), (_187_298)))
end)))
in (

let rec result = (fun x -> (match (x) with
| ("timeout")::tl -> begin
TIMEOUT ([])
end
| ("unknown")::tl -> begin
(let _187_302 = (let _187_301 = (unsat_core_and_lblnegs tl false)
in (Prims.snd _187_301))
in UNKNOWN (_187_302))
end
| ("sat")::tl -> begin
(let _187_304 = (let _187_303 = (unsat_core_and_lblnegs tl false)
in (Prims.snd _187_303))
in SAT (_187_304))
end
| ("unsat")::tl -> begin
(let _187_306 = (let _187_305 = (unsat_core_and_lblnegs tl true)
in (Prims.fst _187_305))
in UNSAT (_187_306))
end
| ("killed")::tl -> begin
(

let _88_290 = (bg_z3_proc.restart ())
in KILLED)
end
| (hd)::tl -> begin
(

let _88_295 = (let _187_308 = (let _187_307 = (query_logging.get_module_name ())
in (FStar_Util.format2 "%s: Unexpected output from Z3: %s\n" _187_307 hd))
in (FStar_TypeChecker_Errors.warn FStar_Range.dummyRange _187_308))
in (result tl))
end
| _88_298 -> begin
(let _187_312 = (let _187_311 = (let _187_310 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _187_310))
in (FStar_Util.format1 "Unexpected output from Z3: got output lines: %s\n" _187_311))
in (FStar_All.pipe_left failwith _187_312))
end))
in (result lines))))))))
in (

let stdout = (FStar_Util.ask_process z3proc input)
in (parse (FStar_Util.trim_string stdout)))))


let doZ3Exe : Prims.bool  ->  Prims.string  ->  z3status = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun fresh input -> (

let z3proc = if fresh then begin
(

let _88_304 = (FStar_Util.incr ctr)
in (let _187_318 = (let _187_317 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _187_317))
in (new_z3proc _187_318)))
end else begin
(bg_z3_proc.grab ())
end
in (

let res = (doZ3Exe' input z3proc)
in (

let _88_308 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))


let z3_options : Prims.unit  ->  Prims.string = (fun _88_310 -> (match (()) with
| () -> begin
(let _187_322 = (let _187_321 = (FStar_Options.z3_seed ())
in (FStar_Util.string_of_int _187_321))
in (FStar_Util.format1 "(set-option :global-decls false)(set-option :smt.mbqi false)(set-option :auto_config false)(set-option :produce-unsat-cores true)(set-option :smt.random_seed %s)\n" _187_322))
end))


type 'a job =
{job : Prims.unit  ->  'a; callback : 'a  ->  Prims.unit}


let is_Mkjob = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkjob"))))


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

let _88_317 = (FStar_Util.monitor_enter m)
in (

let res = (f ())
in (

let _88_320 = (FStar_Util.monitor_exit m)
in res))))


let z3_job : Prims.bool  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list  ->  Prims.string  ->  Prims.unit  ->  ((unsat_core, (FStar_SMTEncoding_Term.error_labels * error_kind)) FStar_Util.either * Prims.int) = (fun fresh label_messages input _88_325 -> (match (()) with
| () -> begin
(

let ekind = (fun _88_3 -> (match (_88_3) with
| TIMEOUT (_88_328) -> begin
Timeout
end
| (SAT (_)) | (UNKNOWN (_)) -> begin
Default
end
| KILLED -> begin
Kill
end
| _88_338 -> begin
(failwith "Impossible")
end))
in (

let start = (FStar_Util.now ())
in (

let status = (doZ3Exe fresh input)
in (

let _88_345 = (let _187_361 = (FStar_Util.now ())
in (FStar_Util.time_diff start _187_361))
in (match (_88_345) with
| (_88_343, elapsed_time) -> begin
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

let _88_353 = if (FStar_Options.debug_any ()) then begin
(let _187_362 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _187_362))
end else begin
()
end
in (

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _88_361 -> (match (_88_361) with
| (m, _88_358, _88_360) -> begin
((Prims.fst m) = l)
end))))) with
| None -> begin
[]
end
| Some (lbl, msg, r) -> begin
(((lbl), (msg), (r)))::[]
end))))
in (let _187_367 = (let _187_366 = (let _187_365 = (ekind status)
in ((failing_assertions), (_187_365)))
in FStar_Util.Inr (_187_366))
in ((_187_367), (elapsed_time)))))
end)
in result)
end)))))
end))


let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _88_370 -> (match (()) with
| () -> begin
(

let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(failwith "Impossible")
end
| (hd)::tl -> begin
(

let _88_375 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (

let _88_378 = (FStar_Util.incr pending_jobs)
in (

let _88_380 = (FStar_Util.monitor_exit job_queue)
in (

let _88_382 = (run_job j)
in (

let _88_385 = (with_monitor job_queue (fun _88_384 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (

let _88_387 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _88_389 -> (match (()) with
| () -> begin
(

let _88_390 = (FStar_Util.monitor_enter job_queue)
in (

let rec aux = (fun _88_393 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(

let _88_395 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _88_398 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _187_377 = (j.job ())
in (FStar_All.pipe_left j.callback _187_377)))


let init : Prims.unit  ->  Prims.unit = (fun _88_400 -> (match (()) with
| () -> begin
(

let n_runners = ((FStar_Options.n_cores ()) - (Prims.parse_int "1"))
in (

let rec aux = (fun n -> if (n = (Prims.parse_int "0")) then begin
()
end else begin
(

let _88_404 = (FStar_Util.spawn dequeue)
in (aux (n - (Prims.parse_int "1"))))
end)
in (aux n_runners)))
end))


let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(

let _88_408 = (FStar_Util.monitor_enter job_queue)
in (

let _88_410 = (let _187_387 = (let _187_386 = (FStar_ST.read job_queue)
in (FStar_List.append _187_386 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _187_387))
in (

let _88_412 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)


let finish : Prims.unit  ->  Prims.unit = (fun _88_414 -> (match (()) with
| () -> begin
(

let bg = (bg_z3_proc.grab ())
in (

let _88_416 = (FStar_Util.kill_process bg)
in (

let _88_418 = (bg_z3_proc.release ())
in (

let rec aux = (fun _88_421 -> (match (()) with
| () -> begin
(

let _88_425 = (with_monitor job_queue (fun _88_422 -> (match (()) with
| () -> begin
(let _187_395 = (FStar_ST.read pending_jobs)
in (let _187_394 = (let _187_393 = (FStar_ST.read job_queue)
in (FStar_List.length _187_393))
in ((_187_395), (_187_394))))
end)))
in (match (_88_425) with
| (n, m) -> begin
if ((n + m) = (Prims.parse_int "0")) then begin
(let _187_396 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _187_396 Prims.ignore))
end else begin
(

let _88_426 = (FStar_Util.sleep (Prims.parse_int "500"))
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

let _88_429 = (let _187_400 = (let _187_399 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[])::_187_399)
in (FStar_ST.op_Colon_Equals fresh_scope _187_400))
in (let _187_402 = (let _187_401 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[]) _187_401))
in (FStar_ST.op_Colon_Equals bg_scope _187_402))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _88_432 = (let _187_406 = (let _187_405 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _187_405))
in (FStar_ST.op_Colon_Equals fresh_scope _187_406))
in (let _187_408 = (let _187_407 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Pop)::(FStar_SMTEncoding_Term.Caption (msg))::[]) _187_407))
in (FStar_ST.op_Colon_Equals bg_scope _187_408))))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (

let _88_440 = (FStar_All.pipe_right decls (FStar_List.iter (fun _88_4 -> (match (_88_4) with
| (FStar_SMTEncoding_Term.Push) | (FStar_SMTEncoding_Term.Pop) -> begin
(failwith "Unexpected push/pop")
end
| _88_439 -> begin
()
end))))
in (

let _88_447 = (match ((FStar_ST.read fresh_scope)) with
| (hd)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _88_446 -> begin
(failwith "Impossible")
end)
in (let _187_413 = (let _187_412 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _187_412))
in (FStar_ST.op_Colon_Equals bg_scope _187_413)))))


let bgtheory : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun fresh -> if fresh then begin
(

let _88_450 = (FStar_ST.op_Colon_Equals bg_scope [])
in (let _187_417 = (let _187_416 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _187_416))
in (FStar_All.pipe_right _187_417 FStar_List.flatten)))
end else begin
(

let bg = (FStar_ST.read bg_scope)
in (

let _88_453 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)


let refresh : Prims.unit  ->  Prims.unit = (fun _88_455 -> (match (()) with
| () -> begin
(

let _88_456 = (bg_z3_proc.refresh ())
in (

let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _88_461 = (pop msg)
in (refresh ())))


let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| (hd)::(s)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _88_470 -> begin
(failwith "Impossible")
end))


let ask : unsat_core  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  (((unsat_core, (FStar_SMTEncoding_Term.error_labels * error_kind)) FStar_Util.either * Prims.int)  ->  Prims.unit)  ->  Prims.unit = (fun core label_messages qry cb -> (

let filter_assertions = (fun theory -> (match (core) with
| None -> begin
((theory), (false))
end
| Some (core) -> begin
(

let _88_498 = (FStar_List.fold_right (fun d _88_484 -> (match (_88_484) with
| (theory, n_retained, n_pruned) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (_88_486, _88_488, Some (name)) -> begin
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
| _88_494 -> begin
(((d)::theory), (n_retained), (n_pruned))
end)
end)) theory (([]), ((Prims.parse_int "0")), ((Prims.parse_int "0"))))
in (match (_88_498) with
| (theory', n_retained, n_pruned) -> begin
(

let missed_assertions = (fun th core -> (

let missed = (let _187_449 = (FStar_All.pipe_right core (FStar_List.filter (fun nm -> (let _187_448 = (FStar_All.pipe_right th (FStar_Util.for_some (fun _88_5 -> (match (_88_5) with
| FStar_SMTEncoding_Term.Assume (_88_505, _88_507, Some (nm')) -> begin
(nm = nm')
end
| _88_513 -> begin
false
end))))
in (FStar_All.pipe_right _187_448 Prims.op_Negation)))))
in (FStar_All.pipe_right _187_449 (FStar_String.concat ", ")))
in (

let included = (let _187_451 = (FStar_All.pipe_right th (FStar_List.collect (fun _88_6 -> (match (_88_6) with
| FStar_SMTEncoding_Term.Assume (_88_517, _88_519, Some (nm)) -> begin
(nm)::[]
end
| _88_525 -> begin
[]
end))))
in (FStar_All.pipe_right _187_451 (FStar_String.concat ", ")))
in (FStar_Util.format2 "missed={%s}; included={%s}" missed included))))
in (

let _88_529 = if ((FStar_Options.hint_info ()) && (FStar_Options.debug_any ())) then begin
(

let n = (FStar_List.length core)
in (

let missed = if (n <> n_retained) then begin
(missed_assertions theory' core)
end else begin
""
end
in (let _187_455 = (FStar_Util.string_of_int n_retained)
in (let _187_454 = if (n <> n_retained) then begin
(let _187_452 = (FStar_Util.string_of_int n)
in (FStar_Util.format2 " (expected %s (%s); replay may be inaccurate)" _187_452 missed))
end else begin
""
end
in (let _187_453 = (FStar_Util.string_of_int n_pruned)
in (FStar_Util.print3 "Hint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n" _187_455 _187_454 _187_453))))))
end else begin
()
end
in (let _187_460 = (let _187_459 = (let _187_458 = (let _187_457 = (let _187_456 = (FStar_All.pipe_right core (FStar_String.concat ", "))
in (Prims.strcat "UNSAT CORE: " _187_456))
in FStar_SMTEncoding_Term.Caption (_187_457))
in (_187_458)::[])
in (FStar_List.append theory' _187_459))
in ((_187_460), (true)))))
end))
end))
in (

let theory = (bgtheory false)
in (

let theory = (FStar_List.append theory (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[]))))
in (

let _88_535 = (filter_assertions theory)
in (match (_88_535) with
| (theory, used_unsat_core) -> begin
(

let cb = (fun _88_539 -> (match (_88_539) with
| (uc_errs, time) -> begin
if used_unsat_core then begin
(match (uc_errs) with
| FStar_Util.Inl (_88_541) -> begin
(cb ((uc_errs), (time)))
end
| FStar_Util.Inr (_88_544, ek) -> begin
(cb ((FStar_Util.Inr ((([]), (ek)))), (time)))
end)
end else begin
(cb ((uc_errs), (time)))
end
end))
in (

let input = (let _187_465 = (let _187_464 = (let _187_463 = (z3_options ())
in (FStar_SMTEncoding_Term.declToSmt _187_463))
in (FStar_List.map _187_464 theory))
in (FStar_All.pipe_right _187_465 (FStar_String.concat "\n")))
in (

let _88_549 = if (FStar_Options.log_queries ()) then begin
(query_logging.append_to_log input)
end else begin
()
end
in (enqueue false {job = (z3_job false label_messages input); callback = cb}))))
end))))))




