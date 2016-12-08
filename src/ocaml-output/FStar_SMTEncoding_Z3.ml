
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
in (FStar_Util.format1 "Z3 4.5.0 recommended; at least Z3 v4.4.1 required; got %s\n" _180_51))
in FStar_Util.Failure (_180_52))
in (FStar_All.pipe_left Prims.raise _180_53))
end else begin
()
end
in (let _180_55 = (let _180_54 = (FStar_Options.z3_seed ())
in (FStar_Util.string_of_int _180_54))
in (FStar_Util.format1 "-smt2 -in AUTO_CONFIG=false MODEL=true SMT.RELEVANCY=2 SMT.RANDOM_SEED=%s" _180_55))))
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
(let _180_117 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _180_117 FStar_Util.string_of_int))
end))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (let _180_125 = (FStar_Options.z3_exe ())
in (let _180_124 = (ini_params ())
in (FStar_Util.start_process id _180_125 _180_124 cond)))))


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

let file_name = (match ((let _180_216 = (FStar_ST.read used_file_names)
in (FStar_List.tryFind (fun _85_140 -> (match (_85_140) with
| (m, _85_139) -> begin
(n = m)
end)) _180_216))) with
| None -> begin
(

let _85_142 = (let _180_218 = (let _180_217 = (FStar_ST.read used_file_names)
in (((n), ((Prims.parse_int "0"))))::_180_217)
in (FStar_ST.op_Colon_Equals used_file_names _180_218))
in n)
end
| Some (_85_145, k) -> begin
(

let _85_149 = (let _180_220 = (let _180_219 = (FStar_ST.read used_file_names)
in (((n), ((k + (Prims.parse_int "1")))))::_180_219)
in (FStar_ST.op_Colon_Equals used_file_names _180_220))
in (let _180_221 = (FStar_Util.string_of_int (k + (Prims.parse_int "1")))
in (FStar_Util.format2 "%s-%s" n _180_221)))
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

let append_to_log = (fun str -> (let _180_226 = (get_log_file ())
in (FStar_Util.append_to_file _180_226 str)))
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
(let _180_235 = (let _180_234 = (

let _85_180 = (FStar_Util.incr ctr)
in (let _180_233 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _180_233 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _180_234))
in (new_z3proc _180_235))
end)))
in (

let z3proc = (fun _85_184 -> (match (()) with
| () -> begin
(

let _85_185 = if ((FStar_ST.read the_z3proc) = None) then begin
(let _180_239 = (let _180_238 = (new_proc ())
in Some (_180_238))
in (FStar_ST.op_Colon_Equals the_z3proc _180_239))
end else begin
()
end
in (let _180_240 = (FStar_ST.read the_z3proc)
in (FStar_Util.must _180_240)))
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

let _85_199 = (let _180_248 = (let _180_247 = (new_proc ())
in Some (_180_247))
in (FStar_ST.op_Colon_Equals the_z3proc _180_248))
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

let _85_211 = (let _180_252 = (let _180_251 = (new_proc ())
in Some (_180_251))
in (FStar_ST.op_Colon_Equals the_z3proc _180_252))
in (FStar_Util.monitor_exit ())))))
end))
in {grab = grab; release = release; refresh = refresh; restart = restart}))))))))


let at_log_file : Prims.unit  ->  Prims.string = (fun _85_213 -> (match (()) with
| () -> begin
if (FStar_Options.log_queries ()) then begin
(let _180_255 = (query_logging.log_file_name ())
in (Prims.strcat "@" _180_255))
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
if ((((FStar_List.length lines) >= (Prims.parse_int "2")) && (let _180_274 = (FStar_List.hd lines)
in (starts_with '(' _180_274))) && (let _180_275 = (last lines)
in (ends_with ')' _180_275))) then begin
(

let _85_229 = (let _180_279 = (let _180_278 = (let _180_276 = (query_logging.get_module_name ())
in (FStar_Util.format1 "BEGIN-STATS %s\n" _180_276))
in (let _180_277 = (at_log_file ())
in (Prims.strcat _180_278 _180_277)))
in (FStar_Util.print_string _180_279))
in (

let _85_232 = (FStar_List.iter (fun s -> (let _180_281 = (FStar_Util.format1 "%s\n" s)
in (FStar_Util.print_string _180_281))) lines)
in (FStar_Util.print_string "END-STATS\n")))
end else begin
(FStar_All.failwith "Unexpected output from Z3: could not find statistics\n")
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
(let _180_287 = (FStar_All.pipe_right (FStar_Util.split s " ") (FStar_Util.sort_with FStar_String.compare))
in (FStar_All.pipe_right _180_287 (fun _180_286 -> Some (_180_286))))
end)))
in (match (lines) with
| ("<unsat-core>")::(core)::("</unsat-core>")::rest -> begin
(let _180_288 = (parse_core core)
in ((_180_288), (lines)))
end
| _85_248 -> begin
((None), (lines))
end)))
in (

let rec lblnegs = (fun lines succeeded -> (match (lines) with
| (lname)::("false")::rest when (FStar_Util.starts_with lname "label_") -> begin
(let _180_293 = (lblnegs rest succeeded)
in (lname)::_180_293)
end
| (lname)::(_85_259)::rest when (FStar_Util.starts_with lname "label_") -> begin
(lblnegs rest succeeded)
end
| _85_264 -> begin
(

let _85_265 = if succeeded then begin
(print_stats lines)
end else begin
()
end
in [])
end))
in (

let unsat_core_and_lblnegs = (fun lines succeeded -> (

let _85_272 = (unsat_core lines)
in (match (_85_272) with
| (core_opt, rest) -> begin
(let _180_298 = (lblnegs rest succeeded)
in ((core_opt), (_180_298)))
end)))
in (

let rec result = (fun x -> (match (x) with
| ("timeout")::tl -> begin
TIMEOUT ([])
end
| ("unknown")::tl -> begin
(let _180_302 = (let _180_301 = (unsat_core_and_lblnegs tl false)
in (Prims.snd _180_301))
in UNKNOWN (_180_302))
end
| ("sat")::tl -> begin
(let _180_304 = (let _180_303 = (unsat_core_and_lblnegs tl false)
in (Prims.snd _180_303))
in SAT (_180_304))
end
| ("unsat")::tl -> begin
(let _180_306 = (let _180_305 = (unsat_core_and_lblnegs tl true)
in (Prims.fst _180_305))
in UNSAT (_180_306))
end
| ("killed")::tl -> begin
(

let _85_290 = (bg_z3_proc.restart ())
in KILLED)
end
| (hd)::tl -> begin
(

let _85_295 = (let _180_308 = (let _180_307 = (query_logging.get_module_name ())
in (FStar_Util.format2 "%s: Unexpected output from Z3: %s\n" _180_307 hd))
in (FStar_TypeChecker_Errors.warn FStar_Range.dummyRange _180_308))
in (result tl))
end
| _85_298 -> begin
(let _180_312 = (let _180_311 = (let _180_310 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _180_310))
in (FStar_Util.format1 "Unexpected output from Z3: got output lines: %s\n" _180_311))
in (FStar_All.pipe_left FStar_All.failwith _180_312))
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

let _85_304 = (FStar_Util.incr ctr)
in (let _180_318 = (let _180_317 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _180_317))
in (new_z3proc _180_318)))
end else begin
(bg_z3_proc.grab ())
end
in (

let res = (doZ3Exe' input z3proc)
in (

let _85_308 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))


let z3_options : Prims.unit  ->  Prims.string = (fun _85_310 -> (match (()) with
| () -> begin
(let _180_322 = (let _180_321 = (FStar_Options.z3_seed ())
in (FStar_Util.string_of_int _180_321))
in (FStar_Util.format1 "(set-option :global-decls false)(set-option :smt.mbqi false)(set-option :produce-unsat-cores true)(set-option :smt.random_seed %s)\n" _180_322))
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

let _85_317 = (FStar_Util.monitor_enter m)
in (

let res = (f ())
in (

let _85_320 = (FStar_Util.monitor_exit m)
in res))))


let z3_job : Prims.bool  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list  ->  Prims.string  ->  Prims.unit  ->  ((unsat_core, (FStar_SMTEncoding_Term.error_labels * error_kind)) FStar_Util.either * Prims.int) = (fun fresh label_messages input _85_325 -> (match (()) with
| () -> begin
(

let ekind = (fun _85_3 -> (match (_85_3) with
| TIMEOUT (_85_328) -> begin
Timeout
end
| (SAT (_)) | (UNKNOWN (_)) -> begin
Default
end
| KILLED -> begin
Kill
end
| _85_338 -> begin
(FStar_All.failwith "Impossible")
end))
in (

let start = (FStar_Util.now ())
in (

let status = (doZ3Exe fresh input)
in (

let _85_345 = (let _180_361 = (FStar_Util.now ())
in (FStar_Util.time_diff start _180_361))
in (match (_85_345) with
| (_85_343, elapsed_time) -> begin
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

let _85_353 = if (FStar_Options.debug_any ()) then begin
(let _180_362 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _180_362))
end else begin
()
end
in (

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _85_361 -> (match (_85_361) with
| (m, _85_358, _85_360) -> begin
((Prims.fst m) = l)
end))))) with
| None -> begin
[]
end
| Some (lbl, msg, r) -> begin
(((lbl), (msg), (r)))::[]
end))))
in (let _180_367 = (let _180_366 = (let _180_365 = (ekind status)
in ((failing_assertions), (_180_365)))
in FStar_Util.Inr (_180_366))
in ((_180_367), (elapsed_time)))))
end)
in result)
end)))))
end))


let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _85_370 -> (match (()) with
| () -> begin
(

let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (hd)::tl -> begin
(

let _85_375 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (

let _85_378 = (FStar_Util.incr pending_jobs)
in (

let _85_380 = (FStar_Util.monitor_exit job_queue)
in (

let _85_382 = (run_job j)
in (

let _85_385 = (with_monitor job_queue (fun _85_384 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (

let _85_387 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _85_389 -> (match (()) with
| () -> begin
(

let _85_390 = (FStar_Util.monitor_enter job_queue)
in (

let rec aux = (fun _85_393 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(

let _85_395 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _85_398 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _180_377 = (j.job ())
in (FStar_All.pipe_left j.callback _180_377)))


let init : Prims.unit  ->  Prims.unit = (fun _85_400 -> (match (()) with
| () -> begin
(

let n_runners = ((FStar_Options.n_cores ()) - (Prims.parse_int "1"))
in (

let rec aux = (fun n -> if (n = (Prims.parse_int "0")) then begin
()
end else begin
(

let _85_404 = (FStar_Util.spawn dequeue)
in (aux (n - (Prims.parse_int "1"))))
end)
in (aux n_runners)))
end))


let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(

let _85_408 = (FStar_Util.monitor_enter job_queue)
in (

let _85_410 = (let _180_387 = (let _180_386 = (FStar_ST.read job_queue)
in (FStar_List.append _180_386 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _180_387))
in (

let _85_412 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)


let finish : Prims.unit  ->  Prims.unit = (fun _85_414 -> (match (()) with
| () -> begin
(

let bg = (bg_z3_proc.grab ())
in (

let _85_416 = (FStar_Util.kill_process bg)
in (

let _85_418 = (bg_z3_proc.release ())
in (

let rec aux = (fun _85_421 -> (match (()) with
| () -> begin
(

let _85_425 = (with_monitor job_queue (fun _85_422 -> (match (()) with
| () -> begin
(let _180_395 = (FStar_ST.read pending_jobs)
in (let _180_394 = (let _180_393 = (FStar_ST.read job_queue)
in (FStar_List.length _180_393))
in ((_180_395), (_180_394))))
end)))
in (match (_85_425) with
| (n, m) -> begin
if ((n + m) = (Prims.parse_int "0")) then begin
(let _180_396 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _180_396 Prims.ignore))
end else begin
(

let _85_426 = (FStar_Util.sleep (Prims.parse_int "500"))
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

let _85_429 = (let _180_400 = (let _180_399 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[])::_180_399)
in (FStar_ST.op_Colon_Equals fresh_scope _180_400))
in (let _180_402 = (let _180_401 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[]) _180_401))
in (FStar_ST.op_Colon_Equals bg_scope _180_402))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _85_432 = (let _180_406 = (let _180_405 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _180_405))
in (FStar_ST.op_Colon_Equals fresh_scope _180_406))
in (let _180_408 = (let _180_407 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Pop)::(FStar_SMTEncoding_Term.Caption (msg))::[]) _180_407))
in (FStar_ST.op_Colon_Equals bg_scope _180_408))))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (

let _85_440 = (FStar_All.pipe_right decls (FStar_List.iter (fun _85_4 -> (match (_85_4) with
| (FStar_SMTEncoding_Term.Push) | (FStar_SMTEncoding_Term.Pop) -> begin
(FStar_All.failwith "Unexpected push/pop")
end
| _85_439 -> begin
()
end))))
in (

let _85_447 = (match ((FStar_ST.read fresh_scope)) with
| (hd)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _85_446 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _180_413 = (let _180_412 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _180_412))
in (FStar_ST.op_Colon_Equals bg_scope _180_413)))))


let bgtheory : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun fresh -> if fresh then begin
(

let _85_450 = (FStar_ST.op_Colon_Equals bg_scope [])
in (let _180_417 = (let _180_416 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _180_416))
in (FStar_All.pipe_right _180_417 FStar_List.flatten)))
end else begin
(

let bg = (FStar_ST.read bg_scope)
in (

let _85_453 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)


let refresh : Prims.unit  ->  Prims.unit = (fun _85_455 -> (match (()) with
| () -> begin
(

let _85_456 = (bg_z3_proc.refresh ())
in (

let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _85_461 = (pop msg)
in (refresh ())))


let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| (hd)::(s)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _85_470 -> begin
(FStar_All.failwith "Impossible")
end))


let ask : unsat_core  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  (((unsat_core, (FStar_SMTEncoding_Term.error_labels * error_kind)) FStar_Util.either * Prims.int)  ->  Prims.unit)  ->  Prims.unit = (fun core label_messages qry cb -> (

let filter_assertions = (fun theory -> (match (core) with
| None -> begin
((theory), (false))
end
| Some (core) -> begin
(

let _85_498 = (FStar_List.fold_right (fun d _85_484 -> (match (_85_484) with
| (theory, n_retained, n_pruned) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (_85_486, _85_488, Some (name)) -> begin
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
| _85_494 -> begin
(((d)::theory), (n_retained), (n_pruned))
end)
end)) theory (([]), ((Prims.parse_int "0")), ((Prims.parse_int "0"))))
in (match (_85_498) with
| (theory', n_retained, n_pruned) -> begin
(

let missed_assertions = (fun th core -> (

let missed = (let _180_449 = (FStar_All.pipe_right core (FStar_List.filter (fun nm -> (let _180_448 = (FStar_All.pipe_right th (FStar_Util.for_some (fun _85_5 -> (match (_85_5) with
| FStar_SMTEncoding_Term.Assume (_85_505, _85_507, Some (nm')) -> begin
(nm = nm')
end
| _85_513 -> begin
false
end))))
in (FStar_All.pipe_right _180_448 Prims.op_Negation)))))
in (FStar_All.pipe_right _180_449 (FStar_String.concat ", ")))
in (

let included = (let _180_451 = (FStar_All.pipe_right th (FStar_List.collect (fun _85_6 -> (match (_85_6) with
| FStar_SMTEncoding_Term.Assume (_85_517, _85_519, Some (nm)) -> begin
(nm)::[]
end
| _85_525 -> begin
[]
end))))
in (FStar_All.pipe_right _180_451 (FStar_String.concat ", ")))
in (FStar_Util.format2 "missed={%s}; included={%s}" missed included))))
in (

let _85_529 = if ((FStar_Options.hint_info ()) && (FStar_Options.debug_any ())) then begin
(

let n = (FStar_List.length core)
in (

let missed = if (n <> n_retained) then begin
(missed_assertions theory' core)
end else begin
""
end
in (let _180_455 = (FStar_Util.string_of_int n_retained)
in (let _180_454 = if (n <> n_retained) then begin
(let _180_452 = (FStar_Util.string_of_int n)
in (FStar_Util.format2 " (expected %s (%s); replay may be inaccurate)" _180_452 missed))
end else begin
""
end
in (let _180_453 = (FStar_Util.string_of_int n_pruned)
in (FStar_Util.print3 "Hint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n" _180_455 _180_454 _180_453))))))
end else begin
()
end
in (let _180_460 = (let _180_459 = (let _180_458 = (let _180_457 = (let _180_456 = (FStar_All.pipe_right core (FStar_String.concat ", "))
in (Prims.strcat "UNSAT CORE: " _180_456))
in FStar_SMTEncoding_Term.Caption (_180_457))
in (_180_458)::[])
in (FStar_List.append theory' _180_459))
in ((_180_460), (true)))))
end))
end))
in (

let theory = (bgtheory false)
in (

let theory = (FStar_List.append theory (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[]))))
in (

let _85_535 = (filter_assertions theory)
in (match (_85_535) with
| (theory, used_unsat_core) -> begin
(

let cb = (fun _85_539 -> (match (_85_539) with
| (uc_errs, time) -> begin
if used_unsat_core then begin
(match (uc_errs) with
| FStar_Util.Inl (_85_541) -> begin
(cb ((uc_errs), (time)))
end
| FStar_Util.Inr (_85_544, ek) -> begin
(cb ((FStar_Util.Inr ((([]), (ek)))), (time)))
end)
end else begin
(cb ((uc_errs), (time)))
end
end))
in (

let input = (let _180_465 = (let _180_464 = (let _180_463 = (z3_options ())
in (FStar_SMTEncoding_Term.declToSmt _180_463))
in (FStar_List.map _180_464 theory))
in (FStar_All.pipe_right _180_465 (FStar_String.concat "\n")))
in (

let _85_549 = if (FStar_Options.log_queries ()) then begin
(query_logging.append_to_log input)
end else begin
()
end
in (enqueue false {job = (z3_job false label_messages input); callback = cb}))))
end))))))




