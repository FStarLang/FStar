
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
| Z3V_Unknown (_90_3) -> begin
_90_3
end))


let ___Z3V____0 = (fun projectee -> (match (projectee) with
| Z3V (_90_6) -> begin
_90_6
end))


let z3version_as_string : z3version  ->  Prims.string = (fun uu___572 -> (match (uu___572) with
| Z3V_Unknown (s) -> begin
(FStar_Util.format1 "unknown version: %s" s)
end
| Z3V (i, j, k) -> begin
(let _191_33 = (FStar_Util.string_of_int i)
in (let _191_32 = (FStar_Util.string_of_int j)
in (let _191_31 = (FStar_Util.string_of_int k)
in (FStar_Util.format3 "%s.%s.%s" _191_33 _191_32 _191_31))))
end))


let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _90_19 -> (match (_90_19) with
| (w1, w2, w3) -> begin
(match (known) with
| Z3V_Unknown (_90_21) -> begin
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


let get_z3version : Prims.unit  ->  z3version = (fun _90_33 -> (match (()) with
| () -> begin
(

let prefix = "Z3 version "
in (match ((FStar_ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(

let _90_43 = (let _191_44 = (FStar_Options.z3_exe ())
in (FStar_Util.run_proc _191_44 "-version" ""))
in (match (_90_43) with
| (_90_39, out, _90_42) -> begin
(

let out = (match ((FStar_Util.splitlines out)) with
| (x)::_90_45 when (FStar_Util.starts_with x prefix) -> begin
(

let x = (let _191_45 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _191_45))
in (

let x = try
(match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)
with
| _90_51 -> begin
[]
end
in (match (x) with
| (i1)::(i2)::(i3)::[] -> begin
Z3V (((i1), (i2), (i3)))
end
| _90_60 -> begin
Z3V_Unknown (out)
end)))
end
| _90_62 -> begin
Z3V_Unknown (out)
end)
in (

let _90_64 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))


let ini_params : Prims.unit  ->  Prims.string = (fun _90_66 -> (match (()) with
| () -> begin
(

let z3_v = (get_z3version ())
in (

let _90_68 = if (let _191_50 = (get_z3version ())
in (z3v_le _191_50 (((Prims.parse_int "4")), ((Prims.parse_int "4")), ((Prims.parse_int "0"))))) then begin
(let _191_53 = (let _191_52 = (let _191_51 = (z3version_as_string z3_v)
in (FStar_Util.format1 "Z3 4.5.0 recommended; at least Z3 v4.4.1 required; got %s\n" _191_51))
in FStar_Util.Failure (_191_52))
in (FStar_All.pipe_left Prims.raise _191_53))
end else begin
()
end
in (let _191_55 = (let _191_54 = (FStar_Options.z3_seed ())
in (FStar_Util.string_of_int _191_54))
in (FStar_Util.format1 "-smt2 -in AUTO_CONFIG=false MODEL=true SMT.RELEVANCY=2 SMT.RANDOM_SEED=%s" _191_55))))
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
| UNSAT (_90_72) -> begin
_90_72
end))


let ___SAT____0 = (fun projectee -> (match (projectee) with
| SAT (_90_75) -> begin
_90_75
end))


let ___UNKNOWN____0 = (fun projectee -> (match (projectee) with
| UNKNOWN (_90_78) -> begin
_90_78
end))


let ___TIMEOUT____0 = (fun projectee -> (match (projectee) with
| TIMEOUT (_90_81) -> begin
_90_81
end))


let status_to_string : z3status  ->  Prims.string = (fun uu___573 -> (match (uu___573) with
| SAT (_90_84) -> begin
"sat"
end
| UNSAT (_90_87) -> begin
"unsat"
end
| UNKNOWN (_90_90) -> begin
"unknown"
end
| TIMEOUT (_90_93) -> begin
"timeout"
end
| KILLED -> begin
"killed"
end))


let tid : Prims.unit  ->  Prims.string = (fun _90_96 -> (match (()) with
| () -> begin
(let _191_117 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _191_117 FStar_Util.string_of_int))
end))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (let _191_125 = (FStar_Options.z3_exe ())
in (let _191_124 = (ini_params ())
in (FStar_Util.start_process id _191_125 _191_124 cond)))))


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

let get_module_name = (fun _90_120 -> (match (()) with
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

let new_log_file = (fun _90_125 -> (match (()) with
| () -> begin
(match ((FStar_ST.read current_module_name)) with
| None -> begin
(failwith "current module not set")
end
| Some (n) -> begin
(

let file_name = (match ((let _191_216 = (FStar_ST.read used_file_names)
in (FStar_List.tryFind (fun _90_132 -> (match (_90_132) with
| (m, _90_131) -> begin
(n = m)
end)) _191_216))) with
| None -> begin
(

let _90_134 = (let _191_218 = (let _191_217 = (FStar_ST.read used_file_names)
in (((n), ((Prims.parse_int "0"))))::_191_217)
in (FStar_ST.op_Colon_Equals used_file_names _191_218))
in n)
end
| Some (_90_137, k) -> begin
(

let _90_141 = (let _191_220 = (let _191_219 = (FStar_ST.read used_file_names)
in (((n), ((k + (Prims.parse_int "1")))))::_191_219)
in (FStar_ST.op_Colon_Equals used_file_names _191_220))
in (let _191_221 = (FStar_Util.string_of_int (k + (Prims.parse_int "1")))
in (FStar_Util.format2 "%s-%s" n _191_221)))
end)
in (

let file_name = (FStar_Util.format1 "queries-%s.smt2" file_name)
in (

let _90_145 = (FStar_ST.op_Colon_Equals current_file_name (Some (file_name)))
in (

let fh = (FStar_Util.open_file_for_writing file_name)
in (

let _90_148 = (FStar_ST.op_Colon_Equals log_file_opt (Some (fh)))
in fh)))))
end)
end))
in (

let get_log_file = (fun _90_151 -> (match (()) with
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

let append_to_log = (fun str -> (let _191_226 = (get_log_file ())
in (FStar_Util.append_to_file _191_226 str)))
in (

let close_log = (fun _90_158 -> (match (()) with
| () -> begin
(match ((FStar_ST.read log_file_opt)) with
| None -> begin
()
end
| Some (fh) -> begin
(

let _90_162 = (FStar_Util.close_file fh)
in (FStar_ST.op_Colon_Equals log_file_opt None))
end)
end))
in (

let log_file_name = (fun _90_165 -> (match (()) with
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
in (fun _90_171 -> (match (()) with
| () -> begin
(let _191_235 = (let _191_234 = (

let _90_172 = (FStar_Util.incr ctr)
in (let _191_233 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _191_233 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _191_234))
in (new_z3proc _191_235))
end)))
in (

let z3proc = (fun _90_176 -> (match (()) with
| () -> begin
(

let _90_177 = if ((FStar_ST.read the_z3proc) = None) then begin
(let _191_239 = (let _191_238 = (new_proc ())
in Some (_191_238))
in (FStar_ST.op_Colon_Equals the_z3proc _191_239))
end else begin
()
end
in (let _191_240 = (FStar_ST.read the_z3proc)
in (FStar_Util.must _191_240)))
end))
in (

let x = []
in (

let grab = (fun _90_181 -> (match (()) with
| () -> begin
(

let _90_182 = (FStar_Util.monitor_enter x)
in (z3proc ()))
end))
in (

let release = (fun _90_185 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (

let refresh = (fun _90_187 -> (match (()) with
| () -> begin
(

let proc = (grab ())
in (

let _90_189 = (FStar_Util.kill_process proc)
in (

let _90_191 = (let _191_248 = (let _191_247 = (new_proc ())
in Some (_191_247))
in (FStar_ST.op_Colon_Equals the_z3proc _191_248))
in (

let _90_193 = (query_logging.close_log ())
in (release ())))))
end))
in (

let restart = (fun _90_196 -> (match (()) with
| () -> begin
(

let _90_197 = (FStar_Util.monitor_enter ())
in (

let _90_199 = (query_logging.close_log ())
in (

let _90_201 = (FStar_ST.op_Colon_Equals the_z3proc None)
in (

let _90_203 = (let _191_252 = (let _191_251 = (new_proc ())
in Some (_191_251))
in (FStar_ST.op_Colon_Equals the_z3proc _191_252))
in (FStar_Util.monitor_exit ())))))
end))
in {grab = grab; release = release; refresh = refresh; restart = restart}))))))))


let at_log_file : Prims.unit  ->  Prims.string = (fun _90_205 -> (match (()) with
| () -> begin
if (FStar_Options.log_queries ()) then begin
(let _191_255 = (query_logging.log_file_name ())
in (Prims.strcat "@" _191_255))
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
if ((((FStar_List.length lines) >= (Prims.parse_int "2")) && (let _191_274 = (FStar_List.hd lines)
in (starts_with '(' _191_274))) && (let _191_275 = (last lines)
in (ends_with ')' _191_275))) then begin
(

let _90_221 = (let _191_279 = (let _191_278 = (let _191_276 = (query_logging.get_module_name ())
in (FStar_Util.format1 "BEGIN-STATS %s\n" _191_276))
in (let _191_277 = (at_log_file ())
in (Prims.strcat _191_278 _191_277)))
in (FStar_Util.print_string _191_279))
in (

let _90_224 = (FStar_List.iter (fun s -> (let _191_281 = (FStar_Util.format1 "%s\n" s)
in (FStar_Util.print_string _191_281))) lines)
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
(let _191_287 = (FStar_All.pipe_right (FStar_Util.split s " ") (FStar_Util.sort_with FStar_String.compare))
in (FStar_All.pipe_right _191_287 (fun _191_286 -> Some (_191_286))))
end)))
in (match (lines) with
| ("<unsat-core>")::(core)::("</unsat-core>")::rest -> begin
(let _191_288 = (parse_core core)
in ((_191_288), (lines)))
end
| _90_240 -> begin
((None), (lines))
end)))
in (

let rec lblnegs = (fun lines succeeded -> (match (lines) with
| (lname)::("false")::rest when (FStar_Util.starts_with lname "label_") -> begin
(let _191_293 = (lblnegs rest succeeded)
in (lname)::_191_293)
end
| (lname)::(_90_251)::rest when (FStar_Util.starts_with lname "label_") -> begin
(lblnegs rest succeeded)
end
| _90_256 -> begin
(

let _90_257 = if succeeded then begin
(print_stats lines)
end else begin
()
end
in [])
end))
in (

let unsat_core_and_lblnegs = (fun lines succeeded -> (

let _90_264 = (unsat_core lines)
in (match (_90_264) with
| (core_opt, rest) -> begin
(let _191_298 = (lblnegs rest succeeded)
in ((core_opt), (_191_298)))
end)))
in (

let rec result = (fun x -> (match (x) with
| ("timeout")::tl -> begin
TIMEOUT ([])
end
| ("unknown")::tl -> begin
(let _191_302 = (let _191_301 = (unsat_core_and_lblnegs tl false)
in (Prims.snd _191_301))
in UNKNOWN (_191_302))
end
| ("sat")::tl -> begin
(let _191_304 = (let _191_303 = (unsat_core_and_lblnegs tl false)
in (Prims.snd _191_303))
in SAT (_191_304))
end
| ("unsat")::tl -> begin
(let _191_306 = (let _191_305 = (unsat_core_and_lblnegs tl true)
in (Prims.fst _191_305))
in UNSAT (_191_306))
end
| ("killed")::tl -> begin
(

let _90_282 = (bg_z3_proc.restart ())
in KILLED)
end
| (hd)::tl -> begin
(

let _90_287 = (let _191_308 = (let _191_307 = (query_logging.get_module_name ())
in (FStar_Util.format2 "%s: Unexpected output from Z3: %s\n" _191_307 hd))
in (FStar_Errors.warn FStar_Range.dummyRange _191_308))
in (result tl))
end
| _90_290 -> begin
(let _191_312 = (let _191_311 = (let _191_310 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _191_310))
in (FStar_Util.format1 "Unexpected output from Z3: got output lines: %s\n" _191_311))
in (FStar_All.pipe_left failwith _191_312))
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

let _90_296 = (FStar_Util.incr ctr)
in (let _191_318 = (let _191_317 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _191_317))
in (new_z3proc _191_318)))
end else begin
(bg_z3_proc.grab ())
end
in (

let res = (doZ3Exe' input z3proc)
in (

let _90_300 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))


let z3_options : Prims.unit  ->  Prims.string = (fun _90_302 -> (match (()) with
| () -> begin
(let _191_322 = (let _191_321 = (FStar_Options.z3_seed ())
in (FStar_Util.string_of_int _191_321))
in (FStar_Util.format1 "(set-option :global-decls false)(set-option :smt.mbqi false)(set-option :auto_config false)(set-option :produce-unsat-cores true)(set-option :smt.random_seed %s)\n" _191_322))
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

let _90_309 = (FStar_Util.monitor_enter m)
in (

let res = (f ())
in (

let _90_312 = (FStar_Util.monitor_exit m)
in res))))


let z3_job : Prims.bool  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list  ->  Prims.string  ->  Prims.unit  ->  ((unsat_core, (FStar_SMTEncoding_Term.error_labels * error_kind)) FStar_Util.either * Prims.int) = (fun fresh label_messages input _90_317 -> (match (()) with
| () -> begin
(

let ekind = (fun uu___574 -> (match (uu___574) with
| TIMEOUT (_90_320) -> begin
Timeout
end
| (SAT (_)) | (UNKNOWN (_)) -> begin
Default
end
| KILLED -> begin
Kill
end
| _90_330 -> begin
(failwith "Impossible")
end))
in (

let start = (FStar_Util.now ())
in (

let status = (doZ3Exe fresh input)
in (

let _90_337 = (let _191_361 = (FStar_Util.now ())
in (FStar_Util.time_diff start _191_361))
in (match (_90_337) with
| (_90_335, elapsed_time) -> begin
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

let _90_345 = if (FStar_Options.debug_any ()) then begin
(let _191_362 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _191_362))
end else begin
()
end
in (

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _90_353 -> (match (_90_353) with
| (m, _90_350, _90_352) -> begin
((Prims.fst m) = l)
end))))) with
| None -> begin
[]
end
| Some (lbl, msg, r) -> begin
(((lbl), (msg), (r)))::[]
end))))
in (let _191_367 = (let _191_366 = (let _191_365 = (ekind status)
in ((failing_assertions), (_191_365)))
in FStar_Util.Inr (_191_366))
in ((_191_367), (elapsed_time)))))
end)
in result)
end)))))
end))


let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _90_362 -> (match (()) with
| () -> begin
(

let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(failwith "Impossible")
end
| (hd)::tl -> begin
(

let _90_367 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (

let _90_370 = (FStar_Util.incr pending_jobs)
in (

let _90_372 = (FStar_Util.monitor_exit job_queue)
in (

let _90_374 = (run_job j)
in (

let _90_377 = (with_monitor job_queue (fun _90_376 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (

let _90_379 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _90_381 -> (match (()) with
| () -> begin
(

let _90_382 = (FStar_Util.monitor_enter job_queue)
in (

let rec aux = (fun _90_385 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(

let _90_387 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _90_390 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _191_377 = (j.job ())
in (FStar_All.pipe_left j.callback _191_377)))


let init : Prims.unit  ->  Prims.unit = (fun _90_392 -> (match (()) with
| () -> begin
(

let n_runners = ((FStar_Options.n_cores ()) - (Prims.parse_int "1"))
in (

let rec aux = (fun n -> if (n = (Prims.parse_int "0")) then begin
()
end else begin
(

let _90_396 = (FStar_Util.spawn dequeue)
in (aux (n - (Prims.parse_int "1"))))
end)
in (aux n_runners)))
end))


let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(

let _90_400 = (FStar_Util.monitor_enter job_queue)
in (

let _90_402 = (let _191_387 = (let _191_386 = (FStar_ST.read job_queue)
in (FStar_List.append _191_386 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _191_387))
in (

let _90_404 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)


let finish : Prims.unit  ->  Prims.unit = (fun _90_406 -> (match (()) with
| () -> begin
(

let bg = (bg_z3_proc.grab ())
in (

let _90_408 = (FStar_Util.kill_process bg)
in (

let _90_410 = (bg_z3_proc.release ())
in (

let rec aux = (fun _90_413 -> (match (()) with
| () -> begin
(

let _90_417 = (with_monitor job_queue (fun _90_414 -> (match (()) with
| () -> begin
(let _191_395 = (FStar_ST.read pending_jobs)
in (let _191_394 = (let _191_393 = (FStar_ST.read job_queue)
in (FStar_List.length _191_393))
in ((_191_395), (_191_394))))
end)))
in (match (_90_417) with
| (n, m) -> begin
if ((n + m) = (Prims.parse_int "0")) then begin
(let _191_396 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right _191_396 Prims.ignore))
end else begin
(

let _90_418 = (FStar_Util.sleep (Prims.parse_int "500"))
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

let _90_421 = (let _191_400 = (let _191_399 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[])::_191_399)
in (FStar_ST.op_Colon_Equals fresh_scope _191_400))
in (let _191_402 = (let _191_401 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[]) _191_401))
in (FStar_ST.op_Colon_Equals bg_scope _191_402))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _90_424 = (let _191_406 = (let _191_405 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _191_405))
in (FStar_ST.op_Colon_Equals fresh_scope _191_406))
in (let _191_408 = (let _191_407 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Pop)::(FStar_SMTEncoding_Term.Caption (msg))::[]) _191_407))
in (FStar_ST.op_Colon_Equals bg_scope _191_408))))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (

let _90_432 = (FStar_All.pipe_right decls (FStar_List.iter (fun uu___575 -> (match (uu___575) with
| (FStar_SMTEncoding_Term.Push) | (FStar_SMTEncoding_Term.Pop) -> begin
(failwith "Unexpected push/pop")
end
| _90_431 -> begin
()
end))))
in (

let _90_439 = (match ((FStar_ST.read fresh_scope)) with
| (hd)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _90_438 -> begin
(failwith "Impossible")
end)
in (let _191_413 = (let _191_412 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _191_412))
in (FStar_ST.op_Colon_Equals bg_scope _191_413)))))


let bgtheory : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun fresh -> if fresh then begin
(

let _90_442 = (FStar_ST.op_Colon_Equals bg_scope [])
in (let _191_417 = (let _191_416 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _191_416))
in (FStar_All.pipe_right _191_417 FStar_List.flatten)))
end else begin
(

let bg = (FStar_ST.read bg_scope)
in (

let _90_445 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)


let refresh : Prims.unit  ->  Prims.unit = (fun _90_447 -> (match (()) with
| () -> begin
(

let _90_448 = (bg_z3_proc.refresh ())
in (

let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _90_453 = (pop msg)
in (refresh ())))


let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| (hd)::(s)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _90_462 -> begin
(failwith "Impossible")
end))


let ask : unsat_core  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  (((unsat_core, (FStar_SMTEncoding_Term.error_labels * error_kind)) FStar_Util.either * Prims.int)  ->  Prims.unit)  ->  Prims.unit = (fun core label_messages qry cb -> (

let filter_assertions = (fun theory -> (match (core) with
| None -> begin
((theory), (false))
end
| Some (core) -> begin
(

let _90_490 = (FStar_List.fold_right (fun d _90_476 -> (match (_90_476) with
| (theory, n_retained, n_pruned) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (_90_478, _90_480, Some (name)) -> begin
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
| _90_486 -> begin
(((d)::theory), (n_retained), (n_pruned))
end)
end)) theory (([]), ((Prims.parse_int "0")), ((Prims.parse_int "0"))))
in (match (_90_490) with
| (theory', n_retained, n_pruned) -> begin
(

let missed_assertions = (fun th core -> (

let missed = (let _191_449 = (FStar_All.pipe_right core (FStar_List.filter (fun nm -> (let _191_448 = (FStar_All.pipe_right th (FStar_Util.for_some (fun uu___576 -> (match (uu___576) with
| FStar_SMTEncoding_Term.Assume (_90_497, _90_499, Some (nm')) -> begin
(nm = nm')
end
| _90_505 -> begin
false
end))))
in (FStar_All.pipe_right _191_448 Prims.op_Negation)))))
in (FStar_All.pipe_right _191_449 (FStar_String.concat ", ")))
in (

let included = (let _191_451 = (FStar_All.pipe_right th (FStar_List.collect (fun uu___577 -> (match (uu___577) with
| FStar_SMTEncoding_Term.Assume (_90_509, _90_511, Some (nm)) -> begin
(nm)::[]
end
| _90_517 -> begin
[]
end))))
in (FStar_All.pipe_right _191_451 (FStar_String.concat ", ")))
in (FStar_Util.format2 "missed={%s}; included={%s}" missed included))))
in (

let _90_521 = if ((FStar_Options.hint_info ()) && (FStar_Options.debug_any ())) then begin
(

let n = (FStar_List.length core)
in (

let missed = if (n <> n_retained) then begin
(missed_assertions theory' core)
end else begin
""
end
in (let _191_455 = (FStar_Util.string_of_int n_retained)
in (let _191_454 = if (n <> n_retained) then begin
(let _191_452 = (FStar_Util.string_of_int n)
in (FStar_Util.format2 " (expected %s (%s); replay may be inaccurate)" _191_452 missed))
end else begin
""
end
in (let _191_453 = (FStar_Util.string_of_int n_pruned)
in (FStar_Util.print3 "Hint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n" _191_455 _191_454 _191_453))))))
end else begin
()
end
in (let _191_460 = (let _191_459 = (let _191_458 = (let _191_457 = (let _191_456 = (FStar_All.pipe_right core (FStar_String.concat ", "))
in (Prims.strcat "UNSAT CORE: " _191_456))
in FStar_SMTEncoding_Term.Caption (_191_457))
in (_191_458)::[])
in (FStar_List.append theory' _191_459))
in ((_191_460), (true)))))
end))
end))
in (

let theory = (bgtheory false)
in (

let theory = (FStar_List.append theory (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[]))))
in (

let _90_527 = (filter_assertions theory)
in (match (_90_527) with
| (theory, used_unsat_core) -> begin
(

let cb = (fun _90_531 -> (match (_90_531) with
| (uc_errs, time) -> begin
if used_unsat_core then begin
(match (uc_errs) with
| FStar_Util.Inl (_90_533) -> begin
(cb ((uc_errs), (time)))
end
| FStar_Util.Inr (_90_536, ek) -> begin
(cb ((FStar_Util.Inr ((([]), (ek)))), (time)))
end)
end else begin
(cb ((uc_errs), (time)))
end
end))
in (

let input = (let _191_465 = (let _191_464 = (let _191_463 = (z3_options ())
in (FStar_SMTEncoding_Term.declToSmt _191_463))
in (FStar_List.map _191_464 theory))
in (FStar_All.pipe_right _191_465 (FStar_String.concat "\n")))
in (

let _90_541 = if (FStar_Options.log_queries ()) then begin
(query_logging.append_to_log input)
end else begin
()
end
in (enqueue false {job = (z3_job false label_messages input); callback = cb}))))
end))))))




