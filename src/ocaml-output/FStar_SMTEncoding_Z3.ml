
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
| Z3V_Unknown (_80_5) -> begin
_80_5
end))


let ___Z3V____0 = (fun projectee -> (match (projectee) with
| Z3V (_80_8) -> begin
_80_8
end))


let z3version_as_string : z3version  ->  Prims.string = (fun _80_1 -> (match (_80_1) with
| Z3V_Unknown (s) -> begin
(FStar_Util.format1 "unknown version: %s" s)
end
| Z3V (i, j, k) -> begin
(let _170_33 = (FStar_Util.string_of_int i)
in (let _170_32 = (FStar_Util.string_of_int j)
in (let _170_31 = (FStar_Util.string_of_int k)
in (FStar_Util.format3 "%s.%s.%s" _170_33 _170_32 _170_31))))
end))


let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _80_21 -> (match (_80_21) with
| (w1, w2, w3) -> begin
(match (known) with
| Z3V_Unknown (_80_23) -> begin
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


let get_z3version : Prims.unit  ->  z3version = (fun _80_35 -> (match (()) with
| () -> begin
(

let prefix = "Z3 version "
in (match ((FStar_ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(

let _80_45 = (let _170_44 = (FStar_Options.z3_exe ())
in (FStar_Util.run_proc _170_44 "-version" ""))
in (match (_80_45) with
| (_80_41, out, _80_44) -> begin
(

let out = (match ((FStar_Util.splitlines out)) with
| (x)::_80_47 when (FStar_Util.starts_with x prefix) -> begin
(

let x = (let _170_45 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _170_45))
in (

let x = try
(match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)
with
| _80_55 -> begin
[]
end
in (match (x) with
| (i1)::(i2)::(i3)::[] -> begin
Z3V ((i1, i2, i3))
end
| _80_64 -> begin
Z3V_Unknown (out)
end)))
end
| _80_66 -> begin
Z3V_Unknown (out)
end)
in (

let _80_68 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))


let ini_params : Prims.unit  ->  Prims.string = (fun _80_70 -> (match (()) with
| () -> begin
(

let z3_v = (get_z3version ())
in (

let _80_72 = if (let _170_50 = (get_z3version ())
in (z3v_le _170_50 (4, 4, 0))) then begin
(let _170_53 = (let _170_52 = (let _170_51 = (z3version_as_string z3_v)
in (FStar_Util.format1 "Z3 v4.4.1 is required; got %s\n" _170_51))
in FStar_Util.Failure (_170_52))
in (FStar_All.pipe_left Prims.raise _170_53))
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
| UNSAT (_80_76) -> begin
_80_76
end))


let ___SAT____0 = (fun projectee -> (match (projectee) with
| SAT (_80_79) -> begin
_80_79
end))


let ___UNKNOWN____0 = (fun projectee -> (match (projectee) with
| UNKNOWN (_80_82) -> begin
_80_82
end))


let ___TIMEOUT____0 = (fun projectee -> (match (projectee) with
| TIMEOUT (_80_85) -> begin
_80_85
end))


let status_to_string : z3status  ->  Prims.string = (fun _80_2 -> (match (_80_2) with
| SAT (_80_88) -> begin
"sat"
end
| UNSAT (_80_91) -> begin
"unsat"
end
| UNKNOWN (_80_94) -> begin
"unknown"
end
| TIMEOUT (_80_97) -> begin
"timeout"
end))


let tid : Prims.unit  ->  Prims.string = (fun _80_99 -> (match (()) with
| () -> begin
(let _170_114 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _170_114 FStar_Util.string_of_int))
end))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (let _170_122 = (FStar_Options.z3_exe ())
in (let _170_121 = (ini_params ())
in (FStar_Util.start_process id _170_122 _170_121 cond)))))


type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}


let is_Mkbgproc : bgproc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbgproc"))))


let queries_dot_smt2 : FStar_Util.file_handle Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let get_qfile : Prims.bool  ->  FStar_Util.file_handle = (

let ctr = (FStar_Util.mk_ref 0)
in (fun fresh -> if fresh then begin
(

let _80_111 = (FStar_Util.incr ctr)
in (let _170_155 = (let _170_154 = (let _170_153 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _170_153))
in (FStar_Util.format1 "queries-%s.smt2" _170_154))
in (FStar_Util.open_file_for_writing _170_155)))
end else begin
(match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
(

let fh = (FStar_Util.open_file_for_writing "queries-bg-0.smt2")
in (

let _80_115 = (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
in fh))
end
| Some (fh) -> begin
fh
end)
end))


let log_query : Prims.bool  ->  Prims.string  ->  Prims.unit = (fun fresh i -> (

let fh = (get_qfile fresh)
in (

let _80_122 = (FStar_Util.append_to_file fh i)
in if fresh then begin
(FStar_Util.close_file fh)
end else begin
()
end)))


let the_z3proc : FStar_Util.proc Prims.option FStar_ST.ref = (FStar_ST.alloc None)


let ctr : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (- (1)))


let new_proc : Prims.unit  ->  FStar_Util.proc = (fun _80_124 -> (match (()) with
| () -> begin
(let _170_164 = (let _170_163 = (

let _80_125 = (FStar_Util.incr ctr)
in (let _170_162 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _170_162 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _170_163))
in (new_z3proc _170_164))
end))


let z3proc : Prims.unit  ->  FStar_Util.proc = (fun _80_127 -> (match (()) with
| () -> begin
(

let _80_128 = if ((FStar_ST.read the_z3proc) = None) then begin
(let _170_168 = (let _170_167 = (new_proc ())
in Some (_170_167))
in (FStar_ST.op_Colon_Equals the_z3proc _170_168))
end else begin
()
end
in (let _170_169 = (FStar_ST.read the_z3proc)
in (FStar_Util.must _170_169)))
end))


let bg_z3_proc : bgproc = (

let x = []
in (

let grab = (fun _80_132 -> (match (()) with
| () -> begin
(

let _80_133 = (FStar_Util.monitor_enter x)
in (z3proc ()))
end))
in (

let release = (fun _80_136 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (

let refresh = (fun _80_138 -> (match (()) with
| () -> begin
(

let proc = (grab ())
in (

let _80_140 = (FStar_Util.kill_process proc)
in (

let _80_142 = (let _170_177 = (let _170_176 = (new_proc ())
in Some (_170_176))
in (FStar_ST.op_Colon_Equals the_z3proc _170_177))
in (

let _80_150 = (match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
()
end
| Some (fh) -> begin
(

let _80_147 = (FStar_Util.close_file fh)
in (

let fh = (let _170_180 = (let _170_179 = (let _170_178 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _170_178 FStar_Util.string_of_int))
in (FStar_Util.format1 "queries-bg-%s.smt2" _170_179))
in (FStar_Util.open_file_for_writing _170_180))
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

let s = (FStar_Util.substring s 1 ((FStar_String.length s) - 1))
in if (FStar_Util.starts_with s "error") then begin
None
end else begin
(FStar_All.pipe_right (FStar_Util.split s " ") (fun _170_191 -> Some (_170_191)))
end))
in (match (lines) with
| ("<unsat-core>")::(core)::("</unsat-core>")::rest -> begin
(let _170_192 = (parse_core core)
in (_170_192, rest))
end
| _80_170 -> begin
(None, lines)
end)))
in (

let rec lblnegs = (fun lines -> (match (lines) with
| (lname)::("false")::rest -> begin
(let _170_195 = (lblnegs rest)
in (lname)::_170_195)
end
| (lname)::(_80_180)::rest -> begin
(lblnegs rest)
end
| _80_185 -> begin
[]
end))
in (

let rec unsat_core_and_lblnegs = (fun lines -> (

let _80_190 = (unsat_core lines)
in (match (_80_190) with
| (core_opt, rest) -> begin
(let _170_198 = (lblnegs rest)
in (core_opt, _170_198))
end)))
in (

let rec result = (fun x -> (match (x) with
| ("timeout")::tl -> begin
TIMEOUT ([])
end
| ("unknown")::tl -> begin
(let _170_202 = (let _170_201 = (unsat_core_and_lblnegs tl)
in (Prims.snd _170_201))
in UNKNOWN (_170_202))
end
| ("sat")::tl -> begin
(let _170_204 = (let _170_203 = (unsat_core_and_lblnegs tl)
in (Prims.snd _170_203))
in SAT (_170_204))
end
| ("unsat")::tl -> begin
(let _170_206 = (let _170_205 = (unsat_core tl)
in (Prims.fst _170_205))
in UNSAT (_170_206))
end
| (_80_207)::tl -> begin
(result tl)
end
| _80_210 -> begin
(let _170_210 = (let _170_209 = (let _170_208 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _170_208))
in (FStar_Util.format1 "Got output lines: %s\n" _170_209))
in (FStar_All.pipe_left FStar_All.failwith _170_210))
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

let _80_216 = (FStar_Util.incr ctr)
in (let _170_216 = (let _170_215 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _170_215))
in (new_z3proc _170_216)))
end else begin
(bg_z3_proc.grab ())
end
in (

let res = (doZ3Exe' input z3proc)
in (

let _80_220 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))


let z3_options : Prims.unit  ->  Prims.string = (fun _80_222 -> (match (()) with
| () -> begin
"(set-option :global-decls false)(set-option :smt.mbqi false)(set-option :produce-unsat-cores true)\n"
end))


type 'a job =
{job : Prims.unit  ->  'a; callback : 'a  ->  Prims.unit}


let is_Mkjob = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkjob"))))


type z3job =
((unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either * FStar_BaseTypes.float) job


let job_queue : z3job Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 0)


let with_monitor = (fun m f -> (

let _80_229 = (FStar_Util.monitor_enter m)
in (

let res = (f ())
in (

let _80_232 = (FStar_Util.monitor_exit m)
in res))))


let z3_job : Prims.bool  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  Prims.string  ->  Prims.unit  ->  ((unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either * FStar_BaseTypes.float) = (fun fresh label_messages input _80_237 -> (match (()) with
| () -> begin
(

let start = (FStar_Util.now ())
in (

let status = (doZ3Exe fresh input)
in (

let elapsed_time = (let _170_252 = (FStar_Util.now ())
in (FStar_Util.time_diff _170_252 start))
in (

let result = (match (status) with
| UNSAT (core) -> begin
(FStar_Util.Inl (core), elapsed_time)
end
| (TIMEOUT (lblnegs)) | (SAT (lblnegs)) | (UNKNOWN (lblnegs)) -> begin
(

let _80_247 = if (FStar_Options.debug_any ()) then begin
(let _170_253 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _170_253))
end else begin
()
end
in (

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _80_255 -> (match (_80_255) with
| (m, _80_252, _80_254) -> begin
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
in result))))
end))


let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _80_264 -> (match (()) with
| () -> begin
(

let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (hd)::tl -> begin
(

let _80_269 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (

let _80_272 = (FStar_Util.incr pending_jobs)
in (

let _80_274 = (FStar_Util.monitor_exit job_queue)
in (

let _80_276 = (run_job j)
in (

let _80_279 = (with_monitor job_queue (fun _80_278 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (

let _80_281 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _80_283 -> (match (()) with
| () -> begin
(

let _80_284 = (FStar_Util.monitor_enter job_queue)
in (

let rec aux = (fun _80_287 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(

let _80_289 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _80_292 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _170_265 = (j.job ())
in (FStar_All.pipe_left j.callback _170_265)))


let init : Prims.unit  ->  Prims.unit = (fun _80_294 -> (match (()) with
| () -> begin
(

let n_runners = ((FStar_Options.n_cores ()) - 1)
in (

let rec aux = (fun n -> if (n = 0) then begin
()
end else begin
(

let _80_298 = (FStar_Util.spawn dequeue)
in (aux (n - 1)))
end)
in (aux n_runners)))
end))


let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(

let _80_302 = (FStar_Util.monitor_enter job_queue)
in (

let _80_304 = (let _170_275 = (let _170_274 = (FStar_ST.read job_queue)
in (FStar_List.append _170_274 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _170_275))
in (

let _80_306 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)


let finish : Prims.unit  ->  Prims.unit = (fun _80_308 -> (match (()) with
| () -> begin
(

let bg = (bg_z3_proc.grab ())
in (

let _80_310 = (FStar_Util.kill_process bg)
in (

let _80_312 = (bg_z3_proc.release ())
in (

let rec aux = (fun _80_315 -> (match (()) with
| () -> begin
(

let _80_319 = (with_monitor job_queue (fun _80_316 -> (match (()) with
| () -> begin
(let _170_283 = (FStar_ST.read pending_jobs)
in (let _170_282 = (let _170_281 = (FStar_ST.read job_queue)
in (FStar_List.length _170_281))
in (_170_283, _170_282)))
end)))
in (match (_80_319) with
| (n, m) -> begin
if ((n + m) = 0) then begin
(let _170_284 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _170_284 Prims.ignore))
end else begin
(

let _80_320 = (FStar_Util.sleep 500)
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

let _80_323 = (let _170_288 = (let _170_287 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::[])::_170_287)
in (FStar_ST.op_Colon_Equals fresh_scope _170_288))
in (let _170_290 = (let _170_289 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[]) _170_289))
in (FStar_ST.op_Colon_Equals bg_scope _170_290))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _80_326 = (let _170_294 = (let _170_293 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _170_293))
in (FStar_ST.op_Colon_Equals fresh_scope _170_294))
in (let _170_296 = (let _170_295 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[]) _170_295))
in (FStar_ST.op_Colon_Equals bg_scope _170_296))))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (

let _80_334 = (match ((FStar_ST.read fresh_scope)) with
| (hd)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _80_333 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _170_300 = (let _170_299 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _170_299))
in (FStar_ST.op_Colon_Equals bg_scope _170_300))))


let bgtheory : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun fresh -> if fresh then begin
(let _170_304 = (let _170_303 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _170_303))
in (FStar_All.pipe_right _170_304 FStar_List.flatten))
end else begin
(

let bg = (FStar_ST.read bg_scope)
in (

let _80_338 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)


let refresh : Prims.unit  ->  Prims.unit = (fun _80_340 -> (match (()) with
| () -> begin
(

let _80_341 = (bg_z3_proc.refresh ())
in (

let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _80_346 = (pop msg)
in (refresh ())))


let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| (hd)::(s)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _80_355 -> begin
(FStar_All.failwith "Impossible")
end))


let ask : Prims.bool  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  (((unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either * FStar_BaseTypes.float)  ->  Prims.unit)  ->  Prims.unit = (fun fresh label_messages qry cb -> (

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

let input = (let _170_325 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ())) theory)
in (FStar_All.pipe_right _170_325 (FStar_String.concat "\n")))
in (

let _80_364 = if (FStar_Options.log_queries ()) then begin
(log_query fresh input)
end else begin
()
end
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb})))))))




