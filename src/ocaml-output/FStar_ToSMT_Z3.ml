
open Prims

type z3version =
| Z3V_Unknown
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


let ___Z3V____0 = (fun projectee -> (match (projectee) with
| Z3V (_48_4) -> begin
_48_4
end))


let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _48_9 -> (match (_48_9) with
| (w1, w2, w3) -> begin
(match (known) with
| Z3V_Unknown -> begin
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


let get_z3version : Prims.unit  ->  z3version = (fun _48_21 -> (match (()) with
| () -> begin
(

let prefix = "Z3 version "
in (match ((FStar_ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(

let _48_40 = try
(match (()) with
| () -> begin
(let _145_27 = (FStar_Options.z3_exe ())
in (FStar_Util.run_proc _145_27 "-version" ""))
end)
with
| _48_30 -> begin
(

let _48_31 = (FStar_Util.print_string "Error: No z3 executable was found\n")
in (FStar_All.exit (Prims.parse_int "1")))
end
in (match (_48_40) with
| (_48_36, out, _48_39) -> begin
(

let out = (match ((FStar_Util.splitlines out)) with
| (x)::_48_42 when (FStar_Util.starts_with x prefix) -> begin
(

let x = (let _145_29 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _145_29))
in (

let x = try
(match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)
with
| _48_50 -> begin
[]
end
in (match (x) with
| (i1)::(i2)::(i3)::[] -> begin
Z3V (((i1), (i2), (i3)))
end
| _48_59 -> begin
Z3V_Unknown
end)))
end
| _48_61 -> begin
Z3V_Unknown
end)
in (

let _48_63 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))


let ini_params : Prims.unit  ->  Prims.string = (fun _48_65 -> (match (()) with
| () -> begin
(

let t = if (let _145_34 = (get_z3version ())
in (z3v_le _145_34 (((Prims.parse_int "4")), ((Prims.parse_int "3")), ((Prims.parse_int "1"))))) then begin
(FStar_Options.z3_timeout ())
end else begin
((FStar_Options.z3_timeout ()) * (Prims.parse_int "1000"))
end
in (

let timeout = (let _145_35 = (FStar_Util.string_of_int t)
in (FStar_Util.format1 "-t:%s" _145_35))
in (

let relevancy = if (let _145_36 = (get_z3version ())
in (z3v_le _145_36 (((Prims.parse_int "4")), ((Prims.parse_int "3")), ((Prims.parse_int "1"))))) then begin
"RELEVANCY"
end else begin
"SMT.RELEVANCY"
end
in (FStar_Util.format2 "-smt2 -in %s AUTO_CONFIG=false MODEL=true %s=2" timeout relevancy))))
end))


type z3status =
| SAT
| UNSAT
| UNKNOWN
| TIMEOUT


let is_SAT = (fun _discr_ -> (match (_discr_) with
| SAT (_) -> begin
true
end
| _ -> begin
false
end))


let is_UNSAT = (fun _discr_ -> (match (_discr_) with
| UNSAT (_) -> begin
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


let status_to_string : z3status  ->  Prims.string = (fun _48_1 -> (match (_48_1) with
| SAT -> begin
"sat"
end
| UNSAT -> begin
"unsat"
end
| UNKNOWN -> begin
"unknown"
end
| TIMEOUT -> begin
"timeout"
end))


let tid : Prims.unit  ->  Prims.string = (fun _48_74 -> (match (()) with
| () -> begin
(let _145_45 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _145_45 FStar_Util.string_of_int))
end))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (let _145_53 = (FStar_Options.z3_exe ())
in (let _145_52 = (ini_params ())
in (FStar_Util.start_process id _145_53 _145_52 cond)))))


type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}


let is_Mkbgproc : bgproc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbgproc"))))


let queries_dot_smt2 : FStar_Util.file_handle Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let get_qfile : Prims.bool  ->  FStar_Util.file_handle = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun fresh -> if fresh then begin
(

let _48_86 = (FStar_Util.incr ctr)
in (let _145_86 = (let _145_85 = (let _145_84 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _145_84))
in (FStar_Util.format1 "queries-%s.smt2" _145_85))
in (FStar_Util.open_file_for_writing _145_86)))
end else begin
(match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
(

let fh = (FStar_Util.open_file_for_writing "queries-bg-0.smt2")
in (

let _48_90 = (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
in fh))
end
| Some (fh) -> begin
fh
end)
end))


let log_query : Prims.bool  ->  Prims.string  ->  Prims.unit = (fun fresh i -> (

let fh = (get_qfile fresh)
in (

let _48_97 = (FStar_Util.append_to_file fh i)
in if fresh then begin
(FStar_Util.close_file fh)
end else begin
()
end)))


let the_z3proc : FStar_Util.proc Prims.option FStar_ST.ref = (FStar_ST.alloc None)


let ctr : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (~- ((Prims.parse_int "1"))))


let new_proc : Prims.unit  ->  FStar_Util.proc = (fun _48_99 -> (match (()) with
| () -> begin
(let _145_95 = (let _145_94 = (

let _48_100 = (FStar_Util.incr ctr)
in (let _145_93 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _145_93 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _145_94))
in (new_z3proc _145_95))
end))


let z3proc : Prims.unit  ->  FStar_Util.proc = (fun _48_102 -> (match (()) with
| () -> begin
(

let _48_103 = if ((FStar_ST.read the_z3proc) = None) then begin
(let _145_99 = (let _145_98 = (new_proc ())
in Some (_145_98))
in (FStar_ST.op_Colon_Equals the_z3proc _145_99))
end else begin
()
end
in (let _145_100 = (FStar_ST.read the_z3proc)
in (FStar_Util.must _145_100)))
end))


let bg_z3_proc : bgproc = (

let x = []
in (

let grab = (fun _48_107 -> (match (()) with
| () -> begin
(

let _48_108 = (FStar_Util.monitor_enter x)
in (z3proc ()))
end))
in (

let release = (fun _48_111 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (

let refresh = (fun _48_113 -> (match (()) with
| () -> begin
(

let proc = (grab ())
in (

let _48_115 = (FStar_Util.kill_process proc)
in (

let _48_117 = (let _145_108 = (let _145_107 = (new_proc ())
in Some (_145_107))
in (FStar_ST.op_Colon_Equals the_z3proc _145_108))
in (

let _48_125 = (match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
()
end
| Some (fh) -> begin
(

let _48_122 = (FStar_Util.close_file fh)
in (

let fh = (let _145_111 = (let _145_110 = (let _145_109 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _145_109 FStar_Util.string_of_int))
in (FStar_Util.format1 "queries-bg-%s.smt2" _145_110))
in (FStar_Util.open_file_for_writing _145_111))
in (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))))
end)
in (release ())))))
end))
in {grab = grab; release = release; refresh = refresh}))))


let doZ3Exe' : Prims.string  ->  FStar_Util.proc  ->  (z3status * Prims.string Prims.list) = (fun input z3proc -> (

let parse = (fun z3out -> (

let lines = (FStar_All.pipe_right (FStar_String.split (('\n')::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (

let rec lblnegs = (fun lines -> (match (lines) with
| (lname)::("false")::rest -> begin
(let _145_120 = (lblnegs rest)
in (lname)::_145_120)
end
| (lname)::(_48_141)::rest -> begin
(lblnegs rest)
end
| _48_146 -> begin
[]
end))
in (

let rec result = (fun x -> (match (x) with
| ("timeout")::tl -> begin
((TIMEOUT), ([]))
end
| ("unknown")::tl -> begin
(let _145_123 = (lblnegs tl)
in ((UNKNOWN), (_145_123)))
end
| ("sat")::tl -> begin
(let _145_124 = (lblnegs tl)
in ((SAT), (_145_124)))
end
| ("unsat")::tl -> begin
((UNSAT), ([]))
end
| (_48_163)::tl -> begin
(result tl)
end
| _48_166 -> begin
(let _145_128 = (let _145_127 = (let _145_126 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _145_126))
in (FStar_Util.format1 "Got output lines: %s\n" _145_127))
in (FStar_All.pipe_left FStar_All.failwith _145_128))
end))
in (result lines)))))
in (

let stdout = (FStar_Util.ask_process z3proc input)
in (parse (FStar_Util.trim_string stdout)))))


let doZ3Exe : Prims.bool  ->  Prims.string  ->  (z3status * Prims.string Prims.list) = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun fresh input -> (

let z3proc = if fresh then begin
(

let _48_172 = (FStar_Util.incr ctr)
in (let _145_134 = (let _145_133 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _145_133))
in (new_z3proc _145_134)))
end else begin
(bg_z3_proc.grab ())
end
in (

let res = (doZ3Exe' input z3proc)
in (

let _48_176 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))


let z3_options : Prims.unit  ->  Prims.string = (fun _48_178 -> (match (()) with
| () -> begin
(

let mbqi = if (let _145_137 = (get_z3version ())
in (z3v_le _145_137 (((Prims.parse_int "4")), ((Prims.parse_int "3")), ((Prims.parse_int "1"))))) then begin
"mbqi"
end else begin
"smt.mbqi"
end
in (

let model_on_timeout = if (let _145_138 = (get_z3version ())
in (z3v_le _145_138 (((Prims.parse_int "4")), ((Prims.parse_int "3")), ((Prims.parse_int "1"))))) then begin
"(set-option :model-on-timeout true)\n"
end else begin
""
end
in (Prims.strcat "(set-option :global-decls false)\n" (Prims.strcat "(set-option :" (Prims.strcat mbqi (Prims.strcat " false)\n" model_on_timeout))))))
end))


type 'a job =
{job : Prims.unit  ->  'a; callback : 'a  ->  Prims.unit}


let is_Mkjob = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkjob"))))


type z3job =
(Prims.bool * (Prims.string * FStar_Range.range) Prims.list) job


let job_queue : z3job Prims.list FStar_ST.ref = (

let x = (FStar_Util.mk_ref (({job = (fun _48_185 -> (match (()) with
| () -> begin
(let _145_162 = (let _145_161 = (let _145_160 = (FStar_Range.mk_range "" (Prims.parse_int "0") (Prims.parse_int "0"))
in ((""), (_145_160)))
in (_145_161)::[])
in ((false), (_145_162)))
end)); callback = (fun a -> ())})::[]))
in (

let _48_188 = (FStar_ST.op_Colon_Equals x [])
in x))


let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let with_monitor = (fun m f -> (

let _48_192 = (FStar_Util.monitor_enter m)
in (

let res = (f ())
in (

let _48_195 = (FStar_Util.monitor_exit m)
in res))))


let z3_job = (fun fresh label_messages input _48_200 -> (match (()) with
| () -> begin
(

let _48_203 = (doZ3Exe fresh input)
in (match (_48_203) with
| (status, lblnegs) -> begin
(

let result = (match (status) with
| UNSAT -> begin
((true), ([]))
end
| _48_206 -> begin
(

let _48_207 = if (FStar_Options.debug_any ()) then begin
(let _145_173 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _145_173))
end else begin
()
end
in (

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _48_215 -> (match (_48_215) with
| (m, _48_212, _48_214) -> begin
((Prims.fst m) = l)
end))))) with
| None -> begin
[]
end
| Some (_48_218, msg, r) -> begin
(((msg), (r)))::[]
end))))
in ((false), (failing_assertions))))
end)
in result)
end))
end))


let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _48_225 -> (match (()) with
| () -> begin
(

let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (hd)::tl -> begin
(

let _48_230 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (

let _48_233 = (FStar_Util.incr pending_jobs)
in (

let _48_235 = (FStar_Util.monitor_exit job_queue)
in (

let _48_237 = (run_job j)
in (

let _48_240 = (with_monitor job_queue (fun _48_239 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (

let _48_242 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _48_244 -> (match (()) with
| () -> begin
(

let _48_245 = (FStar_Util.monitor_enter job_queue)
in (

let rec aux = (fun _48_248 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(

let _48_250 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _48_253 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _145_185 = (j.job ())
in (FStar_All.pipe_left j.callback _145_185)))


let init : Prims.unit  ->  Prims.unit = (fun _48_255 -> (match (()) with
| () -> begin
(

let n_runners = ((FStar_Options.n_cores ()) - (Prims.parse_int "1"))
in (

let rec aux = (fun n -> if (n = (Prims.parse_int "0")) then begin
()
end else begin
(

let _48_259 = (FStar_Util.spawn dequeue)
in (aux (n - (Prims.parse_int "1"))))
end)
in (aux n_runners)))
end))


let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(

let _48_263 = (FStar_Util.monitor_enter job_queue)
in (

let _48_265 = (let _145_195 = (let _145_194 = (FStar_ST.read job_queue)
in (FStar_List.append _145_194 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _145_195))
in (

let _48_267 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)


let finish : Prims.unit  ->  Prims.unit = (fun _48_269 -> (match (()) with
| () -> begin
(

let bg = (bg_z3_proc.grab ())
in (

let _48_271 = (FStar_Util.kill_process bg)
in (

let _48_273 = (bg_z3_proc.release ())
in (

let rec aux = (fun _48_276 -> (match (()) with
| () -> begin
(

let _48_280 = (with_monitor job_queue (fun _48_277 -> (match (()) with
| () -> begin
(let _145_203 = (FStar_ST.read pending_jobs)
in (let _145_202 = (let _145_201 = (FStar_ST.read job_queue)
in (FStar_List.length _145_201))
in ((_145_203), (_145_202))))
end)))
in (match (_48_280) with
| (n, m) -> begin
if ((n + m) = (Prims.parse_int "0")) then begin
(let _145_204 = (FStar_Tc_Errors.report_all ())
in (FStar_All.pipe_right _145_204 Prims.ignore))
end else begin
(

let _48_281 = (FStar_Util.sleep (Prims.parse_int "500"))
in (aux ()))
end
end))
end))
in (aux ())))))
end))


type scope_t =
FStar_ToSMT_Term.decl Prims.list Prims.list


let fresh_scope : FStar_ToSMT_Term.decl Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let bg_scope : FStar_ToSMT_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : Prims.string  ->  Prims.unit = (fun msg -> (

let _48_284 = (let _145_208 = (let _145_207 = (FStar_ST.read fresh_scope)
in ((FStar_ToSMT_Term.Caption (msg))::[])::_145_207)
in (FStar_ST.op_Colon_Equals fresh_scope _145_208))
in (let _145_210 = (let _145_209 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::(FStar_ToSMT_Term.Push)::[]) _145_209))
in (FStar_ST.op_Colon_Equals bg_scope _145_210))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _48_287 = (let _145_214 = (let _145_213 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _145_213))
in (FStar_ST.op_Colon_Equals fresh_scope _145_214))
in (let _145_216 = (let _145_215 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::(FStar_ToSMT_Term.Pop)::[]) _145_215))
in (FStar_ST.op_Colon_Equals bg_scope _145_216))))


let giveZ3 : FStar_ToSMT_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (

let _48_295 = (match ((FStar_ST.read fresh_scope)) with
| (hd)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _48_294 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _145_220 = (let _145_219 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _145_219))
in (FStar_ST.op_Colon_Equals bg_scope _145_220))))


let bgtheory : Prims.bool  ->  FStar_ToSMT_Term.decl Prims.list = (fun fresh -> if fresh then begin
(let _145_224 = (let _145_223 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _145_223))
in (FStar_All.pipe_right _145_224 FStar_List.flatten))
end else begin
(

let bg = (FStar_ST.read bg_scope)
in (

let _48_299 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)


let refresh : Prims.unit  ->  Prims.unit = (fun _48_301 -> (match (()) with
| () -> begin
(

let _48_302 = (bg_z3_proc.refresh ())
in (

let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _48_307 = (pop msg)
in (refresh ())))


let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| (hd)::(s)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _48_316 -> begin
(FStar_All.failwith "Impossible")
end))


let ask = (fun fresh label_messages qry cb -> (

let fresh = (fresh && ((FStar_Options.n_cores ()) > (Prims.parse_int "1")))
in (

let theory = (bgtheory fresh)
in (

let theory = if fresh then begin
(FStar_List.append theory qry)
end else begin
(FStar_List.append theory (FStar_List.append ((FStar_ToSMT_Term.Push)::[]) (FStar_List.append qry ((FStar_ToSMT_Term.Pop)::[]))))
end
in (

let input = (let _145_241 = (let _145_240 = (let _145_239 = (z3_options ())
in (FStar_ToSMT_Term.declToSmt _145_239))
in (FStar_List.map _145_240 theory))
in (FStar_All.pipe_right _145_241 (FStar_String.concat "\n")))
in (

let _48_325 = if (FStar_Options.log_queries ()) then begin
(log_query fresh input)
end else begin
()
end
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb})))))))




