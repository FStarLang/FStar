
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
| Z3V (_51_3) -> begin
_51_3
end))


let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _51_8 -> (match (_51_8) with
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


let get_z3version : Prims.unit  ->  z3version = (fun _51_20 -> (match (()) with
| () -> begin
(

let prefix = "Z3 version "
in (match ((FStar_ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(

let _51_37 = try
(match (()) with
| () -> begin
(let _152_27 = (FStar_Options.z3_exe ())
in (FStar_Util.run_proc _152_27 "-version" ""))
end)
with
| _51_27 -> begin
(

let _51_28 = (FStar_Util.print_string "Error: No z3 executable was found\n")
in (FStar_All.exit (Prims.parse_int "1")))
end
in (match (_51_37) with
| (_51_33, out, _51_36) -> begin
(

let out = (match ((FStar_Util.splitlines out)) with
| (x)::_51_39 when (FStar_Util.starts_with x prefix) -> begin
(

let x = (let _152_29 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _152_29))
in (

let x = try
(match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)
with
| _51_45 -> begin
[]
end
in (match (x) with
| (i1)::(i2)::(i3)::[] -> begin
Z3V (((i1), (i2), (i3)))
end
| _51_54 -> begin
Z3V_Unknown
end)))
end
| _51_56 -> begin
Z3V_Unknown
end)
in (

let _51_58 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))


let ini_params : Prims.unit  ->  Prims.string = (fun _51_60 -> (match (()) with
| () -> begin
(

let t = if (let _152_34 = (get_z3version ())
in (z3v_le _152_34 (((Prims.parse_int "4")), ((Prims.parse_int "3")), ((Prims.parse_int "1"))))) then begin
(FStar_Options.z3_timeout ())
end else begin
((FStar_Options.z3_timeout ()) * (Prims.parse_int "1000"))
end
in (

let timeout = (let _152_35 = (FStar_Util.string_of_int t)
in (FStar_Util.format1 "-t:%s" _152_35))
in (

let relevancy = if (let _152_36 = (get_z3version ())
in (z3v_le _152_36 (((Prims.parse_int "4")), ((Prims.parse_int "3")), ((Prims.parse_int "1"))))) then begin
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


let status_to_string : z3status  ->  Prims.string = (fun uu___202 -> (match (uu___202) with
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


let tid : Prims.unit  ->  Prims.string = (fun _51_69 -> (match (()) with
| () -> begin
(let _152_45 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _152_45 FStar_Util.string_of_int))
end))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (let _152_53 = (FStar_Options.z3_exe ())
in (let _152_52 = (ini_params ())
in (FStar_Util.start_process id _152_53 _152_52 cond)))))


type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}


let is_Mkbgproc : bgproc  ->  Prims.bool = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkbgproc"))))


let queries_dot_smt2 : FStar_Util.file_handle Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let get_qfile : Prims.bool  ->  FStar_Util.file_handle = (

let ctr = (FStar_Util.mk_ref (Prims.parse_int "0"))
in (fun fresh -> if fresh then begin
(

let _51_81 = (FStar_Util.incr ctr)
in (let _152_86 = (let _152_85 = (let _152_84 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _152_84))
in (FStar_Util.format1 "queries-%s.smt2" _152_85))
in (FStar_Util.open_file_for_writing _152_86)))
end else begin
(match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
(

let fh = (FStar_Util.open_file_for_writing "queries-bg-0.smt2")
in (

let _51_85 = (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
in fh))
end
| Some (fh) -> begin
fh
end)
end))


let log_query : Prims.bool  ->  Prims.string  ->  Prims.unit = (fun fresh i -> (

let fh = (get_qfile fresh)
in (

let _51_92 = (FStar_Util.append_to_file fh i)
in if fresh then begin
(FStar_Util.close_file fh)
end else begin
()
end)))


let the_z3proc : FStar_Util.proc Prims.option FStar_ST.ref = (FStar_ST.alloc None)


let ctr : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (~- ((Prims.parse_int "1"))))


let new_proc : Prims.unit  ->  FStar_Util.proc = (fun _51_94 -> (match (()) with
| () -> begin
(let _152_95 = (let _152_94 = (

let _51_95 = (FStar_Util.incr ctr)
in (let _152_93 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _152_93 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _152_94))
in (new_z3proc _152_95))
end))


let z3proc : Prims.unit  ->  FStar_Util.proc = (fun _51_97 -> (match (()) with
| () -> begin
(

let _51_98 = if ((FStar_ST.read the_z3proc) = None) then begin
(let _152_99 = (let _152_98 = (new_proc ())
in Some (_152_98))
in (FStar_ST.op_Colon_Equals the_z3proc _152_99))
end else begin
()
end
in (let _152_100 = (FStar_ST.read the_z3proc)
in (FStar_Util.must _152_100)))
end))


let bg_z3_proc : bgproc = (

let x = []
in (

let grab = (fun _51_102 -> (match (()) with
| () -> begin
(

let _51_103 = (FStar_Util.monitor_enter x)
in (z3proc ()))
end))
in (

let release = (fun _51_106 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (

let refresh = (fun _51_108 -> (match (()) with
| () -> begin
(

let proc = (grab ())
in (

let _51_110 = (FStar_Util.kill_process proc)
in (

let _51_112 = (let _152_108 = (let _152_107 = (new_proc ())
in Some (_152_107))
in (FStar_ST.op_Colon_Equals the_z3proc _152_108))
in (

let _51_120 = (match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
()
end
| Some (fh) -> begin
(

let _51_117 = (FStar_Util.close_file fh)
in (

let fh = (let _152_111 = (let _152_110 = (let _152_109 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _152_109 FStar_Util.string_of_int))
in (FStar_Util.format1 "queries-bg-%s.smt2" _152_110))
in (FStar_Util.open_file_for_writing _152_111))
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
(let _152_120 = (lblnegs rest)
in (lname)::_152_120)
end
| (lname)::(_51_136)::rest -> begin
(lblnegs rest)
end
| _51_141 -> begin
[]
end))
in (

let rec result = (fun x -> (match (x) with
| ("timeout")::tl -> begin
((TIMEOUT), ([]))
end
| ("unknown")::tl -> begin
(let _152_123 = (lblnegs tl)
in ((UNKNOWN), (_152_123)))
end
| ("sat")::tl -> begin
(let _152_124 = (lblnegs tl)
in ((SAT), (_152_124)))
end
| ("unsat")::tl -> begin
((UNSAT), ([]))
end
| (_51_158)::tl -> begin
(result tl)
end
| _51_161 -> begin
(let _152_128 = (let _152_127 = (let _152_126 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _152_126))
in (FStar_Util.format1 "Got output lines: %s\n" _152_127))
in (FStar_All.pipe_left failwith _152_128))
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

let _51_167 = (FStar_Util.incr ctr)
in (let _152_134 = (let _152_133 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _152_133))
in (new_z3proc _152_134)))
end else begin
(bg_z3_proc.grab ())
end
in (

let res = (doZ3Exe' input z3proc)
in (

let _51_171 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))


let z3_options : Prims.unit  ->  Prims.string = (fun _51_173 -> (match (()) with
| () -> begin
(

let mbqi = if (let _152_137 = (get_z3version ())
in (z3v_le _152_137 (((Prims.parse_int "4")), ((Prims.parse_int "3")), ((Prims.parse_int "1"))))) then begin
"mbqi"
end else begin
"smt.mbqi"
end
in (

let model_on_timeout = if (let _152_138 = (get_z3version ())
in (z3v_le _152_138 (((Prims.parse_int "4")), ((Prims.parse_int "3")), ((Prims.parse_int "1"))))) then begin
"(set-option :model-on-timeout true)\n"
end else begin
""
end
in (Prims.strcat "(set-option :global-decls false)\n" (Prims.strcat "(set-option :" (Prims.strcat mbqi (Prims.strcat " false)\n" model_on_timeout))))))
end))


type 'a job =
{job : Prims.unit  ->  'a; callback : 'a  ->  Prims.unit}


let is_Mkjob = (Obj.magic ((fun _ -> (failwith "Not yet implemented:is_Mkjob"))))


type z3job =
(Prims.bool * (Prims.string * FStar_Range.range) Prims.list) job


let job_queue : z3job Prims.list FStar_ST.ref = (

let x = (FStar_Util.mk_ref (({job = (fun _51_180 -> (match (()) with
| () -> begin
(let _152_162 = (let _152_161 = (let _152_160 = (FStar_Range.mk_range "" FStar_Range.zeroPos FStar_Range.zeroPos)
in ((""), (_152_160)))
in (_152_161)::[])
in ((false), (_152_162)))
end)); callback = (fun a -> ())})::[]))
in (

let _51_183 = (FStar_ST.op_Colon_Equals x [])
in x))


let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (Prims.parse_int "0"))


let with_monitor = (fun m f -> (

let _51_187 = (FStar_Util.monitor_enter m)
in (

let res = (f ())
in (

let _51_190 = (FStar_Util.monitor_exit m)
in res))))


let z3_job = (fun fresh label_messages input _51_195 -> (match (()) with
| () -> begin
(

let _51_198 = (doZ3Exe fresh input)
in (match (_51_198) with
| (status, lblnegs) -> begin
(

let result = (match (status) with
| UNSAT -> begin
((true), ([]))
end
| _51_201 -> begin
(

let _51_202 = if (FStar_Options.debug_any ()) then begin
(let _152_173 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _152_173))
end else begin
()
end
in (

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _51_210 -> (match (_51_210) with
| (m, _51_207, _51_209) -> begin
((Prims.fst m) = l)
end))))) with
| None -> begin
[]
end
| Some (_51_213, msg, r) -> begin
(((msg), (r)))::[]
end))))
in ((false), (failing_assertions))))
end)
in result)
end))
end))


let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _51_220 -> (match (()) with
| () -> begin
(

let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(failwith "Impossible")
end
| (hd)::tl -> begin
(

let _51_225 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (

let _51_228 = (FStar_Util.incr pending_jobs)
in (

let _51_230 = (FStar_Util.monitor_exit job_queue)
in (

let _51_232 = (run_job j)
in (

let _51_235 = (with_monitor job_queue (fun _51_234 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (

let _51_237 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _51_239 -> (match (()) with
| () -> begin
(

let _51_240 = (FStar_Util.monitor_enter job_queue)
in (

let rec aux = (fun _51_243 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(

let _51_245 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _51_248 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _152_185 = (j.job ())
in (FStar_All.pipe_left j.callback _152_185)))


let init : Prims.unit  ->  Prims.unit = (fun _51_250 -> (match (()) with
| () -> begin
(

let n_runners = ((FStar_Options.n_cores ()) - (Prims.parse_int "1"))
in (

let rec aux = (fun n -> if (n = (Prims.parse_int "0")) then begin
()
end else begin
(

let _51_254 = (FStar_Util.spawn dequeue)
in (aux (n - (Prims.parse_int "1"))))
end)
in (aux n_runners)))
end))


let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(

let _51_258 = (FStar_Util.monitor_enter job_queue)
in (

let _51_260 = (let _152_195 = (let _152_194 = (FStar_ST.read job_queue)
in (FStar_List.append _152_194 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _152_195))
in (

let _51_262 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)


let finish : Prims.unit  ->  Prims.unit = (fun _51_264 -> (match (()) with
| () -> begin
(

let bg = (bg_z3_proc.grab ())
in (

let _51_266 = (FStar_Util.kill_process bg)
in (

let _51_268 = (bg_z3_proc.release ())
in (

let rec aux = (fun _51_271 -> (match (()) with
| () -> begin
(

let _51_275 = (with_monitor job_queue (fun _51_272 -> (match (()) with
| () -> begin
(let _152_203 = (FStar_ST.read pending_jobs)
in (let _152_202 = (let _152_201 = (FStar_ST.read job_queue)
in (FStar_List.length _152_201))
in ((_152_203), (_152_202))))
end)))
in (match (_51_275) with
| (n, m) -> begin
if ((n + m) = (Prims.parse_int "0")) then begin
(let _152_204 = (FStar_Errors.report_all ())
in (FStar_All.pipe_right _152_204 Prims.ignore))
end else begin
(

let _51_276 = (FStar_Util.sleep (Prims.parse_int "500"))
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

let _51_279 = (let _152_208 = (let _152_207 = (FStar_ST.read fresh_scope)
in ((FStar_ToSMT_Term.Caption (msg))::[])::_152_207)
in (FStar_ST.op_Colon_Equals fresh_scope _152_208))
in (let _152_210 = (let _152_209 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::(FStar_ToSMT_Term.Push)::[]) _152_209))
in (FStar_ST.op_Colon_Equals bg_scope _152_210))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _51_282 = (let _152_214 = (let _152_213 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _152_213))
in (FStar_ST.op_Colon_Equals fresh_scope _152_214))
in (let _152_216 = (let _152_215 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::(FStar_ToSMT_Term.Pop)::[]) _152_215))
in (FStar_ST.op_Colon_Equals bg_scope _152_216))))


let giveZ3 : FStar_ToSMT_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (

let _51_290 = (match ((FStar_ST.read fresh_scope)) with
| (hd)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _51_289 -> begin
(failwith "Impossible")
end)
in (let _152_220 = (let _152_219 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _152_219))
in (FStar_ST.op_Colon_Equals bg_scope _152_220))))


let bgtheory : Prims.bool  ->  FStar_ToSMT_Term.decl Prims.list = (fun fresh -> if fresh then begin
(let _152_224 = (let _152_223 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _152_223))
in (FStar_All.pipe_right _152_224 FStar_List.flatten))
end else begin
(

let bg = (FStar_ST.read bg_scope)
in (

let _51_294 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)


let refresh : Prims.unit  ->  Prims.unit = (fun _51_296 -> (match (()) with
| () -> begin
(

let _51_297 = (bg_z3_proc.refresh ())
in (

let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _51_302 = (pop msg)
in (refresh ())))


let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| (hd)::(s)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _51_311 -> begin
(failwith "Impossible")
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

let input = (let _152_241 = (let _152_240 = (let _152_239 = (z3_options ())
in (FStar_ToSMT_Term.declToSmt _152_239))
in (FStar_List.map _152_240 theory))
in (FStar_All.pipe_right _152_241 (FStar_String.concat "\n")))
in (

let _51_320 = if (FStar_Options.log_queries ()) then begin
(log_query fresh input)
end else begin
()
end
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb})))))))




