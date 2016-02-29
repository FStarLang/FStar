
open Prims
# 21 "FStar.SMTEncoding.Z3.fst"
type z3version =
| Z3V_Unknown
| Z3V of (Prims.int * Prims.int * Prims.int)

# 27 "FStar.SMTEncoding.Z3.fst"
let is_Z3V_Unknown = (fun _discr_ -> (match (_discr_) with
| Z3V_Unknown (_) -> begin
true
end
| _ -> begin
false
end))

# 28 "FStar.SMTEncoding.Z3.fst"
let is_Z3V = (fun _discr_ -> (match (_discr_) with
| Z3V (_) -> begin
true
end
| _ -> begin
false
end))

# 28 "FStar.SMTEncoding.Z3.fst"
let ___Z3V____0 : z3version  ->  (Prims.int * Prims.int * Prims.int) = (fun projectee -> (match (projectee) with
| Z3V (_74_4) -> begin
_74_4
end))

# 28 "FStar.SMTEncoding.Z3.fst"
let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _74_9 -> (match (_74_9) with
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

# 37 "FStar.SMTEncoding.Z3.fst"
let z3v_le : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.bool = (fun known wanted -> (match ((z3v_compare known wanted)) with
| None -> begin
false
end
| Some (i) -> begin
(i >= 0)
end))

# 42 "FStar.SMTEncoding.Z3.fst"
let _z3version : z3version Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 44 "FStar.SMTEncoding.Z3.fst"
let get_z3version : Prims.unit  ->  z3version = (fun _74_21 -> (match (()) with
| () -> begin
(
# 47 "FStar.SMTEncoding.Z3.fst"
let prefix = "Z3 version "
in (match ((FStar_ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(
# 52 "FStar.SMTEncoding.Z3.fst"
let _74_31 = (let _155_26 = (FStar_ST.read FStar_Options.z3_exe)
in (FStar_Util.run_proc _155_26 "-version" ""))
in (match (_74_31) with
| (_74_27, out, _74_30) -> begin
(
# 53 "FStar.SMTEncoding.Z3.fst"
let out = (match ((FStar_Util.splitlines out)) with
| x::_74_33 when (FStar_Util.starts_with x prefix) -> begin
(
# 56 "FStar.SMTEncoding.Z3.fst"
let x = (let _155_27 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _155_27))
in (
# 57 "FStar.SMTEncoding.Z3.fst"
let x = (FStar_All.try_with (fun _74_38 -> (match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)) (fun _74_37 -> (match (_74_37) with
| _74_41 -> begin
[]
end)))
in (match (x) with
| i1::i2::i3::[] -> begin
Z3V ((i1, i2, i3))
end
| _74_50 -> begin
Z3V_Unknown
end)))
end
| _74_52 -> begin
Z3V_Unknown
end)
in (
# 64 "FStar.SMTEncoding.Z3.fst"
let _74_54 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))

# 64 "FStar.SMTEncoding.Z3.fst"
let ini_params : Prims.unit  ->  Prims.string = (fun _74_56 -> (match (()) with
| () -> begin
(
# 67 "FStar.SMTEncoding.Z3.fst"
let t = if (let _155_32 = (get_z3version ())
in (z3v_le _155_32 (4, 3, 1))) then begin
(FStar_ST.read FStar_Options.z3timeout)
end else begin
((FStar_ST.read FStar_Options.z3timeout) * 1000)
end
in (
# 72 "FStar.SMTEncoding.Z3.fst"
let timeout = (let _155_33 = (FStar_Util.string_of_int t)
in (FStar_Util.format1 "-t:%s" _155_33))
in (
# 73 "FStar.SMTEncoding.Z3.fst"
let relevancy = if (let _155_34 = (get_z3version ())
in (z3v_le _155_34 (4, 3, 1))) then begin
"RELEVANCY"
end else begin
"SMT.RELEVANCY"
end
in (FStar_Util.format2 "-smt2 -in %s AUTO_CONFIG=false MODEL=true %s=2" timeout relevancy))))
end))

# 82 "FStar.SMTEncoding.Z3.fst"
type z3status =
| SAT
| UNSAT
| UNKNOWN
| TIMEOUT

# 85 "FStar.SMTEncoding.Z3.fst"
let is_SAT = (fun _discr_ -> (match (_discr_) with
| SAT (_) -> begin
true
end
| _ -> begin
false
end))

# 86 "FStar.SMTEncoding.Z3.fst"
let is_UNSAT = (fun _discr_ -> (match (_discr_) with
| UNSAT (_) -> begin
true
end
| _ -> begin
false
end))

# 87 "FStar.SMTEncoding.Z3.fst"
let is_UNKNOWN = (fun _discr_ -> (match (_discr_) with
| UNKNOWN (_) -> begin
true
end
| _ -> begin
false
end))

# 88 "FStar.SMTEncoding.Z3.fst"
let is_TIMEOUT = (fun _discr_ -> (match (_discr_) with
| TIMEOUT (_) -> begin
true
end
| _ -> begin
false
end))

# 88 "FStar.SMTEncoding.Z3.fst"
let status_to_string : z3status  ->  Prims.string = (fun _74_1 -> (match (_74_1) with
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

# 94 "FStar.SMTEncoding.Z3.fst"
let tid : Prims.unit  ->  Prims.string = (fun _74_65 -> (match (()) with
| () -> begin
(let _155_43 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _155_43 FStar_Util.string_of_int))
end))

# 96 "FStar.SMTEncoding.Z3.fst"
let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (
# 98 "FStar.SMTEncoding.Z3.fst"
let cond = (fun pid s -> (
# 99 "FStar.SMTEncoding.Z3.fst"
let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (let _155_51 = (FStar_ST.read FStar_Options.z3_exe)
in (let _155_50 = (ini_params ())
in (FStar_Util.start_process id _155_51 _155_50 cond)))))

# 102 "FStar.SMTEncoding.Z3.fst"
type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}

# 104 "FStar.SMTEncoding.Z3.fst"
let is_Mkbgproc : bgproc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbgproc"))))

# 108 "FStar.SMTEncoding.Z3.fst"
let queries_dot_smt2 : FStar_Util.file_handle Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 111 "FStar.SMTEncoding.Z3.fst"
let get_qfile : Prims.bool  ->  FStar_Util.file_handle = (
# 114 "FStar.SMTEncoding.Z3.fst"
let ctr = (FStar_Util.mk_ref 0)
in (fun fresh -> if fresh then begin
(
# 117 "FStar.SMTEncoding.Z3.fst"
let _74_77 = (FStar_Util.incr ctr)
in (let _155_84 = (let _155_83 = (let _155_82 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _155_82))
in (FStar_Util.format1 "queries-%s.smt2" _155_83))
in (FStar_Util.open_file_for_writing _155_84)))
end else begin
(match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
(
# 120 "FStar.SMTEncoding.Z3.fst"
let fh = (FStar_Util.open_file_for_writing "queries-bg-0.smt2")
in (
# 120 "FStar.SMTEncoding.Z3.fst"
let _74_81 = (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
in fh))
end
| Some (fh) -> begin
fh
end)
end))

# 121 "FStar.SMTEncoding.Z3.fst"
let log_query : Prims.bool  ->  Prims.string  ->  Prims.unit = (fun fresh i -> (
# 124 "FStar.SMTEncoding.Z3.fst"
let fh = (get_qfile fresh)
in (
# 125 "FStar.SMTEncoding.Z3.fst"
let _74_88 = (FStar_Util.append_to_file fh i)
in if fresh then begin
(FStar_Util.close_file fh)
end else begin
()
end)))

# 126 "FStar.SMTEncoding.Z3.fst"
let bg_z3_proc : bgproc = (
# 129 "FStar.SMTEncoding.Z3.fst"
let ctr = (FStar_Util.mk_ref (- (1)))
in (
# 130 "FStar.SMTEncoding.Z3.fst"
let new_proc = (fun _74_92 -> (match (()) with
| () -> begin
(let _155_93 = (let _155_92 = (
# 130 "FStar.SMTEncoding.Z3.fst"
let _74_93 = (FStar_Util.incr ctr)
in (let _155_91 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _155_91 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _155_92))
in (new_z3proc _155_93))
end))
in (
# 131 "FStar.SMTEncoding.Z3.fst"
let z3proc = (let _155_94 = (new_proc ())
in (FStar_Util.mk_ref _155_94))
in (
# 132 "FStar.SMTEncoding.Z3.fst"
let x = []
in (
# 133 "FStar.SMTEncoding.Z3.fst"
let grab = (fun _74_98 -> (match (()) with
| () -> begin
(
# 133 "FStar.SMTEncoding.Z3.fst"
let _74_99 = (FStar_Util.monitor_enter x)
in (FStar_ST.read z3proc))
end))
in (
# 134 "FStar.SMTEncoding.Z3.fst"
let release = (fun _74_102 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (
# 135 "FStar.SMTEncoding.Z3.fst"
let refresh = (fun _74_104 -> (match (()) with
| () -> begin
(
# 136 "FStar.SMTEncoding.Z3.fst"
let proc = (grab ())
in (
# 137 "FStar.SMTEncoding.Z3.fst"
let _74_106 = (FStar_Util.kill_process proc)
in (
# 138 "FStar.SMTEncoding.Z3.fst"
let _74_108 = (let _155_101 = (new_proc ())
in (FStar_ST.op_Colon_Equals z3proc _155_101))
in (
# 139 "FStar.SMTEncoding.Z3.fst"
let _74_116 = (match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
()
end
| Some (fh) -> begin
(
# 142 "FStar.SMTEncoding.Z3.fst"
let _74_113 = (FStar_Util.close_file fh)
in (
# 143 "FStar.SMTEncoding.Z3.fst"
let fh = (let _155_104 = (let _155_103 = (let _155_102 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _155_102 FStar_Util.string_of_int))
in (FStar_Util.format1 "queries-bg-%s.smt2" _155_103))
in (FStar_Util.open_file_for_writing _155_104))
in (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))))
end)
in (release ())))))
end))
in {grab = grab; release = release; refresh = refresh})))))))

# 149 "FStar.SMTEncoding.Z3.fst"
let doZ3Exe' : Prims.string  ->  FStar_Util.proc  ->  (z3status * Prims.string Prims.list) = (fun input z3proc -> (
# 152 "FStar.SMTEncoding.Z3.fst"
let parse = (fun z3out -> (
# 153 "FStar.SMTEncoding.Z3.fst"
let lines = (FStar_All.pipe_right (FStar_String.split (('\n')::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (
# 154 "FStar.SMTEncoding.Z3.fst"
let rec lblnegs = (fun lines -> (match (lines) with
| lname::"false"::rest -> begin
(let _155_113 = (lblnegs rest)
in (lname)::_155_113)
end
| lname::_74_132::rest -> begin
(lblnegs rest)
end
| _74_137 -> begin
[]
end))
in (
# 158 "FStar.SMTEncoding.Z3.fst"
let rec result = (fun x -> (match (x) with
| "timeout"::tl -> begin
(TIMEOUT, [])
end
| "unknown"::tl -> begin
(let _155_116 = (lblnegs tl)
in (UNKNOWN, _155_116))
end
| "sat"::tl -> begin
(let _155_117 = (lblnegs tl)
in (SAT, _155_117))
end
| "unsat"::tl -> begin
(UNSAT, [])
end
| _74_154::tl -> begin
(result tl)
end
| _74_157 -> begin
(let _155_121 = (let _155_120 = (let _155_119 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _155_119))
in (FStar_Util.format1 "Got output lines: %s\n" _155_120))
in (FStar_All.pipe_left FStar_All.failwith _155_121))
end))
in (result lines)))))
in (
# 166 "FStar.SMTEncoding.Z3.fst"
let stdout = (FStar_Util.ask_process z3proc input)
in (parse (FStar_Util.trim_string stdout)))))

# 167 "FStar.SMTEncoding.Z3.fst"
let doZ3Exe : Prims.bool  ->  Prims.string  ->  (z3status * Prims.string Prims.list) = (
# 170 "FStar.SMTEncoding.Z3.fst"
let ctr = (FStar_Util.mk_ref 0)
in (fun fresh input -> (
# 172 "FStar.SMTEncoding.Z3.fst"
let z3proc = if fresh then begin
(
# 172 "FStar.SMTEncoding.Z3.fst"
let _74_163 = (FStar_Util.incr ctr)
in (let _155_127 = (let _155_126 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _155_126))
in (new_z3proc _155_127)))
end else begin
(bg_z3_proc.grab ())
end
in (
# 173 "FStar.SMTEncoding.Z3.fst"
let res = (doZ3Exe' input z3proc)
in (
# 175 "FStar.SMTEncoding.Z3.fst"
let _74_167 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))

# 176 "FStar.SMTEncoding.Z3.fst"
let z3_options : Prims.unit  ->  Prims.string = (fun _74_169 -> (match (()) with
| () -> begin
(
# 179 "FStar.SMTEncoding.Z3.fst"
let mbqi = if (let _155_130 = (get_z3version ())
in (z3v_le _155_130 (4, 3, 1))) then begin
"mbqi"
end else begin
"smt.mbqi"
end
in (
# 183 "FStar.SMTEncoding.Z3.fst"
let model_on_timeout = if (let _155_131 = (get_z3version ())
in (z3v_le _155_131 (4, 3, 1))) then begin
"(set-option :model-on-timeout true)\n"
end else begin
""
end
in (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "(set-option :global-decls false)\n" "(set-option :") mbqi) " false)\n") model_on_timeout)))
end))

# 189 "FStar.SMTEncoding.Z3.fst"
type 'a job =
{job : Prims.unit  ->  'a; callback : 'a  ->  Prims.unit}

# 191 "FStar.SMTEncoding.Z3.fst"
let is_Mkjob = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkjob"))))

# 194 "FStar.SMTEncoding.Z3.fst"
type z3job =
(Prims.bool * (Prims.string * FStar_Range.range) Prims.list) job

# 195 "FStar.SMTEncoding.Z3.fst"
let job_queue : z3job Prims.list FStar_ST.ref = (
# 199 "FStar.SMTEncoding.Z3.fst"
let x = (FStar_Util.mk_ref (({job = (fun _74_176 -> (match (()) with
| () -> begin
(let _155_155 = (let _155_154 = (let _155_153 = (FStar_Range.mk_range "" 0 0)
in ("", _155_153))
in (_155_154)::[])
in (false, _155_155))
end)); callback = (fun a -> ())})::[]))
in (
# 200 "FStar.SMTEncoding.Z3.fst"
let _74_179 = (FStar_ST.op_Colon_Equals x [])
in x))

# 200 "FStar.SMTEncoding.Z3.fst"
let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 0)

# 202 "FStar.SMTEncoding.Z3.fst"
let with_monitor = (fun m f -> (
# 204 "FStar.SMTEncoding.Z3.fst"
let _74_183 = (FStar_Util.monitor_enter m)
in (
# 205 "FStar.SMTEncoding.Z3.fst"
let res = (f ())
in (
# 206 "FStar.SMTEncoding.Z3.fst"
let _74_186 = (FStar_Util.monitor_exit m)
in res))))

# 207 "FStar.SMTEncoding.Z3.fst"
let z3_job = (fun fresh label_messages input _74_191 -> (match (()) with
| () -> begin
(
# 210 "FStar.SMTEncoding.Z3.fst"
let _74_194 = (doZ3Exe fresh input)
in (match (_74_194) with
| (status, lblnegs) -> begin
(
# 211 "FStar.SMTEncoding.Z3.fst"
let result = (match (status) with
| UNSAT -> begin
(true, [])
end
| _74_197 -> begin
(
# 214 "FStar.SMTEncoding.Z3.fst"
let _74_198 = if ((FStar_ST.read FStar_Options.debug) <> []) then begin
(let _155_166 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _155_166))
end else begin
()
end
in (
# 215 "FStar.SMTEncoding.Z3.fst"
let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _74_206 -> (match (_74_206) with
| (m, _74_203, _74_205) -> begin
((Prims.fst m) = l)
end))))) with
| None -> begin
[]
end
| Some (_74_209, msg, r) -> begin
((msg, r))::[]
end))))
in (false, failing_assertions)))
end)
in result)
end))
end))

# 220 "FStar.SMTEncoding.Z3.fst"
let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _74_216 -> (match (()) with
| () -> begin
(
# 223 "FStar.SMTEncoding.Z3.fst"
let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| hd::tl -> begin
(
# 226 "FStar.SMTEncoding.Z3.fst"
let _74_221 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (
# 228 "FStar.SMTEncoding.Z3.fst"
let _74_224 = (FStar_Util.incr pending_jobs)
in (
# 229 "FStar.SMTEncoding.Z3.fst"
let _74_226 = (FStar_Util.monitor_exit job_queue)
in (
# 230 "FStar.SMTEncoding.Z3.fst"
let _74_228 = (run_job j)
in (
# 231 "FStar.SMTEncoding.Z3.fst"
let _74_231 = (with_monitor job_queue (fun _74_230 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (
# 232 "FStar.SMTEncoding.Z3.fst"
let _74_233 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _74_235 -> (match (()) with
| () -> begin
(
# 235 "FStar.SMTEncoding.Z3.fst"
let _74_236 = (FStar_Util.monitor_enter job_queue)
in (
# 236 "FStar.SMTEncoding.Z3.fst"
let rec aux = (fun _74_239 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(
# 238 "FStar.SMTEncoding.Z3.fst"
let _74_241 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _74_244 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _155_178 = (j.job ())
in (FStar_All.pipe_left j.callback _155_178)))

# 243 "FStar.SMTEncoding.Z3.fst"
let init : Prims.unit  ->  Prims.unit = (fun _74_246 -> (match (()) with
| () -> begin
(
# 246 "FStar.SMTEncoding.Z3.fst"
let n_runners = ((FStar_ST.read FStar_Options.n_cores) - 1)
in (
# 247 "FStar.SMTEncoding.Z3.fst"
let rec aux = (fun n -> if (n = 0) then begin
()
end else begin
(
# 249 "FStar.SMTEncoding.Z3.fst"
let _74_250 = (FStar_Util.spawn dequeue)
in (aux (n - 1)))
end)
in (aux n_runners)))
end))

# 250 "FStar.SMTEncoding.Z3.fst"
let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(
# 257 "FStar.SMTEncoding.Z3.fst"
let _74_254 = (FStar_Util.monitor_enter job_queue)
in (
# 258 "FStar.SMTEncoding.Z3.fst"
let _74_256 = (let _155_188 = (let _155_187 = (FStar_ST.read job_queue)
in (FStar_List.append _155_187 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _155_188))
in (
# 259 "FStar.SMTEncoding.Z3.fst"
let _74_258 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)

# 261 "FStar.SMTEncoding.Z3.fst"
let finish : Prims.unit  ->  Prims.unit = (fun _74_260 -> (match (()) with
| () -> begin
(
# 264 "FStar.SMTEncoding.Z3.fst"
let bg = (bg_z3_proc.grab ())
in (
# 265 "FStar.SMTEncoding.Z3.fst"
let _74_262 = (FStar_Util.kill_process bg)
in (
# 266 "FStar.SMTEncoding.Z3.fst"
let _74_264 = (bg_z3_proc.release ())
in (
# 267 "FStar.SMTEncoding.Z3.fst"
let rec aux = (fun _74_267 -> (match (()) with
| () -> begin
(
# 268 "FStar.SMTEncoding.Z3.fst"
let _74_271 = (with_monitor job_queue (fun _74_268 -> (match (()) with
| () -> begin
(let _155_196 = (FStar_ST.read pending_jobs)
in (let _155_195 = (let _155_194 = (FStar_ST.read job_queue)
in (FStar_List.length _155_194))
in (_155_196, _155_195)))
end)))
in (match (_74_271) with
| (n, m) -> begin
if ((n + m) = 0) then begin
(let _155_197 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _155_197 Prims.ignore))
end else begin
(
# 272 "FStar.SMTEncoding.Z3.fst"
let _74_272 = (FStar_Util.sleep 500)
in (aux ()))
end
end))
end))
in (aux ())))))
end))

# 274 "FStar.SMTEncoding.Z3.fst"
type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list

# 276 "FStar.SMTEncoding.Z3.fst"
let fresh_scope : FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))

# 277 "FStar.SMTEncoding.Z3.fst"
let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 278 "FStar.SMTEncoding.Z3.fst"
let push : Prims.string  ->  Prims.unit = (fun msg -> (
# 280 "FStar.SMTEncoding.Z3.fst"
let _74_275 = (let _155_201 = (let _155_200 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::[])::_155_200)
in (FStar_ST.op_Colon_Equals fresh_scope _155_201))
in (let _155_203 = (let _155_202 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[]) _155_202))
in (FStar_ST.op_Colon_Equals bg_scope _155_203))))

# 281 "FStar.SMTEncoding.Z3.fst"
let pop : Prims.string  ->  Prims.unit = (fun msg -> (
# 283 "FStar.SMTEncoding.Z3.fst"
let _74_278 = (let _155_207 = (let _155_206 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _155_206))
in (FStar_ST.op_Colon_Equals fresh_scope _155_207))
in (let _155_209 = (let _155_208 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[]) _155_208))
in (FStar_ST.op_Colon_Equals bg_scope _155_209))))

# 284 "FStar.SMTEncoding.Z3.fst"
let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (
# 286 "FStar.SMTEncoding.Z3.fst"
let _74_286 = (match ((FStar_ST.read fresh_scope)) with
| hd::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _74_285 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _155_213 = (let _155_212 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _155_212))
in (FStar_ST.op_Colon_Equals bg_scope _155_213))))

# 289 "FStar.SMTEncoding.Z3.fst"
let bgtheory : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun fresh -> if fresh then begin
(let _155_217 = (let _155_216 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _155_216))
in (FStar_All.pipe_right _155_217 FStar_List.flatten))
end else begin
(
# 293 "FStar.SMTEncoding.Z3.fst"
let bg = (FStar_ST.read bg_scope)
in (
# 294 "FStar.SMTEncoding.Z3.fst"
let _74_290 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)

# 295 "FStar.SMTEncoding.Z3.fst"
let refresh : Prims.unit  ->  Prims.unit = (fun _74_292 -> (match (()) with
| () -> begin
(
# 297 "FStar.SMTEncoding.Z3.fst"
let _74_293 = (bg_z3_proc.refresh ())
in (
# 298 "FStar.SMTEncoding.Z3.fst"
let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))

# 299 "FStar.SMTEncoding.Z3.fst"
let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))

# 301 "FStar.SMTEncoding.Z3.fst"
let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 303 "FStar.SMTEncoding.Z3.fst"
let _74_298 = (pop msg)
in (refresh ())))

# 304 "FStar.SMTEncoding.Z3.fst"
let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| hd::s::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _74_307 -> begin
(FStar_All.failwith "Impossible")
end))

# 309 "FStar.SMTEncoding.Z3.fst"
let ask = (fun fresh label_messages qry cb -> (
# 311 "FStar.SMTEncoding.Z3.fst"
let fresh = (fresh && ((FStar_ST.read FStar_Options.n_cores) > 1))
in (
# 312 "FStar.SMTEncoding.Z3.fst"
let theory = (bgtheory fresh)
in (
# 313 "FStar.SMTEncoding.Z3.fst"
let theory = if fresh then begin
(FStar_List.append theory qry)
end else begin
(FStar_List.append (FStar_List.append (FStar_List.append theory ((FStar_SMTEncoding_Term.Push)::[])) qry) ((FStar_SMTEncoding_Term.Pop)::[]))
end
in (
# 317 "FStar.SMTEncoding.Z3.fst"
let input = (let _155_234 = (let _155_233 = (let _155_232 = (z3_options ())
in (FStar_SMTEncoding_Term.declToSmt _155_232))
in (FStar_List.map _155_233 theory))
in (FStar_All.pipe_right _155_234 (FStar_String.concat "\n")))
in (
# 318 "FStar.SMTEncoding.Z3.fst"
let _74_316 = if (FStar_ST.read FStar_Options.logQueries) then begin
(log_query fresh input)
end else begin
()
end
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb})))))))




