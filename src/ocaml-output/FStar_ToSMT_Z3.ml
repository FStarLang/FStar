
open Prims
# 26 "FStar.ToSMT.Z3.fst"
type z3version =
| Z3V_Unknown
| Z3V of (Prims.int * Prims.int * Prims.int)

# 27 "FStar.ToSMT.Z3.fst"
let is_Z3V_Unknown = (fun _discr_ -> (match (_discr_) with
| Z3V_Unknown (_) -> begin
true
end
| _ -> begin
false
end))

# 28 "FStar.ToSMT.Z3.fst"
let is_Z3V = (fun _discr_ -> (match (_discr_) with
| Z3V (_) -> begin
true
end
| _ -> begin
false
end))

# 28 "FStar.ToSMT.Z3.fst"
let ___Z3V____0 : z3version  ->  (Prims.int * Prims.int * Prims.int) = (fun projectee -> (match (projectee) with
| Z3V (_45_4) -> begin
_45_4
end))

# 30 "FStar.ToSMT.Z3.fst"
let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _45_9 -> (match (_45_9) with
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

# 39 "FStar.ToSMT.Z3.fst"
let z3v_le : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.bool = (fun known wanted -> (match ((z3v_compare known wanted)) with
| None -> begin
false
end
| Some (i) -> begin
(i >= 0)
end))

# 44 "FStar.ToSMT.Z3.fst"
let _z3version : z3version Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 46 "FStar.ToSMT.Z3.fst"
let get_z3version : Prims.unit  ->  z3version = (fun _45_21 -> (match (()) with
| () -> begin
(
# 47 "FStar.ToSMT.Z3.fst"
let prefix = "Z3 version "
in (match ((FStar_ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(
# 52 "FStar.ToSMT.Z3.fst"
let _45_31 = (let _124_26 = (FStar_ST.read FStar_Options.z3_exe)
in (FStar_Util.run_proc _124_26 "-version" ""))
in (match (_45_31) with
| (_45_27, out, _45_30) -> begin
(
# 53 "FStar.ToSMT.Z3.fst"
let out = (match ((FStar_Util.splitlines out)) with
| x::_45_33 when (FStar_Util.starts_with x prefix) -> begin
(
# 56 "FStar.ToSMT.Z3.fst"
let x = (let _124_27 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _124_27))
in (
# 57 "FStar.ToSMT.Z3.fst"
let x = (FStar_All.try_with (fun _45_38 -> (match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)) (fun _45_37 -> (match (_45_37) with
| _45_41 -> begin
[]
end)))
in (match (x) with
| i1::i2::i3::[] -> begin
Z3V ((i1, i2, i3))
end
| _45_50 -> begin
Z3V_Unknown
end)))
end
| _45_52 -> begin
Z3V_Unknown
end)
in (
# 64 "FStar.ToSMT.Z3.fst"
let _45_54 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))

# 66 "FStar.ToSMT.Z3.fst"
let ini_params : Prims.unit  ->  Prims.string = (fun _45_56 -> (match (()) with
| () -> begin
(
# 67 "FStar.ToSMT.Z3.fst"
let t = if (let _124_32 = (get_z3version ())
in (z3v_le _124_32 (4, 3, 1))) then begin
(FStar_ST.read FStar_Options.z3timeout)
end else begin
((FStar_ST.read FStar_Options.z3timeout) * 1000)
end
in (
# 72 "FStar.ToSMT.Z3.fst"
let timeout = (let _124_33 = (FStar_Util.string_of_int t)
in (FStar_Util.format1 "-t:%s" _124_33))
in (
# 73 "FStar.ToSMT.Z3.fst"
let relevancy = if (let _124_34 = (get_z3version ())
in (z3v_le _124_34 (4, 3, 1))) then begin
"RELEVANCY"
end else begin
"SMT.RELEVANCY"
end
in (FStar_Util.format2 "-smt2 -in %s AUTO_CONFIG=false MODEL=true %s=2" timeout relevancy))))
end))

# 84 "FStar.ToSMT.Z3.fst"
type z3status =
| SAT
| UNSAT
| UNKNOWN
| TIMEOUT

# 85 "FStar.ToSMT.Z3.fst"
let is_SAT = (fun _discr_ -> (match (_discr_) with
| SAT (_) -> begin
true
end
| _ -> begin
false
end))

# 86 "FStar.ToSMT.Z3.fst"
let is_UNSAT = (fun _discr_ -> (match (_discr_) with
| UNSAT (_) -> begin
true
end
| _ -> begin
false
end))

# 87 "FStar.ToSMT.Z3.fst"
let is_UNKNOWN = (fun _discr_ -> (match (_discr_) with
| UNKNOWN (_) -> begin
true
end
| _ -> begin
false
end))

# 88 "FStar.ToSMT.Z3.fst"
let is_TIMEOUT = (fun _discr_ -> (match (_discr_) with
| TIMEOUT (_) -> begin
true
end
| _ -> begin
false
end))

# 90 "FStar.ToSMT.Z3.fst"
let status_to_string : z3status  ->  Prims.string = (fun _45_1 -> (match (_45_1) with
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

# 96 "FStar.ToSMT.Z3.fst"
let tid : Prims.unit  ->  Prims.string = (fun _45_65 -> (match (()) with
| () -> begin
(let _124_43 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _124_43 FStar_Util.string_of_int))
end))

# 97 "FStar.ToSMT.Z3.fst"
let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (
# 98 "FStar.ToSMT.Z3.fst"
let cond = (fun pid s -> (
# 99 "FStar.ToSMT.Z3.fst"
let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (let _124_51 = (FStar_ST.read FStar_Options.z3_exe)
in (let _124_50 = (ini_params ())
in (FStar_Util.start_process id _124_51 _124_50 cond)))))

# 104 "FStar.ToSMT.Z3.fst"
type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}

# 104 "FStar.ToSMT.Z3.fst"
let is_Mkbgproc : bgproc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbgproc"))))

# 111 "FStar.ToSMT.Z3.fst"
let queries_dot_smt2 : FStar_Util.file_handle Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 113 "FStar.ToSMT.Z3.fst"
let get_qfile : Prims.bool  ->  FStar_Util.file_handle = (
# 114 "FStar.ToSMT.Z3.fst"
let ctr = (FStar_Util.mk_ref 0)
in (fun fresh -> if fresh then begin
(
# 117 "FStar.ToSMT.Z3.fst"
let _45_77 = (FStar_Util.incr ctr)
in (let _124_84 = (let _124_83 = (let _124_82 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _124_82))
in (FStar_Util.format1 "queries-%s.smt2" _124_83))
in (FStar_Util.open_file_for_writing _124_84)))
end else begin
(match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
(
# 120 "FStar.ToSMT.Z3.fst"
let fh = (FStar_Util.open_file_for_writing "queries-bg-0.smt2")
in (
# 120 "FStar.ToSMT.Z3.fst"
let _45_81 = (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
in fh))
end
| Some (fh) -> begin
fh
end)
end))

# 123 "FStar.ToSMT.Z3.fst"
let log_query : Prims.bool  ->  Prims.string  ->  Prims.unit = (fun fresh i -> (
# 124 "FStar.ToSMT.Z3.fst"
let fh = (get_qfile fresh)
in (
# 125 "FStar.ToSMT.Z3.fst"
let _45_88 = (FStar_Util.append_to_file fh i)
in if fresh then begin
(FStar_Util.close_file fh)
end else begin
()
end)))

# 128 "FStar.ToSMT.Z3.fst"
let bg_z3_proc : bgproc = (
# 129 "FStar.ToSMT.Z3.fst"
let ctr = (FStar_Util.mk_ref (- (1)))
in (
# 130 "FStar.ToSMT.Z3.fst"
let new_proc = (fun _45_92 -> (match (()) with
| () -> begin
(let _124_93 = (let _124_92 = (
# 130 "FStar.ToSMT.Z3.fst"
let _45_93 = (FStar_Util.incr ctr)
in (let _124_91 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _124_91 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _124_92))
in (new_z3proc _124_93))
end))
in (
# 131 "FStar.ToSMT.Z3.fst"
let z3proc = (let _124_94 = (new_proc ())
in (FStar_Util.mk_ref _124_94))
in (
# 132 "FStar.ToSMT.Z3.fst"
let x = []
in (
# 133 "FStar.ToSMT.Z3.fst"
let grab = (fun _45_98 -> (match (()) with
| () -> begin
(
# 133 "FStar.ToSMT.Z3.fst"
let _45_99 = (FStar_Util.monitor_enter x)
in (FStar_ST.read z3proc))
end))
in (
# 134 "FStar.ToSMT.Z3.fst"
let release = (fun _45_102 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (
# 135 "FStar.ToSMT.Z3.fst"
let refresh = (fun _45_104 -> (match (()) with
| () -> begin
(
# 136 "FStar.ToSMT.Z3.fst"
let proc = (grab ())
in (
# 137 "FStar.ToSMT.Z3.fst"
let _45_106 = (FStar_Util.kill_process proc)
in (
# 138 "FStar.ToSMT.Z3.fst"
let _45_108 = (let _124_101 = (new_proc ())
in (FStar_ST.op_Colon_Equals z3proc _124_101))
in (
# 139 "FStar.ToSMT.Z3.fst"
let _45_116 = (match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
()
end
| Some (fh) -> begin
(
# 142 "FStar.ToSMT.Z3.fst"
let _45_113 = (FStar_Util.close_file fh)
in (
# 143 "FStar.ToSMT.Z3.fst"
let fh = (let _124_104 = (let _124_103 = (let _124_102 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _124_102 FStar_Util.string_of_int))
in (FStar_Util.format1 "queries-bg-%s.smt2" _124_103))
in (FStar_Util.open_file_for_writing _124_104))
in (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))))
end)
in (release ())))))
end))
in {grab = grab; release = release; refresh = refresh})))))))

# 151 "FStar.ToSMT.Z3.fst"
let doZ3Exe' : Prims.string  ->  FStar_Util.proc  ->  (z3status * Prims.string Prims.list) = (fun input z3proc -> (
# 152 "FStar.ToSMT.Z3.fst"
let parse = (fun z3out -> (
# 153 "FStar.ToSMT.Z3.fst"
let lines = (FStar_All.pipe_right (FStar_String.split (('\n')::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (
# 154 "FStar.ToSMT.Z3.fst"
let rec lblnegs = (fun lines -> (match (lines) with
| lname::"false"::rest -> begin
(let _124_113 = (lblnegs rest)
in (lname)::_124_113)
end
| lname::_45_132::rest -> begin
(lblnegs rest)
end
| _45_137 -> begin
[]
end))
in (
# 158 "FStar.ToSMT.Z3.fst"
let rec result = (fun x -> (match (x) with
| "timeout"::tl -> begin
(TIMEOUT, [])
end
| "unknown"::tl -> begin
(let _124_116 = (lblnegs tl)
in (UNKNOWN, _124_116))
end
| "sat"::tl -> begin
(let _124_117 = (lblnegs tl)
in (SAT, _124_117))
end
| "unsat"::tl -> begin
(UNSAT, [])
end
| _45_154::tl -> begin
(result tl)
end
| _45_157 -> begin
(let _124_121 = (let _124_120 = (let _124_119 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _124_119))
in (FStar_Util.format1 "Got output lines: %s\n" _124_120))
in (FStar_All.pipe_left FStar_All.failwith _124_121))
end))
in (result lines)))))
in (
# 166 "FStar.ToSMT.Z3.fst"
let stdout = (FStar_Util.ask_process z3proc input)
in (parse (FStar_Util.trim_string stdout)))))

# 169 "FStar.ToSMT.Z3.fst"
let doZ3Exe : Prims.bool  ->  Prims.string  ->  (z3status * Prims.string Prims.list) = (
# 170 "FStar.ToSMT.Z3.fst"
let ctr = (FStar_Util.mk_ref 0)
in (fun fresh input -> (
# 172 "FStar.ToSMT.Z3.fst"
let z3proc = if fresh then begin
(
# 172 "FStar.ToSMT.Z3.fst"
let _45_163 = (FStar_Util.incr ctr)
in (let _124_127 = (let _124_126 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _124_126))
in (new_z3proc _124_127)))
end else begin
(bg_z3_proc.grab ())
end
in (
# 173 "FStar.ToSMT.Z3.fst"
let res = (doZ3Exe' input z3proc)
in (
# 175 "FStar.ToSMT.Z3.fst"
let _45_167 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))

# 178 "FStar.ToSMT.Z3.fst"
let z3_options : Prims.unit  ->  Prims.string = (fun _45_169 -> (match (()) with
| () -> begin
(
# 179 "FStar.ToSMT.Z3.fst"
let mbqi = if (let _124_130 = (get_z3version ())
in (z3v_le _124_130 (4, 3, 1))) then begin
"mbqi"
end else begin
"smt.mbqi"
end
in (
# 183 "FStar.ToSMT.Z3.fst"
let model_on_timeout = if (let _124_131 = (get_z3version ())
in (z3v_le _124_131 (4, 3, 1))) then begin
"(set-option :model-on-timeout true)\n"
end else begin
""
end
in (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "(set-option :global-decls false)\n" "(set-option :") mbqi) " false)\n") model_on_timeout)))
end))

# 191 "FStar.ToSMT.Z3.fst"
type 'a job =
{job : Prims.unit  ->  'a; callback : 'a  ->  Prims.unit}

# 191 "FStar.ToSMT.Z3.fst"
let is_Mkjob = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkjob"))))

# 195 "FStar.ToSMT.Z3.fst"
type z3job =
(Prims.bool * (Prims.string * FStar_Range.range) Prims.list) job

# 198 "FStar.ToSMT.Z3.fst"
let job_queue : z3job Prims.list FStar_ST.ref = (
# 199 "FStar.ToSMT.Z3.fst"
let x = (FStar_Util.mk_ref (({job = (fun _45_176 -> (match (()) with
| () -> begin
(let _124_155 = (let _124_154 = (let _124_153 = (FStar_Range.mk_range "" 0 0)
in ("", _124_153))
in (_124_154)::[])
in (false, _124_155))
end)); callback = (fun a -> ())})::[]))
in (
# 200 "FStar.ToSMT.Z3.fst"
let _45_179 = (FStar_ST.op_Colon_Equals x [])
in x))

# 202 "FStar.ToSMT.Z3.fst"
let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 0)

# 203 "FStar.ToSMT.Z3.fst"
let with_monitor = (fun m f -> (
# 204 "FStar.ToSMT.Z3.fst"
let _45_183 = (FStar_Util.monitor_enter m)
in (
# 205 "FStar.ToSMT.Z3.fst"
let res = (f ())
in (
# 206 "FStar.ToSMT.Z3.fst"
let _45_186 = (FStar_Util.monitor_exit m)
in res))))

# 209 "FStar.ToSMT.Z3.fst"
let z3_job = (fun fresh label_messages input _45_191 -> (match (()) with
| () -> begin
(
# 210 "FStar.ToSMT.Z3.fst"
let _45_194 = (doZ3Exe fresh input)
in (match (_45_194) with
| (status, lblnegs) -> begin
(
# 211 "FStar.ToSMT.Z3.fst"
let result = (match (status) with
| UNSAT -> begin
(true, [])
end
| _45_197 -> begin
(
# 214 "FStar.ToSMT.Z3.fst"
let _45_198 = if ((FStar_ST.read FStar_Options.debug) <> []) then begin
(let _124_166 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _124_166))
end else begin
()
end
in (
# 215 "FStar.ToSMT.Z3.fst"
let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _45_206 -> (match (_45_206) with
| (m, _45_203, _45_205) -> begin
((Prims.fst m) = l)
end))))) with
| None -> begin
[]
end
| Some (_45_209, msg, r) -> begin
((msg, r))::[]
end))))
in (false, failing_assertions)))
end)
in result)
end))
end))

# 222 "FStar.ToSMT.Z3.fst"
let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _45_216 -> (match (()) with
| () -> begin
(
# 223 "FStar.ToSMT.Z3.fst"
let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| hd::tl -> begin
(
# 226 "FStar.ToSMT.Z3.fst"
let _45_221 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (
# 228 "FStar.ToSMT.Z3.fst"
let _45_224 = (FStar_Util.incr pending_jobs)
in (
# 229 "FStar.ToSMT.Z3.fst"
let _45_226 = (FStar_Util.monitor_exit job_queue)
in (
# 230 "FStar.ToSMT.Z3.fst"
let _45_228 = (run_job j)
in (
# 231 "FStar.ToSMT.Z3.fst"
let _45_231 = (with_monitor job_queue (fun _45_230 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (
# 232 "FStar.ToSMT.Z3.fst"
let _45_233 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _45_235 -> (match (()) with
| () -> begin
(
# 235 "FStar.ToSMT.Z3.fst"
let _45_236 = (FStar_Util.monitor_enter job_queue)
in (
# 236 "FStar.ToSMT.Z3.fst"
let rec aux = (fun _45_239 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(
# 238 "FStar.ToSMT.Z3.fst"
let _45_241 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _45_244 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _124_178 = (j.job ())
in (FStar_All.pipe_left j.callback _124_178)))

# 245 "FStar.ToSMT.Z3.fst"
let init : Prims.unit  ->  Prims.unit = (fun _45_246 -> (match (()) with
| () -> begin
(
# 246 "FStar.ToSMT.Z3.fst"
let n_runners = ((FStar_ST.read FStar_Options.n_cores) - 1)
in (
# 247 "FStar.ToSMT.Z3.fst"
let rec aux = (fun n -> if (n = 0) then begin
()
end else begin
(
# 249 "FStar.ToSMT.Z3.fst"
let _45_250 = (FStar_Util.spawn dequeue)
in (aux (n - 1)))
end)
in (aux n_runners)))
end))

# 252 "FStar.ToSMT.Z3.fst"
let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(
# 257 "FStar.ToSMT.Z3.fst"
let _45_254 = (FStar_Util.monitor_enter job_queue)
in (
# 258 "FStar.ToSMT.Z3.fst"
let _45_256 = (let _124_188 = (let _124_187 = (FStar_ST.read job_queue)
in (FStar_List.append _124_187 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _124_188))
in (
# 259 "FStar.ToSMT.Z3.fst"
let _45_258 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)

# 263 "FStar.ToSMT.Z3.fst"
let finish : Prims.unit  ->  Prims.unit = (fun _45_260 -> (match (()) with
| () -> begin
(
# 264 "FStar.ToSMT.Z3.fst"
let bg = (bg_z3_proc.grab ())
in (
# 265 "FStar.ToSMT.Z3.fst"
let _45_262 = (FStar_Util.kill_process bg)
in (
# 266 "FStar.ToSMT.Z3.fst"
let _45_264 = (bg_z3_proc.release ())
in (
# 267 "FStar.ToSMT.Z3.fst"
let rec aux = (fun _45_267 -> (match (()) with
| () -> begin
(
# 268 "FStar.ToSMT.Z3.fst"
let _45_271 = (with_monitor job_queue (fun _45_268 -> (match (()) with
| () -> begin
(let _124_196 = (FStar_ST.read pending_jobs)
in (let _124_195 = (let _124_194 = (FStar_ST.read job_queue)
in (FStar_List.length _124_194))
in (_124_196, _124_195)))
end)))
in (match (_45_271) with
| (n, m) -> begin
if ((n + m) = 0) then begin
(let _124_197 = (FStar_Tc_Errors.report_all ())
in (FStar_All.pipe_right _124_197 Prims.ignore))
end else begin
(
# 272 "FStar.ToSMT.Z3.fst"
let _45_272 = (FStar_Util.sleep 500)
in (aux ()))
end
end))
end))
in (aux ())))))
end))

# 276 "FStar.ToSMT.Z3.fst"
type scope_t =
FStar_ToSMT_Term.decl Prims.list Prims.list

# 277 "FStar.ToSMT.Z3.fst"
let fresh_scope : FStar_ToSMT_Term.decl Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))

# 278 "FStar.ToSMT.Z3.fst"
let bg_scope : FStar_ToSMT_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 279 "FStar.ToSMT.Z3.fst"
let push : Prims.string  ->  Prims.unit = (fun msg -> (
# 280 "FStar.ToSMT.Z3.fst"
let _45_275 = (let _124_201 = (let _124_200 = (FStar_ST.read fresh_scope)
in ((FStar_ToSMT_Term.Caption (msg))::[])::_124_200)
in (FStar_ST.op_Colon_Equals fresh_scope _124_201))
in (let _124_203 = (let _124_202 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::(FStar_ToSMT_Term.Push)::[]) _124_202))
in (FStar_ST.op_Colon_Equals bg_scope _124_203))))

# 282 "FStar.ToSMT.Z3.fst"
let pop : Prims.string  ->  Prims.unit = (fun msg -> (
# 283 "FStar.ToSMT.Z3.fst"
let _45_278 = (let _124_207 = (let _124_206 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _124_206))
in (FStar_ST.op_Colon_Equals fresh_scope _124_207))
in (let _124_209 = (let _124_208 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::(FStar_ToSMT_Term.Pop)::[]) _124_208))
in (FStar_ST.op_Colon_Equals bg_scope _124_209))))

# 285 "FStar.ToSMT.Z3.fst"
let giveZ3 : FStar_ToSMT_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (
# 286 "FStar.ToSMT.Z3.fst"
let _45_286 = (match ((FStar_ST.read fresh_scope)) with
| hd::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _45_285 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _124_213 = (let _124_212 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _124_212))
in (FStar_ST.op_Colon_Equals bg_scope _124_213))))

# 290 "FStar.ToSMT.Z3.fst"
let bgtheory : Prims.bool  ->  FStar_ToSMT_Term.decl Prims.list = (fun fresh -> if fresh then begin
(let _124_217 = (let _124_216 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _124_216))
in (FStar_All.pipe_right _124_217 FStar_List.flatten))
end else begin
(
# 293 "FStar.ToSMT.Z3.fst"
let bg = (FStar_ST.read bg_scope)
in (
# 294 "FStar.ToSMT.Z3.fst"
let _45_290 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)

# 296 "FStar.ToSMT.Z3.fst"
let refresh : Prims.unit  ->  Prims.unit = (fun _45_292 -> (match (()) with
| () -> begin
(
# 297 "FStar.ToSMT.Z3.fst"
let _45_293 = (bg_z3_proc.refresh ())
in (
# 298 "FStar.ToSMT.Z3.fst"
let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))

# 300 "FStar.ToSMT.Z3.fst"
let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))

# 302 "FStar.ToSMT.Z3.fst"
let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 303 "FStar.ToSMT.Z3.fst"
let _45_298 = (pop msg)
in (refresh ())))

# 305 "FStar.ToSMT.Z3.fst"
let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| hd::s::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _45_307 -> begin
(FStar_All.failwith "Impossible")
end))

# 310 "FStar.ToSMT.Z3.fst"
let ask = (fun fresh label_messages qry cb -> (
# 311 "FStar.ToSMT.Z3.fst"
let fresh = (fresh && ((FStar_ST.read FStar_Options.n_cores) > 1))
in (
# 312 "FStar.ToSMT.Z3.fst"
let theory = (bgtheory fresh)
in (
# 313 "FStar.ToSMT.Z3.fst"
let theory = if fresh then begin
(FStar_List.append theory qry)
end else begin
(FStar_List.append (FStar_List.append (FStar_List.append theory ((FStar_ToSMT_Term.Push)::[])) qry) ((FStar_ToSMT_Term.Pop)::[]))
end
in (
# 317 "FStar.ToSMT.Z3.fst"
let input = (let _124_234 = (let _124_233 = (let _124_232 = (z3_options ())
in (FStar_ToSMT_Term.declToSmt _124_232))
in (FStar_List.map _124_233 theory))
in (FStar_All.pipe_right _124_234 (FStar_String.concat "\n")))
in (
# 318 "FStar.ToSMT.Z3.fst"
let _45_316 = if (FStar_ST.read FStar_Options.logQueries) then begin
(log_query fresh input)
end else begin
()
end
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb})))))))




