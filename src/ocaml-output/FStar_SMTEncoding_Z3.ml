
open Prims
# 26 "FStar.SMTEncoding.Z3.fst"
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
let ___Z3V____0 = (fun projectee -> (match (projectee) with
| Z3V (_75_4) -> begin
_75_4
end))

# 30 "FStar.SMTEncoding.Z3.fst"
let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _75_9 -> (match (_75_9) with
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

# 39 "FStar.SMTEncoding.Z3.fst"
let z3v_le : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.bool = (fun known wanted -> (match ((z3v_compare known wanted)) with
| None -> begin
false
end
| Some (i) -> begin
(i >= 0)
end))

# 44 "FStar.SMTEncoding.Z3.fst"
let _z3version : z3version Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 46 "FStar.SMTEncoding.Z3.fst"
let get_z3version : Prims.unit  ->  z3version = (fun _75_21 -> (match (()) with
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
let _75_31 = (let _159_26 = (FStar_ST.read FStar_Options.z3_exe)
in (FStar_Util.run_proc _159_26 "-version" ""))
in (match (_75_31) with
| (_75_27, out, _75_30) -> begin
(
# 53 "FStar.SMTEncoding.Z3.fst"
let out = (match ((FStar_Util.splitlines out)) with
| x::_75_33 when (FStar_Util.starts_with x prefix) -> begin
(
# 56 "FStar.SMTEncoding.Z3.fst"
let x = (let _159_27 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _159_27))
in (
# 57 "FStar.SMTEncoding.Z3.fst"
let x = (FStar_All.try_with (fun _75_38 -> (match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)) (fun _75_37 -> (match (_75_37) with
| _75_41 -> begin
[]
end)))
in (match (x) with
| i1::i2::i3::[] -> begin
Z3V ((i1, i2, i3))
end
| _75_50 -> begin
Z3V_Unknown
end)))
end
| _75_52 -> begin
Z3V_Unknown
end)
in (
# 64 "FStar.SMTEncoding.Z3.fst"
let _75_54 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))

# 66 "FStar.SMTEncoding.Z3.fst"
let ini_params : Prims.unit  ->  Prims.string = (fun _75_56 -> (match (()) with
| () -> begin
(
# 67 "FStar.SMTEncoding.Z3.fst"
let t = if (let _159_32 = (get_z3version ())
in (z3v_le _159_32 (4, 3, 1))) then begin
(FStar_ST.read FStar_Options.z3timeout)
end else begin
((FStar_ST.read FStar_Options.z3timeout) * 1000)
end
in (
# 72 "FStar.SMTEncoding.Z3.fst"
let timeout = (let _159_33 = (FStar_Util.string_of_int t)
in (FStar_Util.format1 "-t:%s" _159_33))
in (
# 73 "FStar.SMTEncoding.Z3.fst"
let relevancy = if (let _159_34 = (get_z3version ())
in (z3v_le _159_34 (4, 3, 1))) then begin
"RELEVANCY"
end else begin
"SMT.RELEVANCY"
end
in (FStar_Util.format2 "-smt2 -in %s AUTO_CONFIG=false MODEL=true %s=2" timeout relevancy))))
end))

# 84 "FStar.SMTEncoding.Z3.fst"
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

# 90 "FStar.SMTEncoding.Z3.fst"
let status_to_string : z3status  ->  Prims.string = (fun _75_1 -> (match (_75_1) with
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

# 96 "FStar.SMTEncoding.Z3.fst"
let tid : Prims.unit  ->  Prims.string = (fun _75_65 -> (match (()) with
| () -> begin
(let _159_43 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _159_43 FStar_Util.string_of_int))
end))

# 97 "FStar.SMTEncoding.Z3.fst"
let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (
# 98 "FStar.SMTEncoding.Z3.fst"
let cond = (fun pid s -> (
# 99 "FStar.SMTEncoding.Z3.fst"
let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (let _159_51 = (FStar_ST.read FStar_Options.z3_exe)
in (let _159_50 = (ini_params ())
in (FStar_Util.start_process id _159_51 _159_50 cond)))))

# 104 "FStar.SMTEncoding.Z3.fst"
type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}

# 104 "FStar.SMTEncoding.Z3.fst"
let is_Mkbgproc : bgproc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbgproc"))))

# 111 "FStar.SMTEncoding.Z3.fst"
let queries_dot_smt2 : FStar_Util.file_handle Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 113 "FStar.SMTEncoding.Z3.fst"
let get_qfile : Prims.bool  ->  FStar_Util.file_handle = (
# 114 "FStar.SMTEncoding.Z3.fst"
let ctr = (FStar_Util.mk_ref 0)
in (fun fresh -> if fresh then begin
(
# 117 "FStar.SMTEncoding.Z3.fst"
let _75_77 = (FStar_Util.incr ctr)
in (let _159_84 = (let _159_83 = (let _159_82 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _159_82))
in (FStar_Util.format1 "queries-%s.smt2" _159_83))
in (FStar_Util.open_file_for_writing _159_84)))
end else begin
(match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
(
# 120 "FStar.SMTEncoding.Z3.fst"
let fh = (FStar_Util.open_file_for_writing "queries-bg-0.smt2")
in (
# 120 "FStar.SMTEncoding.Z3.fst"
let _75_81 = (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
in fh))
end
| Some (fh) -> begin
fh
end)
end))

# 123 "FStar.SMTEncoding.Z3.fst"
let log_query : Prims.bool  ->  Prims.string  ->  Prims.unit = (fun fresh i -> (
# 124 "FStar.SMTEncoding.Z3.fst"
let fh = (get_qfile fresh)
in (
# 125 "FStar.SMTEncoding.Z3.fst"
let _75_88 = (FStar_Util.append_to_file fh i)
in if fresh then begin
(FStar_Util.close_file fh)
end else begin
()
end)))

# 128 "FStar.SMTEncoding.Z3.fst"
let bg_z3_proc : bgproc = (
# 129 "FStar.SMTEncoding.Z3.fst"
let ctr = (FStar_Util.mk_ref (- (1)))
in (
# 130 "FStar.SMTEncoding.Z3.fst"
let new_proc = (fun _75_92 -> (match (()) with
| () -> begin
(let _159_93 = (let _159_92 = (
# 130 "FStar.SMTEncoding.Z3.fst"
let _75_93 = (FStar_Util.incr ctr)
in (let _159_91 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _159_91 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _159_92))
in (new_z3proc _159_93))
end))
in (
# 131 "FStar.SMTEncoding.Z3.fst"
let z3proc = (let _159_94 = (new_proc ())
in (FStar_Util.mk_ref _159_94))
in (
# 132 "FStar.SMTEncoding.Z3.fst"
let x = []
in (
# 133 "FStar.SMTEncoding.Z3.fst"
let grab = (fun _75_98 -> (match (()) with
| () -> begin
(
# 133 "FStar.SMTEncoding.Z3.fst"
let _75_99 = (FStar_Util.monitor_enter x)
in (FStar_ST.read z3proc))
end))
in (
# 134 "FStar.SMTEncoding.Z3.fst"
let release = (fun _75_102 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (
# 135 "FStar.SMTEncoding.Z3.fst"
let refresh = (fun _75_104 -> (match (()) with
| () -> begin
(
# 136 "FStar.SMTEncoding.Z3.fst"
let proc = (grab ())
in (
# 137 "FStar.SMTEncoding.Z3.fst"
let _75_106 = (FStar_Util.kill_process proc)
in (
# 138 "FStar.SMTEncoding.Z3.fst"
let _75_108 = (let _159_101 = (new_proc ())
in (FStar_ST.op_Colon_Equals z3proc _159_101))
in (
# 139 "FStar.SMTEncoding.Z3.fst"
let _75_116 = (match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
()
end
| Some (fh) -> begin
(
# 142 "FStar.SMTEncoding.Z3.fst"
let _75_113 = (FStar_Util.close_file fh)
in (
# 143 "FStar.SMTEncoding.Z3.fst"
let fh = (let _159_104 = (let _159_103 = (let _159_102 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _159_102 FStar_Util.string_of_int))
in (FStar_Util.format1 "queries-bg-%s.smt2" _159_103))
in (FStar_Util.open_file_for_writing _159_104))
in (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))))
end)
in (release ())))))
end))
in {grab = grab; release = release; refresh = refresh})))))))

# 151 "FStar.SMTEncoding.Z3.fst"
let doZ3Exe' : Prims.string  ->  FStar_Util.proc  ->  (z3status * Prims.string Prims.list) = (fun input z3proc -> (
# 152 "FStar.SMTEncoding.Z3.fst"
let parse = (fun z3out -> (
# 153 "FStar.SMTEncoding.Z3.fst"
let lines = (FStar_All.pipe_right (FStar_String.split (('\n')::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (
# 154 "FStar.SMTEncoding.Z3.fst"
let rec lblnegs = (fun lines -> (match (lines) with
| lname::"false"::rest -> begin
(let _159_113 = (lblnegs rest)
in (lname)::_159_113)
end
| lname::_75_132::rest -> begin
(lblnegs rest)
end
| _75_137 -> begin
[]
end))
in (
# 158 "FStar.SMTEncoding.Z3.fst"
let rec result = (fun x -> (match (x) with
| "timeout"::tl -> begin
(TIMEOUT, [])
end
| "unknown"::tl -> begin
(let _159_116 = (lblnegs tl)
in (UNKNOWN, _159_116))
end
| "sat"::tl -> begin
(let _159_117 = (lblnegs tl)
in (SAT, _159_117))
end
| "unsat"::tl -> begin
(UNSAT, [])
end
| _75_154::tl -> begin
(result tl)
end
| _75_157 -> begin
(let _159_121 = (let _159_120 = (let _159_119 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _159_119))
in (FStar_Util.format1 "Got output lines: %s\n" _159_120))
in (FStar_All.pipe_left FStar_All.failwith _159_121))
end))
in (result lines)))))
in (
# 166 "FStar.SMTEncoding.Z3.fst"
let stdout = (FStar_Util.ask_process z3proc input)
in (parse (FStar_Util.trim_string stdout)))))

# 169 "FStar.SMTEncoding.Z3.fst"
let doZ3Exe : Prims.bool  ->  Prims.string  ->  (z3status * Prims.string Prims.list) = (
# 170 "FStar.SMTEncoding.Z3.fst"
let ctr = (FStar_Util.mk_ref 0)
in (fun fresh input -> (
# 172 "FStar.SMTEncoding.Z3.fst"
let z3proc = if fresh then begin
(
# 172 "FStar.SMTEncoding.Z3.fst"
let _75_163 = (FStar_Util.incr ctr)
in (let _159_127 = (let _159_126 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _159_126))
in (new_z3proc _159_127)))
end else begin
(bg_z3_proc.grab ())
end
in (
# 173 "FStar.SMTEncoding.Z3.fst"
let res = (doZ3Exe' input z3proc)
in (
# 175 "FStar.SMTEncoding.Z3.fst"
let _75_167 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))

# 178 "FStar.SMTEncoding.Z3.fst"
let z3_options : Prims.unit  ->  Prims.string = (fun _75_169 -> (match (()) with
| () -> begin
(
# 179 "FStar.SMTEncoding.Z3.fst"
let mbqi = if (let _159_130 = (get_z3version ())
in (z3v_le _159_130 (4, 3, 1))) then begin
"mbqi"
end else begin
"smt.mbqi"
end
in (
# 183 "FStar.SMTEncoding.Z3.fst"
let model_on_timeout = if (let _159_131 = (get_z3version ())
in (z3v_le _159_131 (4, 3, 1))) then begin
"(set-option :model-on-timeout true)\n"
end else begin
""
end
in (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "(set-option :global-decls false)\n" "(set-option :") mbqi) " false)\n") model_on_timeout)))
end))

# 191 "FStar.SMTEncoding.Z3.fst"
type 'a job =
{job : Prims.unit  ->  'a; callback : 'a  ->  Prims.unit}

# 191 "FStar.SMTEncoding.Z3.fst"
let is_Mkjob = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkjob"))))

# 195 "FStar.SMTEncoding.Z3.fst"
type z3job =
(Prims.bool * FStar_SMTEncoding_Term.error_label Prims.list) job

# 197 "FStar.SMTEncoding.Z3.fst"
let job_queue : z3job Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 201 "FStar.SMTEncoding.Z3.fst"
let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 0)

# 202 "FStar.SMTEncoding.Z3.fst"
let with_monitor = (fun m f -> (
# 203 "FStar.SMTEncoding.Z3.fst"
let _75_178 = (FStar_Util.monitor_enter m)
in (
# 204 "FStar.SMTEncoding.Z3.fst"
let res = (f ())
in (
# 205 "FStar.SMTEncoding.Z3.fst"
let _75_181 = (FStar_Util.monitor_exit m)
in res))))

# 208 "FStar.SMTEncoding.Z3.fst"
let z3_job = (fun fresh label_messages input _75_186 -> (match (()) with
| () -> begin
(
# 209 "FStar.SMTEncoding.Z3.fst"
let _75_189 = (doZ3Exe fresh input)
in (match (_75_189) with
| (status, lblnegs) -> begin
(
# 210 "FStar.SMTEncoding.Z3.fst"
let result = (match (status) with
| UNSAT -> begin
(true, [])
end
| _75_192 -> begin
(
# 213 "FStar.SMTEncoding.Z3.fst"
let _75_193 = if ((FStar_ST.read FStar_Options.debug) <> []) then begin
(let _159_161 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _159_161))
end else begin
()
end
in (
# 214 "FStar.SMTEncoding.Z3.fst"
let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _75_201 -> (match (_75_201) with
| (m, _75_198, _75_200) -> begin
((Prims.fst m) = l)
end))))) with
| None -> begin
[]
end
| Some (lbl, msg, r) -> begin
((lbl, msg, r))::[]
end))))
in (false, failing_assertions)))
end)
in result)
end))
end))

# 221 "FStar.SMTEncoding.Z3.fst"
let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _75_210 -> (match (()) with
| () -> begin
(
# 222 "FStar.SMTEncoding.Z3.fst"
let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| hd::tl -> begin
(
# 225 "FStar.SMTEncoding.Z3.fst"
let _75_215 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (
# 227 "FStar.SMTEncoding.Z3.fst"
let _75_218 = (FStar_Util.incr pending_jobs)
in (
# 228 "FStar.SMTEncoding.Z3.fst"
let _75_220 = (FStar_Util.monitor_exit job_queue)
in (
# 229 "FStar.SMTEncoding.Z3.fst"
let _75_222 = (run_job j)
in (
# 230 "FStar.SMTEncoding.Z3.fst"
let _75_225 = (with_monitor job_queue (fun _75_224 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (
# 231 "FStar.SMTEncoding.Z3.fst"
let _75_227 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _75_229 -> (match (()) with
| () -> begin
(
# 234 "FStar.SMTEncoding.Z3.fst"
let _75_230 = (FStar_Util.monitor_enter job_queue)
in (
# 235 "FStar.SMTEncoding.Z3.fst"
let rec aux = (fun _75_233 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(
# 237 "FStar.SMTEncoding.Z3.fst"
let _75_235 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _75_238 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _159_173 = (j.job ())
in (FStar_All.pipe_left j.callback _159_173)))

# 244 "FStar.SMTEncoding.Z3.fst"
let init : Prims.unit  ->  Prims.unit = (fun _75_240 -> (match (()) with
| () -> begin
(
# 245 "FStar.SMTEncoding.Z3.fst"
let n_runners = ((FStar_ST.read FStar_Options.n_cores) - 1)
in (
# 246 "FStar.SMTEncoding.Z3.fst"
let rec aux = (fun n -> if (n = 0) then begin
()
end else begin
(
# 248 "FStar.SMTEncoding.Z3.fst"
let _75_244 = (FStar_Util.spawn dequeue)
in (aux (n - 1)))
end)
in (aux n_runners)))
end))

# 251 "FStar.SMTEncoding.Z3.fst"
let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(
# 256 "FStar.SMTEncoding.Z3.fst"
let _75_248 = (FStar_Util.monitor_enter job_queue)
in (
# 257 "FStar.SMTEncoding.Z3.fst"
let _75_250 = (let _159_183 = (let _159_182 = (FStar_ST.read job_queue)
in (FStar_List.append _159_182 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _159_183))
in (
# 258 "FStar.SMTEncoding.Z3.fst"
let _75_252 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)

# 262 "FStar.SMTEncoding.Z3.fst"
let finish : Prims.unit  ->  Prims.unit = (fun _75_254 -> (match (()) with
| () -> begin
(
# 263 "FStar.SMTEncoding.Z3.fst"
let bg = (bg_z3_proc.grab ())
in (
# 264 "FStar.SMTEncoding.Z3.fst"
let _75_256 = (FStar_Util.kill_process bg)
in (
# 265 "FStar.SMTEncoding.Z3.fst"
let _75_258 = (bg_z3_proc.release ())
in (
# 266 "FStar.SMTEncoding.Z3.fst"
let rec aux = (fun _75_261 -> (match (()) with
| () -> begin
(
# 267 "FStar.SMTEncoding.Z3.fst"
let _75_265 = (with_monitor job_queue (fun _75_262 -> (match (()) with
| () -> begin
(let _159_191 = (FStar_ST.read pending_jobs)
in (let _159_190 = (let _159_189 = (FStar_ST.read job_queue)
in (FStar_List.length _159_189))
in (_159_191, _159_190)))
end)))
in (match (_75_265) with
| (n, m) -> begin
if ((n + m) = 0) then begin
(let _159_192 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _159_192 Prims.ignore))
end else begin
(
# 271 "FStar.SMTEncoding.Z3.fst"
let _75_266 = (FStar_Util.sleep 500)
in (aux ()))
end
end))
end))
in (aux ())))))
end))

# 275 "FStar.SMTEncoding.Z3.fst"
type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list

# 276 "FStar.SMTEncoding.Z3.fst"
let fresh_scope : FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))

# 277 "FStar.SMTEncoding.Z3.fst"
let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 278 "FStar.SMTEncoding.Z3.fst"
let push : Prims.string  ->  Prims.unit = (fun msg -> (
# 279 "FStar.SMTEncoding.Z3.fst"
let _75_269 = (let _159_196 = (let _159_195 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::[])::_159_195)
in (FStar_ST.op_Colon_Equals fresh_scope _159_196))
in (let _159_198 = (let _159_197 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[]) _159_197))
in (FStar_ST.op_Colon_Equals bg_scope _159_198))))

# 281 "FStar.SMTEncoding.Z3.fst"
let pop : Prims.string  ->  Prims.unit = (fun msg -> (
# 282 "FStar.SMTEncoding.Z3.fst"
let _75_272 = (let _159_202 = (let _159_201 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _159_201))
in (FStar_ST.op_Colon_Equals fresh_scope _159_202))
in (let _159_204 = (let _159_203 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[]) _159_203))
in (FStar_ST.op_Colon_Equals bg_scope _159_204))))

# 284 "FStar.SMTEncoding.Z3.fst"
let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (
# 285 "FStar.SMTEncoding.Z3.fst"
let _75_280 = (match ((FStar_ST.read fresh_scope)) with
| hd::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _75_279 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _159_208 = (let _159_207 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _159_207))
in (FStar_ST.op_Colon_Equals bg_scope _159_208))))

# 289 "FStar.SMTEncoding.Z3.fst"
let bgtheory : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun fresh -> if fresh then begin
(let _159_212 = (let _159_211 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _159_211))
in (FStar_All.pipe_right _159_212 FStar_List.flatten))
end else begin
(
# 292 "FStar.SMTEncoding.Z3.fst"
let bg = (FStar_ST.read bg_scope)
in (
# 293 "FStar.SMTEncoding.Z3.fst"
let _75_284 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)

# 295 "FStar.SMTEncoding.Z3.fst"
let refresh : Prims.unit  ->  Prims.unit = (fun _75_286 -> (match (()) with
| () -> begin
(
# 296 "FStar.SMTEncoding.Z3.fst"
let _75_287 = (bg_z3_proc.refresh ())
in (
# 297 "FStar.SMTEncoding.Z3.fst"
let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))

# 299 "FStar.SMTEncoding.Z3.fst"
let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))

# 301 "FStar.SMTEncoding.Z3.fst"
let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 302 "FStar.SMTEncoding.Z3.fst"
let _75_292 = (pop msg)
in (refresh ())))

# 304 "FStar.SMTEncoding.Z3.fst"
let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| hd::s::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _75_301 -> begin
(FStar_All.failwith "Impossible")
end))

# 309 "FStar.SMTEncoding.Z3.fst"
let ask : Prims.bool  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * Prims.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  ((Prims.bool * FStar_SMTEncoding_Term.error_labels)  ->  Prims.unit)  ->  Prims.unit = (fun fresh label_messages qry cb -> (
# 310 "FStar.SMTEncoding.Z3.fst"
let fresh = (fresh && ((FStar_ST.read FStar_Options.n_cores) > 1))
in (
# 311 "FStar.SMTEncoding.Z3.fst"
let theory = (bgtheory fresh)
in (
# 312 "FStar.SMTEncoding.Z3.fst"
let theory = if fresh then begin
(FStar_List.append theory qry)
end else begin
(FStar_List.append (FStar_List.append (FStar_List.append theory ((FStar_SMTEncoding_Term.Push)::[])) qry) ((FStar_SMTEncoding_Term.Pop)::[]))
end
in (
# 316 "FStar.SMTEncoding.Z3.fst"
let input = (let _159_235 = (let _159_234 = (let _159_233 = (z3_options ())
in (FStar_SMTEncoding_Term.declToSmt _159_233))
in (FStar_List.map _159_234 theory))
in (FStar_All.pipe_right _159_235 (FStar_String.concat "\n")))
in (
# 317 "FStar.SMTEncoding.Z3.fst"
let _75_310 = if (FStar_ST.read FStar_Options.logQueries) then begin
(log_query fresh input)
end else begin
()
end
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb})))))))




