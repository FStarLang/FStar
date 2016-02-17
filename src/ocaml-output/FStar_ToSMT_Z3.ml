
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
# 51 "FStar.ToSMT.Z3.fst"
let _45_40 = (FStar_All.try_with (fun _45_27 -> (match (()) with
| () -> begin
(let _124_27 = (FStar_ST.read FStar_Options.z3_exe)
in (FStar_Util.run_proc _124_27 "-version" ""))
end)) (fun _45_26 -> (match (_45_26) with
| _45_30 -> begin
(
# 52 "FStar.ToSMT.Z3.fst"
let _45_31 = (FStar_Util.print_string "Error: No z3 executable was found\n")
in (FStar_All.exit 1))
end)))
in (match (_45_40) with
| (_45_36, out, _45_39) -> begin
(
# 54 "FStar.ToSMT.Z3.fst"
let out = (match ((FStar_Util.splitlines out)) with
| x::_45_42 when (FStar_Util.starts_with x prefix) -> begin
(
# 57 "FStar.ToSMT.Z3.fst"
let x = (let _124_29 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _124_29))
in (
# 58 "FStar.ToSMT.Z3.fst"
let x = (FStar_All.try_with (fun _45_47 -> (match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)) (fun _45_46 -> (match (_45_46) with
| _45_50 -> begin
[]
end)))
in (match (x) with
| i1::i2::i3::[] -> begin
Z3V ((i1, i2, i3))
end
| _45_59 -> begin
Z3V_Unknown
end)))
end
| _45_61 -> begin
Z3V_Unknown
end)
in (
# 65 "FStar.ToSMT.Z3.fst"
let _45_63 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))

# 67 "FStar.ToSMT.Z3.fst"
let ini_params : Prims.unit  ->  Prims.string = (fun _45_65 -> (match (()) with
| () -> begin
(
# 68 "FStar.ToSMT.Z3.fst"
let t = if (let _124_34 = (get_z3version ())
in (z3v_le _124_34 (4, 3, 1))) then begin
(FStar_ST.read FStar_Options.z3timeout)
end else begin
((FStar_ST.read FStar_Options.z3timeout) * 1000)
end
in (
# 73 "FStar.ToSMT.Z3.fst"
let timeout = (let _124_35 = (FStar_Util.string_of_int t)
in (FStar_Util.format1 "-t:%s" _124_35))
in (
# 74 "FStar.ToSMT.Z3.fst"
let relevancy = if (let _124_36 = (get_z3version ())
in (z3v_le _124_36 (4, 3, 1))) then begin
"RELEVANCY"
end else begin
"SMT.RELEVANCY"
end
in (FStar_Util.format2 "-smt2 -in %s AUTO_CONFIG=false MODEL=true %s=2" timeout relevancy))))
end))

# 85 "FStar.ToSMT.Z3.fst"
type z3status =
| SAT
| UNSAT
| UNKNOWN
| TIMEOUT

# 86 "FStar.ToSMT.Z3.fst"
let is_SAT = (fun _discr_ -> (match (_discr_) with
| SAT (_) -> begin
true
end
| _ -> begin
false
end))

# 87 "FStar.ToSMT.Z3.fst"
let is_UNSAT = (fun _discr_ -> (match (_discr_) with
| UNSAT (_) -> begin
true
end
| _ -> begin
false
end))

# 88 "FStar.ToSMT.Z3.fst"
let is_UNKNOWN = (fun _discr_ -> (match (_discr_) with
| UNKNOWN (_) -> begin
true
end
| _ -> begin
false
end))

# 89 "FStar.ToSMT.Z3.fst"
let is_TIMEOUT = (fun _discr_ -> (match (_discr_) with
| TIMEOUT (_) -> begin
true
end
| _ -> begin
false
end))

# 91 "FStar.ToSMT.Z3.fst"
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

# 97 "FStar.ToSMT.Z3.fst"
let tid : Prims.unit  ->  Prims.string = (fun _45_74 -> (match (()) with
| () -> begin
(let _124_45 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _124_45 FStar_Util.string_of_int))
end))

# 98 "FStar.ToSMT.Z3.fst"
let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (
# 99 "FStar.ToSMT.Z3.fst"
let cond = (fun pid s -> (
# 100 "FStar.ToSMT.Z3.fst"
let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (let _124_53 = (FStar_ST.read FStar_Options.z3_exe)
in (let _124_52 = (ini_params ())
in (FStar_Util.start_process id _124_53 _124_52 cond)))))

# 105 "FStar.ToSMT.Z3.fst"
type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}

# 105 "FStar.ToSMT.Z3.fst"
let is_Mkbgproc : bgproc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbgproc"))))

# 112 "FStar.ToSMT.Z3.fst"
let queries_dot_smt2 : FStar_Util.file_handle Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 114 "FStar.ToSMT.Z3.fst"
let get_qfile : Prims.bool  ->  FStar_Util.file_handle = (
# 115 "FStar.ToSMT.Z3.fst"
let ctr = (FStar_Util.mk_ref 0)
in (fun fresh -> if fresh then begin
(
# 118 "FStar.ToSMT.Z3.fst"
let _45_86 = (FStar_Util.incr ctr)
in (let _124_86 = (let _124_85 = (let _124_84 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _124_84))
in (FStar_Util.format1 "queries-%s.smt2" _124_85))
in (FStar_Util.open_file_for_writing _124_86)))
end else begin
(match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
(
# 121 "FStar.ToSMT.Z3.fst"
let fh = (FStar_Util.open_file_for_writing "queries-bg-0.smt2")
in (
# 121 "FStar.ToSMT.Z3.fst"
let _45_90 = (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
in fh))
end
| Some (fh) -> begin
fh
end)
end))

# 124 "FStar.ToSMT.Z3.fst"
let log_query : Prims.bool  ->  Prims.string  ->  Prims.unit = (fun fresh i -> (
# 125 "FStar.ToSMT.Z3.fst"
let fh = (get_qfile fresh)
in (
# 126 "FStar.ToSMT.Z3.fst"
let _45_97 = (FStar_Util.append_to_file fh i)
in if fresh then begin
(FStar_Util.close_file fh)
end else begin
()
end)))

# 129 "FStar.ToSMT.Z3.fst"
let bg_z3_proc : bgproc = (
# 130 "FStar.ToSMT.Z3.fst"
let ctr = (FStar_Util.mk_ref (- (1)))
in (
# 131 "FStar.ToSMT.Z3.fst"
let new_proc = (fun _45_101 -> (match (()) with
| () -> begin
(let _124_95 = (let _124_94 = (
# 131 "FStar.ToSMT.Z3.fst"
let _45_102 = (FStar_Util.incr ctr)
in (let _124_93 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _124_93 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _124_94))
in (new_z3proc _124_95))
end))
in (
# 132 "FStar.ToSMT.Z3.fst"
let z3proc = (let _124_96 = (new_proc ())
in (FStar_Util.mk_ref _124_96))
in (
# 133 "FStar.ToSMT.Z3.fst"
let x = []
in (
# 134 "FStar.ToSMT.Z3.fst"
let grab = (fun _45_107 -> (match (()) with
| () -> begin
(
# 134 "FStar.ToSMT.Z3.fst"
let _45_108 = (FStar_Util.monitor_enter x)
in (FStar_ST.read z3proc))
end))
in (
# 135 "FStar.ToSMT.Z3.fst"
let release = (fun _45_111 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (
# 136 "FStar.ToSMT.Z3.fst"
let refresh = (fun _45_113 -> (match (()) with
| () -> begin
(
# 137 "FStar.ToSMT.Z3.fst"
let proc = (grab ())
in (
# 138 "FStar.ToSMT.Z3.fst"
let _45_115 = (FStar_Util.kill_process proc)
in (
# 139 "FStar.ToSMT.Z3.fst"
let _45_117 = (let _124_103 = (new_proc ())
in (FStar_ST.op_Colon_Equals z3proc _124_103))
in (
# 140 "FStar.ToSMT.Z3.fst"
let _45_125 = (match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
()
end
| Some (fh) -> begin
(
# 143 "FStar.ToSMT.Z3.fst"
let _45_122 = (FStar_Util.close_file fh)
in (
# 144 "FStar.ToSMT.Z3.fst"
let fh = (let _124_106 = (let _124_105 = (let _124_104 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _124_104 FStar_Util.string_of_int))
in (FStar_Util.format1 "queries-bg-%s.smt2" _124_105))
in (FStar_Util.open_file_for_writing _124_106))
in (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))))
end)
in (release ())))))
end))
in {grab = grab; release = release; refresh = refresh})))))))

# 152 "FStar.ToSMT.Z3.fst"
let doZ3Exe' : Prims.string  ->  FStar_Util.proc  ->  (z3status * Prims.string Prims.list) = (fun input z3proc -> (
# 153 "FStar.ToSMT.Z3.fst"
let parse = (fun z3out -> (
# 154 "FStar.ToSMT.Z3.fst"
let lines = (FStar_All.pipe_right (FStar_String.split (('\n')::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (
# 155 "FStar.ToSMT.Z3.fst"
let rec lblnegs = (fun lines -> (match (lines) with
| lname::"false"::rest -> begin
(let _124_115 = (lblnegs rest)
in (lname)::_124_115)
end
| lname::_45_141::rest -> begin
(lblnegs rest)
end
| _45_146 -> begin
[]
end))
in (
# 159 "FStar.ToSMT.Z3.fst"
let rec result = (fun x -> (match (x) with
| "timeout"::tl -> begin
(TIMEOUT, [])
end
| "unknown"::tl -> begin
(let _124_118 = (lblnegs tl)
in (UNKNOWN, _124_118))
end
| "sat"::tl -> begin
(let _124_119 = (lblnegs tl)
in (SAT, _124_119))
end
| "unsat"::tl -> begin
(UNSAT, [])
end
| _45_163::tl -> begin
(result tl)
end
| _45_166 -> begin
(let _124_123 = (let _124_122 = (let _124_121 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _124_121))
in (FStar_Util.format1 "Got output lines: %s\n" _124_122))
in (FStar_All.pipe_left FStar_All.failwith _124_123))
end))
in (result lines)))))
in (
# 167 "FStar.ToSMT.Z3.fst"
let stdout = (FStar_Util.ask_process z3proc input)
in (parse (FStar_Util.trim_string stdout)))))

# 170 "FStar.ToSMT.Z3.fst"
let doZ3Exe : Prims.bool  ->  Prims.string  ->  (z3status * Prims.string Prims.list) = (
# 171 "FStar.ToSMT.Z3.fst"
let ctr = (FStar_Util.mk_ref 0)
in (fun fresh input -> (
# 173 "FStar.ToSMT.Z3.fst"
let z3proc = if fresh then begin
(
# 173 "FStar.ToSMT.Z3.fst"
let _45_172 = (FStar_Util.incr ctr)
in (let _124_129 = (let _124_128 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _124_128))
in (new_z3proc _124_129)))
end else begin
(bg_z3_proc.grab ())
end
in (
# 174 "FStar.ToSMT.Z3.fst"
let res = (doZ3Exe' input z3proc)
in (
# 176 "FStar.ToSMT.Z3.fst"
let _45_176 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))

# 179 "FStar.ToSMT.Z3.fst"
let z3_options : Prims.unit  ->  Prims.string = (fun _45_178 -> (match (()) with
| () -> begin
(
# 180 "FStar.ToSMT.Z3.fst"
let mbqi = if (let _124_132 = (get_z3version ())
in (z3v_le _124_132 (4, 3, 1))) then begin
"mbqi"
end else begin
"smt.mbqi"
end
in (
# 184 "FStar.ToSMT.Z3.fst"
let model_on_timeout = if (let _124_133 = (get_z3version ())
in (z3v_le _124_133 (4, 3, 1))) then begin
"(set-option :model-on-timeout true)\n"
end else begin
""
end
in (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "(set-option :global-decls false)\n" "(set-option :") mbqi) " false)\n") model_on_timeout)))
end))

# 192 "FStar.ToSMT.Z3.fst"
type 'a job =
{job : Prims.unit  ->  'a; callback : 'a  ->  Prims.unit}

# 192 "FStar.ToSMT.Z3.fst"
let is_Mkjob = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkjob"))))

# 196 "FStar.ToSMT.Z3.fst"
type z3job =
(Prims.bool * (Prims.string * FStar_Range.range) Prims.list) job

# 199 "FStar.ToSMT.Z3.fst"
let job_queue : z3job Prims.list FStar_ST.ref = (
# 200 "FStar.ToSMT.Z3.fst"
let x = (FStar_Util.mk_ref (({job = (fun _45_185 -> (match (()) with
| () -> begin
(let _124_157 = (let _124_156 = (let _124_155 = (FStar_Range.mk_range "" 0 0)
in ("", _124_155))
in (_124_156)::[])
in (false, _124_157))
end)); callback = (fun a -> ())})::[]))
in (
# 201 "FStar.ToSMT.Z3.fst"
let _45_188 = (FStar_ST.op_Colon_Equals x [])
in x))

# 203 "FStar.ToSMT.Z3.fst"
let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 0)

# 204 "FStar.ToSMT.Z3.fst"
let with_monitor = (fun m f -> (
# 205 "FStar.ToSMT.Z3.fst"
let _45_192 = (FStar_Util.monitor_enter m)
in (
# 206 "FStar.ToSMT.Z3.fst"
let res = (f ())
in (
# 207 "FStar.ToSMT.Z3.fst"
let _45_195 = (FStar_Util.monitor_exit m)
in res))))

# 210 "FStar.ToSMT.Z3.fst"
let z3_job = (fun fresh label_messages input _45_200 -> (match (()) with
| () -> begin
(
# 211 "FStar.ToSMT.Z3.fst"
let _45_203 = (doZ3Exe fresh input)
in (match (_45_203) with
| (status, lblnegs) -> begin
(
# 212 "FStar.ToSMT.Z3.fst"
let result = (match (status) with
| UNSAT -> begin
(true, [])
end
| _45_206 -> begin
(
# 215 "FStar.ToSMT.Z3.fst"
let _45_207 = if ((FStar_ST.read FStar_Options.debug) <> []) then begin
(let _124_168 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _124_168))
end else begin
()
end
in (
# 216 "FStar.ToSMT.Z3.fst"
let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _45_215 -> (match (_45_215) with
| (m, _45_212, _45_214) -> begin
((Prims.fst m) = l)
end))))) with
| None -> begin
[]
end
| Some (_45_218, msg, r) -> begin
((msg, r))::[]
end))))
in (false, failing_assertions)))
end)
in result)
end))
end))

# 223 "FStar.ToSMT.Z3.fst"
let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _45_225 -> (match (()) with
| () -> begin
(
# 224 "FStar.ToSMT.Z3.fst"
let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| hd::tl -> begin
(
# 227 "FStar.ToSMT.Z3.fst"
let _45_230 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (
# 229 "FStar.ToSMT.Z3.fst"
let _45_233 = (FStar_Util.incr pending_jobs)
in (
# 230 "FStar.ToSMT.Z3.fst"
let _45_235 = (FStar_Util.monitor_exit job_queue)
in (
# 231 "FStar.ToSMT.Z3.fst"
let _45_237 = (run_job j)
in (
# 232 "FStar.ToSMT.Z3.fst"
let _45_240 = (with_monitor job_queue (fun _45_239 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (
# 233 "FStar.ToSMT.Z3.fst"
let _45_242 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _45_244 -> (match (()) with
| () -> begin
(
# 236 "FStar.ToSMT.Z3.fst"
let _45_245 = (FStar_Util.monitor_enter job_queue)
in (
# 237 "FStar.ToSMT.Z3.fst"
let rec aux = (fun _45_248 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(
# 239 "FStar.ToSMT.Z3.fst"
let _45_250 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _45_253 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _124_180 = (j.job ())
in (FStar_All.pipe_left j.callback _124_180)))

# 246 "FStar.ToSMT.Z3.fst"
let init : Prims.unit  ->  Prims.unit = (fun _45_255 -> (match (()) with
| () -> begin
(
# 247 "FStar.ToSMT.Z3.fst"
let n_runners = ((FStar_ST.read FStar_Options.n_cores) - 1)
in (
# 248 "FStar.ToSMT.Z3.fst"
let rec aux = (fun n -> if (n = 0) then begin
()
end else begin
(
# 250 "FStar.ToSMT.Z3.fst"
let _45_259 = (FStar_Util.spawn dequeue)
in (aux (n - 1)))
end)
in (aux n_runners)))
end))

# 253 "FStar.ToSMT.Z3.fst"
let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(
# 258 "FStar.ToSMT.Z3.fst"
let _45_263 = (FStar_Util.monitor_enter job_queue)
in (
# 259 "FStar.ToSMT.Z3.fst"
let _45_265 = (let _124_190 = (let _124_189 = (FStar_ST.read job_queue)
in (FStar_List.append _124_189 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _124_190))
in (
# 260 "FStar.ToSMT.Z3.fst"
let _45_267 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)

# 264 "FStar.ToSMT.Z3.fst"
let finish : Prims.unit  ->  Prims.unit = (fun _45_269 -> (match (()) with
| () -> begin
(
# 265 "FStar.ToSMT.Z3.fst"
let bg = (bg_z3_proc.grab ())
in (
# 266 "FStar.ToSMT.Z3.fst"
let _45_271 = (FStar_Util.kill_process bg)
in (
# 267 "FStar.ToSMT.Z3.fst"
let _45_273 = (bg_z3_proc.release ())
in (
# 268 "FStar.ToSMT.Z3.fst"
let rec aux = (fun _45_276 -> (match (()) with
| () -> begin
(
# 269 "FStar.ToSMT.Z3.fst"
let _45_280 = (with_monitor job_queue (fun _45_277 -> (match (()) with
| () -> begin
(let _124_198 = (FStar_ST.read pending_jobs)
in (let _124_197 = (let _124_196 = (FStar_ST.read job_queue)
in (FStar_List.length _124_196))
in (_124_198, _124_197)))
end)))
in (match (_45_280) with
| (n, m) -> begin
if ((n + m) = 0) then begin
(let _124_199 = (FStar_Tc_Errors.report_all ())
in (FStar_All.pipe_right _124_199 Prims.ignore))
end else begin
(
# 273 "FStar.ToSMT.Z3.fst"
let _45_281 = (FStar_Util.sleep 500)
in (aux ()))
end
end))
end))
in (aux ())))))
end))

# 277 "FStar.ToSMT.Z3.fst"
type scope_t =
FStar_ToSMT_Term.decl Prims.list Prims.list

# 278 "FStar.ToSMT.Z3.fst"
let fresh_scope : FStar_ToSMT_Term.decl Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))

# 279 "FStar.ToSMT.Z3.fst"
let bg_scope : FStar_ToSMT_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 280 "FStar.ToSMT.Z3.fst"
let push : Prims.string  ->  Prims.unit = (fun msg -> (
# 281 "FStar.ToSMT.Z3.fst"
let _45_284 = (let _124_203 = (let _124_202 = (FStar_ST.read fresh_scope)
in ((FStar_ToSMT_Term.Caption (msg))::[])::_124_202)
in (FStar_ST.op_Colon_Equals fresh_scope _124_203))
in (let _124_205 = (let _124_204 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::(FStar_ToSMT_Term.Push)::[]) _124_204))
in (FStar_ST.op_Colon_Equals bg_scope _124_205))))

# 283 "FStar.ToSMT.Z3.fst"
let pop : Prims.string  ->  Prims.unit = (fun msg -> (
# 284 "FStar.ToSMT.Z3.fst"
let _45_287 = (let _124_209 = (let _124_208 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _124_208))
in (FStar_ST.op_Colon_Equals fresh_scope _124_209))
in (let _124_211 = (let _124_210 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::(FStar_ToSMT_Term.Pop)::[]) _124_210))
in (FStar_ST.op_Colon_Equals bg_scope _124_211))))

# 286 "FStar.ToSMT.Z3.fst"
let giveZ3 : FStar_ToSMT_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (
# 287 "FStar.ToSMT.Z3.fst"
let _45_295 = (match ((FStar_ST.read fresh_scope)) with
| hd::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _45_294 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _124_215 = (let _124_214 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _124_214))
in (FStar_ST.op_Colon_Equals bg_scope _124_215))))

# 291 "FStar.ToSMT.Z3.fst"
let bgtheory : Prims.bool  ->  FStar_ToSMT_Term.decl Prims.list = (fun fresh -> if fresh then begin
(let _124_219 = (let _124_218 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _124_218))
in (FStar_All.pipe_right _124_219 FStar_List.flatten))
end else begin
(
# 294 "FStar.ToSMT.Z3.fst"
let bg = (FStar_ST.read bg_scope)
in (
# 295 "FStar.ToSMT.Z3.fst"
let _45_299 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)

# 297 "FStar.ToSMT.Z3.fst"
let refresh : Prims.unit  ->  Prims.unit = (fun _45_301 -> (match (()) with
| () -> begin
(
# 298 "FStar.ToSMT.Z3.fst"
let _45_302 = (bg_z3_proc.refresh ())
in (
# 299 "FStar.ToSMT.Z3.fst"
let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))

# 301 "FStar.ToSMT.Z3.fst"
let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))

# 303 "FStar.ToSMT.Z3.fst"
let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 304 "FStar.ToSMT.Z3.fst"
let _45_307 = (pop msg)
in (refresh ())))

# 306 "FStar.ToSMT.Z3.fst"
let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| hd::s::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _45_316 -> begin
(FStar_All.failwith "Impossible")
end))

# 311 "FStar.ToSMT.Z3.fst"
let ask = (fun fresh label_messages qry cb -> (
# 312 "FStar.ToSMT.Z3.fst"
let fresh = (fresh && ((FStar_ST.read FStar_Options.n_cores) > 1))
in (
# 313 "FStar.ToSMT.Z3.fst"
let theory = (bgtheory fresh)
in (
# 314 "FStar.ToSMT.Z3.fst"
let theory = if fresh then begin
(FStar_List.append theory qry)
end else begin
(FStar_List.append (FStar_List.append (FStar_List.append theory ((FStar_ToSMT_Term.Push)::[])) qry) ((FStar_ToSMT_Term.Pop)::[]))
end
in (
# 318 "FStar.ToSMT.Z3.fst"
let input = (let _124_236 = (let _124_235 = (let _124_234 = (z3_options ())
in (FStar_ToSMT_Term.declToSmt _124_234))
in (FStar_List.map _124_235 theory))
in (FStar_All.pipe_right _124_236 (FStar_String.concat "\n")))
in (
# 319 "FStar.ToSMT.Z3.fst"
let _45_325 = if (FStar_ST.read FStar_Options.logQueries) then begin
(log_query fresh input)
end else begin
()
end
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb})))))))




