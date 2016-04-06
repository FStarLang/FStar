
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
let ___Z3V____0 = (fun projectee -> (match (projectee) with
| Z3V (_80_4) -> begin
_80_4
end))

# 28 "FStar.SMTEncoding.Z3.fst"
let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _80_9 -> (match (_80_9) with
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
let get_z3version : Prims.unit  ->  z3version = (fun _80_21 -> (match (()) with
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
let _80_31 = (let _169_26 = (FStar_ST.read FStar_Options.z3_exe)
in (FStar_Util.run_proc _169_26 "-version" ""))
in (match (_80_31) with
| (_80_27, out, _80_30) -> begin
(
# 53 "FStar.SMTEncoding.Z3.fst"
let out = (match ((FStar_Util.splitlines out)) with
| x::_80_33 when (FStar_Util.starts_with x prefix) -> begin
(
# 56 "FStar.SMTEncoding.Z3.fst"
let x = (let _169_27 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _169_27))
in (
# 57 "FStar.SMTEncoding.Z3.fst"
let x = try
(match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)
with
| _80_41 -> begin
[]
end
in (match (x) with
| i1::i2::i3::[] -> begin
Z3V ((i1, i2, i3))
end
| _80_50 -> begin
Z3V_Unknown
end)))
end
| _80_52 -> begin
Z3V_Unknown
end)
in (
# 64 "FStar.SMTEncoding.Z3.fst"
let _80_54 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))

# 64 "FStar.SMTEncoding.Z3.fst"
let ini_params : Prims.unit  ->  Prims.string = (fun _80_56 -> (match (()) with
| () -> begin
(
# 67 "FStar.SMTEncoding.Z3.fst"
let t = if (let _169_32 = (get_z3version ())
in (z3v_le _169_32 (4, 3, 1))) then begin
(FStar_ST.read FStar_Options.z3timeout)
end else begin
((FStar_ST.read FStar_Options.z3timeout) * 1000)
end
in (
# 72 "FStar.SMTEncoding.Z3.fst"
let timeout = (let _169_33 = (FStar_Util.string_of_int t)
in (FStar_Util.format1 "-t:%s" _169_33))
in (
# 73 "FStar.SMTEncoding.Z3.fst"
let relevancy = if (let _169_34 = (get_z3version ())
in (z3v_le _169_34 (4, 3, 1))) then begin
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
let status_to_string : z3status  ->  Prims.string = (fun _80_1 -> (match (_80_1) with
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
let tid : Prims.unit  ->  Prims.string = (fun _80_65 -> (match (()) with
| () -> begin
(let _169_43 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _169_43 FStar_Util.string_of_int))
end))

# 96 "FStar.SMTEncoding.Z3.fst"
let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (
# 98 "FStar.SMTEncoding.Z3.fst"
let cond = (fun pid s -> (
# 99 "FStar.SMTEncoding.Z3.fst"
let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (let _169_51 = (FStar_ST.read FStar_Options.z3_exe)
in (let _169_50 = (ini_params ())
in (FStar_Util.start_process id _169_51 _169_50 cond)))))

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
let _80_77 = (FStar_Util.incr ctr)
in (let _169_84 = (let _169_83 = (let _169_82 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _169_82))
in (FStar_Util.format1 "queries-%s.smt2" _169_83))
in (FStar_Util.open_file_for_writing _169_84)))
end else begin
(match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
(
# 120 "FStar.SMTEncoding.Z3.fst"
let fh = (FStar_Util.open_file_for_writing "queries-bg-0.smt2")
in (
# 120 "FStar.SMTEncoding.Z3.fst"
let _80_81 = (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
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
let _80_88 = (FStar_Util.append_to_file fh i)
in if fresh then begin
(FStar_Util.close_file fh)
end else begin
()
end)))

# 126 "FStar.SMTEncoding.Z3.fst"
let the_z3proc : FStar_Util.proc Prims.option FStar_ST.ref = (FStar_ST.alloc None)

# 129 "FStar.SMTEncoding.Z3.fst"
let ctr : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (- (1)))

# 131 "FStar.SMTEncoding.Z3.fst"
let new_proc : Prims.unit  ->  FStar_Util.proc = (fun _80_90 -> (match (()) with
| () -> begin
(let _169_93 = (let _169_92 = (
# 134 "FStar.SMTEncoding.Z3.fst"
let _80_91 = (FStar_Util.incr ctr)
in (let _169_91 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _169_91 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _169_92))
in (new_z3proc _169_93))
end))

# 134 "FStar.SMTEncoding.Z3.fst"
let z3proc : Prims.unit  ->  FStar_Util.proc = (fun _80_93 -> (match (()) with
| () -> begin
(
# 137 "FStar.SMTEncoding.Z3.fst"
let _80_94 = if ((FStar_ST.read the_z3proc) = None) then begin
(let _169_97 = (let _169_96 = (new_proc ())
in Some (_169_96))
in (FStar_ST.op_Colon_Equals the_z3proc _169_97))
end else begin
()
end
in (let _169_98 = (FStar_ST.read the_z3proc)
in (FStar_Util.must _169_98)))
end))

# 139 "FStar.SMTEncoding.Z3.fst"
let bg_z3_proc : bgproc = (
# 142 "FStar.SMTEncoding.Z3.fst"
let x = []
in (
# 143 "FStar.SMTEncoding.Z3.fst"
let grab = (fun _80_98 -> (match (()) with
| () -> begin
(
# 143 "FStar.SMTEncoding.Z3.fst"
let _80_99 = (FStar_Util.monitor_enter x)
in (z3proc ()))
end))
in (
# 144 "FStar.SMTEncoding.Z3.fst"
let release = (fun _80_102 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (
# 145 "FStar.SMTEncoding.Z3.fst"
let refresh = (fun _80_104 -> (match (()) with
| () -> begin
(
# 146 "FStar.SMTEncoding.Z3.fst"
let proc = (grab ())
in (
# 147 "FStar.SMTEncoding.Z3.fst"
let _80_106 = (FStar_Util.kill_process proc)
in (
# 148 "FStar.SMTEncoding.Z3.fst"
let _80_108 = (let _169_106 = (let _169_105 = (new_proc ())
in Some (_169_105))
in (FStar_ST.op_Colon_Equals the_z3proc _169_106))
in (
# 149 "FStar.SMTEncoding.Z3.fst"
let _80_116 = (match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
()
end
| Some (fh) -> begin
(
# 152 "FStar.SMTEncoding.Z3.fst"
let _80_113 = (FStar_Util.close_file fh)
in (
# 153 "FStar.SMTEncoding.Z3.fst"
let fh = (let _169_109 = (let _169_108 = (let _169_107 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _169_107 FStar_Util.string_of_int))
in (FStar_Util.format1 "queries-bg-%s.smt2" _169_108))
in (FStar_Util.open_file_for_writing _169_109))
in (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))))
end)
in (release ())))))
end))
in {grab = grab; release = release; refresh = refresh}))))

# 159 "FStar.SMTEncoding.Z3.fst"
let doZ3Exe' : Prims.string  ->  FStar_Util.proc  ->  (z3status * Prims.string Prims.list) = (fun input z3proc -> (
# 162 "FStar.SMTEncoding.Z3.fst"
let parse = (fun z3out -> (
# 163 "FStar.SMTEncoding.Z3.fst"
let lines = (FStar_All.pipe_right (FStar_String.split (('\n')::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (
# 164 "FStar.SMTEncoding.Z3.fst"
let rec lblnegs = (fun lines -> (match (lines) with
| lname::"false"::rest -> begin
(let _169_118 = (lblnegs rest)
in (lname)::_169_118)
end
| lname::_80_132::rest -> begin
(lblnegs rest)
end
| _80_137 -> begin
[]
end))
in (
# 168 "FStar.SMTEncoding.Z3.fst"
let rec result = (fun x -> (match (x) with
| "timeout"::tl -> begin
(TIMEOUT, [])
end
| "unknown"::tl -> begin
(let _169_121 = (lblnegs tl)
in (UNKNOWN, _169_121))
end
| "sat"::tl -> begin
(let _169_122 = (lblnegs tl)
in (SAT, _169_122))
end
| "unsat"::tl -> begin
(UNSAT, [])
end
| _80_154::tl -> begin
(result tl)
end
| _80_157 -> begin
(let _169_126 = (let _169_125 = (let _169_124 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _169_124))
in (FStar_Util.format1 "Got output lines: %s\n" _169_125))
in (FStar_All.pipe_left FStar_All.failwith _169_126))
end))
in (result lines)))))
in (
# 176 "FStar.SMTEncoding.Z3.fst"
let stdout = (FStar_Util.ask_process z3proc input)
in (parse (FStar_Util.trim_string stdout)))))

# 177 "FStar.SMTEncoding.Z3.fst"
let doZ3Exe : Prims.bool  ->  Prims.string  ->  (z3status * Prims.string Prims.list) = (
# 180 "FStar.SMTEncoding.Z3.fst"
let ctr = (FStar_Util.mk_ref 0)
in (fun fresh input -> (
# 182 "FStar.SMTEncoding.Z3.fst"
let z3proc = if fresh then begin
(
# 182 "FStar.SMTEncoding.Z3.fst"
let _80_163 = (FStar_Util.incr ctr)
in (let _169_132 = (let _169_131 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _169_131))
in (new_z3proc _169_132)))
end else begin
(bg_z3_proc.grab ())
end
in (
# 183 "FStar.SMTEncoding.Z3.fst"
let res = (doZ3Exe' input z3proc)
in (
# 185 "FStar.SMTEncoding.Z3.fst"
let _80_167 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))

# 186 "FStar.SMTEncoding.Z3.fst"
let z3_options : Prims.unit  ->  Prims.string = (fun _80_169 -> (match (()) with
| () -> begin
(
# 189 "FStar.SMTEncoding.Z3.fst"
let mbqi = if (let _169_135 = (get_z3version ())
in (z3v_le _169_135 (4, 3, 1))) then begin
"mbqi"
end else begin
"smt.mbqi"
end
in (
# 193 "FStar.SMTEncoding.Z3.fst"
let model_on_timeout = if (let _169_136 = (get_z3version ())
in (z3v_le _169_136 (4, 3, 1))) then begin
"(set-option :model-on-timeout true)\n"
end else begin
""
end
in (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "(set-option :global-decls false)\n" "(set-option :") mbqi) " false)\n") model_on_timeout)))
end))

# 199 "FStar.SMTEncoding.Z3.fst"
type 'a job =
{job : Prims.unit  ->  'a; callback : 'a  ->  Prims.unit}

# 201 "FStar.SMTEncoding.Z3.fst"
let is_Mkjob = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkjob"))))

# 204 "FStar.SMTEncoding.Z3.fst"
type z3job =
(Prims.bool * FStar_SMTEncoding_Term.error_label Prims.list) job

# 205 "FStar.SMTEncoding.Z3.fst"
let job_queue : z3job Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 207 "FStar.SMTEncoding.Z3.fst"
let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 0)

# 211 "FStar.SMTEncoding.Z3.fst"
let with_monitor = (fun m f -> (
# 213 "FStar.SMTEncoding.Z3.fst"
let _80_178 = (FStar_Util.monitor_enter m)
in (
# 214 "FStar.SMTEncoding.Z3.fst"
let res = (f ())
in (
# 215 "FStar.SMTEncoding.Z3.fst"
let _80_181 = (FStar_Util.monitor_exit m)
in res))))

# 216 "FStar.SMTEncoding.Z3.fst"
let z3_job = (fun fresh label_messages input _80_186 -> (match (()) with
| () -> begin
(
# 219 "FStar.SMTEncoding.Z3.fst"
let _80_189 = (doZ3Exe fresh input)
in (match (_80_189) with
| (status, lblnegs) -> begin
(
# 220 "FStar.SMTEncoding.Z3.fst"
let result = (match (status) with
| UNSAT -> begin
(true, [])
end
| _80_192 -> begin
(
# 223 "FStar.SMTEncoding.Z3.fst"
let _80_193 = if ((FStar_ST.read FStar_Options.debug) <> []) then begin
(let _169_166 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _169_166))
end else begin
()
end
in (
# 224 "FStar.SMTEncoding.Z3.fst"
let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _80_201 -> (match (_80_201) with
| (m, _80_198, _80_200) -> begin
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

# 229 "FStar.SMTEncoding.Z3.fst"
let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _80_210 -> (match (()) with
| () -> begin
(
# 232 "FStar.SMTEncoding.Z3.fst"
let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| hd::tl -> begin
(
# 235 "FStar.SMTEncoding.Z3.fst"
let _80_215 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (
# 237 "FStar.SMTEncoding.Z3.fst"
let _80_218 = (FStar_Util.incr pending_jobs)
in (
# 238 "FStar.SMTEncoding.Z3.fst"
let _80_220 = (FStar_Util.monitor_exit job_queue)
in (
# 239 "FStar.SMTEncoding.Z3.fst"
let _80_222 = (run_job j)
in (
# 240 "FStar.SMTEncoding.Z3.fst"
let _80_225 = (with_monitor job_queue (fun _80_224 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (
# 241 "FStar.SMTEncoding.Z3.fst"
let _80_227 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _80_229 -> (match (()) with
| () -> begin
(
# 244 "FStar.SMTEncoding.Z3.fst"
let _80_230 = (FStar_Util.monitor_enter job_queue)
in (
# 245 "FStar.SMTEncoding.Z3.fst"
let rec aux = (fun _80_233 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(
# 247 "FStar.SMTEncoding.Z3.fst"
let _80_235 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _80_238 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _169_178 = (j.job ())
in (FStar_All.pipe_left j.callback _169_178)))

# 252 "FStar.SMTEncoding.Z3.fst"
let init : Prims.unit  ->  Prims.unit = (fun _80_240 -> (match (()) with
| () -> begin
(
# 255 "FStar.SMTEncoding.Z3.fst"
let n_runners = ((FStar_ST.read FStar_Options.n_cores) - 1)
in (
# 256 "FStar.SMTEncoding.Z3.fst"
let rec aux = (fun n -> if (n = 0) then begin
()
end else begin
(
# 258 "FStar.SMTEncoding.Z3.fst"
let _80_244 = (FStar_Util.spawn dequeue)
in (aux (n - 1)))
end)
in (aux n_runners)))
end))

# 259 "FStar.SMTEncoding.Z3.fst"
let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(
# 266 "FStar.SMTEncoding.Z3.fst"
let _80_248 = (FStar_Util.monitor_enter job_queue)
in (
# 267 "FStar.SMTEncoding.Z3.fst"
let _80_250 = (let _169_188 = (let _169_187 = (FStar_ST.read job_queue)
in (FStar_List.append _169_187 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _169_188))
in (
# 268 "FStar.SMTEncoding.Z3.fst"
let _80_252 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)

# 270 "FStar.SMTEncoding.Z3.fst"
let finish : Prims.unit  ->  Prims.unit = (fun _80_254 -> (match (()) with
| () -> begin
(
# 273 "FStar.SMTEncoding.Z3.fst"
let bg = (bg_z3_proc.grab ())
in (
# 274 "FStar.SMTEncoding.Z3.fst"
let _80_256 = (FStar_Util.kill_process bg)
in (
# 275 "FStar.SMTEncoding.Z3.fst"
let _80_258 = (bg_z3_proc.release ())
in (
# 276 "FStar.SMTEncoding.Z3.fst"
let rec aux = (fun _80_261 -> (match (()) with
| () -> begin
(
# 277 "FStar.SMTEncoding.Z3.fst"
let _80_265 = (with_monitor job_queue (fun _80_262 -> (match (()) with
| () -> begin
(let _169_196 = (FStar_ST.read pending_jobs)
in (let _169_195 = (let _169_194 = (FStar_ST.read job_queue)
in (FStar_List.length _169_194))
in (_169_196, _169_195)))
end)))
in (match (_80_265) with
| (n, m) -> begin
if ((n + m) = 0) then begin
(let _169_197 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _169_197 Prims.ignore))
end else begin
(
# 281 "FStar.SMTEncoding.Z3.fst"
let _80_266 = (FStar_Util.sleep 500)
in (aux ()))
end
end))
end))
in (aux ())))))
end))

# 283 "FStar.SMTEncoding.Z3.fst"
type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list

# 285 "FStar.SMTEncoding.Z3.fst"
let fresh_scope : FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))

# 286 "FStar.SMTEncoding.Z3.fst"
let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 287 "FStar.SMTEncoding.Z3.fst"
let push : Prims.string  ->  Prims.unit = (fun msg -> (
# 289 "FStar.SMTEncoding.Z3.fst"
let _80_269 = (let _169_201 = (let _169_200 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::[])::_169_200)
in (FStar_ST.op_Colon_Equals fresh_scope _169_201))
in (let _169_203 = (let _169_202 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[]) _169_202))
in (FStar_ST.op_Colon_Equals bg_scope _169_203))))

# 290 "FStar.SMTEncoding.Z3.fst"
let pop : Prims.string  ->  Prims.unit = (fun msg -> (
# 292 "FStar.SMTEncoding.Z3.fst"
let _80_272 = (let _169_207 = (let _169_206 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _169_206))
in (FStar_ST.op_Colon_Equals fresh_scope _169_207))
in (let _169_209 = (let _169_208 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[]) _169_208))
in (FStar_ST.op_Colon_Equals bg_scope _169_209))))

# 293 "FStar.SMTEncoding.Z3.fst"
let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (
# 295 "FStar.SMTEncoding.Z3.fst"
let _80_280 = (match ((FStar_ST.read fresh_scope)) with
| hd::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _80_279 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _169_213 = (let _169_212 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _169_212))
in (FStar_ST.op_Colon_Equals bg_scope _169_213))))

# 298 "FStar.SMTEncoding.Z3.fst"
let bgtheory : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun fresh -> if fresh then begin
(let _169_217 = (let _169_216 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _169_216))
in (FStar_All.pipe_right _169_217 FStar_List.flatten))
end else begin
(
# 302 "FStar.SMTEncoding.Z3.fst"
let bg = (FStar_ST.read bg_scope)
in (
# 303 "FStar.SMTEncoding.Z3.fst"
let _80_284 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)

# 304 "FStar.SMTEncoding.Z3.fst"
let refresh : Prims.unit  ->  Prims.unit = (fun _80_286 -> (match (()) with
| () -> begin
(
# 306 "FStar.SMTEncoding.Z3.fst"
let _80_287 = (bg_z3_proc.refresh ())
in (
# 307 "FStar.SMTEncoding.Z3.fst"
let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))

# 308 "FStar.SMTEncoding.Z3.fst"
let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))

# 310 "FStar.SMTEncoding.Z3.fst"
let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 312 "FStar.SMTEncoding.Z3.fst"
let _80_292 = (pop msg)
in (refresh ())))

# 313 "FStar.SMTEncoding.Z3.fst"
let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| hd::s::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _80_301 -> begin
(FStar_All.failwith "Impossible")
end))

# 318 "FStar.SMTEncoding.Z3.fst"
let ask : Prims.bool  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  ((Prims.bool * FStar_SMTEncoding_Term.error_labels)  ->  Prims.unit)  ->  Prims.unit = (fun fresh label_messages qry cb -> (
# 320 "FStar.SMTEncoding.Z3.fst"
let fresh = (fresh && ((FStar_ST.read FStar_Options.n_cores) > 1))
in (
# 321 "FStar.SMTEncoding.Z3.fst"
let theory = (bgtheory fresh)
in (
# 322 "FStar.SMTEncoding.Z3.fst"
let theory = if fresh then begin
(FStar_List.append theory qry)
end else begin
(FStar_List.append (FStar_List.append (FStar_List.append theory ((FStar_SMTEncoding_Term.Push)::[])) qry) ((FStar_SMTEncoding_Term.Pop)::[]))
end
in (
# 326 "FStar.SMTEncoding.Z3.fst"
let input = (let _169_240 = (let _169_239 = (let _169_238 = (z3_options ())
in (FStar_SMTEncoding_Term.declToSmt _169_238))
in (FStar_List.map _169_239 theory))
in (FStar_All.pipe_right _169_240 (FStar_String.concat "\n")))
in (
# 327 "FStar.SMTEncoding.Z3.fst"
let _80_310 = if (FStar_ST.read FStar_Options.logQueries) then begin
(log_query fresh input)
end else begin
()
end
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb})))))))




