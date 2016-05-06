
open Prims
# 27 "FStar.SMTEncoding.Z3.fst"
type fuel_trace_identity =
{module_digest : Prims.string; transitive_digest : Prims.string Prims.option}

# 27 "FStar.SMTEncoding.Z3.fst"
let is_Mkfuel_trace_identity : fuel_trace_identity  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkfuel_trace_identity"))))

# 33 "FStar.SMTEncoding.Z3.fst"
type fuel_trace_state =
{identity : fuel_trace_identity; fuels : (Prims.int * Prims.int) Prims.list}

# 33 "FStar.SMTEncoding.Z3.fst"
let is_Mkfuel_trace_state : fuel_trace_state  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkfuel_trace_state"))))

# 39 "FStar.SMTEncoding.Z3.fst"
type fuel_trace_status =
| FuelTraceUnavailable
| RecordFuelTrace of (Prims.int * Prims.int) Prims.list
| ReplayFuelTrace of (Prims.string * (Prims.int * Prims.int) Prims.list)

# 40 "FStar.SMTEncoding.Z3.fst"
let is_FuelTraceUnavailable = (fun _discr_ -> (match (_discr_) with
| FuelTraceUnavailable (_) -> begin
true
end
| _ -> begin
false
end))

# 41 "FStar.SMTEncoding.Z3.fst"
let is_RecordFuelTrace = (fun _discr_ -> (match (_discr_) with
| RecordFuelTrace (_) -> begin
true
end
| _ -> begin
false
end))

# 42 "FStar.SMTEncoding.Z3.fst"
let is_ReplayFuelTrace = (fun _discr_ -> (match (_discr_) with
| ReplayFuelTrace (_) -> begin
true
end
| _ -> begin
false
end))

# 41 "FStar.SMTEncoding.Z3.fst"
let ___RecordFuelTrace____0 = (fun projectee -> (match (projectee) with
| RecordFuelTrace (_80_10) -> begin
_80_10
end))

# 42 "FStar.SMTEncoding.Z3.fst"
let ___ReplayFuelTrace____0 = (fun projectee -> (match (projectee) with
| ReplayFuelTrace (_80_13) -> begin
_80_13
end))

# 44 "FStar.SMTEncoding.Z3.fst"
let fuel_trace : fuel_trace_status FStar_ST.ref = (FStar_All.pipe_left FStar_Util.mk_ref FuelTraceUnavailable)

# 46 "FStar.SMTEncoding.Z3.fst"
let format_fuel_trace_file_name : Prims.string  ->  Prims.string = (fun src_fn -> (let _169_46 = (FStar_Util.format1 "%s.fuel" src_fn)
in (FStar_All.pipe_left FStar_Util.format_value_file_name _169_46)))

# 49 "FStar.SMTEncoding.Z3.fst"
let compute_transitive_digest : Prims.string  ->  Prims.string Prims.list  ->  Prims.string = (fun src_fn deps -> (
# 51 "FStar.SMTEncoding.Z3.fst"
let digests = (let _169_51 = (FStar_All.pipe_left (FStar_List.map FStar_Util.digest_of_file) ((src_fn)::[]))
in (FStar_List.append _169_51 deps))
in (
# 52 "FStar.SMTEncoding.Z3.fst"
let s = (let _169_52 = (FStar_List.sortWith FStar_String.compare digests)
in (FStar_All.pipe_left (FStar_Util.concat_l ",") _169_52))
in (FStar_Util.digest_of_string s))))

# 55 "FStar.SMTEncoding.Z3.fst"
let is_replaying_fuel_trace : Prims.unit  ->  Prims.bool = (fun _80_19 -> (match (()) with
| () -> begin
(match ((FStar_ST.read fuel_trace)) with
| ReplayFuelTrace (_80_21) -> begin
true
end
| _80_24 -> begin
false
end)
end))

# 62 "FStar.SMTEncoding.Z3.fst"
exception BadFuelCache of (Prims.unit)

# 62 "FStar.SMTEncoding.Z3.fst"
let is_BadFuelCache = (fun _discr_ -> (match (_discr_) with
| BadFuelCache (_) -> begin
true
end
| _ -> begin
false
end))

# 62 "FStar.SMTEncoding.Z3.fst"
let ___BadFuelCache____0 = (fun projectee -> ())

# 67 "FStar.SMTEncoding.Z3.fst"
type z3version =
| Z3V_Unknown
| Z3V of (Prims.int * Prims.int * Prims.int)

# 68 "FStar.SMTEncoding.Z3.fst"
let is_Z3V_Unknown = (fun _discr_ -> (match (_discr_) with
| Z3V_Unknown (_) -> begin
true
end
| _ -> begin
false
end))

# 69 "FStar.SMTEncoding.Z3.fst"
let is_Z3V = (fun _discr_ -> (match (_discr_) with
| Z3V (_) -> begin
true
end
| _ -> begin
false
end))

# 69 "FStar.SMTEncoding.Z3.fst"
let ___Z3V____0 = (fun projectee -> (match (projectee) with
| Z3V (_80_29) -> begin
_80_29
end))

# 71 "FStar.SMTEncoding.Z3.fst"
let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _80_34 -> (match (_80_34) with
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

# 80 "FStar.SMTEncoding.Z3.fst"
let z3v_le : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.bool = (fun known wanted -> (match ((z3v_compare known wanted)) with
| None -> begin
false
end
| Some (i) -> begin
(i >= 0)
end))

# 85 "FStar.SMTEncoding.Z3.fst"
let _z3version : z3version Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 87 "FStar.SMTEncoding.Z3.fst"
let get_z3version : Prims.unit  ->  z3version = (fun _80_46 -> (match (()) with
| () -> begin
(
# 88 "FStar.SMTEncoding.Z3.fst"
let prefix = "Z3 version "
in (match ((FStar_ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(
# 93 "FStar.SMTEncoding.Z3.fst"
let _80_56 = (let _169_85 = (FStar_ST.read FStar_Options.z3_exe)
in (FStar_Util.run_proc _169_85 "-version" ""))
in (match (_80_56) with
| (_80_52, out, _80_55) -> begin
(
# 94 "FStar.SMTEncoding.Z3.fst"
let out = (match ((FStar_Util.splitlines out)) with
| x::_80_58 when (FStar_Util.starts_with x prefix) -> begin
(
# 97 "FStar.SMTEncoding.Z3.fst"
let x = (let _169_86 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _169_86))
in (
# 98 "FStar.SMTEncoding.Z3.fst"
let x = try
(match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)
with
| _80_66 -> begin
[]
end
in (match (x) with
| i1::i2::i3::[] -> begin
Z3V ((i1, i2, i3))
end
| _80_75 -> begin
Z3V_Unknown
end)))
end
| _80_77 -> begin
Z3V_Unknown
end)
in (
# 105 "FStar.SMTEncoding.Z3.fst"
let _80_79 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))

# 107 "FStar.SMTEncoding.Z3.fst"
let ini_params : Prims.int Prims.option  ->  Prims.string = (fun opt_timeout -> (
# 108 "FStar.SMTEncoding.Z3.fst"
let timeout = (match (opt_timeout) with
| Some (n) -> begin
(
# 111 "FStar.SMTEncoding.Z3.fst"
let t = if (let _169_91 = (get_z3version ())
in (z3v_le _169_91 (4, 3, 1))) then begin
n
end else begin
(n * 1000)
end
in (let _169_92 = (FStar_Util.string_of_int t)
in (FStar_Util.format1 "-t:%s" _169_92)))
end
| None -> begin
""
end)
in (
# 121 "FStar.SMTEncoding.Z3.fst"
let relevancy = if (let _169_93 = (get_z3version ())
in (z3v_le _169_93 (4, 3, 1))) then begin
"RELEVANCY"
end else begin
"SMT.RELEVANCY"
end
in (FStar_Util.format2 "-smt2 -in %s AUTO_CONFIG=false MODEL=true %s=2" timeout relevancy))))

# 132 "FStar.SMTEncoding.Z3.fst"
type z3status =
| SAT
| UNSAT
| UNKNOWN
| TIMEOUT

# 133 "FStar.SMTEncoding.Z3.fst"
let is_SAT = (fun _discr_ -> (match (_discr_) with
| SAT (_) -> begin
true
end
| _ -> begin
false
end))

# 134 "FStar.SMTEncoding.Z3.fst"
let is_UNSAT = (fun _discr_ -> (match (_discr_) with
| UNSAT (_) -> begin
true
end
| _ -> begin
false
end))

# 135 "FStar.SMTEncoding.Z3.fst"
let is_UNKNOWN = (fun _discr_ -> (match (_discr_) with
| UNKNOWN (_) -> begin
true
end
| _ -> begin
false
end))

# 136 "FStar.SMTEncoding.Z3.fst"
let is_TIMEOUT = (fun _discr_ -> (match (_discr_) with
| TIMEOUT (_) -> begin
true
end
| _ -> begin
false
end))

# 138 "FStar.SMTEncoding.Z3.fst"
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

# 144 "FStar.SMTEncoding.Z3.fst"
let tid : Prims.unit  ->  Prims.string = (fun _80_93 -> (match (()) with
| () -> begin
(let _169_102 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _169_102 FStar_Util.string_of_int))
end))

# 145 "FStar.SMTEncoding.Z3.fst"
let new_z3proc : Prims.string  ->  Prims.int Prims.option  ->  FStar_Util.proc = (fun id timeout -> (
# 146 "FStar.SMTEncoding.Z3.fst"
let cond = (fun pid s -> (
# 147 "FStar.SMTEncoding.Z3.fst"
let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (
# 150 "FStar.SMTEncoding.Z3.fst"
let args = (ini_params timeout)
in (
# 152 "FStar.SMTEncoding.Z3.fst"
let _80_104 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(match (timeout) with
| Some (n) -> begin
(let _169_111 = (FStar_Util.string_of_int n)
in (FStar_All.pipe_left (FStar_Util.print2 "Starting z3 process `%s` with a timeout of %s.\n" id) _169_111))
end
| None -> begin
(FStar_Util.print1 "Starting z3 process `%s` without a timeout.\n" id)
end)
end else begin
()
end
in (let _169_112 = (FStar_ST.read FStar_Options.z3_exe)
in (FStar_Util.start_process id _169_112 args cond))))))

# 162 "FStar.SMTEncoding.Z3.fst"
type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}

# 162 "FStar.SMTEncoding.Z3.fst"
let is_Mkbgproc : bgproc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbgproc"))))

# 169 "FStar.SMTEncoding.Z3.fst"
let queries_dot_smt2 : FStar_Util.file_handle Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 171 "FStar.SMTEncoding.Z3.fst"
let get_qfile : Prims.bool  ->  FStar_Util.file_handle = (
# 172 "FStar.SMTEncoding.Z3.fst"
let ctr = (FStar_Util.mk_ref 0)
in (fun fresh -> if fresh then begin
(
# 175 "FStar.SMTEncoding.Z3.fst"
let _80_112 = (FStar_Util.incr ctr)
in (let _169_145 = (let _169_144 = (let _169_143 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _169_143))
in (FStar_Util.format1 "queries-%s.smt2" _169_144))
in (FStar_Util.open_file_for_writing _169_145)))
end else begin
(match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
(
# 178 "FStar.SMTEncoding.Z3.fst"
let fh = (FStar_Util.open_file_for_writing "queries-bg-0.smt2")
in (
# 178 "FStar.SMTEncoding.Z3.fst"
let _80_116 = (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
in fh))
end
| Some (fh) -> begin
fh
end)
end))

# 181 "FStar.SMTEncoding.Z3.fst"
let log_query : Prims.bool  ->  Prims.string  ->  Prims.unit = (fun fresh i -> (
# 182 "FStar.SMTEncoding.Z3.fst"
let fh = (get_qfile fresh)
in (
# 183 "FStar.SMTEncoding.Z3.fst"
let _80_123 = (FStar_Util.append_to_file fh i)
in if fresh then begin
(FStar_Util.close_file fh)
end else begin
()
end)))

# 186 "FStar.SMTEncoding.Z3.fst"
let the_z3proc : FStar_Util.proc Prims.option FStar_ST.ref = (FStar_ST.alloc None)

# 189 "FStar.SMTEncoding.Z3.fst"
let ctr : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (- (1)))

# 191 "FStar.SMTEncoding.Z3.fst"
let new_proc : Prims.unit  ->  FStar_Util.proc = (fun _80_125 -> (match (()) with
| () -> begin
(
# 192 "FStar.SMTEncoding.Z3.fst"
let timeout = if (is_replaying_fuel_trace ()) then begin
None
end else begin
(let _169_152 = (FStar_ST.read FStar_Options.z3timeout)
in Some (_169_152))
end
in (let _169_155 = (let _169_154 = (
# 198 "FStar.SMTEncoding.Z3.fst"
let _80_127 = (FStar_Util.incr ctr)
in (let _169_153 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _169_153 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _169_154))
in (new_z3proc _169_155 timeout)))
end))

# 200 "FStar.SMTEncoding.Z3.fst"
let z3proc : Prims.unit  ->  FStar_Util.proc = (fun _80_129 -> (match (()) with
| () -> begin
(
# 201 "FStar.SMTEncoding.Z3.fst"
let _80_130 = if ((FStar_ST.read the_z3proc) = None) then begin
(let _169_159 = (let _169_158 = (new_proc ())
in Some (_169_158))
in (FStar_ST.op_Colon_Equals the_z3proc _169_159))
end else begin
()
end
in (let _169_160 = (FStar_ST.read the_z3proc)
in (FStar_Util.must _169_160)))
end))

# 205 "FStar.SMTEncoding.Z3.fst"
let bg_z3_proc : bgproc = (
# 206 "FStar.SMTEncoding.Z3.fst"
let x = []
in (
# 207 "FStar.SMTEncoding.Z3.fst"
let grab = (fun _80_134 -> (match (()) with
| () -> begin
(
# 207 "FStar.SMTEncoding.Z3.fst"
let _80_135 = (FStar_Util.monitor_enter x)
in (z3proc ()))
end))
in (
# 208 "FStar.SMTEncoding.Z3.fst"
let release = (fun _80_138 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (
# 209 "FStar.SMTEncoding.Z3.fst"
let refresh = (fun _80_140 -> (match (()) with
| () -> begin
(
# 210 "FStar.SMTEncoding.Z3.fst"
let proc = (grab ())
in (
# 211 "FStar.SMTEncoding.Z3.fst"
let _80_142 = (FStar_Util.kill_process proc)
in (
# 212 "FStar.SMTEncoding.Z3.fst"
let _80_144 = (let _169_168 = (let _169_167 = (new_proc ())
in Some (_169_167))
in (FStar_ST.op_Colon_Equals the_z3proc _169_168))
in (
# 213 "FStar.SMTEncoding.Z3.fst"
let _80_152 = (match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
()
end
| Some (fh) -> begin
(
# 216 "FStar.SMTEncoding.Z3.fst"
let _80_149 = (FStar_Util.close_file fh)
in (
# 217 "FStar.SMTEncoding.Z3.fst"
let fh = (let _169_171 = (let _169_170 = (let _169_169 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _169_169 FStar_Util.string_of_int))
in (FStar_Util.format1 "queries-bg-%s.smt2" _169_170))
in (FStar_Util.open_file_for_writing _169_171))
in (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))))
end)
in (release ())))))
end))
in {grab = grab; release = release; refresh = refresh}))))

# 225 "FStar.SMTEncoding.Z3.fst"
let doZ3Exe' : Prims.string  ->  FStar_Util.proc  ->  (z3status * Prims.string Prims.list) = (fun input z3proc -> (
# 226 "FStar.SMTEncoding.Z3.fst"
let parse = (fun z3out -> (
# 227 "FStar.SMTEncoding.Z3.fst"
let lines = (FStar_All.pipe_right (FStar_String.split (('\n')::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (
# 228 "FStar.SMTEncoding.Z3.fst"
let rec lblnegs = (fun lines -> (match (lines) with
| lname::"false"::rest -> begin
(let _169_180 = (lblnegs rest)
in (lname)::_169_180)
end
| lname::_80_168::rest -> begin
(lblnegs rest)
end
| _80_173 -> begin
[]
end))
in (
# 232 "FStar.SMTEncoding.Z3.fst"
let rec result = (fun x -> (match (x) with
| "timeout"::tl -> begin
(TIMEOUT, [])
end
| "unknown"::tl -> begin
(let _169_183 = (lblnegs tl)
in (UNKNOWN, _169_183))
end
| "sat"::tl -> begin
(let _169_184 = (lblnegs tl)
in (SAT, _169_184))
end
| "unsat"::tl -> begin
(UNSAT, [])
end
| _80_190::tl -> begin
(result tl)
end
| _80_193 -> begin
(let _169_188 = (let _169_187 = (let _169_186 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _169_186))
in (FStar_Util.format1 "Got output lines: %s\n" _169_187))
in (FStar_All.pipe_left FStar_All.failwith _169_188))
end))
in (result lines)))))
in (
# 240 "FStar.SMTEncoding.Z3.fst"
let stdout = (FStar_Util.ask_process z3proc input)
in (parse (FStar_Util.trim_string stdout)))))

# 243 "FStar.SMTEncoding.Z3.fst"
let doZ3Exe : Prims.bool  ->  Prims.string  ->  (z3status * Prims.string Prims.list) = (
# 244 "FStar.SMTEncoding.Z3.fst"
let ctr = (FStar_Util.mk_ref 0)
in (fun fresh input -> (
# 246 "FStar.SMTEncoding.Z3.fst"
let z3proc = if fresh then begin
(
# 246 "FStar.SMTEncoding.Z3.fst"
let _80_199 = (FStar_Util.incr ctr)
in (let _169_196 = (let _169_193 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _169_193))
in (let _169_195 = (let _169_194 = (FStar_ST.read FStar_Options.z3timeout)
in Some (_169_194))
in (new_z3proc _169_196 _169_195))))
end else begin
(bg_z3_proc.grab ())
end
in (
# 247 "FStar.SMTEncoding.Z3.fst"
let res = (doZ3Exe' input z3proc)
in (
# 249 "FStar.SMTEncoding.Z3.fst"
let _80_203 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))

# 252 "FStar.SMTEncoding.Z3.fst"
let z3_options : Prims.unit  ->  Prims.string = (fun _80_205 -> (match (()) with
| () -> begin
(
# 253 "FStar.SMTEncoding.Z3.fst"
let mbqi = if (let _169_199 = (get_z3version ())
in (z3v_le _169_199 (4, 3, 1))) then begin
"mbqi"
end else begin
"smt.mbqi"
end
in (
# 257 "FStar.SMTEncoding.Z3.fst"
let model_on_timeout = if (let _169_200 = (get_z3version ())
in (z3v_le _169_200 (4, 3, 1))) then begin
"(set-option :model-on-timeout true)\n"
end else begin
""
end
in (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "(set-option :global-decls false)\n" "(set-option :") mbqi) " false)\n") model_on_timeout)))
end))

# 265 "FStar.SMTEncoding.Z3.fst"
type 'a job =
{job : Prims.unit  ->  'a; callback : 'a  ->  Prims.unit}

# 265 "FStar.SMTEncoding.Z3.fst"
let is_Mkjob = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkjob"))))

# 269 "FStar.SMTEncoding.Z3.fst"
type z3job =
(Prims.bool * FStar_SMTEncoding_Term.error_label Prims.list) job

# 271 "FStar.SMTEncoding.Z3.fst"
let job_queue : z3job Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 275 "FStar.SMTEncoding.Z3.fst"
let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 0)

# 276 "FStar.SMTEncoding.Z3.fst"
let with_monitor = (fun m f -> (
# 277 "FStar.SMTEncoding.Z3.fst"
let _80_214 = (FStar_Util.monitor_enter m)
in (
# 278 "FStar.SMTEncoding.Z3.fst"
let res = (f ())
in (
# 279 "FStar.SMTEncoding.Z3.fst"
let _80_217 = (FStar_Util.monitor_exit m)
in res))))

# 282 "FStar.SMTEncoding.Z3.fst"
let z3_job = (fun fresh label_messages input _80_222 -> (match (()) with
| () -> begin
(
# 283 "FStar.SMTEncoding.Z3.fst"
let _80_225 = (doZ3Exe fresh input)
in (match (_80_225) with
| (status, lblnegs) -> begin
(
# 284 "FStar.SMTEncoding.Z3.fst"
let result = (match (status) with
| UNSAT -> begin
(true, [])
end
| _80_228 -> begin
(
# 287 "FStar.SMTEncoding.Z3.fst"
let _80_229 = if ((FStar_ST.read FStar_Options.debug) <> []) then begin
(let _169_230 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _169_230))
end else begin
()
end
in (
# 288 "FStar.SMTEncoding.Z3.fst"
let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _80_237 -> (match (_80_237) with
| (m, _80_234, _80_236) -> begin
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

# 295 "FStar.SMTEncoding.Z3.fst"
let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _80_246 -> (match (()) with
| () -> begin
(
# 296 "FStar.SMTEncoding.Z3.fst"
let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| hd::tl -> begin
(
# 299 "FStar.SMTEncoding.Z3.fst"
let _80_251 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (
# 301 "FStar.SMTEncoding.Z3.fst"
let _80_254 = (FStar_Util.incr pending_jobs)
in (
# 302 "FStar.SMTEncoding.Z3.fst"
let _80_256 = (FStar_Util.monitor_exit job_queue)
in (
# 303 "FStar.SMTEncoding.Z3.fst"
let _80_258 = (run_job j)
in (
# 304 "FStar.SMTEncoding.Z3.fst"
let _80_261 = (with_monitor job_queue (fun _80_260 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (
# 305 "FStar.SMTEncoding.Z3.fst"
let _80_263 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _80_265 -> (match (()) with
| () -> begin
(
# 308 "FStar.SMTEncoding.Z3.fst"
let _80_266 = (FStar_Util.monitor_enter job_queue)
in (
# 309 "FStar.SMTEncoding.Z3.fst"
let rec aux = (fun _80_269 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(
# 311 "FStar.SMTEncoding.Z3.fst"
let _80_271 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _80_274 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _169_242 = (j.job ())
in (FStar_All.pipe_left j.callback _169_242)))

# 318 "FStar.SMTEncoding.Z3.fst"
let init : Prims.unit  ->  Prims.unit = (fun _80_276 -> (match (()) with
| () -> begin
(
# 319 "FStar.SMTEncoding.Z3.fst"
let n_runners = ((FStar_ST.read FStar_Options.n_cores) - 1)
in (
# 320 "FStar.SMTEncoding.Z3.fst"
let rec aux = (fun n -> if (n = 0) then begin
()
end else begin
(
# 322 "FStar.SMTEncoding.Z3.fst"
let _80_280 = (FStar_Util.spawn dequeue)
in (aux (n - 1)))
end)
in (aux n_runners)))
end))

# 325 "FStar.SMTEncoding.Z3.fst"
let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(
# 330 "FStar.SMTEncoding.Z3.fst"
let _80_284 = (FStar_Util.monitor_enter job_queue)
in (
# 331 "FStar.SMTEncoding.Z3.fst"
let _80_286 = (let _169_252 = (let _169_251 = (FStar_ST.read job_queue)
in (FStar_List.append _169_251 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _169_252))
in (
# 332 "FStar.SMTEncoding.Z3.fst"
let _80_288 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)

# 336 "FStar.SMTEncoding.Z3.fst"
let finish : Prims.unit  ->  Prims.unit = (fun _80_290 -> (match (()) with
| () -> begin
(
# 337 "FStar.SMTEncoding.Z3.fst"
let bg = (bg_z3_proc.grab ())
in (
# 338 "FStar.SMTEncoding.Z3.fst"
let _80_292 = (FStar_Util.kill_process bg)
in (
# 339 "FStar.SMTEncoding.Z3.fst"
let _80_294 = (bg_z3_proc.release ())
in (
# 340 "FStar.SMTEncoding.Z3.fst"
let rec aux = (fun _80_297 -> (match (()) with
| () -> begin
(
# 341 "FStar.SMTEncoding.Z3.fst"
let _80_301 = (with_monitor job_queue (fun _80_298 -> (match (()) with
| () -> begin
(let _169_260 = (FStar_ST.read pending_jobs)
in (let _169_259 = (let _169_258 = (FStar_ST.read job_queue)
in (FStar_List.length _169_258))
in (_169_260, _169_259)))
end)))
in (match (_80_301) with
| (n, m) -> begin
if ((n + m) = 0) then begin
(let _169_261 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _169_261 Prims.ignore))
end else begin
(
# 345 "FStar.SMTEncoding.Z3.fst"
let _80_302 = (FStar_Util.sleep 500)
in (aux ()))
end
end))
end))
in (aux ())))))
end))

# 349 "FStar.SMTEncoding.Z3.fst"
type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list

# 350 "FStar.SMTEncoding.Z3.fst"
let fresh_scope : FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))

# 351 "FStar.SMTEncoding.Z3.fst"
let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 352 "FStar.SMTEncoding.Z3.fst"
let push : Prims.string  ->  Prims.unit = (fun msg -> (
# 353 "FStar.SMTEncoding.Z3.fst"
let _80_305 = (let _169_265 = (let _169_264 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::[])::_169_264)
in (FStar_ST.op_Colon_Equals fresh_scope _169_265))
in (let _169_267 = (let _169_266 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[]) _169_266))
in (FStar_ST.op_Colon_Equals bg_scope _169_267))))

# 355 "FStar.SMTEncoding.Z3.fst"
let pop : Prims.string  ->  Prims.unit = (fun msg -> (
# 356 "FStar.SMTEncoding.Z3.fst"
let _80_308 = (let _169_271 = (let _169_270 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _169_270))
in (FStar_ST.op_Colon_Equals fresh_scope _169_271))
in (let _169_273 = (let _169_272 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[]) _169_272))
in (FStar_ST.op_Colon_Equals bg_scope _169_273))))

# 358 "FStar.SMTEncoding.Z3.fst"
let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (
# 359 "FStar.SMTEncoding.Z3.fst"
let _80_316 = (match ((FStar_ST.read fresh_scope)) with
| hd::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _80_315 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _169_277 = (let _169_276 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _169_276))
in (FStar_ST.op_Colon_Equals bg_scope _169_277))))

# 363 "FStar.SMTEncoding.Z3.fst"
let bgtheory : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun fresh -> if fresh then begin
(let _169_281 = (let _169_280 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _169_280))
in (FStar_All.pipe_right _169_281 FStar_List.flatten))
end else begin
(
# 366 "FStar.SMTEncoding.Z3.fst"
let bg = (FStar_ST.read bg_scope)
in (
# 367 "FStar.SMTEncoding.Z3.fst"
let _80_320 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)

# 369 "FStar.SMTEncoding.Z3.fst"
let refresh : Prims.unit  ->  Prims.unit = (fun _80_322 -> (match (()) with
| () -> begin
(
# 370 "FStar.SMTEncoding.Z3.fst"
let _80_323 = (bg_z3_proc.refresh ())
in (
# 371 "FStar.SMTEncoding.Z3.fst"
let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))

# 373 "FStar.SMTEncoding.Z3.fst"
let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))

# 375 "FStar.SMTEncoding.Z3.fst"
let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 376 "FStar.SMTEncoding.Z3.fst"
let _80_328 = (pop msg)
in (refresh ())))

# 378 "FStar.SMTEncoding.Z3.fst"
let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| hd::s::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _80_337 -> begin
(FStar_All.failwith "Impossible")
end))

# 383 "FStar.SMTEncoding.Z3.fst"
let ask : Prims.bool  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  ((Prims.bool * FStar_SMTEncoding_Term.error_labels)  ->  Prims.unit)  ->  Prims.unit = (fun fresh label_messages qry cb -> (
# 384 "FStar.SMTEncoding.Z3.fst"
let fresh = (fresh && ((FStar_ST.read FStar_Options.n_cores) > 1))
in (
# 385 "FStar.SMTEncoding.Z3.fst"
let theory = (bgtheory fresh)
in (
# 386 "FStar.SMTEncoding.Z3.fst"
let theory = if fresh then begin
(FStar_List.append theory qry)
end else begin
(FStar_List.append (FStar_List.append (FStar_List.append theory ((FStar_SMTEncoding_Term.Push)::[])) qry) ((FStar_SMTEncoding_Term.Pop)::[]))
end
in (
# 390 "FStar.SMTEncoding.Z3.fst"
let input = (let _169_304 = (let _169_303 = (let _169_302 = (z3_options ())
in (FStar_SMTEncoding_Term.declToSmt _169_302))
in (FStar_List.map _169_303 theory))
in (FStar_All.pipe_right _169_304 (FStar_String.concat "\n")))
in (
# 391 "FStar.SMTEncoding.Z3.fst"
let _80_346 = if (FStar_ST.read FStar_Options.logQueries) then begin
(log_query fresh input)
end else begin
()
end
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb})))))))

# 398 "FStar.SMTEncoding.Z3.fst"
let initialize_fuel_trace : Prims.string  ->  Prims.string Prims.list  ->  Prims.bool  ->  Prims.unit = (fun src_fn deps force_invalid_cache -> (
# 399 "FStar.SMTEncoding.Z3.fst"
let _80_370 = if force_invalid_cache then begin
(FStar_ST.op_Colon_Equals fuel_trace (RecordFuelTrace ([])))
end else begin
(
# 402 "FStar.SMTEncoding.Z3.fst"
let norm_src_fn = (FStar_Util.normalize_file_path src_fn)
in (
# 403 "FStar.SMTEncoding.Z3.fst"
let val_fn = (format_fuel_trace_file_name norm_src_fn)
in (match ((FStar_Util.load_value_from_file val_fn)) with
| Some (state) -> begin
(
# 406 "FStar.SMTEncoding.Z3.fst"
let _80_362 = if (FStar_ST.read FStar_Options.explicit_deps) then begin
(
# 409 "FStar.SMTEncoding.Z3.fst"
let expected = (FStar_Util.digest_of_file norm_src_fn)
in ("Module", (state.identity.module_digest = expected)))
end else begin
(let _169_311 = (match (state.identity.transitive_digest) with
| None -> begin
false
end
| Some (d) -> begin
(
# 418 "FStar.SMTEncoding.Z3.fst"
let expected = (compute_transitive_digest norm_src_fn deps)
in (d = expected))
end)
in ("Transitive", _169_311))
end
in (match (_80_362) with
| (means, validated) -> begin
if validated then begin
(
# 423 "FStar.SMTEncoding.Z3.fst"
let _80_363 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(FStar_Util.print2 "(%s) %s digest is valid.\n" norm_src_fn means)
end else begin
()
end
in (FStar_ST.op_Colon_Equals fuel_trace (ReplayFuelTrace ((val_fn, state.fuels)))))
end else begin
(
# 430 "FStar.SMTEncoding.Z3.fst"
let _80_365 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(FStar_Util.print2 "(%s) %s digest is invalid.\n" norm_src_fn means)
end else begin
()
end
in (FStar_ST.op_Colon_Equals fuel_trace (RecordFuelTrace ([]))))
end
end))
end
| None -> begin
(
# 437 "FStar.SMTEncoding.Z3.fst"
let _80_368 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(FStar_Util.print1 "(%s) Unable to read cached fuel trace.\n" norm_src_fn)
end else begin
()
end
in (FStar_ST.op_Colon_Equals fuel_trace (RecordFuelTrace ([]))))
end)))
end
in (refresh ())))

# 446 "FStar.SMTEncoding.Z3.fst"
let finalize_fuel_trace : Prims.string  ->  Prims.string Prims.list  ->  Prims.unit = (fun src_fn deps -> (
# 447 "FStar.SMTEncoding.Z3.fst"
let _80_385 = (match ((FStar_ST.read fuel_trace)) with
| (ReplayFuelTrace (_)) | (FuelTraceUnavailable) | (RecordFuelTrace ([])) -> begin
()
end
| RecordFuelTrace (l) -> begin
(
# 456 "FStar.SMTEncoding.Z3.fst"
let val_fn = (format_fuel_trace_file_name src_fn)
in (
# 457 "FStar.SMTEncoding.Z3.fst"
let xd = if (FStar_ST.read FStar_Options.explicit_deps) then begin
None
end else begin
(let _169_317 = (compute_transitive_digest src_fn deps)
in (FStar_All.pipe_left (fun _169_316 -> Some (_169_316)) _169_317))
end
in (
# 464 "FStar.SMTEncoding.Z3.fst"
let state = (let _169_319 = (let _169_318 = (FStar_Util.digest_of_file src_fn)
in {module_digest = _169_318; transitive_digest = xd})
in {identity = _169_319; fuels = l})
in (FStar_Util.save_value_to_file val_fn state))))
end)
in (FStar_ST.op_Colon_Equals fuel_trace FuelTraceUnavailable)))




