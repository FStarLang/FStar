
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

# 65 "FStar.SMTEncoding.Z3.fst"
type z3version =
| Z3V_Unknown
| Z3V of (Prims.int * Prims.int * Prims.int)

# 66 "FStar.SMTEncoding.Z3.fst"
let is_Z3V_Unknown = (fun _discr_ -> (match (_discr_) with
| Z3V_Unknown (_) -> begin
true
end
| _ -> begin
false
end))

# 67 "FStar.SMTEncoding.Z3.fst"
let is_Z3V = (fun _discr_ -> (match (_discr_) with
| Z3V (_) -> begin
true
end
| _ -> begin
false
end))

# 67 "FStar.SMTEncoding.Z3.fst"
let ___Z3V____0 = (fun projectee -> (match (projectee) with
| Z3V (_80_27) -> begin
_80_27
end))

# 69 "FStar.SMTEncoding.Z3.fst"
let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _80_32 -> (match (_80_32) with
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

# 78 "FStar.SMTEncoding.Z3.fst"
let z3v_le : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.bool = (fun known wanted -> (match ((z3v_compare known wanted)) with
| None -> begin
false
end
| Some (i) -> begin
(i >= 0)
end))

# 83 "FStar.SMTEncoding.Z3.fst"
let _z3version : z3version Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 85 "FStar.SMTEncoding.Z3.fst"
let get_z3version : Prims.unit  ->  z3version = (fun _80_44 -> (match (()) with
| () -> begin
(
# 86 "FStar.SMTEncoding.Z3.fst"
let prefix = "Z3 version "
in (match ((FStar_ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(
# 91 "FStar.SMTEncoding.Z3.fst"
let _80_54 = (let _169_80 = (FStar_ST.read FStar_Options.z3_exe)
in (FStar_Util.run_proc _169_80 "-version" ""))
in (match (_80_54) with
| (_80_50, out, _80_53) -> begin
(
# 92 "FStar.SMTEncoding.Z3.fst"
let out = (match ((FStar_Util.splitlines out)) with
| x::_80_56 when (FStar_Util.starts_with x prefix) -> begin
(
# 95 "FStar.SMTEncoding.Z3.fst"
let x = (let _169_81 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _169_81))
in (
# 96 "FStar.SMTEncoding.Z3.fst"
let x = try
(match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)
with
| _80_64 -> begin
[]
end
in (match (x) with
| i1::i2::i3::[] -> begin
Z3V ((i1, i2, i3))
end
| _80_73 -> begin
Z3V_Unknown
end)))
end
| _80_75 -> begin
Z3V_Unknown
end)
in (
# 103 "FStar.SMTEncoding.Z3.fst"
let _80_77 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))

# 105 "FStar.SMTEncoding.Z3.fst"
let ini_params : Prims.int Prims.option  ->  Prims.string = (fun opt_timeout -> (
# 106 "FStar.SMTEncoding.Z3.fst"
let timeout = (match (opt_timeout) with
| Some (n) -> begin
(
# 109 "FStar.SMTEncoding.Z3.fst"
let t = if (let _169_86 = (get_z3version ())
in (z3v_le _169_86 (4, 3, 1))) then begin
n
end else begin
(n * 1000)
end
in (let _169_87 = (FStar_Util.string_of_int t)
in (FStar_Util.format1 "-t:%s" _169_87)))
end
| None -> begin
""
end)
in (
# 119 "FStar.SMTEncoding.Z3.fst"
let relevancy = if (let _169_88 = (get_z3version ())
in (z3v_le _169_88 (4, 3, 1))) then begin
"RELEVANCY"
end else begin
"SMT.RELEVANCY"
end
in (FStar_Util.format2 "-smt2 -in %s AUTO_CONFIG=false MODEL=true %s=2" timeout relevancy))))

# 130 "FStar.SMTEncoding.Z3.fst"
type z3status =
| SAT
| UNSAT
| UNKNOWN
| TIMEOUT

# 131 "FStar.SMTEncoding.Z3.fst"
let is_SAT = (fun _discr_ -> (match (_discr_) with
| SAT (_) -> begin
true
end
| _ -> begin
false
end))

# 132 "FStar.SMTEncoding.Z3.fst"
let is_UNSAT = (fun _discr_ -> (match (_discr_) with
| UNSAT (_) -> begin
true
end
| _ -> begin
false
end))

# 133 "FStar.SMTEncoding.Z3.fst"
let is_UNKNOWN = (fun _discr_ -> (match (_discr_) with
| UNKNOWN (_) -> begin
true
end
| _ -> begin
false
end))

# 134 "FStar.SMTEncoding.Z3.fst"
let is_TIMEOUT = (fun _discr_ -> (match (_discr_) with
| TIMEOUT (_) -> begin
true
end
| _ -> begin
false
end))

# 136 "FStar.SMTEncoding.Z3.fst"
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

# 142 "FStar.SMTEncoding.Z3.fst"
let tid : Prims.unit  ->  Prims.string = (fun _80_91 -> (match (()) with
| () -> begin
(let _169_97 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _169_97 FStar_Util.string_of_int))
end))

# 143 "FStar.SMTEncoding.Z3.fst"
let new_z3proc : Prims.string  ->  Prims.int Prims.option  ->  FStar_Util.proc = (fun id timeout -> (
# 144 "FStar.SMTEncoding.Z3.fst"
let cond = (fun pid s -> (
# 145 "FStar.SMTEncoding.Z3.fst"
let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (
# 148 "FStar.SMTEncoding.Z3.fst"
let args = (ini_params timeout)
in (
# 150 "FStar.SMTEncoding.Z3.fst"
let _80_102 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(match (timeout) with
| Some (n) -> begin
(let _169_106 = (FStar_Util.string_of_int n)
in (FStar_All.pipe_left (FStar_Util.print2 "Starting z3 process `%s` with a timeout of %s.\n" id) _169_106))
end
| None -> begin
(FStar_Util.print1 "Starting z3 process `%s` without a timeout.\n" id)
end)
end else begin
()
end
in (let _169_107 = (FStar_ST.read FStar_Options.z3_exe)
in (FStar_Util.start_process id _169_107 args cond))))))

# 160 "FStar.SMTEncoding.Z3.fst"
type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}

# 160 "FStar.SMTEncoding.Z3.fst"
let is_Mkbgproc : bgproc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbgproc"))))

# 167 "FStar.SMTEncoding.Z3.fst"
let queries_dot_smt2 : FStar_Util.file_handle Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 169 "FStar.SMTEncoding.Z3.fst"
let get_qfile : Prims.bool  ->  FStar_Util.file_handle = (
# 170 "FStar.SMTEncoding.Z3.fst"
let ctr = (FStar_Util.mk_ref 0)
in (fun fresh -> if fresh then begin
(
# 173 "FStar.SMTEncoding.Z3.fst"
let _80_110 = (FStar_Util.incr ctr)
in (let _169_140 = (let _169_139 = (let _169_138 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _169_138))
in (FStar_Util.format1 "queries-%s.smt2" _169_139))
in (FStar_Util.open_file_for_writing _169_140)))
end else begin
(match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
(
# 176 "FStar.SMTEncoding.Z3.fst"
let fh = (FStar_Util.open_file_for_writing "queries-bg-0.smt2")
in (
# 176 "FStar.SMTEncoding.Z3.fst"
let _80_114 = (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
in fh))
end
| Some (fh) -> begin
fh
end)
end))

# 179 "FStar.SMTEncoding.Z3.fst"
let log_query : Prims.bool  ->  Prims.string  ->  Prims.unit = (fun fresh i -> (
# 180 "FStar.SMTEncoding.Z3.fst"
let fh = (get_qfile fresh)
in (
# 181 "FStar.SMTEncoding.Z3.fst"
let _80_121 = (FStar_Util.append_to_file fh i)
in if fresh then begin
(FStar_Util.close_file fh)
end else begin
()
end)))

# 184 "FStar.SMTEncoding.Z3.fst"
let the_z3proc : FStar_Util.proc Prims.option FStar_ST.ref = (FStar_ST.alloc None)

# 187 "FStar.SMTEncoding.Z3.fst"
let ctr : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (- (1)))

# 189 "FStar.SMTEncoding.Z3.fst"
let new_proc : Prims.unit  ->  FStar_Util.proc = (fun _80_123 -> (match (()) with
| () -> begin
(
# 190 "FStar.SMTEncoding.Z3.fst"
let timeout = if (is_replaying_fuel_trace ()) then begin
None
end else begin
(let _169_147 = (FStar_ST.read FStar_Options.z3timeout)
in Some (_169_147))
end
in (let _169_150 = (let _169_149 = (
# 196 "FStar.SMTEncoding.Z3.fst"
let _80_125 = (FStar_Util.incr ctr)
in (let _169_148 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _169_148 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _169_149))
in (new_z3proc _169_150 timeout)))
end))

# 198 "FStar.SMTEncoding.Z3.fst"
let z3proc : Prims.unit  ->  FStar_Util.proc = (fun _80_127 -> (match (()) with
| () -> begin
(
# 199 "FStar.SMTEncoding.Z3.fst"
let _80_128 = if ((FStar_ST.read the_z3proc) = None) then begin
(let _169_154 = (let _169_153 = (new_proc ())
in Some (_169_153))
in (FStar_ST.op_Colon_Equals the_z3proc _169_154))
end else begin
()
end
in (let _169_155 = (FStar_ST.read the_z3proc)
in (FStar_Util.must _169_155)))
end))

# 203 "FStar.SMTEncoding.Z3.fst"
let bg_z3_proc : bgproc = (
# 204 "FStar.SMTEncoding.Z3.fst"
let x = []
in (
# 205 "FStar.SMTEncoding.Z3.fst"
let grab = (fun _80_132 -> (match (()) with
| () -> begin
(
# 205 "FStar.SMTEncoding.Z3.fst"
let _80_133 = (FStar_Util.monitor_enter x)
in (z3proc ()))
end))
in (
# 206 "FStar.SMTEncoding.Z3.fst"
let release = (fun _80_136 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (
# 207 "FStar.SMTEncoding.Z3.fst"
let refresh = (fun _80_138 -> (match (()) with
| () -> begin
(
# 208 "FStar.SMTEncoding.Z3.fst"
let proc = (grab ())
in (
# 209 "FStar.SMTEncoding.Z3.fst"
let _80_140 = (FStar_Util.kill_process proc)
in (
# 210 "FStar.SMTEncoding.Z3.fst"
let _80_142 = (let _169_163 = (let _169_162 = (new_proc ())
in Some (_169_162))
in (FStar_ST.op_Colon_Equals the_z3proc _169_163))
in (
# 211 "FStar.SMTEncoding.Z3.fst"
let _80_150 = (match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
()
end
| Some (fh) -> begin
(
# 214 "FStar.SMTEncoding.Z3.fst"
let _80_147 = (FStar_Util.close_file fh)
in (
# 215 "FStar.SMTEncoding.Z3.fst"
let fh = (let _169_166 = (let _169_165 = (let _169_164 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _169_164 FStar_Util.string_of_int))
in (FStar_Util.format1 "queries-bg-%s.smt2" _169_165))
in (FStar_Util.open_file_for_writing _169_166))
in (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))))
end)
in (release ())))))
end))
in {grab = grab; release = release; refresh = refresh}))))

# 223 "FStar.SMTEncoding.Z3.fst"
let doZ3Exe' : Prims.string  ->  FStar_Util.proc  ->  (z3status * Prims.string Prims.list) = (fun input z3proc -> (
# 224 "FStar.SMTEncoding.Z3.fst"
let parse = (fun z3out -> (
# 225 "FStar.SMTEncoding.Z3.fst"
let lines = (FStar_All.pipe_right (FStar_String.split (('\n')::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (
# 226 "FStar.SMTEncoding.Z3.fst"
let rec lblnegs = (fun lines -> (match (lines) with
| lname::"false"::rest -> begin
(let _169_175 = (lblnegs rest)
in (lname)::_169_175)
end
| lname::_80_166::rest -> begin
(lblnegs rest)
end
| _80_171 -> begin
[]
end))
in (
# 230 "FStar.SMTEncoding.Z3.fst"
let rec result = (fun x -> (match (x) with
| "timeout"::tl -> begin
(TIMEOUT, [])
end
| "unknown"::tl -> begin
(let _169_178 = (lblnegs tl)
in (UNKNOWN, _169_178))
end
| "sat"::tl -> begin
(let _169_179 = (lblnegs tl)
in (SAT, _169_179))
end
| "unsat"::tl -> begin
(UNSAT, [])
end
| _80_188::tl -> begin
(result tl)
end
| _80_191 -> begin
(let _169_183 = (let _169_182 = (let _169_181 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _169_181))
in (FStar_Util.format1 "Got output lines: %s\n" _169_182))
in (FStar_All.pipe_left FStar_All.failwith _169_183))
end))
in (result lines)))))
in (
# 238 "FStar.SMTEncoding.Z3.fst"
let stdout = (FStar_Util.ask_process z3proc input)
in (parse (FStar_Util.trim_string stdout)))))

# 241 "FStar.SMTEncoding.Z3.fst"
let doZ3Exe : Prims.bool  ->  Prims.string  ->  (z3status * Prims.string Prims.list) = (
# 242 "FStar.SMTEncoding.Z3.fst"
let ctr = (FStar_Util.mk_ref 0)
in (fun fresh input -> (
# 244 "FStar.SMTEncoding.Z3.fst"
let z3proc = if fresh then begin
(
# 244 "FStar.SMTEncoding.Z3.fst"
let _80_197 = (FStar_Util.incr ctr)
in (let _169_191 = (let _169_188 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _169_188))
in (let _169_190 = (let _169_189 = (FStar_ST.read FStar_Options.z3timeout)
in Some (_169_189))
in (new_z3proc _169_191 _169_190))))
end else begin
(bg_z3_proc.grab ())
end
in (
# 245 "FStar.SMTEncoding.Z3.fst"
let res = (doZ3Exe' input z3proc)
in (
# 247 "FStar.SMTEncoding.Z3.fst"
let _80_201 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))

# 250 "FStar.SMTEncoding.Z3.fst"
let z3_options : Prims.unit  ->  Prims.string = (fun _80_203 -> (match (()) with
| () -> begin
(
# 251 "FStar.SMTEncoding.Z3.fst"
let mbqi = if (let _169_194 = (get_z3version ())
in (z3v_le _169_194 (4, 3, 1))) then begin
"mbqi"
end else begin
"smt.mbqi"
end
in (
# 255 "FStar.SMTEncoding.Z3.fst"
let model_on_timeout = if (let _169_195 = (get_z3version ())
in (z3v_le _169_195 (4, 3, 1))) then begin
"(set-option :model-on-timeout true)\n"
end else begin
""
end
in (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "(set-option :global-decls false)\n" "(set-option :") mbqi) " false)\n") model_on_timeout)))
end))

# 263 "FStar.SMTEncoding.Z3.fst"
type 'a job =
{job : Prims.unit  ->  'a; callback : 'a  ->  Prims.unit}

# 263 "FStar.SMTEncoding.Z3.fst"
let is_Mkjob = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkjob"))))

# 267 "FStar.SMTEncoding.Z3.fst"
type z3job =
(Prims.bool * FStar_SMTEncoding_Term.error_label Prims.list) job

# 269 "FStar.SMTEncoding.Z3.fst"
let job_queue : z3job Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 273 "FStar.SMTEncoding.Z3.fst"
let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 0)

# 274 "FStar.SMTEncoding.Z3.fst"
let with_monitor = (fun m f -> (
# 275 "FStar.SMTEncoding.Z3.fst"
let _80_212 = (FStar_Util.monitor_enter m)
in (
# 276 "FStar.SMTEncoding.Z3.fst"
let res = (f ())
in (
# 277 "FStar.SMTEncoding.Z3.fst"
let _80_215 = (FStar_Util.monitor_exit m)
in res))))

# 280 "FStar.SMTEncoding.Z3.fst"
let z3_job = (fun fresh label_messages input _80_220 -> (match (()) with
| () -> begin
(
# 281 "FStar.SMTEncoding.Z3.fst"
let _80_223 = (doZ3Exe fresh input)
in (match (_80_223) with
| (status, lblnegs) -> begin
(
# 282 "FStar.SMTEncoding.Z3.fst"
let result = (match (status) with
| UNSAT -> begin
(true, [])
end
| _80_226 -> begin
(
# 285 "FStar.SMTEncoding.Z3.fst"
let _80_227 = if ((FStar_ST.read FStar_Options.debug) <> []) then begin
(let _169_225 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _169_225))
end else begin
()
end
in (
# 286 "FStar.SMTEncoding.Z3.fst"
let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _80_235 -> (match (_80_235) with
| (m, _80_232, _80_234) -> begin
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

# 293 "FStar.SMTEncoding.Z3.fst"
let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _80_244 -> (match (()) with
| () -> begin
(
# 294 "FStar.SMTEncoding.Z3.fst"
let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| hd::tl -> begin
(
# 297 "FStar.SMTEncoding.Z3.fst"
let _80_249 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (
# 299 "FStar.SMTEncoding.Z3.fst"
let _80_252 = (FStar_Util.incr pending_jobs)
in (
# 300 "FStar.SMTEncoding.Z3.fst"
let _80_254 = (FStar_Util.monitor_exit job_queue)
in (
# 301 "FStar.SMTEncoding.Z3.fst"
let _80_256 = (run_job j)
in (
# 302 "FStar.SMTEncoding.Z3.fst"
let _80_259 = (with_monitor job_queue (fun _80_258 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (
# 303 "FStar.SMTEncoding.Z3.fst"
let _80_261 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _80_263 -> (match (()) with
| () -> begin
(
# 306 "FStar.SMTEncoding.Z3.fst"
let _80_264 = (FStar_Util.monitor_enter job_queue)
in (
# 307 "FStar.SMTEncoding.Z3.fst"
let rec aux = (fun _80_267 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(
# 309 "FStar.SMTEncoding.Z3.fst"
let _80_269 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _80_272 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _169_237 = (j.job ())
in (FStar_All.pipe_left j.callback _169_237)))

# 316 "FStar.SMTEncoding.Z3.fst"
let init : Prims.unit  ->  Prims.unit = (fun _80_274 -> (match (()) with
| () -> begin
(
# 317 "FStar.SMTEncoding.Z3.fst"
let n_runners = ((FStar_ST.read FStar_Options.n_cores) - 1)
in (
# 318 "FStar.SMTEncoding.Z3.fst"
let rec aux = (fun n -> if (n = 0) then begin
()
end else begin
(
# 320 "FStar.SMTEncoding.Z3.fst"
let _80_278 = (FStar_Util.spawn dequeue)
in (aux (n - 1)))
end)
in (aux n_runners)))
end))

# 323 "FStar.SMTEncoding.Z3.fst"
let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(
# 328 "FStar.SMTEncoding.Z3.fst"
let _80_282 = (FStar_Util.monitor_enter job_queue)
in (
# 329 "FStar.SMTEncoding.Z3.fst"
let _80_284 = (let _169_247 = (let _169_246 = (FStar_ST.read job_queue)
in (FStar_List.append _169_246 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _169_247))
in (
# 330 "FStar.SMTEncoding.Z3.fst"
let _80_286 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)

# 334 "FStar.SMTEncoding.Z3.fst"
let finish : Prims.unit  ->  Prims.unit = (fun _80_288 -> (match (()) with
| () -> begin
(
# 335 "FStar.SMTEncoding.Z3.fst"
let bg = (bg_z3_proc.grab ())
in (
# 336 "FStar.SMTEncoding.Z3.fst"
let _80_290 = (FStar_Util.kill_process bg)
in (
# 337 "FStar.SMTEncoding.Z3.fst"
let _80_292 = (bg_z3_proc.release ())
in (
# 338 "FStar.SMTEncoding.Z3.fst"
let rec aux = (fun _80_295 -> (match (()) with
| () -> begin
(
# 339 "FStar.SMTEncoding.Z3.fst"
let _80_299 = (with_monitor job_queue (fun _80_296 -> (match (()) with
| () -> begin
(let _169_255 = (FStar_ST.read pending_jobs)
in (let _169_254 = (let _169_253 = (FStar_ST.read job_queue)
in (FStar_List.length _169_253))
in (_169_255, _169_254)))
end)))
in (match (_80_299) with
| (n, m) -> begin
if ((n + m) = 0) then begin
(let _169_256 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _169_256 Prims.ignore))
end else begin
(
# 343 "FStar.SMTEncoding.Z3.fst"
let _80_300 = (FStar_Util.sleep 500)
in (aux ()))
end
end))
end))
in (aux ())))))
end))

# 347 "FStar.SMTEncoding.Z3.fst"
type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list

# 348 "FStar.SMTEncoding.Z3.fst"
let fresh_scope : FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))

# 349 "FStar.SMTEncoding.Z3.fst"
let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 350 "FStar.SMTEncoding.Z3.fst"
let push : Prims.string  ->  Prims.unit = (fun msg -> (
# 351 "FStar.SMTEncoding.Z3.fst"
let _80_303 = (let _169_260 = (let _169_259 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::[])::_169_259)
in (FStar_ST.op_Colon_Equals fresh_scope _169_260))
in (let _169_262 = (let _169_261 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[]) _169_261))
in (FStar_ST.op_Colon_Equals bg_scope _169_262))))

# 353 "FStar.SMTEncoding.Z3.fst"
let pop : Prims.string  ->  Prims.unit = (fun msg -> (
# 354 "FStar.SMTEncoding.Z3.fst"
let _80_306 = (let _169_266 = (let _169_265 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _169_265))
in (FStar_ST.op_Colon_Equals fresh_scope _169_266))
in (let _169_268 = (let _169_267 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[]) _169_267))
in (FStar_ST.op_Colon_Equals bg_scope _169_268))))

# 356 "FStar.SMTEncoding.Z3.fst"
let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (
# 357 "FStar.SMTEncoding.Z3.fst"
let _80_314 = (match ((FStar_ST.read fresh_scope)) with
| hd::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _80_313 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _169_272 = (let _169_271 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _169_271))
in (FStar_ST.op_Colon_Equals bg_scope _169_272))))

# 361 "FStar.SMTEncoding.Z3.fst"
let bgtheory : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun fresh -> if fresh then begin
(let _169_276 = (let _169_275 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _169_275))
in (FStar_All.pipe_right _169_276 FStar_List.flatten))
end else begin
(
# 364 "FStar.SMTEncoding.Z3.fst"
let bg = (FStar_ST.read bg_scope)
in (
# 365 "FStar.SMTEncoding.Z3.fst"
let _80_318 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)

# 367 "FStar.SMTEncoding.Z3.fst"
let refresh : Prims.unit  ->  Prims.unit = (fun _80_320 -> (match (()) with
| () -> begin
(
# 368 "FStar.SMTEncoding.Z3.fst"
let _80_321 = (bg_z3_proc.refresh ())
in (
# 369 "FStar.SMTEncoding.Z3.fst"
let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))

# 371 "FStar.SMTEncoding.Z3.fst"
let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))

# 373 "FStar.SMTEncoding.Z3.fst"
let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 374 "FStar.SMTEncoding.Z3.fst"
let _80_326 = (pop msg)
in (refresh ())))

# 376 "FStar.SMTEncoding.Z3.fst"
let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| hd::s::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _80_335 -> begin
(FStar_All.failwith "Impossible")
end))

# 381 "FStar.SMTEncoding.Z3.fst"
let ask : Prims.bool  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  ((Prims.bool * FStar_SMTEncoding_Term.error_labels)  ->  Prims.unit)  ->  Prims.unit = (fun fresh label_messages qry cb -> (
# 382 "FStar.SMTEncoding.Z3.fst"
let fresh = (fresh && ((FStar_ST.read FStar_Options.n_cores) > 1))
in (
# 383 "FStar.SMTEncoding.Z3.fst"
let theory = (bgtheory fresh)
in (
# 384 "FStar.SMTEncoding.Z3.fst"
let theory = if fresh then begin
(FStar_List.append theory qry)
end else begin
(FStar_List.append (FStar_List.append (FStar_List.append theory ((FStar_SMTEncoding_Term.Push)::[])) qry) ((FStar_SMTEncoding_Term.Pop)::[]))
end
in (
# 388 "FStar.SMTEncoding.Z3.fst"
let input = (let _169_299 = (let _169_298 = (let _169_297 = (z3_options ())
in (FStar_SMTEncoding_Term.declToSmt _169_297))
in (FStar_List.map _169_298 theory))
in (FStar_All.pipe_right _169_299 (FStar_String.concat "\n")))
in (
# 389 "FStar.SMTEncoding.Z3.fst"
let _80_344 = if (FStar_ST.read FStar_Options.logQueries) then begin
(log_query fresh input)
end else begin
()
end
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb})))))))

# 396 "FStar.SMTEncoding.Z3.fst"
let initialize_fuel_trace : Prims.string  ->  Prims.string Prims.list  ->  Prims.unit = (fun src_fn deps -> (
# 397 "FStar.SMTEncoding.Z3.fst"
let norm_src_fn = (FStar_Util.normalize_file_path src_fn)
in (
# 398 "FStar.SMTEncoding.Z3.fst"
let val_fn = (format_fuel_trace_file_name norm_src_fn)
in (
# 399 "FStar.SMTEncoding.Z3.fst"
let _80_367 = (match ((FStar_Util.load_value_from_file val_fn)) with
| Some (state) -> begin
(
# 401 "FStar.SMTEncoding.Z3.fst"
let _80_359 = if (FStar_ST.read FStar_Options.explicit_deps) then begin
(
# 404 "FStar.SMTEncoding.Z3.fst"
let expected = (FStar_Util.digest_of_file norm_src_fn)
in ("Module", (state.identity.module_digest = expected)))
end else begin
(let _169_304 = (match (state.identity.transitive_digest) with
| None -> begin
false
end
| Some (d) -> begin
(
# 413 "FStar.SMTEncoding.Z3.fst"
let expected = (compute_transitive_digest norm_src_fn deps)
in (d = expected))
end)
in ("Transitive", _169_304))
end
in (match (_80_359) with
| (means, validated) -> begin
if validated then begin
(
# 418 "FStar.SMTEncoding.Z3.fst"
let _80_360 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(FStar_Util.print2 "(%s) %s digest is valid.\n" norm_src_fn means)
end else begin
()
end
in (FStar_ST.op_Colon_Equals fuel_trace (ReplayFuelTrace ((val_fn, state.fuels)))))
end else begin
(
# 425 "FStar.SMTEncoding.Z3.fst"
let _80_362 = if (FStar_ST.read FStar_Options.print_fuels) then begin
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
# 432 "FStar.SMTEncoding.Z3.fst"
let _80_365 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(FStar_Util.print1 "(%s) Unable to read cached fuel trace.\n" norm_src_fn)
end else begin
()
end
in (FStar_ST.op_Colon_Equals fuel_trace (RecordFuelTrace ([]))))
end)
in (refresh ())))))

# 440 "FStar.SMTEncoding.Z3.fst"
let finalize_fuel_trace : Prims.string  ->  Prims.string Prims.list  ->  Prims.unit = (fun src_fn deps -> (
# 441 "FStar.SMTEncoding.Z3.fst"
let _80_382 = (match ((FStar_ST.read fuel_trace)) with
| (ReplayFuelTrace (_)) | (FuelTraceUnavailable) | (RecordFuelTrace ([])) -> begin
()
end
| RecordFuelTrace (l) -> begin
(
# 450 "FStar.SMTEncoding.Z3.fst"
let val_fn = (format_fuel_trace_file_name src_fn)
in (
# 451 "FStar.SMTEncoding.Z3.fst"
let xd = if (FStar_ST.read FStar_Options.explicit_deps) then begin
None
end else begin
(let _169_310 = (compute_transitive_digest src_fn deps)
in (FStar_All.pipe_left (fun _169_309 -> Some (_169_309)) _169_310))
end
in (
# 458 "FStar.SMTEncoding.Z3.fst"
let state = (let _169_312 = (let _169_311 = (FStar_Util.digest_of_file src_fn)
in {module_digest = _169_311; transitive_digest = xd})
in {identity = _169_312; fuels = l})
in (FStar_Util.save_value_to_file val_fn state))))
end)
in (FStar_ST.op_Colon_Equals fuel_trace FuelTraceUnavailable)))




