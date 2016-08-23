
open Prims
# 27 "FStar.SMTEncoding.Z3.fst"
type z3version =
| Z3V_Unknown of Prims.string
| Z3V of (Prims.int * Prims.int * Prims.int)

# 28 "FStar.SMTEncoding.Z3.fst"
let is_Z3V_Unknown = (fun _discr_ -> (match (_discr_) with
| Z3V_Unknown (_) -> begin
true
end
| _ -> begin
false
end))

# 29 "FStar.SMTEncoding.Z3.fst"
let is_Z3V = (fun _discr_ -> (match (_discr_) with
| Z3V (_) -> begin
true
end
| _ -> begin
false
end))

# 28 "FStar.SMTEncoding.Z3.fst"
let ___Z3V_Unknown____0 = (fun projectee -> (match (projectee) with
| Z3V_Unknown (_83_7) -> begin
_83_7
end))

# 29 "FStar.SMTEncoding.Z3.fst"
let ___Z3V____0 = (fun projectee -> (match (projectee) with
| Z3V (_83_10) -> begin
_83_10
end))

# 31 "FStar.SMTEncoding.Z3.fst"
let z3version_as_string : z3version  ->  Prims.string = (fun _83_1 -> (match (_83_1) with
| Z3V_Unknown (s) -> begin
(FStar_Util.format1 "unknown version: %s" s)
end
| Z3V (i, j, k) -> begin
(let _176_33 = (FStar_Util.string_of_int i)
in (let _176_32 = (FStar_Util.string_of_int j)
in (let _176_31 = (FStar_Util.string_of_int k)
in (FStar_Util.format3 "%s.%s.%s" _176_33 _176_32 _176_31))))
end))

# 35 "FStar.SMTEncoding.Z3.fst"
let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _83_23 -> (match (_83_23) with
| (w1, w2, w3) -> begin
(match (known) with
| Z3V_Unknown (_83_25) -> begin
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

# 44 "FStar.SMTEncoding.Z3.fst"
let z3v_le : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.bool = (fun known wanted -> (match ((z3v_compare known wanted)) with
| None -> begin
false
end
| Some (i) -> begin
(i >= 0)
end))

# 49 "FStar.SMTEncoding.Z3.fst"
let _z3version : z3version Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 51 "FStar.SMTEncoding.Z3.fst"
let get_z3version : Prims.unit  ->  z3version = (fun _83_37 -> (match (()) with
| () -> begin
(
# 52 "FStar.SMTEncoding.Z3.fst"
let prefix = "Z3 version "
in (match ((FStar_ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(
# 57 "FStar.SMTEncoding.Z3.fst"
let _83_47 = (let _176_44 = (FStar_Options.z3_exe ())
in (FStar_Util.run_proc _176_44 "-version" ""))
in (match (_83_47) with
| (_83_43, out, _83_46) -> begin
(
# 58 "FStar.SMTEncoding.Z3.fst"
let out = (match ((FStar_Util.splitlines out)) with
| (x)::_83_49 when (FStar_Util.starts_with x prefix) -> begin
(
# 61 "FStar.SMTEncoding.Z3.fst"
let x = (let _176_45 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _176_45))
in (
# 62 "FStar.SMTEncoding.Z3.fst"
let x = try
(match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)
with
| _83_57 -> begin
[]
end
in (match (x) with
| (i1)::(i2)::(i3)::[] -> begin
Z3V (((i1), (i2), (i3)))
end
| _83_66 -> begin
Z3V_Unknown (out)
end)))
end
| _83_68 -> begin
Z3V_Unknown (out)
end)
in (
# 69 "FStar.SMTEncoding.Z3.fst"
let _83_70 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))

# 71 "FStar.SMTEncoding.Z3.fst"
let ini_params : Prims.unit  ->  Prims.string = (fun _83_72 -> (match (()) with
| () -> begin
(
# 72 "FStar.SMTEncoding.Z3.fst"
let z3_v = (get_z3version ())
in (
# 73 "FStar.SMTEncoding.Z3.fst"
let _83_74 = if (let _176_50 = (get_z3version ())
in (z3v_le _176_50 ((4), (4), (0)))) then begin
(let _176_53 = (let _176_52 = (let _176_51 = (z3version_as_string z3_v)
in (FStar_Util.format1 "Z3 v4.4.1 is required; got %s\n" _176_51))
in FStar_Util.Failure (_176_52))
in (FStar_All.pipe_left Prims.raise _176_53))
end else begin
()
end
in "-smt2 -in AUTO_CONFIG=false MODEL=true SMT.RELEVANCY=2"))
end))

# 82 "FStar.SMTEncoding.Z3.fst"
type label =
Prims.string

# 83 "FStar.SMTEncoding.Z3.fst"
type unsat_core =
Prims.string Prims.list Prims.option

# 84 "FStar.SMTEncoding.Z3.fst"
type z3status =
| UNSAT of unsat_core
| SAT of label Prims.list
| UNKNOWN of label Prims.list
| TIMEOUT of label Prims.list

# 85 "FStar.SMTEncoding.Z3.fst"
let is_UNSAT = (fun _discr_ -> (match (_discr_) with
| UNSAT (_) -> begin
true
end
| _ -> begin
false
end))

# 86 "FStar.SMTEncoding.Z3.fst"
let is_SAT = (fun _discr_ -> (match (_discr_) with
| SAT (_) -> begin
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

# 85 "FStar.SMTEncoding.Z3.fst"
let ___UNSAT____0 = (fun projectee -> (match (projectee) with
| UNSAT (_83_78) -> begin
_83_78
end))

# 86 "FStar.SMTEncoding.Z3.fst"
let ___SAT____0 = (fun projectee -> (match (projectee) with
| SAT (_83_81) -> begin
_83_81
end))

# 87 "FStar.SMTEncoding.Z3.fst"
let ___UNKNOWN____0 = (fun projectee -> (match (projectee) with
| UNKNOWN (_83_84) -> begin
_83_84
end))

# 88 "FStar.SMTEncoding.Z3.fst"
let ___TIMEOUT____0 = (fun projectee -> (match (projectee) with
| TIMEOUT (_83_87) -> begin
_83_87
end))

# 90 "FStar.SMTEncoding.Z3.fst"
let status_to_string : z3status  ->  Prims.string = (fun _83_2 -> (match (_83_2) with
| SAT (_83_90) -> begin
"sat"
end
| UNSAT (_83_93) -> begin
"unsat"
end
| UNKNOWN (_83_96) -> begin
"unknown"
end
| TIMEOUT (_83_99) -> begin
"timeout"
end))

# 96 "FStar.SMTEncoding.Z3.fst"
let tid : Prims.unit  ->  Prims.string = (fun _83_101 -> (match (()) with
| () -> begin
(let _176_114 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _176_114 FStar_Util.string_of_int))
end))

# 97 "FStar.SMTEncoding.Z3.fst"
let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (
# 98 "FStar.SMTEncoding.Z3.fst"
let cond = (fun pid s -> (
# 99 "FStar.SMTEncoding.Z3.fst"
let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (let _176_122 = (FStar_Options.z3_exe ())
in (let _176_121 = (ini_params ())
in (FStar_Util.start_process id _176_122 _176_121 cond)))))

# 104 "FStar.SMTEncoding.Z3.fst"
type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}

# 104 "FStar.SMTEncoding.Z3.fst"
let is_Mkbgproc : bgproc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbgproc"))))

# 110 "FStar.SMTEncoding.Z3.fst"
type query_log =
{set_module_name : Prims.string  ->  Prims.unit; append_to_log : Prims.string  ->  Prims.unit; close_log : Prims.unit  ->  Prims.unit; log_file_name : Prims.unit  ->  Prims.string}

# 110 "FStar.SMTEncoding.Z3.fst"
let is_Mkquery_log : query_log  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkquery_log"))))

# 117 "FStar.SMTEncoding.Z3.fst"
let query_logging : query_log = (
# 118 "FStar.SMTEncoding.Z3.fst"
let log_file_opt = (FStar_Util.mk_ref None)
in (
# 119 "FStar.SMTEncoding.Z3.fst"
let used_file_names = (FStar_Util.mk_ref [])
in (
# 120 "FStar.SMTEncoding.Z3.fst"
let current_module_name = (FStar_Util.mk_ref None)
in (
# 121 "FStar.SMTEncoding.Z3.fst"
let current_file_name = (FStar_Util.mk_ref None)
in (
# 122 "FStar.SMTEncoding.Z3.fst"
let set_module_name = (fun n -> (FStar_ST.op_Colon_Equals current_module_name (Some (n))))
in (
# 123 "FStar.SMTEncoding.Z3.fst"
let new_log_file = (fun _83_123 -> (match (()) with
| () -> begin
(match ((FStar_ST.read current_module_name)) with
| None -> begin
(FStar_All.failwith "current module not set")
end
| Some (n) -> begin
(
# 127 "FStar.SMTEncoding.Z3.fst"
let file_name = (match ((let _176_193 = (FStar_ST.read used_file_names)
in (FStar_List.tryFind (fun _83_130 -> (match (_83_130) with
| (m, _83_129) -> begin
(n = m)
end)) _176_193))) with
| None -> begin
(
# 130 "FStar.SMTEncoding.Z3.fst"
let _83_132 = (let _176_195 = (let _176_194 = (FStar_ST.read used_file_names)
in (((n), (0)))::_176_194)
in (FStar_ST.op_Colon_Equals used_file_names _176_195))
in n)
end
| Some (_83_135, k) -> begin
(
# 133 "FStar.SMTEncoding.Z3.fst"
let _83_139 = (let _176_197 = (let _176_196 = (FStar_ST.read used_file_names)
in (((n), ((k + 1))))::_176_196)
in (FStar_ST.op_Colon_Equals used_file_names _176_197))
in (let _176_198 = (FStar_Util.string_of_int (k + 1))
in (FStar_Util.format2 "%s-%s" n _176_198)))
end)
in (
# 135 "FStar.SMTEncoding.Z3.fst"
let file_name = (FStar_Util.format1 "queries-%s.smt2" file_name)
in (
# 136 "FStar.SMTEncoding.Z3.fst"
let _83_143 = (FStar_ST.op_Colon_Equals current_file_name (Some (file_name)))
in (
# 137 "FStar.SMTEncoding.Z3.fst"
let fh = (FStar_Util.open_file_for_writing file_name)
in (
# 138 "FStar.SMTEncoding.Z3.fst"
let _83_146 = (FStar_ST.op_Colon_Equals log_file_opt (Some (fh)))
in fh)))))
end)
end))
in (
# 140 "FStar.SMTEncoding.Z3.fst"
let get_log_file = (fun _83_149 -> (match (()) with
| () -> begin
(match ((FStar_ST.read log_file_opt)) with
| None -> begin
(new_log_file ())
end
| Some (fh) -> begin
fh
end)
end))
in (
# 143 "FStar.SMTEncoding.Z3.fst"
let append_to_log = (fun str -> (let _176_203 = (get_log_file ())
in (FStar_Util.append_to_file _176_203 str)))
in (
# 144 "FStar.SMTEncoding.Z3.fst"
let close_log = (fun _83_156 -> (match (()) with
| () -> begin
(match ((FStar_ST.read log_file_opt)) with
| None -> begin
()
end
| Some (fh) -> begin
(
# 146 "FStar.SMTEncoding.Z3.fst"
let _83_160 = (FStar_Util.close_file fh)
in (FStar_ST.op_Colon_Equals log_file_opt None))
end)
end))
in (
# 147 "FStar.SMTEncoding.Z3.fst"
let log_file_name = (fun _83_163 -> (match (()) with
| () -> begin
(match ((FStar_ST.read current_file_name)) with
| None -> begin
(FStar_All.failwith "no log file")
end
| Some (n) -> begin
n
end)
end))
in {set_module_name = set_module_name; append_to_log = append_to_log; close_log = close_log; log_file_name = log_file_name}))))))))))

# 155 "FStar.SMTEncoding.Z3.fst"
let bg_z3_proc : bgproc = (
# 156 "FStar.SMTEncoding.Z3.fst"
let the_z3proc = (FStar_Util.mk_ref None)
in (
# 157 "FStar.SMTEncoding.Z3.fst"
let new_proc = (
# 158 "FStar.SMTEncoding.Z3.fst"
let ctr = (FStar_Util.mk_ref (- (1)))
in (fun _83_169 -> (match (()) with
| () -> begin
(let _176_212 = (let _176_211 = (
# 159 "FStar.SMTEncoding.Z3.fst"
let _83_170 = (FStar_Util.incr ctr)
in (let _176_210 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _176_210 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _176_211))
in (new_z3proc _176_212))
end)))
in (
# 160 "FStar.SMTEncoding.Z3.fst"
let z3proc = (fun _83_174 -> (match (()) with
| () -> begin
(
# 161 "FStar.SMTEncoding.Z3.fst"
let _83_175 = if ((FStar_ST.read the_z3proc) = None) then begin
(let _176_216 = (let _176_215 = (new_proc ())
in Some (_176_215))
in (FStar_ST.op_Colon_Equals the_z3proc _176_216))
end else begin
()
end
in (let _176_217 = (FStar_ST.read the_z3proc)
in (FStar_Util.must _176_217)))
end))
in (
# 164 "FStar.SMTEncoding.Z3.fst"
let x = []
in (
# 165 "FStar.SMTEncoding.Z3.fst"
let grab = (fun _83_179 -> (match (()) with
| () -> begin
(
# 165 "FStar.SMTEncoding.Z3.fst"
let _83_180 = (FStar_Util.monitor_enter x)
in (z3proc ()))
end))
in (
# 166 "FStar.SMTEncoding.Z3.fst"
let release = (fun _83_183 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (
# 167 "FStar.SMTEncoding.Z3.fst"
let refresh = (fun _83_185 -> (match (()) with
| () -> begin
(
# 168 "FStar.SMTEncoding.Z3.fst"
let proc = (grab ())
in (
# 169 "FStar.SMTEncoding.Z3.fst"
let _83_187 = (FStar_Util.kill_process proc)
in (
# 170 "FStar.SMTEncoding.Z3.fst"
let _83_189 = (let _176_225 = (let _176_224 = (new_proc ())
in Some (_176_224))
in (FStar_ST.op_Colon_Equals the_z3proc _176_225))
in (
# 171 "FStar.SMTEncoding.Z3.fst"
let _83_191 = (query_logging.close_log ())
in (release ())))))
end))
in {grab = grab; release = release; refresh = refresh})))))))

# 177 "FStar.SMTEncoding.Z3.fst"
let doZ3Exe' : Prims.string  ->  FStar_Util.proc  ->  z3status = (fun input z3proc -> (
# 178 "FStar.SMTEncoding.Z3.fst"
let parse = (fun z3out -> (
# 179 "FStar.SMTEncoding.Z3.fst"
let lines = (FStar_All.pipe_right (FStar_String.split (('\n')::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (
# 180 "FStar.SMTEncoding.Z3.fst"
let unsat_core = (fun lines -> (
# 181 "FStar.SMTEncoding.Z3.fst"
let parse_core = (fun s -> (
# 182 "FStar.SMTEncoding.Z3.fst"
let s = (FStar_Util.trim_string s)
in (
# 183 "FStar.SMTEncoding.Z3.fst"
let s = (FStar_Util.substring s 1 ((FStar_String.length s) - 2))
in if (FStar_Util.starts_with s "error") then begin
None
end else begin
(let _176_237 = (FStar_All.pipe_right (FStar_Util.split s " ") (FStar_Util.sort_with FStar_String.compare))
in (FStar_All.pipe_right _176_237 (fun _176_236 -> Some (_176_236))))
end)))
in (match (lines) with
| ("<unsat-core>")::(core)::("</unsat-core>")::rest -> begin
(let _176_238 = (parse_core core)
in ((_176_238), (lines)))
end
| _83_212 -> begin
((None), (lines))
end)))
in (
# 191 "FStar.SMTEncoding.Z3.fst"
let rec lblnegs = (fun lines -> (match (lines) with
| (lname)::("false")::rest -> begin
(let _176_241 = (lblnegs rest)
in (lname)::_176_241)
end
| (lname)::(_83_222)::rest -> begin
(lblnegs rest)
end
| _83_227 -> begin
[]
end))
in (
# 195 "FStar.SMTEncoding.Z3.fst"
let rec unsat_core_and_lblnegs = (fun lines -> (
# 196 "FStar.SMTEncoding.Z3.fst"
let _83_232 = (unsat_core lines)
in (match (_83_232) with
| (core_opt, rest) -> begin
(let _176_244 = (lblnegs rest)
in ((core_opt), (_176_244)))
end)))
in (
# 198 "FStar.SMTEncoding.Z3.fst"
let rec result = (fun x -> (match (x) with
| ("timeout")::tl -> begin
TIMEOUT ([])
end
| ("unknown")::tl -> begin
(let _176_248 = (let _176_247 = (unsat_core_and_lblnegs tl)
in (Prims.snd _176_247))
in UNKNOWN (_176_248))
end
| ("sat")::tl -> begin
(let _176_250 = (let _176_249 = (unsat_core_and_lblnegs tl)
in (Prims.snd _176_249))
in SAT (_176_250))
end
| ("unsat")::tl -> begin
(let _176_252 = (let _176_251 = (unsat_core tl)
in (Prims.fst _176_251))
in UNSAT (_176_252))
end
| (_83_249)::tl -> begin
(result tl)
end
| _83_252 -> begin
(let _176_256 = (let _176_255 = (let _176_254 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _176_254))
in (FStar_Util.format1 "Got output lines: %s\n" _176_255))
in (FStar_All.pipe_left FStar_All.failwith _176_256))
end))
in (result lines)))))))
in (
# 206 "FStar.SMTEncoding.Z3.fst"
let stdout = (FStar_Util.ask_process z3proc input)
in (parse (FStar_Util.trim_string stdout)))))

# 209 "FStar.SMTEncoding.Z3.fst"
let doZ3Exe : Prims.bool  ->  Prims.string  ->  z3status = (
# 210 "FStar.SMTEncoding.Z3.fst"
let ctr = (FStar_Util.mk_ref 0)
in (fun fresh input -> (
# 212 "FStar.SMTEncoding.Z3.fst"
let z3proc = if fresh then begin
(
# 212 "FStar.SMTEncoding.Z3.fst"
let _83_258 = (FStar_Util.incr ctr)
in (let _176_262 = (let _176_261 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _176_261))
in (new_z3proc _176_262)))
end else begin
(bg_z3_proc.grab ())
end
in (
# 213 "FStar.SMTEncoding.Z3.fst"
let res = (doZ3Exe' input z3proc)
in (
# 215 "FStar.SMTEncoding.Z3.fst"
let _83_262 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))

# 218 "FStar.SMTEncoding.Z3.fst"
let z3_options : Prims.unit  ->  Prims.string = (fun _83_264 -> (match (()) with
| () -> begin
"(set-option :global-decls false)(set-option :smt.mbqi false)(set-option :produce-unsat-cores true)\n"
end))

# 223 "FStar.SMTEncoding.Z3.fst"
type 'a job =
{job : Prims.unit  ->  'a; callback : 'a  ->  Prims.unit}

# 223 "FStar.SMTEncoding.Z3.fst"
let is_Mkjob = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkjob"))))

# 227 "FStar.SMTEncoding.Z3.fst"
type z3job =
((unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either * Prims.int) job

# 229 "FStar.SMTEncoding.Z3.fst"
let job_queue : z3job Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 231 "FStar.SMTEncoding.Z3.fst"
let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 0)

# 232 "FStar.SMTEncoding.Z3.fst"
let with_monitor = (fun m f -> (
# 233 "FStar.SMTEncoding.Z3.fst"
let _83_271 = (FStar_Util.monitor_enter m)
in (
# 234 "FStar.SMTEncoding.Z3.fst"
let res = (f ())
in (
# 235 "FStar.SMTEncoding.Z3.fst"
let _83_274 = (FStar_Util.monitor_exit m)
in res))))

# 238 "FStar.SMTEncoding.Z3.fst"
let z3_job : Prims.bool  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  Prims.string  ->  Prims.unit  ->  ((unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either * Prims.int) = (fun fresh label_messages input _83_279 -> (match (()) with
| () -> begin
(
# 239 "FStar.SMTEncoding.Z3.fst"
let start = (FStar_Util.now ())
in (
# 240 "FStar.SMTEncoding.Z3.fst"
let status = (doZ3Exe fresh input)
in (
# 241 "FStar.SMTEncoding.Z3.fst"
let _83_285 = (let _176_298 = (FStar_Util.now ())
in (FStar_Util.time_diff start _176_298))
in (match (_83_285) with
| (_83_283, elapsed_time) -> begin
(
# 242 "FStar.SMTEncoding.Z3.fst"
let result = (match (status) with
| UNSAT (core) -> begin
((FStar_Util.Inl (core)), (elapsed_time))
end
| (TIMEOUT (lblnegs)) | (SAT (lblnegs)) | (UNKNOWN (lblnegs)) -> begin
(
# 247 "FStar.SMTEncoding.Z3.fst"
let _83_292 = if (FStar_Options.debug_any ()) then begin
(let _176_299 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _176_299))
end else begin
()
end
in (
# 248 "FStar.SMTEncoding.Z3.fst"
let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _83_300 -> (match (_83_300) with
| (m, _83_297, _83_299) -> begin
((Prims.fst m) = l)
end))))) with
| None -> begin
[]
end
| Some (lbl, msg, r) -> begin
(((lbl), (msg), (r)))::[]
end))))
in ((FStar_Util.Inr (failing_assertions)), (elapsed_time))))
end)
in result)
end))))
end))

# 255 "FStar.SMTEncoding.Z3.fst"
let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _83_309 -> (match (()) with
| () -> begin
(
# 256 "FStar.SMTEncoding.Z3.fst"
let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (hd)::tl -> begin
(
# 259 "FStar.SMTEncoding.Z3.fst"
let _83_314 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (
# 261 "FStar.SMTEncoding.Z3.fst"
let _83_317 = (FStar_Util.incr pending_jobs)
in (
# 262 "FStar.SMTEncoding.Z3.fst"
let _83_319 = (FStar_Util.monitor_exit job_queue)
in (
# 263 "FStar.SMTEncoding.Z3.fst"
let _83_321 = (run_job j)
in (
# 264 "FStar.SMTEncoding.Z3.fst"
let _83_324 = (with_monitor job_queue (fun _83_323 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (
# 265 "FStar.SMTEncoding.Z3.fst"
let _83_326 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _83_328 -> (match (()) with
| () -> begin
(
# 268 "FStar.SMTEncoding.Z3.fst"
let _83_329 = (FStar_Util.monitor_enter job_queue)
in (
# 269 "FStar.SMTEncoding.Z3.fst"
let rec aux = (fun _83_332 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(
# 271 "FStar.SMTEncoding.Z3.fst"
let _83_334 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _83_337 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _176_311 = (j.job ())
in (FStar_All.pipe_left j.callback _176_311)))

# 278 "FStar.SMTEncoding.Z3.fst"
let init : Prims.unit  ->  Prims.unit = (fun _83_339 -> (match (()) with
| () -> begin
(
# 279 "FStar.SMTEncoding.Z3.fst"
let n_runners = ((FStar_Options.n_cores ()) - 1)
in (
# 280 "FStar.SMTEncoding.Z3.fst"
let rec aux = (fun n -> if (n = 0) then begin
()
end else begin
(
# 282 "FStar.SMTEncoding.Z3.fst"
let _83_343 = (FStar_Util.spawn dequeue)
in (aux (n - 1)))
end)
in (aux n_runners)))
end))

# 285 "FStar.SMTEncoding.Z3.fst"
let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(
# 290 "FStar.SMTEncoding.Z3.fst"
let _83_347 = (FStar_Util.monitor_enter job_queue)
in (
# 291 "FStar.SMTEncoding.Z3.fst"
let _83_349 = (let _176_321 = (let _176_320 = (FStar_ST.read job_queue)
in (FStar_List.append _176_320 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _176_321))
in (
# 292 "FStar.SMTEncoding.Z3.fst"
let _83_351 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)

# 296 "FStar.SMTEncoding.Z3.fst"
let finish : Prims.unit  ->  Prims.unit = (fun _83_353 -> (match (()) with
| () -> begin
(
# 297 "FStar.SMTEncoding.Z3.fst"
let bg = (bg_z3_proc.grab ())
in (
# 298 "FStar.SMTEncoding.Z3.fst"
let _83_355 = (FStar_Util.kill_process bg)
in (
# 299 "FStar.SMTEncoding.Z3.fst"
let _83_357 = (bg_z3_proc.release ())
in (
# 300 "FStar.SMTEncoding.Z3.fst"
let rec aux = (fun _83_360 -> (match (()) with
| () -> begin
(
# 301 "FStar.SMTEncoding.Z3.fst"
let _83_364 = (with_monitor job_queue (fun _83_361 -> (match (()) with
| () -> begin
(let _176_329 = (FStar_ST.read pending_jobs)
in (let _176_328 = (let _176_327 = (FStar_ST.read job_queue)
in (FStar_List.length _176_327))
in ((_176_329), (_176_328))))
end)))
in (match (_83_364) with
| (n, m) -> begin
if ((n + m) = 0) then begin
(let _176_330 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _176_330 Prims.ignore))
end else begin
(
# 305 "FStar.SMTEncoding.Z3.fst"
let _83_365 = (FStar_Util.sleep 500)
in (aux ()))
end
end))
end))
in (aux ())))))
end))

# 309 "FStar.SMTEncoding.Z3.fst"
type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list

# 310 "FStar.SMTEncoding.Z3.fst"
let fresh_scope : FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))

# 311 "FStar.SMTEncoding.Z3.fst"
let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 312 "FStar.SMTEncoding.Z3.fst"
let push : Prims.string  ->  Prims.unit = (fun msg -> (
# 313 "FStar.SMTEncoding.Z3.fst"
let _83_368 = (let _176_334 = (let _176_333 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::[])::_176_333)
in (FStar_ST.op_Colon_Equals fresh_scope _176_334))
in (let _176_336 = (let _176_335 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[]) _176_335))
in (FStar_ST.op_Colon_Equals bg_scope _176_336))))

# 315 "FStar.SMTEncoding.Z3.fst"
let pop : Prims.string  ->  Prims.unit = (fun msg -> (
# 316 "FStar.SMTEncoding.Z3.fst"
let _83_371 = (let _176_340 = (let _176_339 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _176_339))
in (FStar_ST.op_Colon_Equals fresh_scope _176_340))
in (let _176_342 = (let _176_341 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[]) _176_341))
in (FStar_ST.op_Colon_Equals bg_scope _176_342))))

# 318 "FStar.SMTEncoding.Z3.fst"
let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (
# 319 "FStar.SMTEncoding.Z3.fst"
let _83_379 = (match ((FStar_ST.read fresh_scope)) with
| (hd)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _83_378 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _176_346 = (let _176_345 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _176_345))
in (FStar_ST.op_Colon_Equals bg_scope _176_346))))

# 323 "FStar.SMTEncoding.Z3.fst"
let bgtheory : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun fresh -> if fresh then begin
(let _176_350 = (let _176_349 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _176_349))
in (FStar_All.pipe_right _176_350 FStar_List.flatten))
end else begin
(
# 326 "FStar.SMTEncoding.Z3.fst"
let bg = (FStar_ST.read bg_scope)
in (
# 327 "FStar.SMTEncoding.Z3.fst"
let _83_383 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)

# 329 "FStar.SMTEncoding.Z3.fst"
let refresh : Prims.unit  ->  Prims.unit = (fun _83_385 -> (match (()) with
| () -> begin
(
# 330 "FStar.SMTEncoding.Z3.fst"
let _83_386 = (bg_z3_proc.refresh ())
in (
# 331 "FStar.SMTEncoding.Z3.fst"
let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))

# 333 "FStar.SMTEncoding.Z3.fst"
let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))

# 335 "FStar.SMTEncoding.Z3.fst"
let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 336 "FStar.SMTEncoding.Z3.fst"
let _83_391 = (pop msg)
in (refresh ())))

# 338 "FStar.SMTEncoding.Z3.fst"
let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| (hd)::(s)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _83_400 -> begin
(FStar_All.failwith "Impossible")
end))

# 344 "FStar.SMTEncoding.Z3.fst"
let ask : unsat_core  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  (((unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either * Prims.int)  ->  Prims.unit)  ->  Prims.unit = (fun core label_messages qry cb -> (
# 345 "FStar.SMTEncoding.Z3.fst"
let filter_assertions = (fun theory -> (match (core) with
| None -> begin
((theory), (false))
end
| Some (core) -> begin
(
# 348 "FStar.SMTEncoding.Z3.fst"
let _83_428 = (FStar_List.fold_right (fun d _83_414 -> (match (_83_414) with
| (theory, n_retained, n_pruned) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (_83_416, _83_418, Some (name)) -> begin
if (FStar_List.contains name core) then begin
(((d)::theory), ((n_retained + 1)), (n_pruned))
end else begin
if (FStar_Util.starts_with name "@") then begin
(((d)::theory), (n_retained), (n_pruned))
end else begin
((theory), (n_retained), ((n_pruned + 1)))
end
end
end
| _83_424 -> begin
(((d)::theory), (n_retained), (n_pruned))
end)
end)) theory (([]), (0), (0)))
in (match (_83_428) with
| (theory', n_retained, n_pruned) -> begin
(
# 358 "FStar.SMTEncoding.Z3.fst"
let missed_assertions = (fun th core -> (
# 359 "FStar.SMTEncoding.Z3.fst"
let missed = (let _176_382 = (FStar_All.pipe_right core (FStar_List.filter (fun nm -> (let _176_381 = (FStar_All.pipe_right th (FStar_Util.for_some (fun _83_3 -> (match (_83_3) with
| FStar_SMTEncoding_Term.Assume (_83_435, _83_437, Some (nm')) -> begin
(nm = nm')
end
| _83_443 -> begin
false
end))))
in (FStar_All.pipe_right _176_381 Prims.op_Negation)))))
in (FStar_All.pipe_right _176_382 (FStar_String.concat ", ")))
in (
# 363 "FStar.SMTEncoding.Z3.fst"
let included = (let _176_384 = (FStar_All.pipe_right th (FStar_List.collect (fun _83_4 -> (match (_83_4) with
| FStar_SMTEncoding_Term.Assume (_83_447, _83_449, Some (nm)) -> begin
(nm)::[]
end
| _83_455 -> begin
[]
end))))
in (FStar_All.pipe_right _176_384 (FStar_String.concat ", ")))
in (FStar_Util.format2 "missed={%s}; included={%s}" missed included))))
in (
# 365 "FStar.SMTEncoding.Z3.fst"
let _83_459 = if ((FStar_Options.hint_info ()) && (FStar_Options.debug_any ())) then begin
(
# 368 "FStar.SMTEncoding.Z3.fst"
let n = (FStar_List.length core)
in (
# 369 "FStar.SMTEncoding.Z3.fst"
let missed = if (n <> n_retained) then begin
(missed_assertions theory' core)
end else begin
""
end
in (let _176_388 = (FStar_Util.string_of_int n_retained)
in (let _176_387 = if (n <> n_retained) then begin
(let _176_385 = (FStar_Util.string_of_int n)
in (FStar_Util.format2 " (expected %s (%s); replay may be inaccurate)" _176_385 missed))
end else begin
""
end
in (let _176_386 = (FStar_Util.string_of_int n_pruned)
in (FStar_Util.print3 "Hint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n" _176_388 _176_387 _176_386))))))
end else begin
()
end
in (let _176_393 = (let _176_392 = (let _176_391 = (let _176_390 = (let _176_389 = (FStar_All.pipe_right core (FStar_String.concat ", "))
in (Prims.strcat "UNSAT CORE: " _176_389))
in FStar_SMTEncoding_Term.Caption (_176_390))
in (_176_391)::[])
in (FStar_List.append theory' _176_392))
in ((_176_393), (true)))))
end))
end))
in (
# 379 "FStar.SMTEncoding.Z3.fst"
let theory = (bgtheory false)
in (
# 380 "FStar.SMTEncoding.Z3.fst"
let theory = (FStar_List.append theory (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[]))))
in (
# 381 "FStar.SMTEncoding.Z3.fst"
let _83_465 = (filter_assertions theory)
in (match (_83_465) with
| (theory, used_unsat_core) -> begin
(
# 382 "FStar.SMTEncoding.Z3.fst"
let cb = (fun _83_469 -> (match (_83_469) with
| (uc_errs, time) -> begin
if used_unsat_core then begin
(match (uc_errs) with
| FStar_Util.Inl (_83_471) -> begin
(cb ((uc_errs), (time)))
end
| FStar_Util.Inr (_83_474) -> begin
(cb ((FStar_Util.Inr ([])), (time)))
end)
end else begin
(cb ((uc_errs), (time)))
end
end))
in (
# 388 "FStar.SMTEncoding.Z3.fst"
let input = (let _176_396 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ())) theory)
in (FStar_All.pipe_right _176_396 (FStar_String.concat "\n")))
in (
# 389 "FStar.SMTEncoding.Z3.fst"
let _83_477 = if (FStar_Options.log_queries ()) then begin
(query_logging.append_to_log input)
end else begin
()
end
in (enqueue false {job = (z3_job false label_messages input); callback = cb}))))
end))))))




