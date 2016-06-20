
open Prims

type z3version =
| Z3V_Unknown of Prims.string
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


let ___Z3V_Unknown____0 = (fun projectee -> (match (projectee) with
<<<<<<< HEAD
| Z3V_Unknown (_80_7) -> begin
_80_7
=======
| Z3V_Unknown (_81_5) -> begin
_81_5
>>>>>>> origin
end))


let ___Z3V____0 = (fun projectee -> (match (projectee) with
<<<<<<< HEAD
| Z3V (_80_10) -> begin
_80_10
=======
| Z3V (_81_8) -> begin
_81_8
>>>>>>> origin
end))


let z3version_as_string : z3version  ->  Prims.string = (fun _81_1 -> (match (_81_1) with
| Z3V_Unknown (s) -> begin
(FStar_Util.format1 "unknown version: %s" s)
end
| Z3V (i, j, k) -> begin
(let _172_33 = (FStar_Util.string_of_int i)
in (let _172_32 = (FStar_Util.string_of_int j)
in (let _172_31 = (FStar_Util.string_of_int k)
in (FStar_Util.format3 "%s.%s.%s" _172_33 _172_32 _172_31))))
end))


<<<<<<< HEAD
let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _80_23 -> (match (_80_23) with
| (w1, w2, w3) -> begin
(match (known) with
| Z3V_Unknown (_80_25) -> begin
=======
let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _81_21 -> (match (_81_21) with
| (w1, w2, w3) -> begin
(match (known) with
| Z3V_Unknown (_81_23) -> begin
>>>>>>> origin
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
(i >= 0)
end))


let _z3version : z3version Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


<<<<<<< HEAD
let get_z3version : Prims.unit  ->  z3version = (fun _80_37 -> (match (()) with
=======
let get_z3version : Prims.unit  ->  z3version = (fun _81_35 -> (match (()) with
>>>>>>> origin
| () -> begin
(

let prefix = "Z3 version "
in (match ((FStar_ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(

<<<<<<< HEAD
let _80_47 = (let _170_44 = (FStar_Options.z3_exe ())
in (FStar_Util.run_proc _170_44 "-version" ""))
in (match (_80_47) with
| (_80_43, out, _80_46) -> begin
(

let out = (match ((FStar_Util.splitlines out)) with
| (x)::_80_49 when (FStar_Util.starts_with x prefix) -> begin
=======
let _81_45 = (let _172_44 = (FStar_Options.z3_exe ())
in (FStar_Util.run_proc _172_44 "-version" ""))
in (match (_81_45) with
| (_81_41, out, _81_44) -> begin
(

let out = (match ((FStar_Util.splitlines out)) with
| (x)::_81_47 when (FStar_Util.starts_with x prefix) -> begin
>>>>>>> origin
(

let x = (let _172_45 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _172_45))
in (

let x = try
(match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)
with
<<<<<<< HEAD
| _80_57 -> begin
=======
| _81_55 -> begin
>>>>>>> origin
[]
end
in (match (x) with
| (i1)::(i2)::(i3)::[] -> begin
Z3V ((i1, i2, i3))
end
<<<<<<< HEAD
| _80_66 -> begin
Z3V_Unknown (out)
end)))
end
| _80_68 -> begin
=======
| _81_64 -> begin
Z3V_Unknown (out)
end)))
end
| _81_66 -> begin
>>>>>>> origin
Z3V_Unknown (out)
end)
in (

<<<<<<< HEAD
let _80_70 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
=======
let _81_68 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
>>>>>>> origin
in out))
end))
end))
end))


<<<<<<< HEAD
let ini_params : Prims.unit  ->  Prims.string = (fun _80_72 -> (match (()) with
=======
let ini_params : Prims.unit  ->  Prims.string = (fun _81_70 -> (match (()) with
>>>>>>> origin
| () -> begin
(

let z3_v = (get_z3version ())
in (

<<<<<<< HEAD
let _80_74 = if (let _170_50 = (get_z3version ())
in (z3v_le _170_50 (4, 4, 0))) then begin
(let _170_53 = (let _170_52 = (let _170_51 = (z3version_as_string z3_v)
in (FStar_Util.format1 "Z3 v4.4.1 is required; got %s\n" _170_51))
in FStar_Util.Failure (_170_52))
in (FStar_All.pipe_left Prims.raise _170_53))
=======
let _81_72 = if (let _172_50 = (get_z3version ())
in (z3v_le _172_50 (4, 4, 0))) then begin
(let _172_53 = (let _172_52 = (let _172_51 = (z3version_as_string z3_v)
in (FStar_Util.format1 "Z3 v4.4.1 is required; got %s\n" _172_51))
in FStar_Util.Failure (_172_52))
in (FStar_All.pipe_left Prims.raise _172_53))
>>>>>>> origin
end else begin
()
end
in "-smt2 -in AUTO_CONFIG=false MODEL=true SMT.RELEVANCY=2"))
end))


type label =
Prims.string


type unsat_core =
Prims.string Prims.list Prims.option


type z3status =
| UNSAT of unsat_core
| SAT of label Prims.list
| UNKNOWN of label Prims.list
| TIMEOUT of label Prims.list


let is_UNSAT = (fun _discr_ -> (match (_discr_) with
| UNSAT (_) -> begin
true
end
| _ -> begin
false
end))


let is_SAT = (fun _discr_ -> (match (_discr_) with
| SAT (_) -> begin
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


let ___UNSAT____0 = (fun projectee -> (match (projectee) with
<<<<<<< HEAD
| UNSAT (_80_78) -> begin
_80_78
=======
| UNSAT (_81_76) -> begin
_81_76
>>>>>>> origin
end))


let ___SAT____0 = (fun projectee -> (match (projectee) with
<<<<<<< HEAD
| SAT (_80_81) -> begin
_80_81
=======
| SAT (_81_79) -> begin
_81_79
>>>>>>> origin
end))


let ___UNKNOWN____0 = (fun projectee -> (match (projectee) with
<<<<<<< HEAD
| UNKNOWN (_80_84) -> begin
_80_84
=======
| UNKNOWN (_81_82) -> begin
_81_82
>>>>>>> origin
end))


let ___TIMEOUT____0 = (fun projectee -> (match (projectee) with
<<<<<<< HEAD
| TIMEOUT (_80_87) -> begin
_80_87
end))


let status_to_string : z3status  ->  Prims.string = (fun _80_2 -> (match (_80_2) with
| SAT (_80_90) -> begin
"sat"
end
| UNSAT (_80_93) -> begin
"unsat"
end
| UNKNOWN (_80_96) -> begin
"unknown"
end
| TIMEOUT (_80_99) -> begin
=======
| TIMEOUT (_81_85) -> begin
_81_85
end))


let status_to_string : z3status  ->  Prims.string = (fun _81_2 -> (match (_81_2) with
| SAT (_81_88) -> begin
"sat"
end
| UNSAT (_81_91) -> begin
"unsat"
end
| UNKNOWN (_81_94) -> begin
"unknown"
end
| TIMEOUT (_81_97) -> begin
>>>>>>> origin
"timeout"
end))


<<<<<<< HEAD
let tid : Prims.unit  ->  Prims.string = (fun _80_101 -> (match (()) with
=======
let tid : Prims.unit  ->  Prims.string = (fun _81_99 -> (match (()) with
>>>>>>> origin
| () -> begin
(let _172_114 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _172_114 FStar_Util.string_of_int))
end))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (let _172_122 = (FStar_Options.z3_exe ())
in (let _172_121 = (ini_params ())
in (FStar_Util.start_process id _172_122 _172_121 cond)))))


type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}


let is_Mkbgproc : bgproc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbgproc"))))


let queries_dot_smt2 : FStar_Util.file_handle Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let get_qfile : Prims.bool  ->  FStar_Util.file_handle = (

let ctr = (FStar_Util.mk_ref 0)
in (fun fresh -> if fresh then begin
(

<<<<<<< HEAD
let _80_113 = (FStar_Util.incr ctr)
in (let _170_155 = (let _170_154 = (let _170_153 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _170_153))
in (FStar_Util.format1 "queries-%s.smt2" _170_154))
in (FStar_Util.open_file_for_writing _170_155)))
=======
let _81_111 = (FStar_Util.incr ctr)
in (let _172_155 = (let _172_154 = (let _172_153 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _172_153))
in (FStar_Util.format1 "queries-%s.smt2" _172_154))
in (FStar_Util.open_file_for_writing _172_155)))
>>>>>>> origin
end else begin
(match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
(

let fh = (FStar_Util.open_file_for_writing "queries-bg-0.smt2")
in (

<<<<<<< HEAD
let _80_117 = (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
=======
let _81_115 = (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
>>>>>>> origin
in fh))
end
| Some (fh) -> begin
fh
end)
end))


let log_query : Prims.bool  ->  Prims.string  ->  Prims.unit = (fun fresh i -> (

let fh = (get_qfile fresh)
in (

<<<<<<< HEAD
let _80_124 = (FStar_Util.append_to_file fh i)
=======
let _81_122 = (FStar_Util.append_to_file fh i)
>>>>>>> origin
in if fresh then begin
(FStar_Util.close_file fh)
end else begin
()
end)))


let the_z3proc : FStar_Util.proc Prims.option FStar_ST.ref = (FStar_ST.alloc None)


let ctr : Prims.int FStar_ST.ref = (FStar_Util.mk_ref (- (1)))


<<<<<<< HEAD
let new_proc : Prims.unit  ->  FStar_Util.proc = (fun _80_126 -> (match (()) with
=======
let new_proc : Prims.unit  ->  FStar_Util.proc = (fun _81_124 -> (match (()) with
>>>>>>> origin
| () -> begin
(let _172_164 = (let _172_163 = (

<<<<<<< HEAD
let _80_127 = (FStar_Util.incr ctr)
in (let _170_162 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _170_162 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _170_163))
in (new_z3proc _170_164))
end))


let z3proc : Prims.unit  ->  FStar_Util.proc = (fun _80_129 -> (match (()) with
| () -> begin
(

let _80_130 = if ((FStar_ST.read the_z3proc) = None) then begin
(let _170_168 = (let _170_167 = (new_proc ())
in Some (_170_167))
in (FStar_ST.op_Colon_Equals the_z3proc _170_168))
=======
let _81_125 = (FStar_Util.incr ctr)
in (let _172_162 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _172_162 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _172_163))
in (new_z3proc _172_164))
end))


let z3proc : Prims.unit  ->  FStar_Util.proc = (fun _81_127 -> (match (()) with
| () -> begin
(

let _81_128 = if ((FStar_ST.read the_z3proc) = None) then begin
(let _172_168 = (let _172_167 = (new_proc ())
in Some (_172_167))
in (FStar_ST.op_Colon_Equals the_z3proc _172_168))
>>>>>>> origin
end else begin
()
end
in (let _172_169 = (FStar_ST.read the_z3proc)
in (FStar_Util.must _172_169)))
end))


let bg_z3_proc : bgproc = (

let x = []
in (

<<<<<<< HEAD
let grab = (fun _80_134 -> (match (()) with
| () -> begin
(

let _80_135 = (FStar_Util.monitor_enter x)
=======
let grab = (fun _81_132 -> (match (()) with
| () -> begin
(

let _81_133 = (FStar_Util.monitor_enter x)
>>>>>>> origin
in (z3proc ()))
end))
in (

<<<<<<< HEAD
let release = (fun _80_138 -> (match (()) with
=======
let release = (fun _81_136 -> (match (()) with
>>>>>>> origin
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (

<<<<<<< HEAD
let refresh = (fun _80_140 -> (match (()) with
=======
let refresh = (fun _81_138 -> (match (()) with
>>>>>>> origin
| () -> begin
(

let proc = (grab ())
in (

<<<<<<< HEAD
let _80_142 = (FStar_Util.kill_process proc)
in (

let _80_144 = (let _170_177 = (let _170_176 = (new_proc ())
in Some (_170_176))
in (FStar_ST.op_Colon_Equals the_z3proc _170_177))
in (

let _80_152 = (match ((FStar_ST.read queries_dot_smt2)) with
=======
let _81_140 = (FStar_Util.kill_process proc)
in (

let _81_142 = (let _172_177 = (let _172_176 = (new_proc ())
in Some (_172_176))
in (FStar_ST.op_Colon_Equals the_z3proc _172_177))
in (

let _81_150 = (match ((FStar_ST.read queries_dot_smt2)) with
>>>>>>> origin
| None -> begin
()
end
| Some (fh) -> begin
(

<<<<<<< HEAD
let _80_149 = (FStar_Util.close_file fh)
=======
let _81_147 = (FStar_Util.close_file fh)
>>>>>>> origin
in (

let fh = (let _172_180 = (let _172_179 = (let _172_178 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _172_178 FStar_Util.string_of_int))
in (FStar_Util.format1 "queries-bg-%s.smt2" _172_179))
in (FStar_Util.open_file_for_writing _172_180))
in (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))))
end)
in (release ())))))
end))
in {grab = grab; release = release; refresh = refresh}))))


let doZ3Exe' : Prims.string  ->  FStar_Util.proc  ->  z3status = (fun input z3proc -> (

let parse = (fun z3out -> (

let lines = (FStar_All.pipe_right (FStar_String.split (('\n')::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (

let unsat_core = (fun lines -> (

let parse_core = (fun s -> (

let s = (FStar_Util.trim_string s)
in (

let s = (FStar_Util.substring s 1 ((FStar_String.length s) - 2))
in if (FStar_Util.starts_with s "error") then begin
None
end else begin
(let _172_192 = (FStar_All.pipe_right (FStar_Util.split s " ") (FStar_Util.sort_with FStar_String.compare))
in (FStar_All.pipe_right _172_192 (fun _172_191 -> Some (_172_191))))
end)))
in (match (lines) with
| ("<unsat-core>")::(core)::("</unsat-core>")::rest -> begin
(let _172_193 = (parse_core core)
in (_172_193, lines))
end
<<<<<<< HEAD
| _80_173 -> begin
=======
| _81_171 -> begin
>>>>>>> origin
(None, lines)
end)))
in (

let rec lblnegs = (fun lines -> (match (lines) with
| (lname)::("false")::rest -> begin
(let _172_196 = (lblnegs rest)
in (lname)::_172_196)
end
<<<<<<< HEAD
| (lname)::(_80_183)::rest -> begin
(lblnegs rest)
end
| _80_188 -> begin
=======
| (lname)::(_81_181)::rest -> begin
(lblnegs rest)
end
| _81_186 -> begin
>>>>>>> origin
[]
end))
in (

let rec unsat_core_and_lblnegs = (fun lines -> (

<<<<<<< HEAD
let _80_193 = (unsat_core lines)
in (match (_80_193) with
=======
let _81_191 = (unsat_core lines)
in (match (_81_191) with
>>>>>>> origin
| (core_opt, rest) -> begin
(let _172_199 = (lblnegs rest)
in (core_opt, _172_199))
end)))
in (

let rec result = (fun x -> (match (x) with
| ("timeout")::tl -> begin
TIMEOUT ([])
end
| ("unknown")::tl -> begin
(let _172_203 = (let _172_202 = (unsat_core_and_lblnegs tl)
in (Prims.snd _172_202))
in UNKNOWN (_172_203))
end
| ("sat")::tl -> begin
(let _172_205 = (let _172_204 = (unsat_core_and_lblnegs tl)
in (Prims.snd _172_204))
in SAT (_172_205))
end
| ("unsat")::tl -> begin
(let _172_207 = (let _172_206 = (unsat_core tl)
in (Prims.fst _172_206))
in UNSAT (_172_207))
end
<<<<<<< HEAD
| (_80_210)::tl -> begin
(result tl)
end
| _80_213 -> begin
(let _170_211 = (let _170_210 = (let _170_209 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _170_209))
in (FStar_Util.format1 "Got output lines: %s\n" _170_210))
in (FStar_All.pipe_left FStar_All.failwith _170_211))
=======
| (_81_208)::tl -> begin
(result tl)
end
| _81_211 -> begin
(let _172_211 = (let _172_210 = (let _172_209 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _172_209))
in (FStar_Util.format1 "Got output lines: %s\n" _172_210))
in (FStar_All.pipe_left FStar_All.failwith _172_211))
>>>>>>> origin
end))
in (result lines)))))))
in (

let stdout = (FStar_Util.ask_process z3proc input)
in (parse (FStar_Util.trim_string stdout)))))


let doZ3Exe : Prims.bool  ->  Prims.string  ->  z3status = (

let ctr = (FStar_Util.mk_ref 0)
in (fun fresh input -> (

let z3proc = if fresh then begin
(

<<<<<<< HEAD
let _80_219 = (FStar_Util.incr ctr)
in (let _170_217 = (let _170_216 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _170_216))
in (new_z3proc _170_217)))
=======
let _81_217 = (FStar_Util.incr ctr)
in (let _172_217 = (let _172_216 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _172_216))
in (new_z3proc _172_217)))
>>>>>>> origin
end else begin
(bg_z3_proc.grab ())
end
in (

let res = (doZ3Exe' input z3proc)
in (

<<<<<<< HEAD
let _80_223 = if fresh then begin
=======
let _81_221 = if fresh then begin
>>>>>>> origin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))


<<<<<<< HEAD
let z3_options : Prims.unit  ->  Prims.string = (fun _80_225 -> (match (()) with
=======
let z3_options : Prims.unit  ->  Prims.string = (fun _81_223 -> (match (()) with
>>>>>>> origin
| () -> begin
"(set-option :global-decls false)(set-option :smt.mbqi false)(set-option :produce-unsat-cores true)\n"
end))


type 'a job =
{job : Prims.unit  ->  'a; callback : 'a  ->  Prims.unit}


let is_Mkjob = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkjob"))))


type z3job =
((unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either * Prims.int) job


let job_queue : z3job Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 0)


let with_monitor = (fun m f -> (

<<<<<<< HEAD
let _80_232 = (FStar_Util.monitor_enter m)
=======
let _81_230 = (FStar_Util.monitor_enter m)
>>>>>>> origin
in (

let res = (f ())
in (

<<<<<<< HEAD
let _80_235 = (FStar_Util.monitor_exit m)
in res))))


let z3_job : Prims.bool  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  Prims.string  ->  Prims.unit  ->  ((unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either * Prims.int) = (fun fresh label_messages input _80_240 -> (match (()) with
=======
let _81_233 = (FStar_Util.monitor_exit m)
in res))))


let z3_job : Prims.bool  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  Prims.string  ->  Prims.unit  ->  ((unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either * Prims.int) = (fun fresh label_messages input _81_238 -> (match (()) with
>>>>>>> origin
| () -> begin
(

let start = (FStar_Util.now ())
in (

let status = (doZ3Exe fresh input)
in (

<<<<<<< HEAD
let _80_246 = (let _170_253 = (FStar_Util.now ())
in (FStar_Util.time_diff start _170_253))
in (match (_80_246) with
| (_80_244, elapsed_time) -> begin
=======
let _81_244 = (let _172_253 = (FStar_Util.now ())
in (FStar_Util.time_diff start _172_253))
in (match (_81_244) with
| (_81_242, elapsed_time) -> begin
>>>>>>> origin
(

let result = (match (status) with
| UNSAT (core) -> begin
(FStar_Util.Inl (core), elapsed_time)
end
| (TIMEOUT (lblnegs)) | (SAT (lblnegs)) | (UNKNOWN (lblnegs)) -> begin
(

<<<<<<< HEAD
let _80_253 = if (FStar_Options.debug_any ()) then begin
(let _170_254 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _170_254))
=======
let _81_251 = if (FStar_Options.debug_any ()) then begin
(let _172_254 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _172_254))
>>>>>>> origin
end else begin
()
end
in (

<<<<<<< HEAD
let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _80_261 -> (match (_80_261) with
| (m, _80_258, _80_260) -> begin
=======
let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _81_259 -> (match (_81_259) with
| (m, _81_256, _81_258) -> begin
>>>>>>> origin
((Prims.fst m) = l)
end))))) with
| None -> begin
[]
end
| Some (lbl, msg, r) -> begin
((lbl, msg, r))::[]
end))))
in (FStar_Util.Inr (failing_assertions), elapsed_time)))
end)
in result)
end))))
end))


<<<<<<< HEAD
let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _80_270 -> (match (()) with
=======
let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _81_268 -> (match (()) with
>>>>>>> origin
| () -> begin
(

let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (hd)::tl -> begin
(

<<<<<<< HEAD
let _80_275 = (FStar_ST.op_Colon_Equals job_queue tl)
=======
let _81_273 = (FStar_ST.op_Colon_Equals job_queue tl)
>>>>>>> origin
in hd)
end)
in (

<<<<<<< HEAD
let _80_278 = (FStar_Util.incr pending_jobs)
in (

let _80_280 = (FStar_Util.monitor_exit job_queue)
in (

let _80_282 = (run_job j)
in (

let _80_285 = (with_monitor job_queue (fun _80_284 -> (match (()) with
=======
let _81_276 = (FStar_Util.incr pending_jobs)
in (

let _81_278 = (FStar_Util.monitor_exit job_queue)
in (

let _81_280 = (run_job j)
in (

let _81_283 = (with_monitor job_queue (fun _81_282 -> (match (()) with
>>>>>>> origin
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (

<<<<<<< HEAD
let _80_287 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _80_289 -> (match (()) with
| () -> begin
(

let _80_290 = (FStar_Util.monitor_enter job_queue)
in (

let rec aux = (fun _80_293 -> (match (()) with
=======
let _81_285 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _81_287 -> (match (()) with
| () -> begin
(

let _81_288 = (FStar_Util.monitor_enter job_queue)
in (

let rec aux = (fun _81_291 -> (match (()) with
>>>>>>> origin
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(

<<<<<<< HEAD
let _80_295 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _80_298 -> begin
=======
let _81_293 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _81_296 -> begin
>>>>>>> origin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _172_266 = (j.job ())
in (FStar_All.pipe_left j.callback _172_266)))


<<<<<<< HEAD
let init : Prims.unit  ->  Prims.unit = (fun _80_300 -> (match (()) with
=======
let init : Prims.unit  ->  Prims.unit = (fun _81_298 -> (match (()) with
>>>>>>> origin
| () -> begin
(

let n_runners = ((FStar_Options.n_cores ()) - 1)
in (

let rec aux = (fun n -> if (n = 0) then begin
()
end else begin
(

<<<<<<< HEAD
let _80_304 = (FStar_Util.spawn dequeue)
=======
let _81_302 = (FStar_Util.spawn dequeue)
>>>>>>> origin
in (aux (n - 1)))
end)
in (aux n_runners)))
end))


let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(

<<<<<<< HEAD
let _80_308 = (FStar_Util.monitor_enter job_queue)
in (

let _80_310 = (let _170_276 = (let _170_275 = (FStar_ST.read job_queue)
in (FStar_List.append _170_275 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _170_276))
in (

let _80_312 = (FStar_Util.monitor_pulse job_queue)
=======
let _81_306 = (FStar_Util.monitor_enter job_queue)
in (

let _81_308 = (let _172_276 = (let _172_275 = (FStar_ST.read job_queue)
in (FStar_List.append _172_275 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _172_276))
in (

let _81_310 = (FStar_Util.monitor_pulse job_queue)
>>>>>>> origin
in (FStar_Util.monitor_exit job_queue))))
end)


<<<<<<< HEAD
let finish : Prims.unit  ->  Prims.unit = (fun _80_314 -> (match (()) with
=======
let finish : Prims.unit  ->  Prims.unit = (fun _81_312 -> (match (()) with
>>>>>>> origin
| () -> begin
(

let bg = (bg_z3_proc.grab ())
in (

<<<<<<< HEAD
let _80_316 = (FStar_Util.kill_process bg)
in (

let _80_318 = (bg_z3_proc.release ())
in (

let rec aux = (fun _80_321 -> (match (()) with
| () -> begin
(

let _80_325 = (with_monitor job_queue (fun _80_322 -> (match (()) with
=======
let _81_314 = (FStar_Util.kill_process bg)
in (

let _81_316 = (bg_z3_proc.release ())
in (

let rec aux = (fun _81_319 -> (match (()) with
| () -> begin
(

let _81_323 = (with_monitor job_queue (fun _81_320 -> (match (()) with
>>>>>>> origin
| () -> begin
(let _172_284 = (FStar_ST.read pending_jobs)
in (let _172_283 = (let _172_282 = (FStar_ST.read job_queue)
in (FStar_List.length _172_282))
in (_172_284, _172_283)))
end)))
<<<<<<< HEAD
in (match (_80_325) with
=======
in (match (_81_323) with
>>>>>>> origin
| (n, m) -> begin
if ((n + m) = 0) then begin
(let _172_285 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _172_285 Prims.ignore))
end else begin
(

<<<<<<< HEAD
let _80_326 = (FStar_Util.sleep 500)
=======
let _81_324 = (FStar_Util.sleep 500)
>>>>>>> origin
in (aux ()))
end
end))
end))
in (aux ())))))
end))


type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list


let fresh_scope : FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : Prims.string  ->  Prims.unit = (fun msg -> (

<<<<<<< HEAD
let _80_329 = (let _170_289 = (let _170_288 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::[])::_170_288)
in (FStar_ST.op_Colon_Equals fresh_scope _170_289))
in (let _170_291 = (let _170_290 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[]) _170_290))
in (FStar_ST.op_Colon_Equals bg_scope _170_291))))
=======
let _81_327 = (let _172_289 = (let _172_288 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::[])::_172_288)
in (FStar_ST.op_Colon_Equals fresh_scope _172_289))
in (let _172_291 = (let _172_290 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[]) _172_290))
in (FStar_ST.op_Colon_Equals bg_scope _172_291))))
>>>>>>> origin


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

<<<<<<< HEAD
let _80_332 = (let _170_295 = (let _170_294 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _170_294))
in (FStar_ST.op_Colon_Equals fresh_scope _170_295))
in (let _170_297 = (let _170_296 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[]) _170_296))
in (FStar_ST.op_Colon_Equals bg_scope _170_297))))
=======
let _81_330 = (let _172_295 = (let _172_294 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _172_294))
in (FStar_ST.op_Colon_Equals fresh_scope _172_295))
in (let _172_297 = (let _172_296 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[]) _172_296))
in (FStar_ST.op_Colon_Equals bg_scope _172_297))))
>>>>>>> origin


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (

<<<<<<< HEAD
let _80_340 = (match ((FStar_ST.read fresh_scope)) with
| (hd)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _80_339 -> begin
=======
let _81_338 = (match ((FStar_ST.read fresh_scope)) with
| (hd)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _81_337 -> begin
>>>>>>> origin
(FStar_All.failwith "Impossible")
end)
in (let _172_301 = (let _172_300 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _172_300))
in (FStar_ST.op_Colon_Equals bg_scope _172_301))))


let bgtheory : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun fresh -> if fresh then begin
(let _172_305 = (let _172_304 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _172_304))
in (FStar_All.pipe_right _172_305 FStar_List.flatten))
end else begin
(

let bg = (FStar_ST.read bg_scope)
in (

<<<<<<< HEAD
let _80_344 = (FStar_ST.op_Colon_Equals bg_scope [])
=======
let _81_342 = (FStar_ST.op_Colon_Equals bg_scope [])
>>>>>>> origin
in (FStar_List.rev bg)))
end)


<<<<<<< HEAD
let refresh : Prims.unit  ->  Prims.unit = (fun _80_346 -> (match (()) with
| () -> begin
(

let _80_347 = (bg_z3_proc.refresh ())
=======
let refresh : Prims.unit  ->  Prims.unit = (fun _81_344 -> (match (()) with
| () -> begin
(

let _81_345 = (bg_z3_proc.refresh ())
>>>>>>> origin
in (

let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

<<<<<<< HEAD
let _80_352 = (pop msg)
=======
let _81_350 = (pop msg)
>>>>>>> origin
in (refresh ())))


let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| (hd)::(s)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
<<<<<<< HEAD
| _80_361 -> begin
=======
| _81_359 -> begin
>>>>>>> origin
(FStar_All.failwith "Impossible")
end))


let ask : Prims.bool  ->  unsat_core  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  (((unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either * Prims.int)  ->  Prims.unit)  ->  Prims.unit = (fun fresh core label_messages qry cb -> (

let filter_assertions = (fun theory -> (match (core) with
| None -> begin
(theory, false)
end
| Some (core) -> begin
(

<<<<<<< HEAD
let _80_390 = (FStar_List.fold_right (fun d _80_376 -> (match (_80_376) with
| (theory, n_retained, n_pruned) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (_80_378, _80_380, Some (name)) -> begin
=======
let _81_388 = (FStar_List.fold_right (fun d _81_374 -> (match (_81_374) with
| (theory, n_retained, n_pruned) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (_81_376, _81_378, Some (name)) -> begin
>>>>>>> origin
if (FStar_List.contains name core) then begin
((d)::theory, (n_retained + 1), n_pruned)
end else begin
if (FStar_Util.starts_with name "@") then begin
((d)::theory, n_retained, n_pruned)
end else begin
(theory, n_retained, (n_pruned + 1))
end
end
end
<<<<<<< HEAD
| _80_386 -> begin
((d)::theory, n_retained, n_pruned)
end)
end)) theory ([], 0, 0))
in (match (_80_390) with
| (theory', n_retained, n_pruned) -> begin
(

let missed_assertions = (fun th core -> (

let missed = (let _170_339 = (FStar_All.pipe_right core (FStar_List.filter (fun nm -> (let _170_338 = (FStar_All.pipe_right th (FStar_Util.for_some (fun _80_3 -> (match (_80_3) with
| FStar_SMTEncoding_Term.Assume (_80_397, _80_399, Some (nm')) -> begin
(nm = nm')
end
| _80_405 -> begin
false
end))))
in (FStar_All.pipe_right _170_338 Prims.op_Negation)))))
in (FStar_All.pipe_right _170_339 (FStar_String.concat ", ")))
in (

let included = (let _170_341 = (FStar_All.pipe_right th (FStar_List.collect (fun _80_4 -> (match (_80_4) with
| FStar_SMTEncoding_Term.Assume (_80_409, _80_411, Some (nm)) -> begin
(nm)::[]
end
| _80_417 -> begin
[]
end))))
in (FStar_All.pipe_right _170_341 (FStar_String.concat ", ")))
in (FStar_Util.format2 "missed={%s}; included={%s}" missed included))))
in (

let _80_421 = if (FStar_Options.hint_info ()) then begin
(

let n = (FStar_List.length core)
in (

let missed = if (n <> n_retained) then begin
(missed_assertions theory' core)
end else begin
""
end
in (let _170_345 = (FStar_Util.string_of_int n_retained)
in (let _170_344 = if (n <> n_retained) then begin
(let _170_342 = (FStar_Util.string_of_int n)
in (FStar_Util.format2 " (expected %s (%s); replay may be inaccurate)" _170_342 missed))
end else begin
""
end
in (let _170_343 = (FStar_Util.string_of_int n_pruned)
in (FStar_Util.print3 "Hint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n" _170_345 _170_344 _170_343))))))
end else begin
()
end
in (let _170_350 = (let _170_349 = (let _170_348 = (let _170_347 = (let _170_346 = (FStar_All.pipe_right core (FStar_String.concat ", "))
in (Prims.strcat "UNSAT CORE: " _170_346))
in FStar_SMTEncoding_Term.Caption (_170_347))
in (_170_348)::[])
in (FStar_List.append theory' _170_349))
in (_170_350, true))))
=======
| _81_384 -> begin
((d)::theory, n_retained, n_pruned)
end)
end)) theory ([], 0, 0))
in (match (_81_388) with
| (theory', n_retained, n_pruned) -> begin
(

let _81_390 = if (FStar_Options.hint_info ()) then begin
(

let n = (FStar_List.length core)
in (let _172_335 = (FStar_Util.string_of_int n_retained)
in (let _172_334 = if (n <> n_retained) then begin
(let _172_332 = (FStar_Util.string_of_int n)
in (FStar_Util.format1 " (expected %s; replay may be inaccurate)" _172_332))
end else begin
""
end
in (let _172_333 = (FStar_Util.string_of_int n_pruned)
in (FStar_Util.print3 "Hint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n" _172_335 _172_334 _172_333)))))
end else begin
()
end
in (let _172_340 = (let _172_339 = (let _172_338 = (let _172_337 = (let _172_336 = (FStar_All.pipe_right core (FStar_String.concat ", "))
in (Prims.strcat "UNSAT CORE: " _172_336))
in FStar_SMTEncoding_Term.Caption (_172_337))
in (_172_338)::[])
in (FStar_List.append theory' _172_339))
in (_172_340, true)))
>>>>>>> origin
end))
end))
in (

let theory = (bgtheory fresh)
in (

let theory = if fresh then begin
(FStar_List.append theory qry)
end else begin
(FStar_List.append (FStar_List.append (FStar_List.append theory ((FStar_SMTEncoding_Term.Push)::[])) qry) ((FStar_SMTEncoding_Term.Pop)::[]))
end
in (

<<<<<<< HEAD
let _80_427 = (filter_assertions theory)
in (match (_80_427) with
| (theory, used_unsat_core) -> begin
(

let cb = (fun _80_431 -> (match (_80_431) with
| (uc_errs, time) -> begin
if used_unsat_core then begin
(match (uc_errs) with
| FStar_Util.Inl (_80_433) -> begin
(cb (uc_errs, time))
end
| FStar_Util.Inr (_80_436) -> begin
=======
let _81_396 = (filter_assertions theory)
in (match (_81_396) with
| (theory, used_unsat_core) -> begin
(

let cb = (fun _81_400 -> (match (_81_400) with
| (uc_errs, time) -> begin
if used_unsat_core then begin
(match (uc_errs) with
| FStar_Util.Inl (_81_402) -> begin
(cb (uc_errs, time))
end
| FStar_Util.Inr (_81_405) -> begin
>>>>>>> origin
(cb (FStar_Util.Inr ([]), time))
end)
end else begin
(cb (uc_errs, time))
end
end))
in (

<<<<<<< HEAD
let input = (let _170_353 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ())) theory)
in (FStar_All.pipe_right _170_353 (FStar_String.concat "\n")))
in (

let _80_439 = if (FStar_Options.log_queries ()) then begin
=======
let input = (let _172_343 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ())) theory)
in (FStar_All.pipe_right _172_343 (FStar_String.concat "\n")))
in (

let _81_408 = if (FStar_Options.log_queries ()) then begin
>>>>>>> origin
(log_query fresh input)
end else begin
()
end
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb}))))
end))))))




