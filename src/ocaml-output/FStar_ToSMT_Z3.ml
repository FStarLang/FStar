
open Prims
# 26 "z3.fs"
type z3version =
| Z3V_Unknown
| Z3V of (Prims.int * Prims.int * Prims.int)

# 27 "z3.fs"
let is_Z3V_Unknown = (fun _discr_ -> (match (_discr_) with
| Z3V_Unknown (_) -> begin
true
end
| _ -> begin
false
end))

# 28 "z3.fs"
let is_Z3V = (fun _discr_ -> (match (_discr_) with
| Z3V (_) -> begin
true
end
| _ -> begin
false
end))

# 28 "z3.fs"
let ___Z3V____0 : z3version  ->  (Prims.int * Prims.int * Prims.int) = (fun projectee -> (match (projectee) with
| Z3V (_56_4) -> begin
_56_4
end))

# 30 "z3.fs"
let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _56_9 -> (match (_56_9) with
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

# 39 "z3.fs"
let z3v_le : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.bool = (fun known wanted -> (match ((z3v_compare known wanted)) with
| None -> begin
false
end
| Some (i) -> begin
(i >= 0)
end))

# 44 "z3.fs"
let _z3version : z3version Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 46 "z3.fs"
let get_z3version : Prims.unit  ->  z3version = (fun _56_21 -> (match (()) with
| () -> begin
(
# 47 "z3.fs"
let prefix = "Z3 version "
in (match ((FStar_ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(
# 52 "z3.fs"
let _56_31 = (let _158_26 = (FStar_ST.read FStar_Options.z3_exe)
in (FStar_Util.run_proc _158_26 "-version" ""))
in (match (_56_31) with
| (_56_27, out, _56_30) -> begin
(
# 53 "z3.fs"
let out = (match ((FStar_Util.splitlines out)) with
| x::_56_33 when (FStar_Util.starts_with x prefix) -> begin
(
# 56 "z3.fs"
let x = (let _158_27 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _158_27))
in (
# 57 "z3.fs"
let x = (FStar_All.try_with (fun _56_38 -> (match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)) (fun _56_37 -> (match (_56_37) with
| _56_41 -> begin
[]
end)))
in (match (x) with
| i1::i2::i3::[] -> begin
Z3V ((i1, i2, i3))
end
| _56_50 -> begin
Z3V_Unknown
end)))
end
| _56_52 -> begin
Z3V_Unknown
end)
in (
# 64 "z3.fs"
let _56_54 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))

# 66 "z3.fs"
let ini_params : Prims.unit  ->  Prims.string = (fun _56_56 -> (match (()) with
| () -> begin
(
# 67 "z3.fs"
let t = if (let _158_32 = (get_z3version ())
in (z3v_le _158_32 (4, 3, 1))) then begin
(FStar_ST.read FStar_Options.z3timeout)
end else begin
((FStar_ST.read FStar_Options.z3timeout) * 1000)
end
in (
# 72 "z3.fs"
let timeout = (let _158_33 = (FStar_Util.string_of_int t)
in (FStar_Util.format1 "-t:%s" _158_33))
in (
# 73 "z3.fs"
let relevancy = if (let _158_34 = (get_z3version ())
in (z3v_le _158_34 (4, 3, 1))) then begin
"RELEVANCY"
end else begin
"SMT.RELEVANCY"
end
in (FStar_Util.format2 "-smt2 -in %s AUTO_CONFIG=false MODEL=true %s=2" timeout relevancy))))
end))

# 84 "z3.fs"
type z3status =
| SAT
| UNSAT
| UNKNOWN
| TIMEOUT

# 85 "z3.fs"
let is_SAT = (fun _discr_ -> (match (_discr_) with
| SAT (_) -> begin
true
end
| _ -> begin
false
end))

# 86 "z3.fs"
let is_UNSAT = (fun _discr_ -> (match (_discr_) with
| UNSAT (_) -> begin
true
end
| _ -> begin
false
end))

# 87 "z3.fs"
let is_UNKNOWN = (fun _discr_ -> (match (_discr_) with
| UNKNOWN (_) -> begin
true
end
| _ -> begin
false
end))

# 88 "z3.fs"
let is_TIMEOUT = (fun _discr_ -> (match (_discr_) with
| TIMEOUT (_) -> begin
true
end
| _ -> begin
false
end))

# 90 "z3.fs"
let status_to_string : z3status  ->  Prims.string = (fun _56_1 -> (match (_56_1) with
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

# 96 "z3.fs"
let tid : Prims.unit  ->  Prims.string = (fun _56_65 -> (match (()) with
| () -> begin
(let _158_43 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _158_43 FStar_Util.string_of_int))
end))

# 97 "z3.fs"
let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (
# 98 "z3.fs"
let cond = (fun pid s -> (
# 99 "z3.fs"
let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (let _158_51 = (FStar_ST.read FStar_Options.z3_exe)
in (let _158_50 = (ini_params ())
in (FStar_Util.start_process id _158_51 _158_50 cond)))))

# 104 "z3.fs"
type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}

# 104 "z3.fs"
let is_Mkbgproc : bgproc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbgproc"))))

# 111 "z3.fs"
let queries_dot_smt2 : FStar_Util.file_handle Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)

# 113 "z3.fs"
let get_qfile : Prims.bool  ->  FStar_Util.file_handle = (
# 114 "z3.fs"
let ctr = (FStar_Util.mk_ref 0)
in (fun fresh -> if fresh then begin
(
# 117 "z3.fs"
let _56_77 = (FStar_Util.incr ctr)
in (let _158_84 = (let _158_83 = (let _158_82 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _158_82))
in (FStar_Util.format1 "queries-%s.smt2" _158_83))
in (FStar_Util.open_file_for_writing _158_84)))
end else begin
(match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
(
# 120 "z3.fs"
let fh = (FStar_Util.open_file_for_writing "queries-bg-0.smt2")
in (
# 120 "z3.fs"
let _56_81 = (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
in fh))
end
| Some (fh) -> begin
fh
end)
end))

# 123 "z3.fs"
let log_query : Prims.bool  ->  Prims.string  ->  Prims.unit = (fun fresh i -> (
# 124 "z3.fs"
let fh = (get_qfile fresh)
in (
# 125 "z3.fs"
let _56_88 = (FStar_Util.append_to_file fh i)
in if fresh then begin
(FStar_Util.close_file fh)
end else begin
()
end)))

# 128 "z3.fs"
let bg_z3_proc : bgproc = (
# 129 "z3.fs"
let ctr = (FStar_Util.mk_ref (- (1)))
in (
# 130 "z3.fs"
let new_proc = (fun _56_92 -> (match (()) with
| () -> begin
(let _158_93 = (let _158_92 = (
# 130 "z3.fs"
let _56_93 = (FStar_Util.incr ctr)
in (let _158_91 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _158_91 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _158_92))
in (new_z3proc _158_93))
end))
in (
# 131 "z3.fs"
let z3proc = (let _158_94 = (new_proc ())
in (FStar_Util.mk_ref _158_94))
in (
# 132 "z3.fs"
let x = []
in (
# 133 "z3.fs"
let grab = (fun _56_98 -> (match (()) with
| () -> begin
(
# 133 "z3.fs"
let _56_99 = (FStar_Util.monitor_enter x)
in (FStar_ST.read z3proc))
end))
in (
# 134 "z3.fs"
let release = (fun _56_102 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (
# 135 "z3.fs"
let refresh = (fun _56_104 -> (match (()) with
| () -> begin
(
# 136 "z3.fs"
let proc = (grab ())
in (
# 137 "z3.fs"
let _56_106 = (FStar_Util.kill_process proc)
in (
# 138 "z3.fs"
let _56_108 = (let _158_101 = (new_proc ())
in (FStar_ST.op_Colon_Equals z3proc _158_101))
in (
# 139 "z3.fs"
let _56_116 = (match ((FStar_ST.read queries_dot_smt2)) with
| None -> begin
()
end
| Some (fh) -> begin
(
# 142 "z3.fs"
let _56_113 = (FStar_Util.close_file fh)
in (
# 143 "z3.fs"
let fh = (let _158_104 = (let _158_103 = (let _158_102 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _158_102 FStar_Util.string_of_int))
in (FStar_Util.format1 "queries-bg-%s.smt2" _158_103))
in (FStar_Util.open_file_for_writing _158_104))
in (FStar_ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))))
end)
in (release ())))))
end))
in {grab = grab; release = release; refresh = refresh})))))))

# 151 "z3.fs"
let doZ3Exe' : Prims.string  ->  FStar_Util.proc  ->  (z3status * Prims.string Prims.list) = (fun input z3proc -> (
# 152 "z3.fs"
let parse = (fun z3out -> (
# 153 "z3.fs"
let lines = (FStar_All.pipe_right (FStar_String.split (('\n')::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (
# 154 "z3.fs"
let rec lblnegs = (fun lines -> (match (lines) with
| lname::"false"::rest -> begin
(let _158_113 = (lblnegs rest)
in (lname)::_158_113)
end
| lname::_56_132::rest -> begin
(lblnegs rest)
end
| _56_137 -> begin
[]
end))
in (
# 158 "z3.fs"
let rec result = (fun x -> (match (x) with
| "timeout"::tl -> begin
(TIMEOUT, [])
end
| "unknown"::tl -> begin
(let _158_116 = (lblnegs tl)
in (UNKNOWN, _158_116))
end
| "sat"::tl -> begin
(let _158_117 = (lblnegs tl)
in (SAT, _158_117))
end
| "unsat"::tl -> begin
(UNSAT, [])
end
| _56_154::tl -> begin
(result tl)
end
| _56_157 -> begin
(let _158_121 = (let _158_120 = (let _158_119 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _158_119))
in (FStar_Util.format1 "Got output lines: %s\n" _158_120))
in (FStar_All.pipe_left FStar_All.failwith _158_121))
end))
in (result lines)))))
in (
# 166 "z3.fs"
let stdout = (FStar_Util.ask_process z3proc input)
in (parse (FStar_Util.trim_string stdout)))))

# 169 "z3.fs"
let doZ3Exe : Prims.bool  ->  Prims.string  ->  (z3status * Prims.string Prims.list) = (
# 170 "z3.fs"
let ctr = (FStar_Util.mk_ref 0)
in (fun fresh input -> (
# 172 "z3.fs"
let z3proc = if fresh then begin
(
# 172 "z3.fs"
let _56_163 = (FStar_Util.incr ctr)
in (let _158_127 = (let _158_126 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _158_126))
in (new_z3proc _158_127)))
end else begin
(bg_z3_proc.grab ())
end
in (
# 173 "z3.fs"
let res = (doZ3Exe' input z3proc)
in (
# 175 "z3.fs"
let _56_167 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))

# 178 "z3.fs"
let z3_options : Prims.unit  ->  Prims.string = (fun _56_169 -> (match (()) with
| () -> begin
(
# 179 "z3.fs"
let mbqi = if (let _158_130 = (get_z3version ())
in (z3v_le _158_130 (4, 3, 1))) then begin
"mbqi"
end else begin
"smt.mbqi"
end
in (
# 183 "z3.fs"
let model_on_timeout = if (let _158_131 = (get_z3version ())
in (z3v_le _158_131 (4, 3, 1))) then begin
"(set-option :model-on-timeout true)\n"
end else begin
""
end
in (Prims.strcat (Prims.strcat (Prims.strcat (Prims.strcat "(set-option :global-decls false)\n" "(set-option :") mbqi) " false)\n") model_on_timeout)))
end))

# 191 "z3.fs"
type 'a job =
{job : Prims.unit  ->  'a; callback : 'a  ->  Prims.unit}

# 191 "z3.fs"
let is_Mkjob = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkjob"))))

# 195 "z3.fs"
type z3job =
(Prims.bool * (Prims.string * FStar_Range.range) Prims.list) job

# 198 "z3.fs"
let job_queue : z3job Prims.list FStar_ST.ref = (
# 199 "z3.fs"
let x = (FStar_Util.mk_ref (({job = (fun _56_176 -> (match (()) with
| () -> begin
(let _158_155 = (let _158_154 = (let _158_153 = (FStar_Range.mk_range "" 0 0)
in ("", _158_153))
in (_158_154)::[])
in (false, _158_155))
end)); callback = (fun a -> ())})::[]))
in (
# 200 "z3.fs"
let _56_179 = (FStar_ST.op_Colon_Equals x [])
in x))

# 202 "z3.fs"
let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 0)

# 203 "z3.fs"
let with_monitor = (fun m f -> (
# 204 "z3.fs"
let _56_183 = (FStar_Util.monitor_enter m)
in (
# 205 "z3.fs"
let res = (f ())
in (
# 206 "z3.fs"
let _56_186 = (FStar_Util.monitor_exit m)
in res))))

# 209 "z3.fs"
let z3_job = (fun fresh label_messages input _56_191 -> (match (()) with
| () -> begin
(
# 210 "z3.fs"
let _56_194 = (doZ3Exe fresh input)
in (match (_56_194) with
| (status, lblnegs) -> begin
(
# 211 "z3.fs"
let result = (match (status) with
| UNSAT -> begin
(true, [])
end
| _56_197 -> begin
(
# 214 "z3.fs"
let _56_198 = if ((FStar_ST.read FStar_Options.debug) <> []) then begin
(let _158_166 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _158_166))
end else begin
()
end
in (
# 215 "z3.fs"
let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _56_206 -> (match (_56_206) with
| (m, _56_203, _56_205) -> begin
((Prims.fst m) = l)
end))))) with
| None -> begin
[]
end
| Some (_56_209, msg, r) -> begin
((msg, r))::[]
end))))
in (false, failing_assertions)))
end)
in result)
end))
end))

# 222 "z3.fs"
let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _56_216 -> (match (()) with
| () -> begin
(
# 223 "z3.fs"
let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| hd::tl -> begin
(
# 226 "z3.fs"
let _56_221 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (
# 228 "z3.fs"
let _56_224 = (FStar_Util.incr pending_jobs)
in (
# 229 "z3.fs"
let _56_226 = (FStar_Util.monitor_exit job_queue)
in (
# 230 "z3.fs"
let _56_228 = (run_job j)
in (
# 231 "z3.fs"
let _56_231 = (with_monitor job_queue (fun _56_230 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (
# 232 "z3.fs"
let _56_233 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _56_235 -> (match (()) with
| () -> begin
(
# 235 "z3.fs"
let _56_236 = (FStar_Util.monitor_enter job_queue)
in (
# 236 "z3.fs"
let rec aux = (fun _56_239 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(
# 238 "z3.fs"
let _56_241 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _56_244 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _158_178 = (j.job ())
in (FStar_All.pipe_left j.callback _158_178)))

# 245 "z3.fs"
let init : Prims.unit  ->  Prims.unit = (fun _56_246 -> (match (()) with
| () -> begin
(
# 246 "z3.fs"
let n_runners = ((FStar_ST.read FStar_Options.n_cores) - 1)
in (
# 247 "z3.fs"
let rec aux = (fun n -> if (n = 0) then begin
()
end else begin
(
# 249 "z3.fs"
let _56_250 = (FStar_Util.spawn dequeue)
in (aux (n - 1)))
end)
in (aux n_runners)))
end))

# 252 "z3.fs"
let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(
# 257 "z3.fs"
let _56_254 = (FStar_Util.monitor_enter job_queue)
in (
# 258 "z3.fs"
let _56_256 = (let _158_188 = (let _158_187 = (FStar_ST.read job_queue)
in (FStar_List.append _158_187 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _158_188))
in (
# 259 "z3.fs"
let _56_258 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)

# 263 "z3.fs"
let finish : Prims.unit  ->  Prims.unit = (fun _56_260 -> (match (()) with
| () -> begin
(
# 264 "z3.fs"
let bg = (bg_z3_proc.grab ())
in (
# 265 "z3.fs"
let _56_262 = (FStar_Util.kill_process bg)
in (
# 266 "z3.fs"
let _56_264 = (bg_z3_proc.release ())
in (
# 267 "z3.fs"
let rec aux = (fun _56_267 -> (match (()) with
| () -> begin
(
# 268 "z3.fs"
let _56_271 = (with_monitor job_queue (fun _56_268 -> (match (()) with
| () -> begin
(let _158_196 = (FStar_ST.read pending_jobs)
in (let _158_195 = (let _158_194 = (FStar_ST.read job_queue)
in (FStar_List.length _158_194))
in (_158_196, _158_195)))
end)))
in (match (_56_271) with
| (n, m) -> begin
if ((n + m) = 0) then begin
(let _158_197 = (FStar_Tc_Errors.report_all ())
in (FStar_All.pipe_right _158_197 Prims.ignore))
end else begin
(
# 272 "z3.fs"
let _56_272 = (FStar_Util.sleep 500)
in (aux ()))
end
end))
end))
in (aux ())))))
end))

# 276 "z3.fs"
type scope_t =
FStar_ToSMT_Term.decl Prims.list Prims.list

# 277 "z3.fs"
let fresh_scope : FStar_ToSMT_Term.decl Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))

# 278 "z3.fs"
let bg_scope : FStar_ToSMT_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])

# 279 "z3.fs"
let push : Prims.string  ->  Prims.unit = (fun msg -> (
# 280 "z3.fs"
let _56_275 = (let _158_201 = (let _158_200 = (FStar_ST.read fresh_scope)
in ((FStar_ToSMT_Term.Caption (msg))::[])::_158_200)
in (FStar_ST.op_Colon_Equals fresh_scope _158_201))
in (let _158_203 = (let _158_202 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::(FStar_ToSMT_Term.Push)::[]) _158_202))
in (FStar_ST.op_Colon_Equals bg_scope _158_203))))

# 282 "z3.fs"
let pop : Prims.string  ->  Prims.unit = (fun msg -> (
# 283 "z3.fs"
let _56_278 = (let _158_207 = (let _158_206 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _158_206))
in (FStar_ST.op_Colon_Equals fresh_scope _158_207))
in (let _158_209 = (let _158_208 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_ToSMT_Term.Caption (msg))::(FStar_ToSMT_Term.Pop)::[]) _158_208))
in (FStar_ST.op_Colon_Equals bg_scope _158_209))))

# 285 "z3.fs"
let giveZ3 : FStar_ToSMT_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (
# 286 "z3.fs"
let _56_286 = (match ((FStar_ST.read fresh_scope)) with
| hd::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _56_285 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _158_213 = (let _158_212 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _158_212))
in (FStar_ST.op_Colon_Equals bg_scope _158_213))))

# 290 "z3.fs"
let bgtheory : Prims.bool  ->  FStar_ToSMT_Term.decl Prims.list = (fun fresh -> if fresh then begin
(let _158_217 = (let _158_216 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _158_216))
in (FStar_All.pipe_right _158_217 FStar_List.flatten))
end else begin
(
# 293 "z3.fs"
let bg = (FStar_ST.read bg_scope)
in (
# 294 "z3.fs"
let _56_290 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)

# 296 "z3.fs"
let refresh : Prims.unit  ->  Prims.unit = (fun _56_292 -> (match (()) with
| () -> begin
(
# 297 "z3.fs"
let _56_293 = (bg_z3_proc.refresh ())
in (
# 298 "z3.fs"
let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))

# 300 "z3.fs"
let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))

# 302 "z3.fs"
let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (
# 303 "z3.fs"
let _56_298 = (pop msg)
in (refresh ())))

# 305 "z3.fs"
let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| hd::s::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _56_307 -> begin
(FStar_All.failwith "Impossible")
end))

# 310 "z3.fs"
let ask = (fun fresh label_messages qry cb -> (
# 311 "z3.fs"
let fresh = (fresh && ((FStar_ST.read FStar_Options.n_cores) > 1))
in (
# 312 "z3.fs"
let theory = (bgtheory fresh)
in (
# 313 "z3.fs"
let theory = if fresh then begin
(FStar_List.append theory qry)
end else begin
(FStar_List.append (FStar_List.append (FStar_List.append theory ((FStar_ToSMT_Term.Push)::[])) qry) ((FStar_ToSMT_Term.Pop)::[]))
end
in (
# 317 "z3.fs"
let input = (let _158_234 = (let _158_233 = (let _158_232 = (z3_options ())
in (FStar_ToSMT_Term.declToSmt _158_232))
in (FStar_List.map _158_233 theory))
in (FStar_All.pipe_right _158_234 (FStar_String.concat "\n")))
in (
# 318 "z3.fs"
let _56_316 = if (FStar_ST.read FStar_Options.logQueries) then begin
(log_query fresh input)
end else begin
()
end
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb})))))))




