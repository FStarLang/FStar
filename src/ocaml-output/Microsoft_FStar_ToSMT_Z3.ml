
type z3version =
| Z3V_Unknown
| Z3V of (int * int * int)

let z3v_compare = (fun known _421977 -> (match (_421977) with
| (w1, w2, w3) -> begin
(match (known) with
| Z3V_Unknown -> begin
None
end
| Z3V ((k1, k2, k3)) -> begin
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

let z3v_le = (fun known wanted -> (match ((z3v_compare known wanted)) with
| None -> begin
false
end
| Some (i) -> begin
(i >= 0)
end))

let _z3version = (Support.Microsoft.FStar.Util.mk_ref None)

let get_z3version = (fun _421989 -> (match (_421989) with
| () -> begin
(let prefix = "Z3 version "
in (match ((! (_z3version))) with
| Some (version) -> begin
version
end
| None -> begin
(let _421999 = (Support.Microsoft.FStar.Util.run_proc (! (Microsoft_FStar_Options.z3_exe)) "-version" "")
in (match (_421999) with
| (_, out, _) -> begin
(let out = (match ((Support.Microsoft.FStar.Util.splitlines out)) with
| x::_ when (Support.Microsoft.FStar.Util.starts_with x prefix) -> begin
(let x = (Support.Microsoft.FStar.Util.trim_string (Support.Microsoft.FStar.Util.substring_from x (Support.String.length prefix)))
in (let x = (Support.Prims.try_with (fun _422006 -> (match (_422006) with
| () -> begin
(Support.List.map Support.Microsoft.FStar.Util.int_of_string (Support.Microsoft.FStar.Util.split x "."))
end)) (fun _422005 -> []))
in (match (x) with
| i1::i2::i3::[] -> begin
Z3V ((i1, i2, i3))
end
| _ -> begin
Z3V_Unknown
end)))
end
| _ -> begin
Z3V_Unknown
end)
in (let _422022 = (_z3version := Some (out))
in out))
end))
end))
end))

let ini_params = (fun _422024 -> (match (_422024) with
| () -> begin
(let t = if (z3v_le (get_z3version ()) (4, 3, 1)) then begin
(! (Microsoft_FStar_Options.z3timeout))
end else begin
((! (Microsoft_FStar_Options.z3timeout)) * 1000)
end
in (let timeout = (Support.Microsoft.FStar.Util.format1 "-t:%s" (Support.Microsoft.FStar.Util.string_of_int t))
in (let relevancy = if (z3v_le (get_z3version ()) (4, 3, 1)) then begin
"RELEVANCY"
end else begin
"SMT.RELEVANCY"
end
in (Support.Microsoft.FStar.Util.format2 "-smt2 -in %s AUTO_CONFIG=false MODEL=true %s=2" timeout relevancy))))
end))

type z3status =
| SAT
| UNSAT
| UNKNOWN
| TIMEOUT

let status_to_string = (fun _421970 -> (match (_421970) with
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

let tid = (fun _422033 -> (match (_422033) with
| () -> begin
(Support.Microsoft.FStar.Util.string_of_int (Support.Microsoft.FStar.Util.current_tid ()))
end))

let new_z3proc = (fun id -> (let cond = (fun pid s -> (let x = ((Support.Microsoft.FStar.Util.trim_string s) = "Done!")
in x))
in (Support.Microsoft.FStar.Util.start_process id (! (Microsoft_FStar_Options.z3_exe)) (ini_params ()) cond)))

type bgproc =
{grab : unit  ->  Support.Microsoft.FStar.Util.proc; release : unit  ->  unit; refresh : unit  ->  unit}

let queries_dot_smt2 = (Support.Microsoft.FStar.Util.mk_ref None)

let get_qfile = (let ctr = (Support.Microsoft.FStar.Util.mk_ref 0)
in (fun fresh -> if fresh then begin
(let _422045 = (Support.Microsoft.FStar.Util.incr ctr)
in (Support.Microsoft.FStar.Util.open_file_for_writing (Support.Microsoft.FStar.Util.format1 "queries-%s.smt2" (Support.Microsoft.FStar.Util.string_of_int (! (ctr))))))
end else begin
(match ((! (queries_dot_smt2))) with
| None -> begin
(let fh = (Support.Microsoft.FStar.Util.open_file_for_writing "queries-bg-0.smt2")
in (let _422049 = (queries_dot_smt2 := Some (fh))
in fh))
end
| Some (fh) -> begin
fh
end)
end))

let log_query = (fun fresh i -> (let fh = (get_qfile fresh)
in (let _422056 = (Support.Microsoft.FStar.Util.append_to_file fh i)
in if fresh then begin
(Support.Microsoft.FStar.Util.close_file fh)
end)))

let bg_z3_proc = (let ctr = (Support.Microsoft.FStar.Util.mk_ref (- (1)))
in (let new_proc = (fun _422060 -> (match (_422060) with
| () -> begin
(new_z3proc (Support.Microsoft.FStar.Util.format1 "bg-%s" (let _422061 = (Support.Microsoft.FStar.Util.incr ctr)
in (Support.Microsoft.FStar.Util.string_of_int (! (ctr))))))
end))
in (let z3proc = (Support.Microsoft.FStar.Util.mk_ref (new_proc ()))
in (let x = []
in (let grab = (fun _422066 -> (match (_422066) with
| () -> begin
(let _422067 = (Support.Microsoft.FStar.Util.monitor_enter x)
in (! (z3proc)))
end))
in (let release = (fun _422070 -> (match (_422070) with
| () -> begin
(Support.Microsoft.FStar.Util.monitor_exit x)
end))
in (let refresh = (fun _422072 -> (match (_422072) with
| () -> begin
(let proc = (grab ())
in (let _422074 = (Support.Microsoft.FStar.Util.kill_process proc)
in (let _422076 = (z3proc := (new_proc ()))
in (let _422084 = (match ((! (queries_dot_smt2))) with
| None -> begin
()
end
| Some (fh) -> begin
(let _422081 = (Support.Microsoft.FStar.Util.close_file fh)
in (let fh = (Support.Microsoft.FStar.Util.open_file_for_writing (Support.Microsoft.FStar.Util.format1 "queries-bg-%s.smt2" (Support.Microsoft.FStar.Util.string_of_int (! (ctr)))))
in (queries_dot_smt2 := Some (fh))))
end)
in (release ())))))
end))
in {grab = grab; release = release; refresh = refresh})))))))

let doZ3Exe' = (fun input z3proc -> (let parse = (fun z3out -> (let lines = ((Support.List.map Support.Microsoft.FStar.Util.trim_string) (Support.String.split (('\n')::[]) z3out))
in (let rec lblnegs = (fun lines -> (match (lines) with
| lname::"false"::rest -> begin
(lname)::(lblnegs rest)
end
| lname::_::rest -> begin
(lblnegs rest)
end
| _ -> begin
[]
end))
in (let rec result = (fun x -> (match (x) with
| "timeout"::tl -> begin
(TIMEOUT, [])
end
| "unknown"::tl -> begin
(UNKNOWN, (lblnegs tl))
end
| "sat"::tl -> begin
(SAT, (lblnegs tl))
end
| "unsat"::tl -> begin
(UNSAT, [])
end
| _::tl -> begin
(result tl)
end
| _ -> begin
((failwith) (Support.Microsoft.FStar.Util.format1 "Got output lines: %s\n" (Support.String.concat "\n" (Support.List.map (fun l -> (Support.Microsoft.FStar.Util.format1 "<%s>" (Support.Microsoft.FStar.Util.trim_string l))) lines))))
end))
in (result lines)))))
in (let stdout = (Support.Microsoft.FStar.Util.ask_process z3proc input)
in (parse (Support.Microsoft.FStar.Util.trim_string stdout)))))

let doZ3Exe = (let ctr = (Support.Microsoft.FStar.Util.mk_ref 0)
in (fun fresh input -> (let z3proc = if fresh then begin
(let _422131 = (Support.Microsoft.FStar.Util.incr ctr)
in (new_z3proc (Support.Microsoft.FStar.Util.string_of_int (! (ctr)))))
end else begin
(bg_z3_proc.grab ())
end
in (let res = (doZ3Exe' input z3proc)
in (let _422135 = if fresh then begin
(Support.Microsoft.FStar.Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))

let z3_options = (fun _422137 -> (match (_422137) with
| () -> begin
(let mbqi = if (z3v_le (get_z3version ()) (4, 3, 1)) then begin
"mbqi"
end else begin
"smt.mbqi"
end
in (let model_on_timeout = if (z3v_le (get_z3version ()) (4, 3, 1)) then begin
"(set-option :model-on-timeout true)\n"
end else begin
""
end
in (Support.String.strcat (Support.String.strcat (Support.String.strcat (Support.String.strcat "(set-option :global-decls false)\n" "(set-option :") mbqi) " false)\n") model_on_timeout)))
end))

type 'a job =
{job : unit  ->  'a; callback : 'a  ->  unit}

type z3job =
(bool * (string * Support.Microsoft.FStar.Range.range) list) job

let job_queue = (let x = (Support.Microsoft.FStar.Util.mk_ref (({job = (fun _422144 -> (match (_422144) with
| () -> begin
(false, (("", (Support.Microsoft.FStar.Range.mk_range "" 0 0)))::[])
end)); callback = (fun a -> ())})::[]))
in (let _422147 = (x := [])
in x))

let pending_jobs = (Support.Microsoft.FStar.Util.mk_ref 0)

let with_monitor = (fun m f -> (let _422151 = (Support.Microsoft.FStar.Util.monitor_enter m)
in (let res = (f ())
in (let _422154 = (Support.Microsoft.FStar.Util.monitor_exit m)
in res))))

let z3_job = (fun fresh label_messages input _422159 -> (match (_422159) with
| () -> begin
(let _422162 = (doZ3Exe fresh input)
in (match (_422162) with
| (status, lblnegs) -> begin
(let result = (match (status) with
| UNSAT -> begin
(true, [])
end
| _ -> begin
(let _422166 = if ((! (Microsoft_FStar_Options.debug)) <> []) then begin
(Support.Microsoft.FStar.Util.print_string (Support.Microsoft.FStar.Util.format1 "Z3 says: %s\n" (status_to_string status)))
end
in (let failing_assertions = ((Support.List.collect (fun l -> (match (((Support.List.tryFind (fun _422174 -> (match (_422174) with
| (m, _, _) -> begin
((Support.Prims.fst m) = l)
end))) label_messages)) with
| None -> begin
[]
end
| Some ((_, msg, r)) -> begin
((msg, r))::[]
end))) lblnegs)
in (false, failing_assertions)))
end)
in result)
end))
end))

let rec dequeue' = (fun _422184 -> (match (_422184) with
| () -> begin
(let j = (match ((! (job_queue))) with
| [] -> begin
(failwith "Impossible")
end
| hd::tl -> begin
(let _422189 = (job_queue := tl)
in hd)
end)
in (let _422192 = (Support.Microsoft.FStar.Util.incr pending_jobs)
in (let _422194 = (Support.Microsoft.FStar.Util.monitor_exit job_queue)
in (let _422196 = (run_job j)
in (let _422199 = (with_monitor job_queue (fun _422198 -> (match (_422198) with
| () -> begin
(Support.Microsoft.FStar.Util.decr pending_jobs)
end)))
in (dequeue ()))))))
end))
and dequeue = (fun _422201 -> (match (_422201) with
| () -> begin
(let _422202 = (Support.Microsoft.FStar.Util.monitor_enter job_queue)
in (let rec aux = (fun _422205 -> (match (_422205) with
| () -> begin
(match ((! (job_queue))) with
| [] -> begin
(let _422207 = (Support.Microsoft.FStar.Util.monitor_wait job_queue)
in (aux ()))
end
| _ -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job = (fun j -> (j.callback (j.job ())))

let init = (fun _422212 -> (match (_422212) with
| () -> begin
(let n_runners = ((! (Microsoft_FStar_Options.n_cores)) - 1)
in (let rec aux = (fun n -> if (n = 0) then begin
()
end else begin
(let _422216 = (Support.Microsoft.FStar.Util.spawn (dequeue))
in (aux (n - 1)))
end)
in (aux n_runners)))
end))

let enqueue = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(let _422220 = (Support.Microsoft.FStar.Util.monitor_enter job_queue)
in (let _422222 = (job_queue := (Support.List.append (! (job_queue)) ((j)::[])))
in (let _422224 = (Support.Microsoft.FStar.Util.monitor_pulse job_queue)
in (Support.Microsoft.FStar.Util.monitor_exit job_queue))))
end)

let finish = (fun _422226 -> (match (_422226) with
| () -> begin
(let bg = (bg_z3_proc.grab ())
in (let _422228 = (Support.Microsoft.FStar.Util.kill_process bg)
in (let _422230 = (bg_z3_proc.release ())
in (let rec aux = (fun _422233 -> (match (_422233) with
| () -> begin
(let _422237 = (with_monitor job_queue (fun _422234 -> (match (_422234) with
| () -> begin
((! (pending_jobs)), (Support.List.length (! (job_queue))))
end)))
in (match (_422237) with
| (n, m) -> begin
if ((n + m) = 0) then begin
((Support.Prims.ignore) (Microsoft_FStar_Tc_Errors.report_all ()))
end else begin
(let _422238 = (Support.Microsoft.FStar.Util.sleep 500)
in (aux ()))
end
end))
end))
in (aux ())))))
end))

type scope_t =
Microsoft_FStar_ToSMT_Term.decl list list

let fresh_scope = (Support.Microsoft.FStar.Util.mk_ref (([])::[]))

let bg_scope = (Support.Microsoft.FStar.Util.mk_ref [])

let push = (fun msg -> (let _422241 = (fresh_scope := ((Microsoft_FStar_ToSMT_Term.Caption (msg))::[])::(! (fresh_scope)))
in (bg_scope := (Support.List.append ((Microsoft_FStar_ToSMT_Term.Caption (msg))::(Microsoft_FStar_ToSMT_Term.Push)::[]) (! (bg_scope))))))

let pop = (fun msg -> (let _422244 = (fresh_scope := (Support.List.tl (! (fresh_scope))))
in (bg_scope := (Support.List.append ((Microsoft_FStar_ToSMT_Term.Caption (msg))::(Microsoft_FStar_ToSMT_Term.Pop)::[]) (! (bg_scope))))))

let giveZ3 = (fun decls -> (let _422252 = (match ((! (fresh_scope))) with
| hd::tl -> begin
(fresh_scope := ((Support.List.append hd decls))::tl)
end
| _ -> begin
(failwith "Impossible")
end)
in (bg_scope := (Support.List.append (Support.List.rev decls) (! (bg_scope))))))

let bgtheory = (fun fresh -> if fresh then begin
((Support.List.flatten) (Support.List.rev (! (fresh_scope))))
end else begin
(let bg = (! (bg_scope))
in (let _422256 = (bg_scope := [])
in (Support.List.rev bg)))
end)

let refresh = (fun _422258 -> (match (_422258) with
| () -> begin
(let _422259 = (bg_z3_proc.refresh ())
in (let theory = (bgtheory true)
in (bg_scope := (Support.List.rev theory))))
end))

let mark = (fun msg -> (push msg))

let reset_mark = (fun msg -> (let _422264 = (pop msg)
in (refresh ())))

let commit_mark = (fun msg -> (match ((! (fresh_scope))) with
| hd::s::tl -> begin
(fresh_scope := ((Support.List.append hd s))::tl)
end
| _ -> begin
(failwith "Impossible")
end))

let ask = (fun fresh label_messages qry cb -> (let fresh = (fresh && ((! (Microsoft_FStar_Options.n_cores)) > 1))
in (let theory = (bgtheory fresh)
in (let theory = if fresh then begin
(Support.List.append theory qry)
end else begin
(Support.List.append (Support.List.append (Support.List.append theory ((Microsoft_FStar_ToSMT_Term.Push)::[])) qry) ((Microsoft_FStar_ToSMT_Term.Pop)::[]))
end
in (let input = ((Support.String.concat "\n") (Support.List.map (Microsoft_FStar_ToSMT_Term.declToSmt (z3_options ())) theory))
in (let _422282 = if (! (Microsoft_FStar_Options.logQueries)) then begin
(log_query fresh input)
end
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb})))))))




