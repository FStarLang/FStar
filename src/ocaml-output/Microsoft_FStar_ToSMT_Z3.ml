
type z3version =
| Z3V_Unknown
| Z3V of (int * int * int)

let is_Z3V_Unknown = (fun ( _discr_ ) -> (match (_discr_) with
| Z3V_Unknown -> begin
true
end
| _ -> begin
false
end))

let is_Z3V = (fun ( _discr_ ) -> (match (_discr_) with
| Z3V (_) -> begin
true
end
| _ -> begin
false
end))

let z3v_compare = (fun ( known  :  z3version ) ( _48_8  :  (int * int * int) ) -> (match (_48_8) with
| (w1, w2, w3) -> begin
(match (known) with
| Z3V_Unknown -> begin
None
end
| Z3V ((k1, k2, k3)) -> begin
Some ((match ((k1 <> w1)) with
| true -> begin
(w1 - k1)
end
| false -> begin
(match ((k2 <> w2)) with
| true -> begin
(w2 - k2)
end
| false -> begin
(w3 - k3)
end)
end))
end)
end))

let z3v_le = (fun ( known  :  z3version ) ( wanted  :  (int * int * int) ) -> (match ((z3v_compare known wanted)) with
| None -> begin
false
end
| Some (i) -> begin
(i >= 0)
end))

let _z3version = (Support.Microsoft.FStar.Util.mk_ref None)

let get_z3version = (fun ( _48_20  :  unit ) -> (match (()) with
| () -> begin
(let prefix = "Z3 version "
in (match ((Support.ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(let _48_30 = (let _52_17582 = (Support.ST.read Microsoft_FStar_Options.z3_exe)
in (Support.Microsoft.FStar.Util.run_proc _52_17582 "-version" ""))
in (match (_48_30) with
| (_, out, _) -> begin
(let out = (match ((Support.Microsoft.FStar.Util.splitlines out)) with
| x::_ when (Support.Microsoft.FStar.Util.starts_with x prefix) -> begin
(let x = (let _52_17583 = (Support.Microsoft.FStar.Util.substring_from x (Support.String.length prefix))
in (Support.Microsoft.FStar.Util.trim_string _52_17583))
in (let x = (Support.Prims.try_with (fun ( _48_37  :  unit ) -> (match (()) with
| () -> begin
(Support.List.map Support.Microsoft.FStar.Util.int_of_string (Support.Microsoft.FStar.Util.split x "."))
end)) (fun ( _48_36  :  Support.Prims.exn ) -> (match (_48_36) with
| _ -> begin
[]
end)))
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
in (let _48_53 = (Support.ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))

let ini_params = (fun ( _48_55  :  unit ) -> (match (()) with
| () -> begin
(let t = (match ((let _52_17588 = (get_z3version ())
in (z3v_le _52_17588 (4, 3, 1)))) with
| true -> begin
(Support.ST.read Microsoft_FStar_Options.z3timeout)
end
| false -> begin
(let _52_17589 = (Support.ST.read Microsoft_FStar_Options.z3timeout)
in (_52_17589 * 1000))
end)
in (let timeout = (let _52_17590 = (Support.Microsoft.FStar.Util.string_of_int t)
in (Support.Microsoft.FStar.Util.format1 "-t:%s" _52_17590))
in (let relevancy = (match ((let _52_17591 = (get_z3version ())
in (z3v_le _52_17591 (4, 3, 1)))) with
| true -> begin
"RELEVANCY"
end
| false -> begin
"SMT.RELEVANCY"
end)
in (Support.Microsoft.FStar.Util.format2 "-smt2 -in %s AUTO_CONFIG=false MODEL=true %s=2" timeout relevancy))))
end))

type z3status =
| SAT
| UNSAT
| UNKNOWN
| TIMEOUT

let is_SAT = (fun ( _discr_ ) -> (match (_discr_) with
| SAT -> begin
true
end
| _ -> begin
false
end))

let is_UNSAT = (fun ( _discr_ ) -> (match (_discr_) with
| UNSAT -> begin
true
end
| _ -> begin
false
end))

let is_UNKNOWN = (fun ( _discr_ ) -> (match (_discr_) with
| UNKNOWN -> begin
true
end
| _ -> begin
false
end))

let is_TIMEOUT = (fun ( _discr_ ) -> (match (_discr_) with
| TIMEOUT -> begin
true
end
| _ -> begin
false
end))

let status_to_string = (fun ( _48_1  :  z3status ) -> (match (_48_1) with
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

let tid = (fun ( _48_64  :  unit ) -> (match (()) with
| () -> begin
(let _52_17600 = (Support.Microsoft.FStar.Util.current_tid ())
in (Support.Prims.pipe_right _52_17600 Support.Microsoft.FStar.Util.string_of_int))
end))

let new_z3proc = (fun ( id  :  string ) -> (let cond = (fun ( pid  :  string ) ( s  :  string ) -> (let x = ((Support.Microsoft.FStar.Util.trim_string s) = "Done!")
in x))
in (let _52_17608 = (Support.ST.read Microsoft_FStar_Options.z3_exe)
in (let _52_17607 = (ini_params ())
in (Support.Microsoft.FStar.Util.start_process id _52_17608 _52_17607 cond)))))

type bgproc =
{grab : unit  ->  Support.Microsoft.FStar.Util.proc; release : unit  ->  unit; refresh : unit  ->  unit}

let is_Mkbgproc = (fun ( _  :  bgproc ) -> (failwith ("Not yet implemented")))

let queries_dot_smt2 = (Support.Microsoft.FStar.Util.mk_ref None)

let get_qfile = (let ctr = (Support.Microsoft.FStar.Util.mk_ref 0)
in (fun ( fresh  :  bool ) -> (match (fresh) with
| true -> begin
(let _48_76 = (Support.Microsoft.FStar.Util.incr ctr)
in (let _52_17641 = (let _52_17640 = (let _52_17639 = (Support.ST.read ctr)
in (Support.Microsoft.FStar.Util.string_of_int _52_17639))
in (Support.Microsoft.FStar.Util.format1 "queries-%s.smt2" _52_17640))
in (Support.Microsoft.FStar.Util.open_file_for_writing _52_17641)))
end
| false -> begin
(match ((Support.ST.read queries_dot_smt2)) with
| None -> begin
(let fh = (Support.Microsoft.FStar.Util.open_file_for_writing "queries-bg-0.smt2")
in (let _48_80 = (Support.ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))
in fh))
end
| Some (fh) -> begin
fh
end)
end)))

let log_query = (fun ( fresh  :  bool ) ( i  :  string ) -> (let fh = (get_qfile fresh)
in (let _48_87 = (Support.Microsoft.FStar.Util.append_to_file fh i)
in (match (fresh) with
| true -> begin
(Support.Microsoft.FStar.Util.close_file fh)
end
| false -> begin
()
end))))

let bg_z3_proc = (let ctr = (Support.Microsoft.FStar.Util.mk_ref (- (1)))
in (let new_proc = (fun ( _48_91  :  unit ) -> (match (()) with
| () -> begin
(let _52_17650 = (let _52_17649 = (let _48_92 = (Support.Microsoft.FStar.Util.incr ctr)
in (let _52_17648 = (Support.ST.read ctr)
in (Support.Prims.pipe_right _52_17648 Support.Microsoft.FStar.Util.string_of_int)))
in (Support.Microsoft.FStar.Util.format1 "bg-%s" _52_17649))
in (new_z3proc _52_17650))
end))
in (let z3proc = (let _52_17651 = (new_proc ())
in (Support.Microsoft.FStar.Util.mk_ref _52_17651))
in (let x = []
in (let grab = (fun ( _48_97  :  unit ) -> (match (()) with
| () -> begin
(let _48_98 = (Support.Microsoft.FStar.Util.monitor_enter x)
in (Support.ST.read z3proc))
end))
in (let release = (fun ( _48_101  :  unit ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.monitor_exit x)
end))
in (let refresh = (fun ( _48_103  :  unit ) -> (match (()) with
| () -> begin
(let proc = (grab ())
in (let _48_105 = (Support.Microsoft.FStar.Util.kill_process proc)
in (let _48_107 = (let _52_17658 = (new_proc ())
in (Support.ST.op_Colon_Equals z3proc _52_17658))
in (let _48_115 = (match ((Support.ST.read queries_dot_smt2)) with
| None -> begin
()
end
| Some (fh) -> begin
(let _48_112 = (Support.Microsoft.FStar.Util.close_file fh)
in (let fh = (let _52_17661 = (let _52_17660 = (let _52_17659 = (Support.ST.read ctr)
in (Support.Prims.pipe_right _52_17659 Support.Microsoft.FStar.Util.string_of_int))
in (Support.Microsoft.FStar.Util.format1 "queries-bg-%s.smt2" _52_17660))
in (Support.Microsoft.FStar.Util.open_file_for_writing _52_17661))
in (Support.ST.op_Colon_Equals queries_dot_smt2 (Some (fh)))))
end)
in (release ())))))
end))
in {grab = grab; release = release; refresh = refresh})))))))

let doZ3Exe' = (fun ( input  :  string ) ( z3proc  :  Support.Microsoft.FStar.Util.proc ) -> (let parse = (fun ( z3out  :  string ) -> (let lines = (Support.Prims.pipe_right (Support.String.split (('\n')::[]) z3out) (Support.List.map Support.Microsoft.FStar.Util.trim_string))
in (let rec lblnegs = (fun ( lines  :  string list ) -> (match (lines) with
| lname::"false"::rest -> begin
(let _52_17670 = (lblnegs rest)
in (lname)::_52_17670)
end
| lname::_::rest -> begin
(lblnegs rest)
end
| _ -> begin
[]
end))
in (let rec result = (fun ( x  :  string list ) -> (match (x) with
| "timeout"::tl -> begin
(TIMEOUT, [])
end
| "unknown"::tl -> begin
(let _52_17673 = (lblnegs tl)
in (UNKNOWN, _52_17673))
end
| "sat"::tl -> begin
(let _52_17674 = (lblnegs tl)
in (SAT, _52_17674))
end
| "unsat"::tl -> begin
(UNSAT, [])
end
| _::tl -> begin
(result tl)
end
| _ -> begin
(let _52_17678 = (let _52_17677 = (let _52_17676 = (Support.List.map (fun ( l  :  string ) -> (Support.Microsoft.FStar.Util.format1 "<%s>" (Support.Microsoft.FStar.Util.trim_string l))) lines)
in (Support.String.concat "\n" _52_17676))
in (Support.Microsoft.FStar.Util.format1 "Got output lines: %s\n" _52_17677))
in (Support.Prims.pipe_left failwith _52_17678))
end))
in (result lines)))))
in (let stdout = (Support.Microsoft.FStar.Util.ask_process z3proc input)
in (parse (Support.Microsoft.FStar.Util.trim_string stdout)))))

let doZ3Exe = (let ctr = (Support.Microsoft.FStar.Util.mk_ref 0)
in (fun ( fresh  :  bool ) ( input  :  string ) -> (let z3proc = (match (fresh) with
| true -> begin
(let _48_162 = (Support.Microsoft.FStar.Util.incr ctr)
in (let _52_17684 = (let _52_17683 = (Support.ST.read ctr)
in (Support.Microsoft.FStar.Util.string_of_int _52_17683))
in (new_z3proc _52_17684)))
end
| false -> begin
(Microsoft_FStar_ToSMT_Z3_Mkbgproc.grab bg_z3_proc ())
end)
in (let res = (doZ3Exe' input z3proc)
in (let _48_166 = (match (fresh) with
| true -> begin
(Support.Microsoft.FStar.Util.kill_process z3proc)
end
| false -> begin
(Microsoft_FStar_ToSMT_Z3_Mkbgproc.release bg_z3_proc ())
end)
in res)))))

let z3_options = (fun ( _48_168  :  unit ) -> (match (()) with
| () -> begin
(let mbqi = (match ((let _52_17687 = (get_z3version ())
in (z3v_le _52_17687 (4, 3, 1)))) with
| true -> begin
"mbqi"
end
| false -> begin
"smt.mbqi"
end)
in (let model_on_timeout = (match ((let _52_17688 = (get_z3version ())
in (z3v_le _52_17688 (4, 3, 1)))) with
| true -> begin
"(set-option :model-on-timeout true)\n"
end
| false -> begin
""
end)
in (Support.String.strcat (Support.String.strcat (Support.String.strcat (Support.String.strcat "(set-option :global-decls false)\n" "(set-option :") mbqi) " false)\n") model_on_timeout)))
end))

type 'a job =
{job : unit  ->  'a; callback : 'a  ->  unit}

let is_Mkjob = (fun ( _  :  'a job ) -> (failwith ("Not yet implemented")))

type z3job =
(bool * (string * Support.Microsoft.FStar.Range.range) list) job

let job_queue = (let x = (Support.Microsoft.FStar.Util.mk_ref (({job = (fun ( _48_175  :  unit ) -> (match (()) with
| () -> begin
(let _52_17712 = (let _52_17711 = (let _52_17710 = (Support.Microsoft.FStar.Range.mk_range "" 0 0)
in ("", _52_17710))
in (_52_17711)::[])
in (false, _52_17712))
end)); callback = (fun ( a  :  (bool * (string * Support.Microsoft.FStar.Range.range) list) ) -> ())})::[]))
in (let _48_178 = (Support.ST.op_Colon_Equals x [])
in x))

let pending_jobs = (Support.Microsoft.FStar.Util.mk_ref 0)

let with_monitor = (fun ( m  :  'u48u2292 ) ( f  :  unit  ->  'u48u2291 ) -> (let _48_182 = (Support.Microsoft.FStar.Util.monitor_enter m)
in (let res = (f ())
in (let _48_185 = (Support.Microsoft.FStar.Util.monitor_exit m)
in res))))

let z3_job = (fun ( fresh  :  bool ) ( label_messages  :  ((string * 'u48u2610) * 'u48u2609 * 'u48u2608) list ) ( input  :  string ) ( _48_190  :  unit ) -> (match (()) with
| () -> begin
(let _48_193 = (doZ3Exe fresh input)
in (match (_48_193) with
| (status, lblnegs) -> begin
(let result = (match (status) with
| UNSAT -> begin
(true, [])
end
| _ -> begin
(let _48_197 = (match ((let _52_17723 = (Support.ST.read Microsoft_FStar_Options.debug)
in (_52_17723 <> []))) with
| true -> begin
(let _52_17724 = (Support.Microsoft.FStar.Util.format1 "Z3 says: %s\n" (status_to_string status))
in (Support.Prims.pipe_left Support.Microsoft.FStar.Util.print_string _52_17724))
end
| false -> begin
()
end)
in (let failing_assertions = (Support.Prims.pipe_right lblnegs (Support.List.collect (fun ( l  :  string ) -> (match ((Support.Prims.pipe_right label_messages (Support.List.tryFind (fun ( _48_205  :  ((string * 'u48u2610) * 'u48u2609 * 'u48u2608) ) -> (match (_48_205) with
| (m, _, _) -> begin
((Support.Prims.fst m) = l)
end))))) with
| None -> begin
[]
end
| Some ((_, msg, r)) -> begin
((msg, r))::[]
end))))
in (false, failing_assertions)))
end)
in result)
end))
end))

let rec dequeue' = (fun ( _48_215  :  unit ) -> (match (()) with
| () -> begin
(Obj.magic (let j = (match ((Support.ST.read job_queue)) with
| [] -> begin
(failwith ("Impossible"))
end
| hd::tl -> begin
(let _48_220 = (Support.ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (let _48_223 = (Support.Microsoft.FStar.Util.incr pending_jobs)
in (let _48_225 = (Support.Microsoft.FStar.Util.monitor_exit job_queue)
in (let _48_227 = (run_job j)
in (let _48_230 = (with_monitor job_queue (fun ( _48_229  :  unit ) -> (match (()) with
| () -> begin
(Support.Microsoft.FStar.Util.decr pending_jobs)
end)))
in dequeue))))))
end))
and dequeue = (fun ( _48_232  :  unit ) -> (match (()) with
| () -> begin
(let _48_233 = (Support.Microsoft.FStar.Util.monitor_enter job_queue)
in (let rec aux = (fun ( _48_236  :  unit ) -> (match (()) with
| () -> begin
(match ((Support.ST.read job_queue)) with
| [] -> begin
(let _48_238 = (Support.Microsoft.FStar.Util.monitor_wait job_queue)
in (aux ()))
end
| _ -> begin
(Obj.magic dequeue')
end)
end))
in (aux ())))
end))
and run_job = (fun ( j  :  z3job ) -> (let _52_17734 = (Microsoft_FStar_ToSMT_Z3_Mkjob.job j ())
in (Support.Prims.pipe_left j.callback _52_17734)))

let init = (fun ( _48_243  :  unit ) -> (match (()) with
| () -> begin
(let n_runners = (let _52_17737 = (Support.ST.read Microsoft_FStar_Options.n_cores)
in (_52_17737 - 1))
in (let rec aux = (fun ( n  :  int ) -> (match ((n = 0)) with
| true -> begin
()
end
| false -> begin
(let _48_247 = (Support.Microsoft.FStar.Util.spawn dequeue)
in (aux (n - 1)))
end))
in (aux n_runners)))
end))

let enqueue = (fun ( fresh  :  bool ) ( j  :  z3job ) -> (match ((not (fresh))) with
| true -> begin
(run_job j)
end
| false -> begin
(let _48_251 = (Support.Microsoft.FStar.Util.monitor_enter job_queue)
in (let _48_253 = (let _52_17745 = (let _52_17744 = (Support.ST.read job_queue)
in (Support.List.append _52_17744 ((j)::[])))
in (Support.ST.op_Colon_Equals job_queue _52_17745))
in (let _48_255 = (Support.Microsoft.FStar.Util.monitor_pulse job_queue)
in (Support.Microsoft.FStar.Util.monitor_exit job_queue))))
end))

let finish = (fun ( _48_257  :  unit ) -> (match (()) with
| () -> begin
(let bg = (Microsoft_FStar_ToSMT_Z3_Mkbgproc.grab bg_z3_proc ())
in (let _48_259 = (Support.Microsoft.FStar.Util.kill_process bg)
in (let _48_261 = (Microsoft_FStar_ToSMT_Z3_Mkbgproc.release bg_z3_proc ())
in (let rec aux = (fun ( _48_264  :  unit ) -> (match (()) with
| () -> begin
(let _48_268 = (with_monitor job_queue (fun ( _48_265  :  unit ) -> (match (()) with
| () -> begin
(let _52_17753 = (Support.ST.read pending_jobs)
in (let _52_17752 = (let _52_17751 = (Support.ST.read job_queue)
in (Support.List.length _52_17751))
in (_52_17753, _52_17752)))
end)))
in (match (_48_268) with
| (n, m) -> begin
(match (((n + m) = 0)) with
| true -> begin
(let _52_17754 = (Microsoft_FStar_Tc_Errors.report_all ())
in (Support.Prims.pipe_right _52_17754 Support.Prims.ignore))
end
| false -> begin
(let _48_269 = (Support.Microsoft.FStar.Util.sleep 500)
in (aux ()))
end)
end))
end))
in (aux ())))))
end))

type scope_t =
Microsoft_FStar_ToSMT_Term.decl list list

let fresh_scope = (Support.Microsoft.FStar.Util.mk_ref (([])::[]))

let bg_scope = (Support.Microsoft.FStar.Util.mk_ref [])

let push = (fun ( msg  :  string ) -> (let _48_272 = (let _52_17758 = (let _52_17757 = (Support.ST.read fresh_scope)
in ((Microsoft_FStar_ToSMT_Term.Caption (msg))::[])::_52_17757)
in (Support.ST.op_Colon_Equals fresh_scope _52_17758))
in (let _52_17760 = (let _52_17759 = (Support.ST.read bg_scope)
in (Support.List.append ((Microsoft_FStar_ToSMT_Term.Caption (msg))::(Microsoft_FStar_ToSMT_Term.Push)::[]) _52_17759))
in (Support.ST.op_Colon_Equals bg_scope _52_17760))))

let pop = (fun ( msg  :  string ) -> (let _48_275 = (let _52_17764 = (let _52_17763 = (Support.ST.read fresh_scope)
in (Support.List.tl _52_17763))
in (Support.ST.op_Colon_Equals fresh_scope _52_17764))
in (let _52_17766 = (let _52_17765 = (Support.ST.read bg_scope)
in (Support.List.append ((Microsoft_FStar_ToSMT_Term.Caption (msg))::(Microsoft_FStar_ToSMT_Term.Pop)::[]) _52_17765))
in (Support.ST.op_Colon_Equals bg_scope _52_17766))))

let giveZ3 = (fun ( decls  :  Microsoft_FStar_ToSMT_Term.decl list ) -> (let _48_283 = (match ((Support.ST.read fresh_scope)) with
| hd::tl -> begin
(Support.ST.op_Colon_Equals fresh_scope (((Support.List.append hd decls))::tl))
end
| _ -> begin
(failwith ("Impossible"))
end)
in (let _52_17770 = (let _52_17769 = (Support.ST.read bg_scope)
in (Support.List.append (Support.List.rev decls) _52_17769))
in (Support.ST.op_Colon_Equals bg_scope _52_17770))))

let bgtheory = (fun ( fresh  :  bool ) -> (match (fresh) with
| true -> begin
(let _52_17774 = (let _52_17773 = (Support.ST.read fresh_scope)
in (Support.List.rev _52_17773))
in (Support.Prims.pipe_right _52_17774 Support.List.flatten))
end
| false -> begin
(let bg = (Support.ST.read bg_scope)
in (let _48_287 = (Support.ST.op_Colon_Equals bg_scope [])
in (Support.List.rev bg)))
end))

let refresh = (fun ( _48_289  :  unit ) -> (match (()) with
| () -> begin
(let _48_290 = (Microsoft_FStar_ToSMT_Z3_Mkbgproc.refresh bg_z3_proc ())
in (let theory = (bgtheory true)
in (Support.ST.op_Colon_Equals bg_scope (Support.List.rev theory))))
end))

let mark = (fun ( msg  :  string ) -> (push msg))

let reset_mark = (fun ( msg  :  string ) -> (let _48_295 = (pop msg)
in (refresh ())))

let commit_mark = (fun ( msg  :  'u48u3661 ) -> (match ((Support.ST.read fresh_scope)) with
| hd::s::tl -> begin
(Support.ST.op_Colon_Equals fresh_scope (((Support.List.append hd s))::tl))
end
| _ -> begin
(failwith ("Impossible"))
end))

let ask = (fun ( fresh  :  bool ) ( label_messages  :  ((string * 'u48u3795) * string * Int64.t) list ) ( qry  :  Microsoft_FStar_ToSMT_Term.decl list ) ( cb  :  (bool * (string * Int64.t) list)  ->  unit ) -> (let fresh = (let _52_17790 = (let _52_17789 = (Support.ST.read Microsoft_FStar_Options.n_cores)
in (_52_17789 > 1))
in (fresh && _52_17790))
in (let theory = (bgtheory fresh)
in (let theory = (match (fresh) with
| true -> begin
(Support.List.append theory qry)
end
| false -> begin
(Support.List.append (Support.List.append (Support.List.append theory ((Microsoft_FStar_ToSMT_Term.Push)::[])) qry) ((Microsoft_FStar_ToSMT_Term.Pop)::[]))
end)
in (let input = (let _52_17793 = (let _52_17792 = (let _52_17791 = (z3_options ())
in (Microsoft_FStar_ToSMT_Term.declToSmt _52_17791))
in (Support.List.map _52_17792 theory))
in (Support.Prims.pipe_right _52_17793 (Support.String.concat "\n")))
in (let _48_313 = (match ((Support.ST.read Microsoft_FStar_Options.logQueries)) with
| true -> begin
(log_query fresh input)
end
| false -> begin
()
end)
in (enqueue fresh {job = (z3_job fresh label_messages input); callback = cb})))))))




