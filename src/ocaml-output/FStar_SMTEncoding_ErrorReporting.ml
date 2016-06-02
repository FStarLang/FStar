
open Prims

type label =
FStar_SMTEncoding_Term.error_label


type labels =
FStar_SMTEncoding_Term.error_labels


let sort_labels : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun l -> (FStar_List.sortWith (fun _83_8 _83_14 -> (match ((_83_8, _83_14)) with
| ((_83_4, _83_6, r1), (_83_10, _83_12, r2)) -> begin
(FStar_Range.compare r1 r2)
end)) l))


let remove_dups : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list = (fun l -> (FStar_Util.remove_dups (fun _83_20 _83_25 -> (match ((_83_20, _83_25)) with
| ((_83_17, m1, r1), (_83_22, m2, r2)) -> begin
((r1 = r2) && (m1 = m2))
end)) l))


type msg =
(Prims.string * FStar_Range.range)


type ranges =
(Prims.string Prims.option * FStar_Range.range) Prims.list


let fresh_label : ranges  ->  FStar_SMTEncoding_Term.term  ->  labels  ->  (FStar_SMTEncoding_Term.term * labels) = (

let ctr = (FStar_ST.alloc 0)
in (fun rs t labs -> (

let l = (

let _83_30 = (FStar_Util.incr ctr)
in (let _173_16 = (let _173_15 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _173_15))
in (FStar_Util.format1 "label_%s" _173_16)))
in (

let lvar = (l, FStar_SMTEncoding_Term.Bool_sort)
in (

let _83_50 = (match (rs) with
| [] -> begin
(t.FStar_SMTEncoding_Term.hash, FStar_Range.dummyRange)
end
| (Some (reason), r)::_83_36 -> begin
(reason, r)
end
| (None, r)::_83_43 -> begin
("failed to prove a pre-condition", r)
end)
in (match (_83_50) with
| (message, range) -> begin
(

let label = (lvar, message, range)
in (

let lterm = (FStar_SMTEncoding_Term.mkFreeV lvar)
in (

let lt = (FStar_SMTEncoding_Term.mkOr (lterm, t))
in (lt, (label)::labs))))
end))))))


let label_goals : (Prims.unit  ->  Prims.string) Prims.option  ->  FStar_Int64.int64  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * labels * ranges) = (fun use_env_msg r q -> (

let _83_62 = (match (use_env_msg) with
| None -> begin
(false, "")
end
| Some (f) -> begin
(let _173_32 = (f ())
in (true, _173_32))
end)
in (match (_83_62) with
| (flag, msg_prefix) -> begin
(

let fresh_label = (fun rs t labs -> (

let rs' = if (not (flag)) then begin
rs
end else begin
(match (rs) with
| (Some (reason), _83_72)::_83_68 -> begin
((Some ((Prims.strcat "Failed to verify implicit argument: " reason)), r))::[]
end
| _83_76 -> begin
((Some ("Failed to verify implicit argument"), r))::[]
end)
end
in (

let _83_80 = (fresh_label rs' t labs)
in (match (_83_80) with
| (lt, labs) -> begin
(lt, labs, rs)
end))))
in (

let rec aux = (fun rs q labs -> (match (q.FStar_SMTEncoding_Term.tm) with
| (FStar_SMTEncoding_Term.BoundV (_)) | (FStar_SMTEncoding_Term.Integer (_)) -> begin
(q, labs, rs)
end
| FStar_SMTEncoding_Term.Labeled (_83_92, "push", r) -> begin
(FStar_SMTEncoding_Term.mkTrue, labs, ((None, r))::rs)
end
| FStar_SMTEncoding_Term.Labeled (_83_98, "pop", r) -> begin
(let _173_45 = (FStar_List.tl rs)
in (FStar_SMTEncoding_Term.mkTrue, labs, _173_45))
end
| FStar_SMTEncoding_Term.Labeled (arg, reason, r) -> begin
(

let _83_111 = (aux (((Some (reason), r))::rs) arg labs)
in (match (_83_111) with
| (tm, labs, rs) -> begin
(let _173_46 = (FStar_List.tl rs)
in (tm, labs, _173_46))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, lhs::rhs::[]) -> begin
(

let _83_121 = (aux rs rhs labs)
in (match (_83_121) with
| (rhs, labs, rs) -> begin
(let _173_47 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]))))
in (_173_47, labs, rs))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(

let _83_138 = (FStar_List.fold_left (fun _83_129 c -> (match (_83_129) with
| (rs, cs, labs) -> begin
(

let _83_134 = (aux rs c labs)
in (match (_83_134) with
| (c, labs, rs) -> begin
(rs, (c)::cs, labs)
end))
end)) (rs, [], labs) conjuncts)
in (match (_83_138) with
| (rs, conjuncts, labs) -> begin
(let _173_50 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.And, (FStar_List.rev conjuncts)))))
in (_173_50, labs, rs))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, hd::q1::q2::[]) -> begin
(

let _83_150 = (aux rs q1 labs)
in (match (_83_150) with
| (q1, labs, _83_149) -> begin
(

let _83_155 = (aux rs q2 labs)
in (match (_83_155) with
| (q2, labs, _83_154) -> begin
(let _173_51 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]))))
in (_173_51, labs, rs))
end))
end))
end
| (FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Exists, _, _, _, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Or, _)) -> begin
(fresh_label rs q labs)
end
| (FStar_SMTEncoding_Term.FreeV (_)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.True, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.False, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Eq, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LT, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.LTE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GT, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.GTE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var (_), _)) -> begin
(fresh_label rs q labs)
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Add, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Sub, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Div, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mul, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Minus, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Mod, _)) -> begin
(FStar_All.failwith "Impossible: non-propositional term")
end
| (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _)) | (FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, _)) -> begin
(FStar_All.failwith "Impossible: arity mismatch")
end
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body) -> begin
(

let _83_277 = (aux rs body labs)
in (match (_83_277) with
| (body, labs, rs) -> begin
(let _173_52 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant ((FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body))))
in (_173_52, labs, rs))
end))
end))
in (aux [] q [])))
end)))


let detail_errors : labels  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  (Prims.bool * labels))  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun all_labels potential_errors askZ3 -> (

let ctr = (FStar_Util.mk_ref 0)
in (

let elim = (fun labs -> (

let _83_284 = (FStar_Util.incr ctr)
in (let _173_75 = (let _173_68 = (let _173_67 = (let _173_66 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _173_66))
in (Prims.strcat "DETAILING ERRORS" _173_67))
in FStar_SMTEncoding_Term.Echo (_173_68))
in (let _173_74 = (FStar_All.pipe_right labs (FStar_List.map (fun _83_291 -> (match (_83_291) with
| (l, _83_288, _83_290) -> begin
(let _173_73 = (let _173_72 = (let _173_71 = (let _173_70 = (FStar_SMTEncoding_Term.mkFreeV l)
in (_173_70, FStar_SMTEncoding_Term.mkTrue))
in (FStar_SMTEncoding_Term.mkEq _173_71))
in (_173_72, Some ("Disabling label"), Some ((Prims.strcat "disable_label_" (Prims.fst l)))))
in FStar_SMTEncoding_Term.Assume (_173_73))
end))))
in (_173_75)::_173_74))))
in (

let print_labs = (fun tag l -> (FStar_All.pipe_right l (FStar_List.iter (fun _83_300 -> (match (_83_300) with
| (l, _83_297, _83_299) -> begin
(FStar_Util.print2 "%s : %s; " tag (Prims.fst l))
end)))))
in (

let minus = (fun l1 l2 -> (FStar_All.pipe_right l1 (FStar_List.filter (fun _83_312 -> (match (_83_312) with
| ((x, _83_306), _83_309, _83_311) -> begin
(not ((FStar_All.pipe_right l2 (FStar_Util.for_some (fun _83_321 -> (match (_83_321) with
| ((y, _83_315), _83_318, _83_320) -> begin
(x = y)
end))))))
end)))))
in (

let rec linear_check = (fun eliminated errors active -> (match (active) with
| [] -> begin
(

let labs = (FStar_All.pipe_right errors sort_labels)
in labs)
end
| hd::tl -> begin
(

let _83_334 = (let _173_93 = (FStar_All.pipe_left elim (FStar_List.append (FStar_List.append eliminated errors) tl))
in (askZ3 _173_93))
in (match (_83_334) with
| (ok, _83_333) -> begin
if ok then begin
(linear_check ((hd)::eliminated) errors tl)
end else begin
(linear_check eliminated ((hd)::errors) tl)
end
end))
end))
in (

let rec bisect = (fun eliminated potential_errors active -> (match (active) with
| [] -> begin
(eliminated, potential_errors)
end
| _83_341 -> begin
(

let _83_349 = (match (active) with
| _83_343::[] -> begin
(active, [])
end
| _83_346 -> begin
(FStar_Util.first_N ((FStar_List.length active) / 2) active)
end)
in (match (_83_349) with
| (pfx, sfx) -> begin
(

let _83_352 = (let _173_100 = (elim (FStar_List.append (FStar_List.append eliminated potential_errors) sfx))
in (askZ3 _173_100))
in (match (_83_352) with
| (ok, pfx_subset) -> begin
if ok then begin
(bisect (FStar_List.append eliminated pfx) potential_errors sfx)
end else begin
(match (pfx_subset) with
| [] -> begin
(bisect eliminated (FStar_List.append potential_errors pfx) sfx)
end
| _83_355 -> begin
(

let potential_errors = (FStar_List.append potential_errors pfx_subset)
in (

let pfx_active = (minus pfx pfx_subset)
in (bisect eliminated potential_errors (FStar_List.append pfx_active sfx))))
end)
end
end))
end))
end))
in (

let rec until_fixpoint = (fun eliminated potential_errors active -> (

let _83_364 = (bisect eliminated potential_errors active)
in (match (_83_364) with
| (eliminated', potential_errors) -> begin
if (FStar_Util.physical_equality eliminated eliminated') then begin
(linear_check eliminated [] potential_errors)
end else begin
(until_fixpoint eliminated' [] potential_errors)
end
end)))
in (

let active = (minus all_labels potential_errors)
in (until_fixpoint [] potential_errors active))))))))))


let askZ3_and_report_errors : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun env use_fresh_z3_context all_labels prefix query suffix -> (

let _83_372 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (

let minimum_workable_fuel = (FStar_Util.mk_ref None)
in (

let set_minimum_workable_fuel = (fun f _83_1 -> (match (_83_1) with
| [] -> begin
()
end
| errs -> begin
(match ((FStar_ST.read minimum_workable_fuel)) with
| Some (_83_381) -> begin
()
end
| None -> begin
(FStar_ST.op_Colon_Equals minimum_workable_fuel (Some ((f, errs))))
end)
end))
in (

let with_fuel = (fun label_assumptions p _83_389 -> (match (_83_389) with
| (n, i) -> begin
(let _173_155 = (let _173_154 = (let _173_153 = (let _173_147 = (let _173_146 = (let _173_131 = (let _173_130 = (FStar_Util.string_of_int n)
in (let _173_129 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _173_130 _173_129)))
in FStar_SMTEncoding_Term.Caption (_173_131))
in (let _173_145 = (let _173_144 = (let _173_136 = (let _173_135 = (let _173_134 = (let _173_133 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (let _173_132 = (FStar_SMTEncoding_Term.n_fuel n)
in (_173_133, _173_132)))
in (FStar_SMTEncoding_Term.mkEq _173_134))
in (_173_135, None, None))
in FStar_SMTEncoding_Term.Assume (_173_136))
in (let _173_143 = (let _173_142 = (let _173_141 = (let _173_140 = (let _173_139 = (let _173_138 = (FStar_SMTEncoding_Term.mkApp ("MaxIFuel", []))
in (let _173_137 = (FStar_SMTEncoding_Term.n_fuel i)
in (_173_138, _173_137)))
in (FStar_SMTEncoding_Term.mkEq _173_139))
in (_173_140, None, None))
in FStar_SMTEncoding_Term.Assume (_173_141))
in (_173_142)::(p)::[])
in (_173_144)::_173_143))
in (_173_146)::_173_145))
in (FStar_List.append _173_147 label_assumptions))
in (let _173_152 = (let _173_151 = (let _173_150 = (let _173_149 = (let _173_148 = ((FStar_Options.z3_timeout ()) * 1000)
in (FStar_All.pipe_left FStar_Util.string_of_int _173_148))
in ("timeout", _173_149))
in FStar_SMTEncoding_Term.SetOption (_173_150))
in (_173_151)::[])
in (FStar_List.append _173_153 _173_152)))
in (FStar_List.append _173_154 ((FStar_SMTEncoding_Term.CheckSat)::[])))
in (FStar_List.append _173_155 suffix))
end))
in (

let check = (fun p -> (

let initial_config = (let _173_159 = (FStar_Options.initial_fuel ())
in (let _173_158 = (FStar_Options.initial_ifuel ())
in (_173_159, _173_158)))
in (

let alt_configs = (let _173_178 = (let _173_177 = if ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ())) then begin
(let _173_162 = (let _173_161 = (FStar_Options.initial_fuel ())
in (let _173_160 = (FStar_Options.max_ifuel ())
in (_173_161, _173_160)))
in (_173_162)::[])
end else begin
[]
end
in (let _173_176 = (let _173_175 = if (((FStar_Options.max_fuel ()) / 2) > (FStar_Options.initial_fuel ())) then begin
(let _173_165 = (let _173_164 = ((FStar_Options.max_fuel ()) / 2)
in (let _173_163 = (FStar_Options.max_ifuel ())
in (_173_164, _173_163)))
in (_173_165)::[])
end else begin
[]
end
in (let _173_174 = (let _173_173 = if (((FStar_Options.max_fuel ()) > (FStar_Options.initial_fuel ())) && ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ()))) then begin
(let _173_168 = (let _173_167 = (FStar_Options.max_fuel ())
in (let _173_166 = (FStar_Options.max_ifuel ())
in (_173_167, _173_166)))
in (_173_168)::[])
end else begin
[]
end
in (let _173_172 = (let _173_171 = if ((FStar_Options.min_fuel ()) < (FStar_Options.initial_fuel ())) then begin
(let _173_170 = (let _173_169 = (FStar_Options.min_fuel ())
in (_173_169, 1))
in (_173_170)::[])
end else begin
[]
end
in (_173_171)::[])
in (_173_173)::_173_172))
in (_173_175)::_173_174))
in (_173_177)::_173_176))
in (FStar_List.flatten _173_178))
in (

let report = (fun p errs -> (

let errs = if ((FStar_Options.detail_errors ()) && ((FStar_Options.n_cores ()) = 1)) then begin
(

let _83_404 = (match ((FStar_ST.read minimum_workable_fuel)) with
| Some (f, errs) -> begin
(f, errs)
end
| None -> begin
(let _173_184 = (let _173_183 = (FStar_Options.min_fuel ())
in (_173_183, 1))
in (_173_184, errs))
end)
in (match (_83_404) with
| (min_fuel, potential_errors) -> begin
(

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref None)
in (

let _83_409 = (let _173_188 = (with_fuel label_assumptions p min_fuel)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _173_188 (fun r -> (FStar_ST.op_Colon_Equals res (Some (r))))))
in (let _173_189 = (FStar_ST.read res)
in (FStar_Option.get _173_189)))))
in (detail_errors all_labels errs ask_z3))
end))
end else begin
errs
end
in (

let errs = (match (errs) with
| [] -> begin
((("", FStar_SMTEncoding_Term.Term_sort), "Unknown assertion failed", FStar_Range.dummyRange))::[]
end
| _83_414 -> begin
errs
end)
in (

let _83_416 = if (FStar_Options.print_fuels ()) then begin
(let _173_195 = (let _173_190 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _173_190))
in (let _173_194 = (let _173_191 = (FStar_Options.max_fuel ())
in (FStar_All.pipe_right _173_191 FStar_Util.string_of_int))
in (let _173_193 = (let _173_192 = (FStar_Options.max_ifuel ())
in (FStar_All.pipe_right _173_192 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _173_195 _173_194 _173_193))))
end else begin
()
end
in (

let _83_423 = (let _173_197 = (FStar_All.pipe_right errs (FStar_List.map (fun _83_422 -> (match (_83_422) with
| (_83_419, x, y) -> begin
(x, y)
end))))
in (FStar_TypeChecker_Errors.add_errors env _173_197))
in if (FStar_Options.detail_errors ()) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Detailed error report follows\n")))
end else begin
()
end)))))
in (

let rec try_alt_configs = (fun prev_f p errs cfgs -> (

let _83_431 = (set_minimum_workable_fuel prev_f errs)
in (match (cfgs) with
| [] -> begin
(report p errs)
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _173_210 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _173_210 (cb mi p [])))
end
| _83_438 -> begin
(

let _83_439 = (set_minimum_workable_fuel prev_f errs)
in (report p errs))
end)
end
| mi::tl -> begin
(let _173_212 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _173_212 (fun _83_446 -> (match (_83_446) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _83_449 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end)))
and cb = (fun _83_452 p alt _83_457 -> (match ((_83_452, _83_457)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
if (FStar_Options.print_fuels ()) then begin
(let _173_220 = (let _173_217 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _173_217))
in (let _173_219 = (FStar_Util.string_of_int prev_fuel)
in (let _173_218 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _173_220 _173_219 _173_218))))
end else begin
()
end
end else begin
(

let _83_458 = if (FStar_Options.print_fuels ()) then begin
(let _173_224 = (let _173_221 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _173_221))
in (let _173_223 = (FStar_Util.string_of_int prev_fuel)
in (let _173_222 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query failed with fuel %s and ifuel %s ... retrying \n" _173_224 _173_223 _173_222))))
end else begin
()
end
in (try_alt_configs (prev_fuel, prev_ifuel) p errs alt))
end
end))
in (let _173_225 = (with_fuel [] p initial_config)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _173_225 (cb initial_config p alt_configs))))))))
in (

let process_query = (fun q -> if ((FStar_Options.split_cases ()) > 0) then begin
(

let _83_464 = (let _173_231 = (FStar_Options.split_cases ())
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _173_231 q))
in (match (_83_464) with
| (b, cb) -> begin
if b then begin
(FStar_SMTEncoding_SplitQueryCases.handle_query cb check)
end else begin
(check q)
end
end))
end else begin
(check q)
end)
in if (FStar_Options.admit_smt_queries ()) then begin
()
end else begin
(process_query query)
end)))))))




