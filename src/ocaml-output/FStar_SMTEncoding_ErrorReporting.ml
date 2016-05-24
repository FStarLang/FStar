
open Prims

type label =
FStar_SMTEncoding_Term.error_label


type labels =
FStar_SMTEncoding_Term.error_labels


let sort_labels : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun l -> (FStar_List.sortWith (fun _82_8 _82_14 -> (match ((_82_8, _82_14)) with
| ((_82_4, _82_6, r1), (_82_10, _82_12, r2)) -> begin
(FStar_Range.compare r1 r2)
end)) l))


let remove_dups : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list = (fun l -> (FStar_Util.remove_dups (fun _82_20 _82_25 -> (match ((_82_20, _82_25)) with
| ((_82_17, m1, r1), (_82_22, m2, r2)) -> begin
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

let _82_30 = (FStar_Util.incr ctr)
in (let _171_16 = (let _171_15 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _171_15))
in (FStar_Util.format1 "label_%s" _171_16)))
in (

let lvar = (l, FStar_SMTEncoding_Term.Bool_sort)
in (

let _82_50 = (match (rs) with
| [] -> begin
(t.FStar_SMTEncoding_Term.hash, FStar_Range.dummyRange)
end
| (Some (reason), r)::_82_36 -> begin
(reason, r)
end
| (None, r)::_82_43 -> begin
("failed to prove a pre-condition", r)
end)
in (match (_82_50) with
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

let _82_62 = (match (use_env_msg) with
| None -> begin
(false, "")
end
| Some (f) -> begin
(let _171_32 = (f ())
in (true, _171_32))
end)
in (match (_82_62) with
| (flag, msg_prefix) -> begin
(

let fresh_label = (fun rs t labs -> (

let rs' = if (not (flag)) then begin
rs
end else begin
(match (rs) with
| (Some (reason), _82_72)::_82_68 -> begin
((Some ((Prims.strcat "Failed to verify implicit argument: " reason)), r))::[]
end
| _82_76 -> begin
((Some ("Failed to verify implicit argument"), r))::[]
end)
end
in (

let _82_80 = (fresh_label rs' t labs)
in (match (_82_80) with
| (lt, labs) -> begin
(lt, labs, rs)
end))))
in (

let rec aux = (fun rs q labs -> (match (q.FStar_SMTEncoding_Term.tm) with
| (FStar_SMTEncoding_Term.BoundV (_)) | (FStar_SMTEncoding_Term.Integer (_)) -> begin
(q, labs, rs)
end
| FStar_SMTEncoding_Term.Labeled (_82_92, "push", r) -> begin
(FStar_SMTEncoding_Term.mkTrue, labs, ((None, r))::rs)
end
| FStar_SMTEncoding_Term.Labeled (_82_98, "pop", r) -> begin
(let _171_45 = (FStar_List.tl rs)
in (FStar_SMTEncoding_Term.mkTrue, labs, _171_45))
end
| FStar_SMTEncoding_Term.Labeled (arg, reason, r) -> begin
(

let _82_111 = (aux (((Some (reason), r))::rs) arg labs)
in (match (_82_111) with
| (tm, labs, rs) -> begin
(let _171_46 = (FStar_List.tl rs)
in (tm, labs, _171_46))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, lhs::rhs::[]) -> begin
(

let _82_121 = (aux rs rhs labs)
in (match (_82_121) with
| (rhs, labs, rs) -> begin
(let _171_47 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]))))
in (_171_47, labs, rs))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(

let _82_138 = (FStar_List.fold_left (fun _82_129 c -> (match (_82_129) with
| (rs, cs, labs) -> begin
(

let _82_134 = (aux rs c labs)
in (match (_82_134) with
| (c, labs, rs) -> begin
(rs, (c)::cs, labs)
end))
end)) (rs, [], labs) conjuncts)
in (match (_82_138) with
| (rs, conjuncts, labs) -> begin
(let _171_50 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.And, (FStar_List.rev conjuncts)))))
in (_171_50, labs, rs))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, hd::q1::q2::[]) -> begin
(

let _82_150 = (aux rs q1 labs)
in (match (_82_150) with
| (q1, labs, _82_149) -> begin
(

let _82_155 = (aux rs q2 labs)
in (match (_82_155) with
| (q2, labs, _82_154) -> begin
(let _171_51 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]))))
in (_171_51, labs, rs))
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

let _82_277 = (aux rs body labs)
in (match (_82_277) with
| (body, labs, rs) -> begin
(let _171_52 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant ((FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body))))
in (_171_52, labs, rs))
end))
end))
in (aux [] q [])))
end)))


let detail_errors : labels  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  (Prims.bool * labels))  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun all_labels potential_errors askZ3 -> (

let ctr = (FStar_Util.mk_ref 0)
in (

let elim = (fun labs -> (

let _82_284 = (FStar_Util.incr ctr)
in (let _171_75 = (let _171_68 = (let _171_67 = (let _171_66 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _171_66))
in (Prims.strcat "DETAILING ERRORS" _171_67))
in FStar_SMTEncoding_Term.Echo (_171_68))
in (let _171_74 = (FStar_All.pipe_right labs (FStar_List.map (fun _82_291 -> (match (_82_291) with
| (l, _82_288, _82_290) -> begin
(let _171_73 = (let _171_72 = (let _171_71 = (let _171_70 = (FStar_SMTEncoding_Term.mkFreeV l)
in (_171_70, FStar_SMTEncoding_Term.mkTrue))
in (FStar_SMTEncoding_Term.mkEq _171_71))
in (_171_72, Some ("Disabling label")))
in FStar_SMTEncoding_Term.Assume (_171_73))
end))))
in (_171_75)::_171_74))))
in (

let print_labs = (fun tag l -> (FStar_All.pipe_right l (FStar_List.iter (fun _82_300 -> (match (_82_300) with
| (l, _82_297, _82_299) -> begin
(FStar_Util.print2 "%s : %s; " tag (Prims.fst l))
end)))))
in (

let minus = (fun l1 l2 -> (FStar_All.pipe_right l1 (FStar_List.filter (fun _82_312 -> (match (_82_312) with
| ((x, _82_306), _82_309, _82_311) -> begin
(not ((FStar_All.pipe_right l2 (FStar_Util.for_some (fun _82_321 -> (match (_82_321) with
| ((y, _82_315), _82_318, _82_320) -> begin
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

let _82_334 = (let _171_93 = (FStar_All.pipe_left elim (FStar_List.append (FStar_List.append eliminated errors) tl))
in (askZ3 _171_93))
in (match (_82_334) with
| (ok, _82_333) -> begin
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
| _82_341 -> begin
(

let _82_349 = (match (active) with
| _82_343::[] -> begin
(active, [])
end
| _82_346 -> begin
(FStar_Util.first_N ((FStar_List.length active) / 2) active)
end)
in (match (_82_349) with
| (pfx, sfx) -> begin
(

let _82_352 = (let _171_100 = (elim (FStar_List.append (FStar_List.append eliminated potential_errors) sfx))
in (askZ3 _171_100))
in (match (_82_352) with
| (ok, pfx_subset) -> begin
if ok then begin
(bisect (FStar_List.append eliminated pfx) potential_errors sfx)
end else begin
(match (pfx_subset) with
| [] -> begin
(bisect eliminated (FStar_List.append potential_errors pfx) sfx)
end
| _82_355 -> begin
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

let _82_364 = (bisect eliminated potential_errors active)
in (match (_82_364) with
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

let _82_372 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (

let minimum_workable_fuel = (FStar_Util.mk_ref None)
in (

let set_minimum_workable_fuel = (fun f _82_1 -> (match (_82_1) with
| [] -> begin
()
end
| errs -> begin
(match ((FStar_ST.read minimum_workable_fuel)) with
| Some (_82_381) -> begin
()
end
| None -> begin
(FStar_ST.op_Colon_Equals minimum_workable_fuel (Some ((f, errs))))
end)
end))
in (

let with_fuel = (fun label_assumptions p _82_389 use_timeout -> (match (_82_389) with
| (n, i) -> begin
(

let timeout_ms = if use_timeout then begin
((FStar_Options.z3_timeout ()) * 1000)
end else begin
(60 * 1000)
end
in (let _171_156 = (let _171_155 = (let _171_154 = (let _171_149 = (let _171_148 = (let _171_133 = (let _171_132 = (FStar_Util.string_of_int n)
in (let _171_131 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _171_132 _171_131)))
in FStar_SMTEncoding_Term.Caption (_171_133))
in (let _171_147 = (let _171_146 = (let _171_138 = (let _171_137 = (let _171_136 = (let _171_135 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (let _171_134 = (FStar_SMTEncoding_Term.n_fuel n)
in (_171_135, _171_134)))
in (FStar_SMTEncoding_Term.mkEq _171_136))
in (_171_137, None))
in FStar_SMTEncoding_Term.Assume (_171_138))
in (let _171_145 = (let _171_144 = (let _171_143 = (let _171_142 = (let _171_141 = (let _171_140 = (FStar_SMTEncoding_Term.mkApp ("MaxIFuel", []))
in (let _171_139 = (FStar_SMTEncoding_Term.n_fuel i)
in (_171_140, _171_139)))
in (FStar_SMTEncoding_Term.mkEq _171_141))
in (_171_142, None))
in FStar_SMTEncoding_Term.Assume (_171_143))
in (_171_144)::(p)::[])
in (_171_146)::_171_145))
in (_171_148)::_171_147))
in (FStar_List.append _171_149 label_assumptions))
in (let _171_153 = (let _171_152 = (let _171_151 = (let _171_150 = (FStar_Util.string_of_int timeout_ms)
in ("timeout", _171_150))
in FStar_SMTEncoding_Term.SetOption (_171_151))
in (_171_152)::[])
in (FStar_List.append _171_154 _171_153)))
in (FStar_List.append _171_155 ((FStar_SMTEncoding_Term.CheckSat)::[])))
in (FStar_List.append _171_156 suffix)))
end))
in (

let check = (fun p -> (

let default_config = (let _171_160 = (FStar_Options.initial_fuel ())
in (let _171_159 = (FStar_Options.initial_ifuel ())
in (_171_160, _171_159)))
in (

let is_cached_config = (FStar_Util.mk_ref false)
in (

let initial_config = (match ((FStar_ST.read FStar_SMTEncoding_Z3.fuel_trace)) with
| FStar_SMTEncoding_Z3.ReplayFuelTrace (fname, hd::tl) -> begin
(

let _82_411 = (match (hd) with
| Some (a, b) -> begin
(

let _82_406 = (FStar_ST.op_Colon_Equals is_cached_config true)
in (a, b))
end
| None -> begin
default_config
end)
in (match (_82_411) with
| (fuel, ifuel) -> begin
(

let _82_412 = (FStar_ST.op_Colon_Equals FStar_SMTEncoding_Z3.fuel_trace (FStar_SMTEncoding_Z3.ReplayFuelTrace ((fname, tl))))
in (fuel, ifuel))
end))
end
| _82_415 -> begin
default_config
end)
in (

let alt_configs = (let _171_180 = (let _171_179 = (let _171_178 = if ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ())) then begin
(let _171_163 = (let _171_162 = (FStar_Options.initial_fuel ())
in (let _171_161 = (FStar_Options.max_ifuel ())
in (_171_162, _171_161)))
in (_171_163)::[])
end else begin
[]
end
in (let _171_177 = (let _171_176 = if (((FStar_Options.max_fuel ()) / 2) > (FStar_Options.initial_fuel ())) then begin
(let _171_166 = (let _171_165 = ((FStar_Options.max_fuel ()) / 2)
in (let _171_164 = (FStar_Options.max_ifuel ())
in (_171_165, _171_164)))
in (_171_166)::[])
end else begin
[]
end
in (let _171_175 = (let _171_174 = if (((FStar_Options.max_fuel ()) > (FStar_Options.initial_fuel ())) && ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ()))) then begin
(let _171_169 = (let _171_168 = (FStar_Options.max_fuel ())
in (let _171_167 = (FStar_Options.max_ifuel ())
in (_171_168, _171_167)))
in (_171_169)::[])
end else begin
[]
end
in (let _171_173 = (let _171_172 = if ((FStar_Options.min_fuel ()) < (FStar_Options.initial_fuel ())) then begin
(let _171_171 = (let _171_170 = (FStar_Options.min_fuel ())
in (_171_170, 1))
in (_171_171)::[])
end else begin
[]
end
in (_171_172)::[])
in (_171_174)::_171_173))
in (_171_176)::_171_175))
in (_171_178)::_171_177))
in (if (default_config = initial_config) then begin
[]
end else begin
(default_config)::[]
end)::_171_179)
in (FStar_List.flatten _171_180))
in (

let report = (fun p errs -> (

let errs = if ((FStar_Options.detail_errors ()) && ((FStar_Options.n_cores ()) = 1)) then begin
(

let _82_428 = (match ((FStar_ST.read minimum_workable_fuel)) with
| Some (f, errs) -> begin
(f, errs)
end
| None -> begin
(let _171_186 = (let _171_185 = (FStar_Options.min_fuel ())
in (_171_185, 1))
in (_171_186, errs))
end)
in (match (_82_428) with
| (min_fuel, potential_errors) -> begin
(

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref None)
in (

let _82_433 = (let _171_190 = (with_fuel label_assumptions p min_fuel true)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _171_190 (fun r -> (FStar_ST.op_Colon_Equals res (Some (r))))))
in (let _171_191 = (FStar_ST.read res)
in (FStar_Option.get _171_191)))))
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
| _82_438 -> begin
errs
end)
in (

let _82_446 = (match ((FStar_ST.read FStar_SMTEncoding_Z3.fuel_trace)) with
| (FStar_SMTEncoding_Z3.FuelTraceUnavailable) | (FStar_SMTEncoding_Z3.ReplayFuelTrace (_)) -> begin
()
end
| FStar_SMTEncoding_Z3.RecordFuelTrace (l) -> begin
(FStar_ST.op_Colon_Equals FStar_SMTEncoding_Z3.fuel_trace (FStar_SMTEncoding_Z3.RecordFuelTrace ((FStar_List.append l ((None)::[])))))
end)
in (

let _82_448 = if (FStar_Options.print_fuels ()) then begin
(let _171_197 = (let _171_192 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _171_192))
in (let _171_196 = (let _171_193 = (FStar_Options.max_fuel ())
in (FStar_All.pipe_right _171_193 FStar_Util.string_of_int))
in (let _171_195 = (let _171_194 = (FStar_Options.max_ifuel ())
in (FStar_All.pipe_right _171_194 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _171_197 _171_196 _171_195))))
end else begin
()
end
in (

let _82_455 = (let _171_199 = (FStar_All.pipe_right errs (FStar_List.map (fun _82_454 -> (match (_82_454) with
| (_82_451, x, y) -> begin
(x, y)
end))))
in (FStar_TypeChecker_Errors.add_errors env _171_199))
in if (FStar_Options.detail_errors ()) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Detailed error report follows\n")))
end else begin
()
end))))))
in (

let rec try_alt_configs = (fun prev_f p errs cfgs -> (

let _82_463 = (set_minimum_workable_fuel prev_f errs)
in (match (cfgs) with
| [] -> begin
(report p errs)
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _171_212 = (with_fuel [] p mi true)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _171_212 (cb mi p [])))
end
| _82_470 -> begin
(

let _82_471 = (set_minimum_workable_fuel prev_f errs)
in (report p errs))
end)
end
| mi::tl -> begin
(let _171_214 = (with_fuel [] p mi true)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _171_214 (fun _82_478 -> (match (_82_478) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _82_481 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end)))
and cb = (fun _82_484 p alt _82_489 -> (match ((_82_484, _82_489)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
(

let _82_496 = (match ((FStar_ST.read FStar_SMTEncoding_Z3.fuel_trace)) with
| (FStar_SMTEncoding_Z3.ReplayFuelTrace (_)) | (FStar_SMTEncoding_Z3.FuelTraceUnavailable) -> begin
()
end
| FStar_SMTEncoding_Z3.RecordFuelTrace (l) -> begin
(FStar_ST.op_Colon_Equals FStar_SMTEncoding_Z3.fuel_trace (FStar_SMTEncoding_Z3.RecordFuelTrace ((FStar_List.append l ((Some ((prev_fuel, prev_ifuel)))::[])))))
end)
in if (FStar_Options.print_fuels ()) then begin
(let _171_223 = (let _171_219 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _171_219))
in (let _171_222 = (FStar_Util.string_of_int prev_fuel)
in (let _171_221 = (FStar_Util.string_of_int prev_ifuel)
in (let _171_220 = if (FStar_ST.read is_cached_config) then begin
" (cached)"
end else begin
""
end
in (FStar_Util.print4 "(%s) Query succeeded with fuel %s and ifuel %s%s\n" _171_223 _171_222 _171_221 _171_220)))))
end else begin
()
end)
end else begin
(

let _82_498 = if (FStar_Options.print_fuels ()) then begin
(let _171_227 = (let _171_224 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _171_224))
in (let _171_226 = (FStar_Util.string_of_int prev_fuel)
in (let _171_225 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query failed with fuel %s and ifuel %s ... retrying \n" _171_227 _171_226 _171_225))))
end else begin
()
end
in (

let _82_500 = (FStar_ST.op_Colon_Equals is_cached_config false)
in (try_alt_configs (prev_fuel, prev_ifuel) p errs alt)))
end
end))
in (let _171_229 = (let _171_228 = (not ((FStar_ST.read is_cached_config)))
in (with_fuel [] p initial_config _171_228))
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _171_229 (cb initial_config p alt_configs))))))))))
in (

let process_query = (fun q -> if ((FStar_Options.split_cases ()) > 0) then begin
(

let _82_506 = (let _171_235 = (FStar_Options.split_cases ())
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _171_235 q))
in (match (_82_506) with
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




