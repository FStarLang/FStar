
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
| ((Some (reason), r))::_82_36 -> begin
(reason, r)
end
| ((None, r))::_82_43 -> begin
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
| ((Some (reason), _82_72))::_82_68 -> begin
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
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]) -> begin
(match (lhs.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, (typing)::({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.hash = _82_127; FStar_SMTEncoding_Term.freevars = _82_125})::[])::[], iopt, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r)::[]); FStar_SMTEncoding_Term.hash = _82_142; FStar_SMTEncoding_Term.freevars = _82_140}); FStar_SMTEncoding_Term.hash = _82_122; FStar_SMTEncoding_Term.freevars = _82_120})::[]) -> begin
(

let _82_160 = (aux rs r labs)
in (match (_82_160) with
| (r, labs, rs) -> begin
(

let q = (let _171_49 = (let _171_48 = (let _171_47 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.Iff, (l)::(r)::[]))))
in (FStar_SMTEncoding_Term.Forall, ((p)::[])::[], Some (0), sorts, _171_47))
in FStar_SMTEncoding_Term.Quant (_171_48))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk _171_49))
in (

let lhs = (FStar_All.pipe_left FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.And, (typing)::(q)::[]))))
in (

let _82_166 = (aux rs rhs labs)
in (match (_82_166) with
| (rhs, labs, rs) -> begin
(let _171_50 = (FStar_SMTEncoding_Term.mkImp (lhs, rhs))
in (_171_50, labs, rs))
end))))
end))
end
| _82_168 -> begin
(

let _82_172 = (aux rs rhs labs)
in (match (_82_172) with
| (rhs, labs, rs) -> begin
(let _171_51 = (FStar_SMTEncoding_Term.mkImp (lhs, rhs))
in (_171_51, labs, rs))
end))
end)
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(

let _82_189 = (FStar_List.fold_left (fun _82_180 c -> (match (_82_180) with
| (rs, cs, labs) -> begin
(

let _82_185 = (aux rs c labs)
in (match (_82_185) with
| (c, labs, rs) -> begin
(rs, (c)::cs, labs)
end))
end)) (rs, [], labs) conjuncts)
in (match (_82_189) with
| (rs, conjuncts, labs) -> begin
(

let tm = (FStar_List.fold_left (fun out conjunct -> (FStar_SMTEncoding_Term.mkAnd (out, conjunct))) FStar_SMTEncoding_Term.mkTrue conjuncts)
in (tm, labs, rs))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]) -> begin
(

let _82_204 = (aux rs q1 labs)
in (match (_82_204) with
| (q1, labs, _82_203) -> begin
(

let _82_209 = (aux rs q2 labs)
in (match (_82_209) with
| (q2, labs, _82_208) -> begin
(let _171_56 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]))))
in (_171_56, labs, rs))
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

let _82_331 = (aux rs body labs)
in (match (_82_331) with
| (body, labs, rs) -> begin
(let _171_57 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant ((FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body))))
in (_171_57, labs, rs))
end))
end))
in (aux [] q [])))
end)))


let detail_errors : labels  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  (Prims.bool * labels))  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun all_labels potential_errors askZ3 -> (

let ctr = (FStar_Util.mk_ref 0)
in (

let elim = (fun labs -> (

let _82_338 = (FStar_Util.incr ctr)
in (let _171_80 = (let _171_73 = (let _171_72 = (let _171_71 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _171_71))
in (Prims.strcat "DETAILING ERRORS" _171_72))
in FStar_SMTEncoding_Term.Echo (_171_73))
in (let _171_79 = (FStar_All.pipe_right labs (FStar_List.map (fun _82_345 -> (match (_82_345) with
| (l, _82_342, _82_344) -> begin
(let _171_78 = (let _171_77 = (let _171_76 = (let _171_75 = (FStar_SMTEncoding_Term.mkFreeV l)
in (_171_75, FStar_SMTEncoding_Term.mkTrue))
in (FStar_SMTEncoding_Term.mkEq _171_76))
in (_171_77, Some ("Disabling label"), Some ((Prims.strcat "disable_label_" (Prims.fst l)))))
in FStar_SMTEncoding_Term.Assume (_171_78))
end))))
in (_171_80)::_171_79))))
in (

let print_labs = (fun tag l -> (FStar_All.pipe_right l (FStar_List.iter (fun _82_354 -> (match (_82_354) with
| (l, _82_351, _82_353) -> begin
(FStar_Util.print2 "%s : %s; " tag (Prims.fst l))
end)))))
in (

let minus = (fun l1 l2 -> (FStar_All.pipe_right l1 (FStar_List.filter (fun _82_366 -> (match (_82_366) with
| ((x, _82_360), _82_363, _82_365) -> begin
(not ((FStar_All.pipe_right l2 (FStar_Util.for_some (fun _82_375 -> (match (_82_375) with
| ((y, _82_369), _82_372, _82_374) -> begin
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
| (hd)::tl -> begin
(

let _82_388 = (let _171_98 = (FStar_All.pipe_left elim (FStar_List.append (FStar_List.append eliminated errors) tl))
in (askZ3 _171_98))
in (match (_82_388) with
| (ok, _82_387) -> begin
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
| _82_395 -> begin
(

let _82_403 = (match (active) with
| (_82_397)::[] -> begin
(active, [])
end
| _82_400 -> begin
(FStar_Util.first_N ((FStar_List.length active) / 2) active)
end)
in (match (_82_403) with
| (pfx, sfx) -> begin
(

let _82_406 = (let _171_105 = (elim (FStar_List.append (FStar_List.append eliminated potential_errors) sfx))
in (askZ3 _171_105))
in (match (_82_406) with
| (ok, pfx_subset) -> begin
if ok then begin
(bisect (FStar_List.append eliminated pfx) potential_errors sfx)
end else begin
(match (pfx_subset) with
| [] -> begin
(bisect eliminated (FStar_List.append potential_errors pfx) sfx)
end
| _82_409 -> begin
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

let _82_418 = (bisect eliminated potential_errors active)
in (match (_82_418) with
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

let _82_426 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (

let minimum_workable_fuel = (FStar_Util.mk_ref None)
in (

let set_minimum_workable_fuel = (fun f _82_1 -> (match (_82_1) with
| [] -> begin
()
end
| errs -> begin
(match ((FStar_ST.read minimum_workable_fuel)) with
| Some (_82_435) -> begin
()
end
| None -> begin
(FStar_ST.op_Colon_Equals minimum_workable_fuel (Some ((f, errs))))
end)
end))
in (

let with_fuel = (fun label_assumptions p _82_443 -> (match (_82_443) with
| (n, i) -> begin
(let _171_160 = (let _171_159 = (let _171_158 = (let _171_152 = (let _171_151 = (let _171_136 = (let _171_135 = (FStar_Util.string_of_int n)
in (let _171_134 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _171_135 _171_134)))
in FStar_SMTEncoding_Term.Caption (_171_136))
in (let _171_150 = (let _171_149 = (let _171_141 = (let _171_140 = (let _171_139 = (let _171_138 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (let _171_137 = (FStar_SMTEncoding_Term.n_fuel n)
in (_171_138, _171_137)))
in (FStar_SMTEncoding_Term.mkEq _171_139))
in (_171_140, None, None))
in FStar_SMTEncoding_Term.Assume (_171_141))
in (let _171_148 = (let _171_147 = (let _171_146 = (let _171_145 = (let _171_144 = (let _171_143 = (FStar_SMTEncoding_Term.mkApp ("MaxIFuel", []))
in (let _171_142 = (FStar_SMTEncoding_Term.n_fuel i)
in (_171_143, _171_142)))
in (FStar_SMTEncoding_Term.mkEq _171_144))
in (_171_145, None, None))
in FStar_SMTEncoding_Term.Assume (_171_146))
in (_171_147)::(p)::[])
in (_171_149)::_171_148))
in (_171_151)::_171_150))
in (FStar_List.append _171_152 label_assumptions))
in (let _171_157 = (let _171_156 = (let _171_155 = (let _171_154 = (let _171_153 = ((FStar_Options.z3_timeout ()) * 1000)
in (FStar_All.pipe_left FStar_Util.string_of_int _171_153))
in ("timeout", _171_154))
in FStar_SMTEncoding_Term.SetOption (_171_155))
in (_171_156)::[])
in (FStar_List.append _171_158 _171_157)))
in (FStar_List.append _171_159 ((FStar_SMTEncoding_Term.CheckSat)::[])))
in (FStar_List.append _171_160 suffix))
end))
in (

let check = (fun p -> (

let initial_config = (let _171_164 = (FStar_Options.initial_fuel ())
in (let _171_163 = (FStar_Options.initial_ifuel ())
in (_171_164, _171_163)))
in (

let alt_configs = (let _171_183 = (let _171_182 = if ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ())) then begin
(let _171_167 = (let _171_166 = (FStar_Options.initial_fuel ())
in (let _171_165 = (FStar_Options.max_ifuel ())
in (_171_166, _171_165)))
in (_171_167)::[])
end else begin
[]
end
in (let _171_181 = (let _171_180 = if (((FStar_Options.max_fuel ()) / 2) > (FStar_Options.initial_fuel ())) then begin
(let _171_170 = (let _171_169 = ((FStar_Options.max_fuel ()) / 2)
in (let _171_168 = (FStar_Options.max_ifuel ())
in (_171_169, _171_168)))
in (_171_170)::[])
end else begin
[]
end
in (let _171_179 = (let _171_178 = if (((FStar_Options.max_fuel ()) > (FStar_Options.initial_fuel ())) && ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ()))) then begin
(let _171_173 = (let _171_172 = (FStar_Options.max_fuel ())
in (let _171_171 = (FStar_Options.max_ifuel ())
in (_171_172, _171_171)))
in (_171_173)::[])
end else begin
[]
end
in (let _171_177 = (let _171_176 = if ((FStar_Options.min_fuel ()) < (FStar_Options.initial_fuel ())) then begin
(let _171_175 = (let _171_174 = (FStar_Options.min_fuel ())
in (_171_174, 1))
in (_171_175)::[])
end else begin
[]
end
in (_171_176)::[])
in (_171_178)::_171_177))
in (_171_180)::_171_179))
in (_171_182)::_171_181))
in (FStar_List.flatten _171_183))
in (

let report = (fun p errs -> (

let errs = if ((FStar_Options.detail_errors ()) && ((FStar_Options.n_cores ()) = 1)) then begin
(

let _82_458 = (match ((FStar_ST.read minimum_workable_fuel)) with
| Some (f, errs) -> begin
(f, errs)
end
| None -> begin
(let _171_189 = (let _171_188 = (FStar_Options.min_fuel ())
in (_171_188, 1))
in (_171_189, errs))
end)
in (match (_82_458) with
| (min_fuel, potential_errors) -> begin
(

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref None)
in (

let _82_463 = (let _171_193 = (with_fuel label_assumptions p min_fuel)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _171_193 (fun r -> (FStar_ST.op_Colon_Equals res (Some (r))))))
in (let _171_194 = (FStar_ST.read res)
in (FStar_Option.get _171_194)))))
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
| _82_468 -> begin
errs
end)
in (

let _82_470 = if (FStar_Options.print_fuels ()) then begin
(let _171_200 = (let _171_195 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _171_195))
in (let _171_199 = (let _171_196 = (FStar_Options.max_fuel ())
in (FStar_All.pipe_right _171_196 FStar_Util.string_of_int))
in (let _171_198 = (let _171_197 = (FStar_Options.max_ifuel ())
in (FStar_All.pipe_right _171_197 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _171_200 _171_199 _171_198))))
end else begin
()
end
in (

let _82_477 = (let _171_202 = (FStar_All.pipe_right errs (FStar_List.map (fun _82_476 -> (match (_82_476) with
| (_82_473, x, y) -> begin
(x, y)
end))))
in (FStar_TypeChecker_Errors.add_errors env _171_202))
in if (FStar_Options.detail_errors ()) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Detailed error report follows\n")))
end else begin
()
end)))))
in (

let rec try_alt_configs = (fun prev_f p errs cfgs -> (

let _82_485 = (set_minimum_workable_fuel prev_f errs)
in (match (cfgs) with
| [] -> begin
(report p errs)
end
| (mi)::[] -> begin
(match (errs) with
| [] -> begin
(let _171_215 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _171_215 (cb mi p [])))
end
| _82_492 -> begin
(

let _82_493 = (set_minimum_workable_fuel prev_f errs)
in (report p errs))
end)
end
| (mi)::tl -> begin
(let _171_217 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _171_217 (fun _82_500 -> (match (_82_500) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _82_503 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end)))
and cb = (fun _82_506 p alt _82_511 -> (match ((_82_506, _82_511)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
if (FStar_Options.print_fuels ()) then begin
(let _171_225 = (let _171_222 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _171_222))
in (let _171_224 = (FStar_Util.string_of_int prev_fuel)
in (let _171_223 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _171_225 _171_224 _171_223))))
end else begin
()
end
end else begin
(

let _82_512 = if (FStar_Options.print_fuels ()) then begin
(let _171_229 = (let _171_226 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _171_226))
in (let _171_228 = (FStar_Util.string_of_int prev_fuel)
in (let _171_227 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query failed with fuel %s and ifuel %s ... retrying \n" _171_229 _171_228 _171_227))))
end else begin
()
end
in (try_alt_configs (prev_fuel, prev_ifuel) p errs alt))
end
end))
in (let _171_230 = (with_fuel [] p initial_config)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _171_230 (cb initial_config p alt_configs))))))))
in (

let process_query = (fun q -> if ((FStar_Options.split_cases ()) > 0) then begin
(

let _82_518 = (let _171_236 = (FStar_Options.split_cases ())
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _171_236 q))
in (match (_82_518) with
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




