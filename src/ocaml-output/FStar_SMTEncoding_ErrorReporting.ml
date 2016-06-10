
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
(

let _82_121 = (aux rs rhs labs)
in (match (_82_121) with
| (rhs, labs, rs) -> begin
(

let _82_179 = (match (lhs.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(

let _82_170 = (FStar_Util.fold_map (fun _82_128 tm -> (match (_82_128) with
| (labs, rs) -> begin
(match (tm.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, (({FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var ("Prims.guard_free"), (p)::[]); FStar_SMTEncoding_Term.hash = _82_134; FStar_SMTEncoding_Term.freevars = _82_132})::[])::[], iopt, sorts, {FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Iff, (l)::(r)::[]); FStar_SMTEncoding_Term.hash = _82_149; FStar_SMTEncoding_Term.freevars = _82_147}) -> begin
(

let _82_162 = (aux rs r labs)
in (match (_82_162) with
| (r, labs, rs) -> begin
(

let q = (let _171_51 = (let _171_50 = (let _171_49 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.Iff, (l)::(r)::[]))))
in (FStar_SMTEncoding_Term.Forall, ((p)::[])::[], Some (0), sorts, _171_49))
in FStar_SMTEncoding_Term.Quant (_171_50))
in (FStar_All.pipe_left FStar_SMTEncoding_Term.mk _171_51))
in ((labs, rs), q))
end))
end
| _82_165 -> begin
((labs, rs), tm)
end)
end)) (labs, rs) conjuncts)
in (match (_82_170) with
| ((labs, rs), conjuncts) -> begin
(

let tm = (FStar_List.fold_right (fun conjunct out -> (FStar_SMTEncoding_Term.mkAnd (out, conjunct))) conjuncts FStar_SMTEncoding_Term.mkTrue)
in (tm, labs, rs))
end))
end
| _82_175 -> begin
(lhs, labs, rs)
end)
in (match (_82_179) with
| (lhs, labs, rs) -> begin
(let _171_54 = (FStar_SMTEncoding_Term.mkImp (lhs, rhs))
in (_171_54, labs, rs))
end))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(

let _82_196 = (FStar_List.fold_left (fun _82_187 c -> (match (_82_187) with
| (rs, cs, labs) -> begin
(

let _82_192 = (aux rs c labs)
in (match (_82_192) with
| (c, labs, rs) -> begin
(rs, (c)::cs, labs)
end))
end)) (rs, [], labs) conjuncts)
in (match (_82_196) with
| (rs, conjuncts, labs) -> begin
(

let tm = (FStar_List.fold_left (fun out conjunct -> (FStar_SMTEncoding_Term.mkAnd (out, conjunct))) FStar_SMTEncoding_Term.mkTrue conjuncts)
in (tm, labs, rs))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]) -> begin
(

let _82_211 = (aux rs q1 labs)
in (match (_82_211) with
| (q1, labs, _82_210) -> begin
(

let _82_216 = (aux rs q2 labs)
in (match (_82_216) with
| (q2, labs, _82_215) -> begin
(let _171_59 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]))))
in (_171_59, labs, rs))
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

let _82_338 = (aux rs body labs)
in (match (_82_338) with
| (body, labs, rs) -> begin
(let _171_60 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant ((FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body))))
in (_171_60, labs, rs))
end))
end))
in (aux [] q [])))
end)))


let detail_errors : labels  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  (Prims.bool * labels))  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun all_labels potential_errors askZ3 -> (

let ctr = (FStar_Util.mk_ref 0)
in (

let elim = (fun labs -> (

let _82_345 = (FStar_Util.incr ctr)
in (let _171_83 = (let _171_76 = (let _171_75 = (let _171_74 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _171_74))
in (Prims.strcat "DETAILING ERRORS" _171_75))
in FStar_SMTEncoding_Term.Echo (_171_76))
in (let _171_82 = (FStar_All.pipe_right labs (FStar_List.map (fun _82_352 -> (match (_82_352) with
| (l, _82_349, _82_351) -> begin
(let _171_81 = (let _171_80 = (let _171_79 = (let _171_78 = (FStar_SMTEncoding_Term.mkFreeV l)
in (_171_78, FStar_SMTEncoding_Term.mkTrue))
in (FStar_SMTEncoding_Term.mkEq _171_79))
in (_171_80, Some ("Disabling label"), Some ((Prims.strcat "disable_label_" (Prims.fst l)))))
in FStar_SMTEncoding_Term.Assume (_171_81))
end))))
in (_171_83)::_171_82))))
in (

let print_labs = (fun tag l -> (FStar_All.pipe_right l (FStar_List.iter (fun _82_361 -> (match (_82_361) with
| (l, _82_358, _82_360) -> begin
(FStar_Util.print2 "%s : %s; " tag (Prims.fst l))
end)))))
in (

let minus = (fun l1 l2 -> (FStar_All.pipe_right l1 (FStar_List.filter (fun _82_373 -> (match (_82_373) with
| ((x, _82_367), _82_370, _82_372) -> begin
(not ((FStar_All.pipe_right l2 (FStar_Util.for_some (fun _82_382 -> (match (_82_382) with
| ((y, _82_376), _82_379, _82_381) -> begin
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

let _82_395 = (let _171_101 = (FStar_All.pipe_left elim (FStar_List.append (FStar_List.append eliminated errors) tl))
in (askZ3 _171_101))
in (match (_82_395) with
| (ok, _82_394) -> begin
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
| _82_402 -> begin
(

let _82_410 = (match (active) with
| (_82_404)::[] -> begin
(active, [])
end
| _82_407 -> begin
(FStar_Util.first_N ((FStar_List.length active) / 2) active)
end)
in (match (_82_410) with
| (pfx, sfx) -> begin
(

let _82_413 = (let _171_108 = (elim (FStar_List.append (FStar_List.append eliminated potential_errors) sfx))
in (askZ3 _171_108))
in (match (_82_413) with
| (ok, pfx_subset) -> begin
if ok then begin
(bisect (FStar_List.append eliminated pfx) potential_errors sfx)
end else begin
(match (pfx_subset) with
| [] -> begin
(bisect eliminated (FStar_List.append potential_errors pfx) sfx)
end
| _82_416 -> begin
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

let _82_425 = (bisect eliminated potential_errors active)
in (match (_82_425) with
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

let _82_433 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (

let minimum_workable_fuel = (FStar_Util.mk_ref None)
in (

let set_minimum_workable_fuel = (fun f _82_1 -> (match (_82_1) with
| [] -> begin
()
end
| errs -> begin
(match ((FStar_ST.read minimum_workable_fuel)) with
| Some (_82_442) -> begin
()
end
| None -> begin
(FStar_ST.op_Colon_Equals minimum_workable_fuel (Some ((f, errs))))
end)
end))
in (

let with_fuel = (fun label_assumptions p _82_450 -> (match (_82_450) with
| (n, i) -> begin
(let _171_163 = (let _171_162 = (let _171_161 = (let _171_155 = (let _171_154 = (let _171_139 = (let _171_138 = (FStar_Util.string_of_int n)
in (let _171_137 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _171_138 _171_137)))
in FStar_SMTEncoding_Term.Caption (_171_139))
in (let _171_153 = (let _171_152 = (let _171_144 = (let _171_143 = (let _171_142 = (let _171_141 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (let _171_140 = (FStar_SMTEncoding_Term.n_fuel n)
in (_171_141, _171_140)))
in (FStar_SMTEncoding_Term.mkEq _171_142))
in (_171_143, None, None))
in FStar_SMTEncoding_Term.Assume (_171_144))
in (let _171_151 = (let _171_150 = (let _171_149 = (let _171_148 = (let _171_147 = (let _171_146 = (FStar_SMTEncoding_Term.mkApp ("MaxIFuel", []))
in (let _171_145 = (FStar_SMTEncoding_Term.n_fuel i)
in (_171_146, _171_145)))
in (FStar_SMTEncoding_Term.mkEq _171_147))
in (_171_148, None, None))
in FStar_SMTEncoding_Term.Assume (_171_149))
in (_171_150)::(p)::[])
in (_171_152)::_171_151))
in (_171_154)::_171_153))
in (FStar_List.append _171_155 label_assumptions))
in (let _171_160 = (let _171_159 = (let _171_158 = (let _171_157 = (let _171_156 = ((FStar_Options.z3_timeout ()) * 1000)
in (FStar_All.pipe_left FStar_Util.string_of_int _171_156))
in ("timeout", _171_157))
in FStar_SMTEncoding_Term.SetOption (_171_158))
in (_171_159)::[])
in (FStar_List.append _171_161 _171_160)))
in (FStar_List.append _171_162 ((FStar_SMTEncoding_Term.CheckSat)::[])))
in (FStar_List.append _171_163 suffix))
end))
in (

let check = (fun p -> (

let initial_config = (let _171_167 = (FStar_Options.initial_fuel ())
in (let _171_166 = (FStar_Options.initial_ifuel ())
in (_171_167, _171_166)))
in (

let alt_configs = (let _171_186 = (let _171_185 = if ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ())) then begin
(let _171_170 = (let _171_169 = (FStar_Options.initial_fuel ())
in (let _171_168 = (FStar_Options.max_ifuel ())
in (_171_169, _171_168)))
in (_171_170)::[])
end else begin
[]
end
in (let _171_184 = (let _171_183 = if (((FStar_Options.max_fuel ()) / 2) > (FStar_Options.initial_fuel ())) then begin
(let _171_173 = (let _171_172 = ((FStar_Options.max_fuel ()) / 2)
in (let _171_171 = (FStar_Options.max_ifuel ())
in (_171_172, _171_171)))
in (_171_173)::[])
end else begin
[]
end
in (let _171_182 = (let _171_181 = if (((FStar_Options.max_fuel ()) > (FStar_Options.initial_fuel ())) && ((FStar_Options.max_ifuel ()) > (FStar_Options.initial_ifuel ()))) then begin
(let _171_176 = (let _171_175 = (FStar_Options.max_fuel ())
in (let _171_174 = (FStar_Options.max_ifuel ())
in (_171_175, _171_174)))
in (_171_176)::[])
end else begin
[]
end
in (let _171_180 = (let _171_179 = if ((FStar_Options.min_fuel ()) < (FStar_Options.initial_fuel ())) then begin
(let _171_178 = (let _171_177 = (FStar_Options.min_fuel ())
in (_171_177, 1))
in (_171_178)::[])
end else begin
[]
end
in (_171_179)::[])
in (_171_181)::_171_180))
in (_171_183)::_171_182))
in (_171_185)::_171_184))
in (FStar_List.flatten _171_186))
in (

let report = (fun p errs -> (

let errs = if ((FStar_Options.detail_errors ()) && ((FStar_Options.n_cores ()) = 1)) then begin
(

let _82_465 = (match ((FStar_ST.read minimum_workable_fuel)) with
| Some (f, errs) -> begin
(f, errs)
end
| None -> begin
(let _171_192 = (let _171_191 = (FStar_Options.min_fuel ())
in (_171_191, 1))
in (_171_192, errs))
end)
in (match (_82_465) with
| (min_fuel, potential_errors) -> begin
(

let ask_z3 = (fun label_assumptions -> (

let res = (FStar_Util.mk_ref None)
in (

let _82_470 = (let _171_196 = (with_fuel label_assumptions p min_fuel)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _171_196 (fun r -> (FStar_ST.op_Colon_Equals res (Some (r))))))
in (let _171_197 = (FStar_ST.read res)
in (FStar_Option.get _171_197)))))
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
| _82_475 -> begin
errs
end)
in (

let _82_477 = if (FStar_Options.print_fuels ()) then begin
(let _171_203 = (let _171_198 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _171_198))
in (let _171_202 = (let _171_199 = (FStar_Options.max_fuel ())
in (FStar_All.pipe_right _171_199 FStar_Util.string_of_int))
in (let _171_201 = (let _171_200 = (FStar_Options.max_ifuel ())
in (FStar_All.pipe_right _171_200 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _171_203 _171_202 _171_201))))
end else begin
()
end
in (

let _82_484 = (let _171_205 = (FStar_All.pipe_right errs (FStar_List.map (fun _82_483 -> (match (_82_483) with
| (_82_480, x, y) -> begin
(x, y)
end))))
in (FStar_TypeChecker_Errors.add_errors env _171_205))
in if (FStar_Options.detail_errors ()) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Detailed error report follows\n")))
end else begin
()
end)))))
in (

let rec try_alt_configs = (fun prev_f p errs cfgs -> (

let _82_492 = (set_minimum_workable_fuel prev_f errs)
in (match (cfgs) with
| [] -> begin
(report p errs)
end
| (mi)::[] -> begin
(match (errs) with
| [] -> begin
(let _171_218 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _171_218 (cb mi p [])))
end
| _82_499 -> begin
(

let _82_500 = (set_minimum_workable_fuel prev_f errs)
in (report p errs))
end)
end
| (mi)::tl -> begin
(let _171_220 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _171_220 (fun _82_507 -> (match (_82_507) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _82_510 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end)))
and cb = (fun _82_513 p alt _82_518 -> (match ((_82_513, _82_518)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
if (FStar_Options.print_fuels ()) then begin
(let _171_228 = (let _171_225 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _171_225))
in (let _171_227 = (FStar_Util.string_of_int prev_fuel)
in (let _171_226 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _171_228 _171_227 _171_226))))
end else begin
()
end
end else begin
(

let _82_519 = if (FStar_Options.print_fuels ()) then begin
(let _171_232 = (let _171_229 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _171_229))
in (let _171_231 = (FStar_Util.string_of_int prev_fuel)
in (let _171_230 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query failed with fuel %s and ifuel %s ... retrying \n" _171_232 _171_231 _171_230))))
end else begin
()
end
in (try_alt_configs (prev_fuel, prev_ifuel) p errs alt))
end
end))
in (let _171_233 = (with_fuel [] p initial_config)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _171_233 (cb initial_config p alt_configs))))))))
in (

let process_query = (fun q -> if ((FStar_Options.split_cases ()) > 0) then begin
(

let _82_525 = (let _171_239 = (FStar_Options.split_cases ())
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _171_239 q))
in (match (_82_525) with
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




