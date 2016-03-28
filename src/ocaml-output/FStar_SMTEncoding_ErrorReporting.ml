
open Prims
# 22 "FStar.SMTEncoding.ErrorReporting.fst"
type label =
FStar_SMTEncoding_Term.error_label

# 24 "FStar.SMTEncoding.ErrorReporting.fst"
type labels =
FStar_SMTEncoding_Term.error_labels

# 25 "FStar.SMTEncoding.ErrorReporting.fst"
let sort_labels : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun l -> (FStar_List.sortWith (fun _78_8 _78_14 -> (match ((_78_8, _78_14)) with
| ((_78_4, _78_6, r1), (_78_10, _78_12, r2)) -> begin
(FStar_Range.compare r1 r2)
end)) l))

# 26 "FStar.SMTEncoding.ErrorReporting.fst"
let remove_dups : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * Prims.int64) Prims.list = (fun l -> (FStar_Util.remove_dups (fun _78_20 _78_25 -> (match ((_78_20, _78_25)) with
| ((_78_17, m1, r1), (_78_22, m2, r2)) -> begin
((r1 = r2) && (m1 = m2))
end)) l))

# 27 "FStar.SMTEncoding.ErrorReporting.fst"
type msg =
(Prims.string * FStar_Range.range)

# 28 "FStar.SMTEncoding.ErrorReporting.fst"
type ranges =
(Prims.string Prims.option * FStar_Range.range) Prims.list

# 29 "FStar.SMTEncoding.ErrorReporting.fst"
let fresh_label : ranges  ->  FStar_SMTEncoding_Term.term  ->  labels  ->  (FStar_SMTEncoding_Term.term * labels) = (
# 32 "FStar.SMTEncoding.ErrorReporting.fst"
let ctr = (FStar_ST.alloc 0)
in (fun rs t labs -> (
# 34 "FStar.SMTEncoding.ErrorReporting.fst"
let l = (
# 34 "FStar.SMTEncoding.ErrorReporting.fst"
let _78_30 = (FStar_Util.incr ctr)
in (let _163_16 = (let _163_15 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _163_15))
in (FStar_Util.format1 "label_%s" _163_16)))
in (
# 35 "FStar.SMTEncoding.ErrorReporting.fst"
let lvar = (l, FStar_SMTEncoding_Term.Bool_sort)
in (
# 36 "FStar.SMTEncoding.ErrorReporting.fst"
let _78_50 = (match (rs) with
| [] -> begin
(t.FStar_SMTEncoding_Term.hash, FStar_Range.dummyRange)
end
| (Some (reason), r)::_78_36 -> begin
(reason, r)
end
| (None, r)::_78_43 -> begin
("failed to prove a pre-condition", r)
end)
in (match (_78_50) with
| (message, range) -> begin
(
# 40 "FStar.SMTEncoding.ErrorReporting.fst"
let label = (lvar, message, range)
in (
# 41 "FStar.SMTEncoding.ErrorReporting.fst"
let lterm = (FStar_SMTEncoding_Term.mkFreeV lvar)
in (
# 42 "FStar.SMTEncoding.ErrorReporting.fst"
let lt = (FStar_SMTEncoding_Term.mkOr (lterm, t))
in (lt, (label)::labs))))
end))))))

# 43 "FStar.SMTEncoding.ErrorReporting.fst"
let label_goals : (Prims.unit  ->  Prims.string) Prims.option  ->  Prims.int64  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * labels * ranges) = (fun use_env_msg r q -> (
# 53 "FStar.SMTEncoding.ErrorReporting.fst"
let _78_62 = (match (use_env_msg) with
| None -> begin
(false, "")
end
| Some (f) -> begin
(let _163_32 = (f ())
in (true, _163_32))
end)
in (match (_78_62) with
| (flag, msg_prefix) -> begin
(
# 56 "FStar.SMTEncoding.ErrorReporting.fst"
let fresh_label = (fun rs t labs -> (
# 57 "FStar.SMTEncoding.ErrorReporting.fst"
let rs' = if (not (flag)) then begin
rs
end else begin
(match (rs) with
| (Some (reason), _78_72)::_78_68 -> begin
((Some ((Prims.strcat "Failed to verify implicit argument: " reason)), r))::[]
end
| _78_76 -> begin
((Some ("Failed to verify implicit argument"), r))::[]
end)
end
in (
# 62 "FStar.SMTEncoding.ErrorReporting.fst"
let _78_80 = (fresh_label rs' t labs)
in (match (_78_80) with
| (lt, labs) -> begin
(lt, labs, rs)
end))))
in (
# 64 "FStar.SMTEncoding.ErrorReporting.fst"
let rec aux = (fun rs q labs -> (match (q.FStar_SMTEncoding_Term.tm) with
| (FStar_SMTEncoding_Term.BoundV (_)) | (FStar_SMTEncoding_Term.Integer (_)) -> begin
(q, labs, rs)
end
| FStar_SMTEncoding_Term.Labeled (_78_92, "push", r) -> begin
(FStar_SMTEncoding_Term.mkTrue, labs, ((None, r))::rs)
end
| FStar_SMTEncoding_Term.Labeled (_78_98, "pop", r) -> begin
(let _163_45 = (FStar_List.tl rs)
in (FStar_SMTEncoding_Term.mkTrue, labs, _163_45))
end
| FStar_SMTEncoding_Term.Labeled (arg, reason, r) -> begin
(
# 76 "FStar.SMTEncoding.ErrorReporting.fst"
let _78_111 = (aux (((Some (reason), r))::rs) arg labs)
in (match (_78_111) with
| (tm, labs, rs) -> begin
(let _163_46 = (FStar_List.tl rs)
in (tm, labs, _163_46))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, lhs::rhs::[]) -> begin
(
# 80 "FStar.SMTEncoding.ErrorReporting.fst"
let _78_121 = (aux rs rhs labs)
in (match (_78_121) with
| (rhs, labs, rs) -> begin
(let _163_47 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]))))
in (_163_47, labs, rs))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(
# 84 "FStar.SMTEncoding.ErrorReporting.fst"
let _78_138 = (FStar_List.fold_left (fun _78_129 c -> (match (_78_129) with
| (rs, cs, labs) -> begin
(
# 85 "FStar.SMTEncoding.ErrorReporting.fst"
let _78_134 = (aux rs c labs)
in (match (_78_134) with
| (c, labs, rs) -> begin
(rs, (c)::cs, labs)
end))
end)) (rs, [], labs) conjuncts)
in (match (_78_138) with
| (rs, conjuncts, labs) -> begin
(let _163_50 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.And, (FStar_List.rev conjuncts)))))
in (_163_50, labs, rs))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, hd::q1::q2::[]) -> begin
(
# 92 "FStar.SMTEncoding.ErrorReporting.fst"
let _78_150 = (aux rs q1 labs)
in (match (_78_150) with
| (q1, labs, _78_149) -> begin
(
# 93 "FStar.SMTEncoding.ErrorReporting.fst"
let _78_155 = (aux rs q2 labs)
in (match (_78_155) with
| (q2, labs, _78_154) -> begin
(let _163_51 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]))))
in (_163_51, labs, rs))
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
# 126 "FStar.SMTEncoding.ErrorReporting.fst"
let _78_277 = (aux rs body labs)
in (match (_78_277) with
| (body, labs, rs) -> begin
(let _163_52 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant ((FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body))))
in (_163_52, labs, rs))
end))
end))
in (aux [] q [])))
end)))

# 128 "FStar.SMTEncoding.ErrorReporting.fst"
let detail_errors : labels  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  (Prims.bool * labels))  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun all_labels potential_errors askZ3 -> (
# 141 "FStar.SMTEncoding.ErrorReporting.fst"
let ctr = (FStar_Util.mk_ref 0)
in (
# 142 "FStar.SMTEncoding.ErrorReporting.fst"
let elim = (fun labs -> (
# 143 "FStar.SMTEncoding.ErrorReporting.fst"
let _78_284 = (FStar_Util.incr ctr)
in (let _163_75 = (let _163_68 = (let _163_67 = (let _163_66 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _163_66))
in (Prims.strcat "DETAILING ERRORS" _163_67))
in FStar_SMTEncoding_Term.Echo (_163_68))
in (let _163_74 = (FStar_All.pipe_right labs (FStar_List.map (fun _78_291 -> (match (_78_291) with
| (l, _78_288, _78_290) -> begin
(let _163_73 = (let _163_72 = (let _163_71 = (let _163_70 = (FStar_SMTEncoding_Term.mkFreeV l)
in (_163_70, FStar_SMTEncoding_Term.mkTrue))
in (FStar_SMTEncoding_Term.mkEq _163_71))
in (_163_72, Some ("Disabling label")))
in FStar_SMTEncoding_Term.Assume (_163_73))
end))))
in (_163_75)::_163_74))))
in (
# 146 "FStar.SMTEncoding.ErrorReporting.fst"
let print_labs = (fun tag l -> (FStar_All.pipe_right l (FStar_List.iter (fun _78_300 -> (match (_78_300) with
| (l, _78_297, _78_299) -> begin
(FStar_Util.print2 "%s : %s; " tag (Prims.fst l))
end)))))
in (
# 148 "FStar.SMTEncoding.ErrorReporting.fst"
let minus = (fun l1 l2 -> (FStar_All.pipe_right l1 (FStar_List.filter (fun _78_312 -> (match (_78_312) with
| ((x, _78_306), _78_309, _78_311) -> begin
(not ((FStar_All.pipe_right l2 (FStar_Util.for_some (fun _78_321 -> (match (_78_321) with
| ((y, _78_315), _78_318, _78_320) -> begin
(x = y)
end))))))
end)))))
in (
# 153 "FStar.SMTEncoding.ErrorReporting.fst"
let rec linear_check = (fun eliminated errors active -> (match (active) with
| [] -> begin
(
# 155 "FStar.SMTEncoding.ErrorReporting.fst"
let labs = (FStar_All.pipe_right errors sort_labels)
in labs)
end
| hd::tl -> begin
(
# 159 "FStar.SMTEncoding.ErrorReporting.fst"
let _78_334 = (let _163_93 = (FStar_All.pipe_left elim (FStar_List.append (FStar_List.append eliminated errors) tl))
in (askZ3 _163_93))
in (match (_78_334) with
| (ok, _78_333) -> begin
if ok then begin
(linear_check ((hd)::eliminated) errors tl)
end else begin
(linear_check eliminated ((hd)::errors) tl)
end
end))
end))
in (
# 165 "FStar.SMTEncoding.ErrorReporting.fst"
let rec bisect = (fun eliminated potential_errors active -> (match (active) with
| [] -> begin
(eliminated, potential_errors)
end
| _78_341 -> begin
(
# 169 "FStar.SMTEncoding.ErrorReporting.fst"
let _78_349 = (match (active) with
| _78_343::[] -> begin
(active, [])
end
| _78_346 -> begin
(FStar_Util.first_N ((FStar_List.length active) / 2) active)
end)
in (match (_78_349) with
| (pfx, sfx) -> begin
(
# 172 "FStar.SMTEncoding.ErrorReporting.fst"
let _78_352 = (let _163_100 = (elim (FStar_List.append (FStar_List.append eliminated potential_errors) sfx))
in (askZ3 _163_100))
in (match (_78_352) with
| (ok, pfx_subset) -> begin
if ok then begin
(bisect (FStar_List.append eliminated pfx) potential_errors sfx)
end else begin
(match (pfx_subset) with
| [] -> begin
(bisect eliminated (FStar_List.append potential_errors pfx) sfx)
end
| _78_355 -> begin
(
# 181 "FStar.SMTEncoding.ErrorReporting.fst"
let potential_errors = (FStar_List.append potential_errors pfx_subset)
in (
# 182 "FStar.SMTEncoding.ErrorReporting.fst"
let pfx_active = (minus pfx pfx_subset)
in (bisect eliminated potential_errors (FStar_List.append pfx_active sfx))))
end)
end
end))
end))
end))
in (
# 187 "FStar.SMTEncoding.ErrorReporting.fst"
let rec until_fixpoint = (fun eliminated potential_errors active -> (
# 188 "FStar.SMTEncoding.ErrorReporting.fst"
let _78_364 = (bisect eliminated potential_errors active)
in (match (_78_364) with
| (eliminated', potential_errors) -> begin
if (FStar_Util.physical_equality eliminated eliminated') then begin
(linear_check eliminated [] potential_errors)
end else begin
(until_fixpoint eliminated' [] potential_errors)
end
end)))
in (
# 193 "FStar.SMTEncoding.ErrorReporting.fst"
let active = (minus all_labels potential_errors)
in (until_fixpoint [] potential_errors active))))))))))

# 196 "FStar.SMTEncoding.ErrorReporting.fst"
let askZ3_and_report_errors : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * Prims.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun env use_fresh_z3_context all_labels prefix query suffix -> (
# 199 "FStar.SMTEncoding.ErrorReporting.fst"
let _78_372 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (
# 200 "FStar.SMTEncoding.ErrorReporting.fst"
let minimum_workable_fuel = (FStar_Util.mk_ref None)
in (
# 201 "FStar.SMTEncoding.ErrorReporting.fst"
let set_minimum_workable_fuel = (fun f _78_1 -> (match (_78_1) with
| [] -> begin
()
end
| errs -> begin
(match ((FStar_ST.read minimum_workable_fuel)) with
| Some (_78_381) -> begin
()
end
| None -> begin
(FStar_ST.op_Colon_Equals minimum_workable_fuel (Some ((f, errs))))
end)
end))
in (
# 207 "FStar.SMTEncoding.ErrorReporting.fst"
let with_fuel = (fun label_assumptions p _78_389 -> (match (_78_389) with
| (n, i) -> begin
(let _163_149 = (let _163_148 = (let _163_147 = (let _163_146 = (let _163_131 = (let _163_130 = (FStar_Util.string_of_int n)
in (let _163_129 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _163_130 _163_129)))
in FStar_SMTEncoding_Term.Caption (_163_131))
in (let _163_145 = (let _163_144 = (let _163_136 = (let _163_135 = (let _163_134 = (let _163_133 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (let _163_132 = (FStar_SMTEncoding_Term.n_fuel n)
in (_163_133, _163_132)))
in (FStar_SMTEncoding_Term.mkEq _163_134))
in (_163_135, None))
in FStar_SMTEncoding_Term.Assume (_163_136))
in (let _163_143 = (let _163_142 = (let _163_141 = (let _163_140 = (let _163_139 = (let _163_138 = (FStar_SMTEncoding_Term.mkApp ("MaxIFuel", []))
in (let _163_137 = (FStar_SMTEncoding_Term.n_fuel i)
in (_163_138, _163_137)))
in (FStar_SMTEncoding_Term.mkEq _163_139))
in (_163_140, None))
in FStar_SMTEncoding_Term.Assume (_163_141))
in (_163_142)::(p)::[])
in (_163_144)::_163_143))
in (_163_146)::_163_145))
in (FStar_List.append _163_147 label_assumptions))
in (FStar_List.append _163_148 ((FStar_SMTEncoding_Term.CheckSat)::[])))
in (FStar_List.append _163_149 suffix))
end))
in (
# 216 "FStar.SMTEncoding.ErrorReporting.fst"
let check = (fun p -> (
# 217 "FStar.SMTEncoding.ErrorReporting.fst"
let initial_config = (let _163_153 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _163_152 = (FStar_ST.read FStar_Options.initial_ifuel)
in (_163_153, _163_152)))
in (
# 218 "FStar.SMTEncoding.ErrorReporting.fst"
let alt_configs = (let _163_172 = (let _163_171 = if ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel)) then begin
(let _163_156 = (let _163_155 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _163_154 = (FStar_ST.read FStar_Options.max_ifuel)
in (_163_155, _163_154)))
in (_163_156)::[])
end else begin
[]
end
in (let _163_170 = (let _163_169 = if (((FStar_ST.read FStar_Options.max_fuel) / 2) > (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _163_159 = (let _163_158 = ((FStar_ST.read FStar_Options.max_fuel) / 2)
in (let _163_157 = (FStar_ST.read FStar_Options.max_ifuel)
in (_163_158, _163_157)))
in (_163_159)::[])
end else begin
[]
end
in (let _163_168 = (let _163_167 = if (((FStar_ST.read FStar_Options.max_fuel) > (FStar_ST.read FStar_Options.initial_fuel)) && ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel))) then begin
(let _163_162 = (let _163_161 = (FStar_ST.read FStar_Options.max_fuel)
in (let _163_160 = (FStar_ST.read FStar_Options.max_ifuel)
in (_163_161, _163_160)))
in (_163_162)::[])
end else begin
[]
end
in (let _163_166 = (let _163_165 = if ((FStar_ST.read FStar_Options.min_fuel) < (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _163_164 = (let _163_163 = (FStar_ST.read FStar_Options.min_fuel)
in (_163_163, 1))
in (_163_164)::[])
end else begin
[]
end
in (_163_165)::[])
in (_163_167)::_163_166))
in (_163_169)::_163_168))
in (_163_171)::_163_170))
in (FStar_List.flatten _163_172))
in (
# 223 "FStar.SMTEncoding.ErrorReporting.fst"
let report = (fun p errs -> (
# 224 "FStar.SMTEncoding.ErrorReporting.fst"
let errs = if ((FStar_ST.read FStar_Options.detail_errors) && ((FStar_ST.read FStar_Options.n_cores) = 1)) then begin
(
# 225 "FStar.SMTEncoding.ErrorReporting.fst"
let _78_404 = (match ((FStar_ST.read minimum_workable_fuel)) with
| Some (f, errs) -> begin
(f, errs)
end
| None -> begin
(let _163_178 = (let _163_177 = (FStar_ST.read FStar_Options.min_fuel)
in (_163_177, 1))
in (_163_178, errs))
end)
in (match (_78_404) with
| (min_fuel, potential_errors) -> begin
(
# 228 "FStar.SMTEncoding.ErrorReporting.fst"
let ask_z3 = (fun label_assumptions -> (
# 229 "FStar.SMTEncoding.ErrorReporting.fst"
let res = (FStar_Util.mk_ref None)
in (
# 230 "FStar.SMTEncoding.ErrorReporting.fst"
let _78_409 = (let _163_182 = (with_fuel label_assumptions p min_fuel)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _163_182 (fun r -> (FStar_ST.op_Colon_Equals res (Some (r))))))
in (let _163_183 = (FStar_ST.read res)
in (FStar_Option.get _163_183)))))
in (detail_errors all_labels errs ask_z3))
end))
end else begin
errs
end
in (
# 235 "FStar.SMTEncoding.ErrorReporting.fst"
let errs = (match (errs) with
| [] -> begin
((("", FStar_SMTEncoding_Term.Term_sort), "Unknown assertion failed", FStar_Range.dummyRange))::[]
end
| _78_414 -> begin
errs
end)
in (
# 238 "FStar.SMTEncoding.ErrorReporting.fst"
let _78_416 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _163_189 = (let _163_184 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _163_184))
in (let _163_188 = (let _163_185 = (FStar_ST.read FStar_Options.max_fuel)
in (FStar_All.pipe_right _163_185 FStar_Util.string_of_int))
in (let _163_187 = (let _163_186 = (FStar_ST.read FStar_Options.max_ifuel)
in (FStar_All.pipe_right _163_186 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _163_189 _163_188 _163_187))))
end else begin
()
end
in (
# 243 "FStar.SMTEncoding.ErrorReporting.fst"
let _78_423 = (let _163_191 = (FStar_All.pipe_right errs (FStar_List.map (fun _78_422 -> (match (_78_422) with
| (_78_419, x, y) -> begin
(x, y)
end))))
in (FStar_TypeChecker_Errors.add_errors env _163_191))
in if (FStar_ST.read FStar_Options.detail_errors) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Detailed error report follows\n")))
end else begin
()
end)))))
in (
# 247 "FStar.SMTEncoding.ErrorReporting.fst"
let rec try_alt_configs = (fun prev_f p errs cfgs -> (
# 248 "FStar.SMTEncoding.ErrorReporting.fst"
let _78_431 = (set_minimum_workable_fuel prev_f errs)
in (match (cfgs) with
| [] -> begin
(report p errs)
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _163_204 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _163_204 (cb mi p [])))
end
| _78_438 -> begin
(
# 254 "FStar.SMTEncoding.ErrorReporting.fst"
let _78_439 = (set_minimum_workable_fuel prev_f errs)
in (report p errs))
end)
end
| mi::tl -> begin
(let _163_206 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _163_206 (fun _78_446 -> (match (_78_446) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _78_449 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end)))
and cb = (fun _78_452 p alt _78_457 -> (match ((_78_452, _78_457)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _163_214 = (let _163_211 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _163_211))
in (let _163_213 = (FStar_Util.string_of_int prev_fuel)
in (let _163_212 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _163_214 _163_213 _163_212))))
end else begin
()
end
end else begin
(try_alt_configs (prev_fuel, prev_ifuel) p errs alt)
end
end))
in (let _163_215 = (with_fuel [] p initial_config)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _163_215 (cb initial_config p alt_configs))))))))
in (
# 279 "FStar.SMTEncoding.ErrorReporting.fst"
let process_query = (fun q -> if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(
# 281 "FStar.SMTEncoding.ErrorReporting.fst"
let _78_462 = (let _163_221 = (FStar_ST.read FStar_Options.split_cases)
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _163_221 q))
in (match (_78_462) with
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
in if (FStar_ST.read FStar_Options.admit_smt_queries) then begin
()
end else begin
(process_query query)
end)))))))




