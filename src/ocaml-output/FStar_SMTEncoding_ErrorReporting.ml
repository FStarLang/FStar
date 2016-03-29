
open Prims
# 22 "FStar.SMTEncoding.ErrorReporting.fst"
type label =
FStar_SMTEncoding_Term.error_label

# 24 "FStar.SMTEncoding.ErrorReporting.fst"
type labels =
FStar_SMTEncoding_Term.error_labels

# 25 "FStar.SMTEncoding.ErrorReporting.fst"
let sort_labels : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun l -> (FStar_List.sortWith (fun _72_8 _72_14 -> (match ((_72_8, _72_14)) with
| ((_72_4, _72_6, r1), (_72_10, _72_12, r2)) -> begin
(FStar_Range.compare r1 r2)
end)) l))

# 26 "FStar.SMTEncoding.ErrorReporting.fst"
let remove_dups : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * Prims.int64) Prims.list = (fun l -> (FStar_Util.remove_dups (fun _72_20 _72_25 -> (match ((_72_20, _72_25)) with
| ((_72_17, m1, r1), (_72_22, m2, r2)) -> begin
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
let _72_30 = (FStar_Util.incr ctr)
in (let _151_16 = (let _151_15 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _151_15))
in (FStar_Util.format1 "label_%s" _151_16)))
in (
# 35 "FStar.SMTEncoding.ErrorReporting.fst"
let lvar = (l, FStar_SMTEncoding_Term.Bool_sort)
in (
# 36 "FStar.SMTEncoding.ErrorReporting.fst"
let _72_50 = (match (rs) with
| [] -> begin
(t.FStar_SMTEncoding_Term.hash, FStar_Range.dummyRange)
end
| (Some (reason), r)::_72_36 -> begin
(reason, r)
end
| (None, r)::_72_43 -> begin
("failed to prove a pre-condition", r)
end)
in (match (_72_50) with
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
let _72_62 = (match (use_env_msg) with
| None -> begin
(false, "")
end
| Some (f) -> begin
(let _151_32 = (f ())
in (true, _151_32))
end)
in (match (_72_62) with
| (flag, msg_prefix) -> begin
(
# 56 "FStar.SMTEncoding.ErrorReporting.fst"
let fresh_label = (fun rs t labs -> (
# 57 "FStar.SMTEncoding.ErrorReporting.fst"
let rs' = if (not (flag)) then begin
rs
end else begin
(match (rs) with
| (Some (reason), _72_72)::_72_68 -> begin
((Some ((Prims.strcat "Failed to verify implicit argument: " reason)), r))::[]
end
| _72_76 -> begin
((Some ("Failed to verify implicit argument"), r))::[]
end)
end
in (
# 62 "FStar.SMTEncoding.ErrorReporting.fst"
let _72_80 = (fresh_label rs' t labs)
in (match (_72_80) with
| (lt, labs) -> begin
(lt, labs, rs)
end))))
in (
# 64 "FStar.SMTEncoding.ErrorReporting.fst"
let rec aux = (fun rs q labs -> (match (q.FStar_SMTEncoding_Term.tm) with
| (FStar_SMTEncoding_Term.BoundV (_)) | (FStar_SMTEncoding_Term.Integer (_)) -> begin
(q, labs, rs)
end
| FStar_SMTEncoding_Term.Labeled (_72_92, "push", r) -> begin
(FStar_SMTEncoding_Term.mkTrue, labs, ((None, r))::rs)
end
| FStar_SMTEncoding_Term.Labeled (_72_98, "pop", r) -> begin
(let _151_45 = (FStar_List.tl rs)
in (FStar_SMTEncoding_Term.mkTrue, labs, _151_45))
end
| FStar_SMTEncoding_Term.Labeled (arg, reason, r) -> begin
(
# 76 "FStar.SMTEncoding.ErrorReporting.fst"
let _72_111 = (aux (((Some (reason), r))::rs) arg labs)
in (match (_72_111) with
| (tm, labs, rs) -> begin
(let _151_46 = (FStar_List.tl rs)
in (tm, labs, _151_46))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, lhs::rhs::[]) -> begin
(
# 80 "FStar.SMTEncoding.ErrorReporting.fst"
let _72_121 = (aux rs rhs labs)
in (match (_72_121) with
| (rhs, labs, rs) -> begin
(let _151_47 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]))))
in (_151_47, labs, rs))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(
# 84 "FStar.SMTEncoding.ErrorReporting.fst"
let _72_138 = (FStar_List.fold_left (fun _72_129 c -> (match (_72_129) with
| (rs, cs, labs) -> begin
(
# 85 "FStar.SMTEncoding.ErrorReporting.fst"
let _72_134 = (aux rs c labs)
in (match (_72_134) with
| (c, labs, rs) -> begin
(rs, (c)::cs, labs)
end))
end)) (rs, [], labs) conjuncts)
in (match (_72_138) with
| (rs, conjuncts, labs) -> begin
(let _151_50 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.And, (FStar_List.rev conjuncts)))))
in (_151_50, labs, rs))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, hd::q1::q2::[]) -> begin
(
# 92 "FStar.SMTEncoding.ErrorReporting.fst"
let _72_150 = (aux rs q1 labs)
in (match (_72_150) with
| (q1, labs, _72_149) -> begin
(
# 93 "FStar.SMTEncoding.ErrorReporting.fst"
let _72_155 = (aux rs q2 labs)
in (match (_72_155) with
| (q2, labs, _72_154) -> begin
(let _151_51 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]))))
in (_151_51, labs, rs))
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
let _72_277 = (aux rs body labs)
in (match (_72_277) with
| (body, labs, rs) -> begin
(let _151_52 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant ((FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body))))
in (_151_52, labs, rs))
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
let _72_284 = (FStar_Util.incr ctr)
in (let _151_75 = (let _151_68 = (let _151_67 = (let _151_66 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _151_66))
in (Prims.strcat "DETAILING ERRORS" _151_67))
in FStar_SMTEncoding_Term.Echo (_151_68))
in (let _151_74 = (FStar_All.pipe_right labs (FStar_List.map (fun _72_291 -> (match (_72_291) with
| (l, _72_288, _72_290) -> begin
(let _151_73 = (let _151_72 = (let _151_71 = (let _151_70 = (FStar_SMTEncoding_Term.mkFreeV l)
in (_151_70, FStar_SMTEncoding_Term.mkTrue))
in (FStar_SMTEncoding_Term.mkEq _151_71))
in (_151_72, Some ("Disabling label")))
in FStar_SMTEncoding_Term.Assume (_151_73))
end))))
in (_151_75)::_151_74))))
in (
# 146 "FStar.SMTEncoding.ErrorReporting.fst"
let print_labs = (fun tag l -> (FStar_All.pipe_right l (FStar_List.iter (fun _72_300 -> (match (_72_300) with
| (l, _72_297, _72_299) -> begin
(FStar_Util.print2 "%s : %s; " tag (Prims.fst l))
end)))))
in (
# 148 "FStar.SMTEncoding.ErrorReporting.fst"
let minus = (fun l1 l2 -> (FStar_All.pipe_right l1 (FStar_List.filter (fun _72_312 -> (match (_72_312) with
| ((x, _72_306), _72_309, _72_311) -> begin
(not ((FStar_All.pipe_right l2 (FStar_Util.for_some (fun _72_321 -> (match (_72_321) with
| ((y, _72_315), _72_318, _72_320) -> begin
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
let _72_334 = (let _151_93 = (FStar_All.pipe_left elim (FStar_List.append (FStar_List.append eliminated errors) tl))
in (askZ3 _151_93))
in (match (_72_334) with
| (ok, _72_333) -> begin
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
| _72_341 -> begin
(
# 169 "FStar.SMTEncoding.ErrorReporting.fst"
let _72_349 = (match (active) with
| _72_343::[] -> begin
(active, [])
end
| _72_346 -> begin
(FStar_Util.first_N ((FStar_List.length active) / 2) active)
end)
in (match (_72_349) with
| (pfx, sfx) -> begin
(
# 172 "FStar.SMTEncoding.ErrorReporting.fst"
let _72_352 = (let _151_100 = (elim (FStar_List.append (FStar_List.append eliminated potential_errors) sfx))
in (askZ3 _151_100))
in (match (_72_352) with
| (ok, pfx_subset) -> begin
if ok then begin
(bisect (FStar_List.append eliminated pfx) potential_errors sfx)
end else begin
(match (pfx_subset) with
| [] -> begin
(bisect eliminated (FStar_List.append potential_errors pfx) sfx)
end
| _72_355 -> begin
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
let _72_364 = (bisect eliminated potential_errors active)
in (match (_72_364) with
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
let _72_372 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (
# 200 "FStar.SMTEncoding.ErrorReporting.fst"
let minimum_workable_fuel = (FStar_Util.mk_ref None)
in (
# 201 "FStar.SMTEncoding.ErrorReporting.fst"
let set_minimum_workable_fuel = (fun f _72_1 -> (match (_72_1) with
| [] -> begin
()
end
| errs -> begin
(match ((FStar_ST.read minimum_workable_fuel)) with
| Some (_72_381) -> begin
()
end
| None -> begin
(FStar_ST.op_Colon_Equals minimum_workable_fuel (Some ((f, errs))))
end)
end))
in (
# 207 "FStar.SMTEncoding.ErrorReporting.fst"
let with_fuel = (fun label_assumptions p _72_389 -> (match (_72_389) with
| (n, i) -> begin
(let _151_149 = (let _151_148 = (let _151_147 = (let _151_146 = (let _151_131 = (let _151_130 = (FStar_Util.string_of_int n)
in (let _151_129 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _151_130 _151_129)))
in FStar_SMTEncoding_Term.Caption (_151_131))
in (let _151_145 = (let _151_144 = (let _151_136 = (let _151_135 = (let _151_134 = (let _151_133 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (let _151_132 = (FStar_SMTEncoding_Term.n_fuel n)
in (_151_133, _151_132)))
in (FStar_SMTEncoding_Term.mkEq _151_134))
in (_151_135, None))
in FStar_SMTEncoding_Term.Assume (_151_136))
in (let _151_143 = (let _151_142 = (let _151_141 = (let _151_140 = (let _151_139 = (let _151_138 = (FStar_SMTEncoding_Term.mkApp ("MaxIFuel", []))
in (let _151_137 = (FStar_SMTEncoding_Term.n_fuel i)
in (_151_138, _151_137)))
in (FStar_SMTEncoding_Term.mkEq _151_139))
in (_151_140, None))
in FStar_SMTEncoding_Term.Assume (_151_141))
in (_151_142)::(p)::[])
in (_151_144)::_151_143))
in (_151_146)::_151_145))
in (FStar_List.append _151_147 label_assumptions))
in (FStar_List.append _151_148 ((FStar_SMTEncoding_Term.CheckSat)::[])))
in (FStar_List.append _151_149 suffix))
end))
in (
# 216 "FStar.SMTEncoding.ErrorReporting.fst"
let check = (fun p -> (
# 217 "FStar.SMTEncoding.ErrorReporting.fst"
let initial_config = (let _151_153 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _151_152 = (FStar_ST.read FStar_Options.initial_ifuel)
in (_151_153, _151_152)))
in (
# 218 "FStar.SMTEncoding.ErrorReporting.fst"
let alt_configs = (let _151_172 = (let _151_171 = if ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel)) then begin
(let _151_156 = (let _151_155 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _151_154 = (FStar_ST.read FStar_Options.max_ifuel)
in (_151_155, _151_154)))
in (_151_156)::[])
end else begin
[]
end
in (let _151_170 = (let _151_169 = if (((FStar_ST.read FStar_Options.max_fuel) / 2) > (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _151_159 = (let _151_158 = ((FStar_ST.read FStar_Options.max_fuel) / 2)
in (let _151_157 = (FStar_ST.read FStar_Options.max_ifuel)
in (_151_158, _151_157)))
in (_151_159)::[])
end else begin
[]
end
in (let _151_168 = (let _151_167 = if (((FStar_ST.read FStar_Options.max_fuel) > (FStar_ST.read FStar_Options.initial_fuel)) && ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel))) then begin
(let _151_162 = (let _151_161 = (FStar_ST.read FStar_Options.max_fuel)
in (let _151_160 = (FStar_ST.read FStar_Options.max_ifuel)
in (_151_161, _151_160)))
in (_151_162)::[])
end else begin
[]
end
in (let _151_166 = (let _151_165 = if ((FStar_ST.read FStar_Options.min_fuel) < (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _151_164 = (let _151_163 = (FStar_ST.read FStar_Options.min_fuel)
in (_151_163, 1))
in (_151_164)::[])
end else begin
[]
end
in (_151_165)::[])
in (_151_167)::_151_166))
in (_151_169)::_151_168))
in (_151_171)::_151_170))
in (FStar_List.flatten _151_172))
in (
# 223 "FStar.SMTEncoding.ErrorReporting.fst"
let report = (fun p errs -> (
# 224 "FStar.SMTEncoding.ErrorReporting.fst"
let errs = if ((FStar_ST.read FStar_Options.detail_errors) && ((FStar_ST.read FStar_Options.n_cores) = 1)) then begin
(
# 225 "FStar.SMTEncoding.ErrorReporting.fst"
let _72_404 = (match ((FStar_ST.read minimum_workable_fuel)) with
| Some (f, errs) -> begin
(f, errs)
end
| None -> begin
(let _151_178 = (let _151_177 = (FStar_ST.read FStar_Options.min_fuel)
in (_151_177, 1))
in (_151_178, errs))
end)
in (match (_72_404) with
| (min_fuel, potential_errors) -> begin
(
# 228 "FStar.SMTEncoding.ErrorReporting.fst"
let ask_z3 = (fun label_assumptions -> (
# 229 "FStar.SMTEncoding.ErrorReporting.fst"
let res = (FStar_Util.mk_ref None)
in (
# 230 "FStar.SMTEncoding.ErrorReporting.fst"
let _72_409 = (let _151_182 = (with_fuel label_assumptions p min_fuel)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _151_182 (fun r -> (FStar_ST.op_Colon_Equals res (Some (r))))))
in (let _151_183 = (FStar_ST.read res)
in (FStar_Option.get _151_183)))))
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
| _72_414 -> begin
errs
end)
in (
# 238 "FStar.SMTEncoding.ErrorReporting.fst"
let _72_416 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _151_189 = (let _151_184 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _151_184))
in (let _151_188 = (let _151_185 = (FStar_ST.read FStar_Options.max_fuel)
in (FStar_All.pipe_right _151_185 FStar_Util.string_of_int))
in (let _151_187 = (let _151_186 = (FStar_ST.read FStar_Options.max_ifuel)
in (FStar_All.pipe_right _151_186 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _151_189 _151_188 _151_187))))
end else begin
()
end
in (
# 243 "FStar.SMTEncoding.ErrorReporting.fst"
let _72_423 = (let _151_191 = (FStar_All.pipe_right errs (FStar_List.map (fun _72_422 -> (match (_72_422) with
| (_72_419, x, y) -> begin
(x, y)
end))))
in (FStar_TypeChecker_Errors.add_errors env _151_191))
in if (FStar_ST.read FStar_Options.detail_errors) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Detailed error report follows\n")))
end else begin
()
end)))))
in (
# 247 "FStar.SMTEncoding.ErrorReporting.fst"
let rec try_alt_configs = (fun prev_f p errs cfgs -> (
# 248 "FStar.SMTEncoding.ErrorReporting.fst"
let _72_431 = (set_minimum_workable_fuel prev_f errs)
in (match (cfgs) with
| [] -> begin
(report p errs)
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _151_204 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _151_204 (cb mi p [])))
end
| _72_438 -> begin
(
# 254 "FStar.SMTEncoding.ErrorReporting.fst"
let _72_439 = (set_minimum_workable_fuel prev_f errs)
in (report p errs))
end)
end
| mi::tl -> begin
(let _151_206 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _151_206 (fun _72_446 -> (match (_72_446) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _72_449 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end)))
and cb = (fun _72_452 p alt _72_457 -> (match ((_72_452, _72_457)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _151_214 = (let _151_211 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _151_211))
in (let _151_213 = (FStar_Util.string_of_int prev_fuel)
in (let _151_212 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _151_214 _151_213 _151_212))))
end else begin
()
end
end else begin
(try_alt_configs (prev_fuel, prev_ifuel) p errs alt)
end
end))
in (let _151_215 = (with_fuel [] p initial_config)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _151_215 (cb initial_config p alt_configs))))))))
in (
# 279 "FStar.SMTEncoding.ErrorReporting.fst"
let process_query = (fun q -> if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(
# 281 "FStar.SMTEncoding.ErrorReporting.fst"
let _72_462 = (let _151_221 = (FStar_ST.read FStar_Options.split_cases)
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _151_221 q))
in (match (_72_462) with
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




