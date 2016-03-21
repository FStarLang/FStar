
open Prims
# 24 "FStar.SMTEncoding.ErrorReporting.fst"
type label =
FStar_SMTEncoding_Term.error_label

# 25 "FStar.SMTEncoding.ErrorReporting.fst"
type labels =
FStar_SMTEncoding_Term.error_labels

# 26 "FStar.SMTEncoding.ErrorReporting.fst"
let sort_labels : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun l -> (FStar_List.sortWith (fun _77_8 _77_14 -> (match ((_77_8, _77_14)) with
| ((_77_4, _77_6, r1), (_77_10, _77_12, r2)) -> begin
(FStar_Range.compare r1 r2)
end)) l))

# 27 "FStar.SMTEncoding.ErrorReporting.fst"
let remove_dups : labels  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * Prims.int64) Prims.list = (fun l -> (FStar_Util.remove_dups (fun _77_20 _77_25 -> (match ((_77_20, _77_25)) with
| ((_77_17, m1, r1), (_77_22, m2, r2)) -> begin
((r1 = r2) && (m1 = m2))
end)) l))

# 28 "FStar.SMTEncoding.ErrorReporting.fst"
type msg =
(Prims.string * FStar_Range.range)

# 29 "FStar.SMTEncoding.ErrorReporting.fst"
type ranges =
(Prims.string Prims.option * FStar_Range.range) Prims.list

# 31 "FStar.SMTEncoding.ErrorReporting.fst"
let fresh_label : ranges  ->  FStar_SMTEncoding_Term.term  ->  labels  ->  (FStar_SMTEncoding_Term.term * labels) = (
# 32 "FStar.SMTEncoding.ErrorReporting.fst"
let ctr = (FStar_ST.alloc 0)
in (fun rs t labs -> (
# 34 "FStar.SMTEncoding.ErrorReporting.fst"
let l = (
# 34 "FStar.SMTEncoding.ErrorReporting.fst"
let _77_30 = (FStar_Util.incr ctr)
in (let _161_16 = (let _161_15 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _161_15))
in (FStar_Util.format1 "label_%s" _161_16)))
in (
# 35 "FStar.SMTEncoding.ErrorReporting.fst"
let lvar = (l, FStar_SMTEncoding_Term.Bool_sort)
in (
# 36 "FStar.SMTEncoding.ErrorReporting.fst"
let _77_50 = (match (rs) with
| [] -> begin
(t.FStar_SMTEncoding_Term.hash, FStar_Range.dummyRange)
end
| (Some (reason), r)::_77_36 -> begin
(reason, r)
end
| (None, r)::_77_43 -> begin
("failed to prove a pre-condition", r)
end)
in (match (_77_50) with
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

# 52 "FStar.SMTEncoding.ErrorReporting.fst"
let label_goals : (Prims.unit  ->  Prims.string) Prims.option  ->  Prims.int64  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * labels * ranges) = (fun use_env_msg r q -> (
# 53 "FStar.SMTEncoding.ErrorReporting.fst"
let _77_62 = (match (use_env_msg) with
| None -> begin
(false, "")
end
| Some (f) -> begin
(let _161_32 = (f ())
in (true, _161_32))
end)
in (match (_77_62) with
| (flag, msg_prefix) -> begin
(
# 56 "FStar.SMTEncoding.ErrorReporting.fst"
let fresh_label = (fun rs t labs -> (
# 57 "FStar.SMTEncoding.ErrorReporting.fst"
let rs' = if (not (flag)) then begin
rs
end else begin
(match (rs) with
| (Some (reason), _77_72)::_77_68 -> begin
((Some ((Prims.strcat "Failed to verify implicit argument: " reason)), r))::[]
end
| _77_76 -> begin
((Some ("Failed to verify implicit argument"), r))::[]
end)
end
in (
# 62 "FStar.SMTEncoding.ErrorReporting.fst"
let _77_80 = (fresh_label rs' t labs)
in (match (_77_80) with
| (lt, labs) -> begin
(lt, labs, rs)
end))))
in (
# 64 "FStar.SMTEncoding.ErrorReporting.fst"
let rec aux = (fun rs q labs -> (match (q.FStar_SMTEncoding_Term.tm) with
| (FStar_SMTEncoding_Term.BoundV (_)) | (FStar_SMTEncoding_Term.Integer (_)) -> begin
(q, labs, rs)
end
| FStar_SMTEncoding_Term.Labeled (_77_92, "push", r) -> begin
(FStar_SMTEncoding_Term.mkTrue, labs, ((None, r))::rs)
end
| FStar_SMTEncoding_Term.Labeled (_77_98, "pop", r) -> begin
(let _161_45 = (FStar_List.tl rs)
in (FStar_SMTEncoding_Term.mkTrue, labs, _161_45))
end
| FStar_SMTEncoding_Term.Labeled (arg, reason, r) -> begin
(
# 79 "FStar.SMTEncoding.ErrorReporting.fst"
let _77_111 = (aux (((Some (reason), r))::rs) arg labs)
in (match (_77_111) with
| (tm, labs, rs) -> begin
(let _161_46 = (FStar_List.tl rs)
in (tm, labs, _161_46))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, lhs::rhs::[]) -> begin
(
# 84 "FStar.SMTEncoding.ErrorReporting.fst"
let _77_121 = (aux rs rhs labs)
in (match (_77_121) with
| (rhs, labs, rs) -> begin
(let _161_47 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]))))
in (_161_47, labs, rs))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(
# 88 "FStar.SMTEncoding.ErrorReporting.fst"
let _77_138 = (FStar_List.fold_left (fun _77_129 c -> (match (_77_129) with
| (rs, cs, labs) -> begin
(
# 89 "FStar.SMTEncoding.ErrorReporting.fst"
let _77_134 = (aux rs c labs)
in (match (_77_134) with
| (c, labs, rs) -> begin
(rs, (c)::cs, labs)
end))
end)) (rs, [], labs) conjuncts)
in (match (_77_138) with
| (rs, conjuncts, labs) -> begin
(let _161_50 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.And, (FStar_List.rev conjuncts)))))
in (_161_50, labs, rs))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, hd::q1::q2::[]) -> begin
(
# 96 "FStar.SMTEncoding.ErrorReporting.fst"
let _77_150 = (aux rs q1 labs)
in (match (_77_150) with
| (q1, labs, _77_149) -> begin
(
# 97 "FStar.SMTEncoding.ErrorReporting.fst"
let _77_155 = (aux rs q2 labs)
in (match (_77_155) with
| (q2, labs, _77_154) -> begin
(let _161_51 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]))))
in (_161_51, labs, rs))
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
# 130 "FStar.SMTEncoding.ErrorReporting.fst"
let _77_277 = (aux rs body labs)
in (match (_77_277) with
| (body, labs, rs) -> begin
(let _161_52 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant ((FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body))))
in (_161_52, labs, rs))
end))
end))
in (aux [] q [])))
end)))

# 144 "FStar.SMTEncoding.ErrorReporting.fst"
let detail_errors : labels  ->  labels  ->  (FStar_SMTEncoding_Term.decls_t  ->  (Prims.bool * labels))  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Range.range) Prims.list = (fun all_labels potential_errors askZ3 -> (
# 145 "FStar.SMTEncoding.ErrorReporting.fst"
let ctr = (FStar_Util.mk_ref 0)
in (
# 146 "FStar.SMTEncoding.ErrorReporting.fst"
let elim = (fun labs -> (
# 147 "FStar.SMTEncoding.ErrorReporting.fst"
let _77_284 = (FStar_Util.incr ctr)
in (let _161_75 = (let _161_68 = (let _161_67 = (let _161_66 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _161_66))
in (Prims.strcat "DETAILING ERRORS" _161_67))
in FStar_SMTEncoding_Term.Echo (_161_68))
in (let _161_74 = (FStar_All.pipe_right labs (FStar_List.map (fun _77_291 -> (match (_77_291) with
| (l, _77_288, _77_290) -> begin
(let _161_73 = (let _161_72 = (let _161_71 = (let _161_70 = (FStar_SMTEncoding_Term.mkFreeV l)
in (_161_70, FStar_SMTEncoding_Term.mkTrue))
in (FStar_SMTEncoding_Term.mkEq _161_71))
in (_161_72, Some ("Disabling label")))
in FStar_SMTEncoding_Term.Assume (_161_73))
end))))
in (_161_75)::_161_74))))
in (
# 150 "FStar.SMTEncoding.ErrorReporting.fst"
let print_labs = (fun tag l -> (FStar_All.pipe_right l (FStar_List.iter (fun _77_300 -> (match (_77_300) with
| (l, _77_297, _77_299) -> begin
(FStar_Util.print2 "%s : %s; " tag (Prims.fst l))
end)))))
in (
# 152 "FStar.SMTEncoding.ErrorReporting.fst"
let minus = (fun l1 l2 -> (FStar_All.pipe_right l1 (FStar_List.filter (fun _77_312 -> (match (_77_312) with
| ((x, _77_306), _77_309, _77_311) -> begin
(not ((FStar_All.pipe_right l2 (FStar_Util.for_some (fun _77_321 -> (match (_77_321) with
| ((y, _77_315), _77_318, _77_320) -> begin
(x = y)
end))))))
end)))))
in (
# 157 "FStar.SMTEncoding.ErrorReporting.fst"
let rec linear_check = (fun eliminated errors active -> (match (active) with
| [] -> begin
(
# 159 "FStar.SMTEncoding.ErrorReporting.fst"
let labs = (FStar_All.pipe_right errors sort_labels)
in labs)
end
| hd::tl -> begin
(
# 163 "FStar.SMTEncoding.ErrorReporting.fst"
let _77_334 = (let _161_93 = (FStar_All.pipe_left elim (FStar_List.append (FStar_List.append eliminated errors) tl))
in (askZ3 _161_93))
in (match (_77_334) with
| (ok, _77_333) -> begin
if ok then begin
(linear_check ((hd)::eliminated) errors tl)
end else begin
(linear_check eliminated ((hd)::errors) tl)
end
end))
end))
in (
# 169 "FStar.SMTEncoding.ErrorReporting.fst"
let rec bisect = (fun eliminated potential_errors active -> (match (active) with
| [] -> begin
(eliminated, potential_errors)
end
| _77_341 -> begin
(
# 173 "FStar.SMTEncoding.ErrorReporting.fst"
let _77_349 = (match (active) with
| _77_343::[] -> begin
(active, [])
end
| _77_346 -> begin
(FStar_Util.first_N ((FStar_List.length active) / 2) active)
end)
in (match (_77_349) with
| (pfx, sfx) -> begin
(
# 176 "FStar.SMTEncoding.ErrorReporting.fst"
let _77_352 = (let _161_100 = (FStar_All.pipe_left elim (FStar_List.append (FStar_List.append eliminated potential_errors) sfx))
in (askZ3 _161_100))
in (match (_77_352) with
| (ok, pfx_subset) -> begin
if ok then begin
(bisect (FStar_List.append eliminated pfx) potential_errors sfx)
end else begin
(match (pfx_subset) with
| [] -> begin
(bisect eliminated (FStar_List.append potential_errors pfx) sfx)
end
| _77_355 -> begin
(
# 185 "FStar.SMTEncoding.ErrorReporting.fst"
let potential_errors = (FStar_List.append potential_errors pfx_subset)
in (
# 186 "FStar.SMTEncoding.ErrorReporting.fst"
let pfx_active = (minus pfx pfx_subset)
in (bisect eliminated potential_errors (FStar_List.append pfx_active sfx))))
end)
end
end))
end))
end))
in (
# 191 "FStar.SMTEncoding.ErrorReporting.fst"
let rec until_fixpoint = (fun eliminated potential_errors active -> (
# 192 "FStar.SMTEncoding.ErrorReporting.fst"
let _77_364 = (bisect eliminated potential_errors active)
in (match (_77_364) with
| (eliminated', potential_errors) -> begin
if (FStar_Util.physical_equality eliminated eliminated') then begin
(linear_check eliminated [] potential_errors)
end else begin
(until_fixpoint eliminated' [] potential_errors)
end
end)))
in (
# 197 "FStar.SMTEncoding.ErrorReporting.fst"
let active = (minus all_labels potential_errors)
in (until_fixpoint [] potential_errors active))))))))))

# 202 "FStar.SMTEncoding.ErrorReporting.fst"
let askZ3_and_report_errors : FStar_TypeChecker_Env.env  ->  Prims.bool  ->  ((Prims.string * FStar_SMTEncoding_Term.sort) * Prims.string * Prims.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  FStar_SMTEncoding_Term.decl  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun env use_fresh_z3_context all_labels prefix query suffix -> (
# 203 "FStar.SMTEncoding.ErrorReporting.fst"
let _77_372 = (FStar_SMTEncoding_Z3.giveZ3 prefix)
in (
# 204 "FStar.SMTEncoding.ErrorReporting.fst"
let minimum_workable_fuel = (FStar_Util.mk_ref None)
in (
# 205 "FStar.SMTEncoding.ErrorReporting.fst"
let set_minimum_workable_fuel = (fun f _77_1 -> (match (_77_1) with
| [] -> begin
()
end
| errs -> begin
(match ((FStar_ST.read minimum_workable_fuel)) with
| Some (_77_381) -> begin
()
end
| None -> begin
(FStar_ST.op_Colon_Equals minimum_workable_fuel (Some ((f, errs))))
end)
end))
in (
# 211 "FStar.SMTEncoding.ErrorReporting.fst"
let with_fuel = (fun label_assumptions p _77_389 -> (match (_77_389) with
| (n, i) -> begin
(let _161_149 = (let _161_148 = (let _161_147 = (let _161_146 = (let _161_131 = (let _161_130 = (FStar_Util.string_of_int n)
in (let _161_129 = (FStar_Util.string_of_int i)
in (FStar_Util.format2 "<fuel=\'%s\' ifuel=\'%s\'>" _161_130 _161_129)))
in FStar_SMTEncoding_Term.Caption (_161_131))
in (let _161_145 = (let _161_144 = (let _161_136 = (let _161_135 = (let _161_134 = (let _161_133 = (FStar_SMTEncoding_Term.mkApp ("MaxFuel", []))
in (let _161_132 = (FStar_SMTEncoding_Term.n_fuel n)
in (_161_133, _161_132)))
in (FStar_SMTEncoding_Term.mkEq _161_134))
in (_161_135, None))
in FStar_SMTEncoding_Term.Assume (_161_136))
in (let _161_143 = (let _161_142 = (let _161_141 = (let _161_140 = (let _161_139 = (let _161_138 = (FStar_SMTEncoding_Term.mkApp ("MaxIFuel", []))
in (let _161_137 = (FStar_SMTEncoding_Term.n_fuel i)
in (_161_138, _161_137)))
in (FStar_SMTEncoding_Term.mkEq _161_139))
in (_161_140, None))
in FStar_SMTEncoding_Term.Assume (_161_141))
in (_161_142)::(p)::[])
in (_161_144)::_161_143))
in (_161_146)::_161_145))
in (FStar_List.append _161_147 label_assumptions))
in (FStar_List.append _161_148 ((FStar_SMTEncoding_Term.CheckSat)::[])))
in (FStar_List.append _161_149 suffix))
end))
in (
# 220 "FStar.SMTEncoding.ErrorReporting.fst"
let check = (fun p -> (
# 221 "FStar.SMTEncoding.ErrorReporting.fst"
let initial_config = (let _161_153 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _161_152 = (FStar_ST.read FStar_Options.initial_ifuel)
in (_161_153, _161_152)))
in (
# 222 "FStar.SMTEncoding.ErrorReporting.fst"
let alt_configs = (let _161_172 = (let _161_171 = if ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel)) then begin
(let _161_156 = (let _161_155 = (FStar_ST.read FStar_Options.initial_fuel)
in (let _161_154 = (FStar_ST.read FStar_Options.max_ifuel)
in (_161_155, _161_154)))
in (_161_156)::[])
end else begin
[]
end
in (let _161_170 = (let _161_169 = if (((FStar_ST.read FStar_Options.max_fuel) / 2) > (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _161_159 = (let _161_158 = ((FStar_ST.read FStar_Options.max_fuel) / 2)
in (let _161_157 = (FStar_ST.read FStar_Options.max_ifuel)
in (_161_158, _161_157)))
in (_161_159)::[])
end else begin
[]
end
in (let _161_168 = (let _161_167 = if (((FStar_ST.read FStar_Options.max_fuel) > (FStar_ST.read FStar_Options.initial_fuel)) && ((FStar_ST.read FStar_Options.max_ifuel) > (FStar_ST.read FStar_Options.initial_ifuel))) then begin
(let _161_162 = (let _161_161 = (FStar_ST.read FStar_Options.max_fuel)
in (let _161_160 = (FStar_ST.read FStar_Options.max_ifuel)
in (_161_161, _161_160)))
in (_161_162)::[])
end else begin
[]
end
in (let _161_166 = (let _161_165 = if ((FStar_ST.read FStar_Options.min_fuel) < (FStar_ST.read FStar_Options.initial_fuel)) then begin
(let _161_164 = (let _161_163 = (FStar_ST.read FStar_Options.min_fuel)
in (_161_163, 1))
in (_161_164)::[])
end else begin
[]
end
in (_161_165)::[])
in (_161_167)::_161_166))
in (_161_169)::_161_168))
in (_161_171)::_161_170))
in (FStar_List.flatten _161_172))
in (
# 227 "FStar.SMTEncoding.ErrorReporting.fst"
let report = (fun p errs -> (
# 228 "FStar.SMTEncoding.ErrorReporting.fst"
let errs = if ((FStar_ST.read FStar_Options.detail_errors) && ((FStar_ST.read FStar_Options.n_cores) = 1)) then begin
(
# 229 "FStar.SMTEncoding.ErrorReporting.fst"
let _77_404 = (match ((FStar_ST.read minimum_workable_fuel)) with
| Some (f, errs) -> begin
(f, errs)
end
| None -> begin
(let _161_178 = (let _161_177 = (FStar_ST.read FStar_Options.min_fuel)
in (_161_177, 1))
in (_161_178, errs))
end)
in (match (_77_404) with
| (min_fuel, potential_errors) -> begin
(
# 232 "FStar.SMTEncoding.ErrorReporting.fst"
let ask_z3 = (fun label_assumptions -> (
# 233 "FStar.SMTEncoding.ErrorReporting.fst"
let res = (FStar_Util.mk_ref None)
in (
# 234 "FStar.SMTEncoding.ErrorReporting.fst"
let _77_409 = (let _161_182 = (with_fuel label_assumptions p min_fuel)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _161_182 (fun r -> (FStar_ST.op_Colon_Equals res (Some (r))))))
in (let _161_183 = (FStar_ST.read res)
in (FStar_Option.get _161_183)))))
in (detail_errors all_labels errs ask_z3))
end))
end else begin
errs
end
in (
# 239 "FStar.SMTEncoding.ErrorReporting.fst"
let errs = (match (errs) with
| [] -> begin
((("", FStar_SMTEncoding_Term.Term_sort), "Unknown assertion failed", FStar_Range.dummyRange))::[]
end
| _77_414 -> begin
errs
end)
in (
# 242 "FStar.SMTEncoding.ErrorReporting.fst"
let _77_416 = if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _161_189 = (let _161_184 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _161_184))
in (let _161_188 = (let _161_185 = (FStar_ST.read FStar_Options.max_fuel)
in (FStar_All.pipe_right _161_185 FStar_Util.string_of_int))
in (let _161_187 = (let _161_186 = (FStar_ST.read FStar_Options.max_ifuel)
in (FStar_All.pipe_right _161_186 FStar_Util.string_of_int))
in (FStar_Util.print3 "(%s) Query failed with maximum fuel %s and ifuel %s\n" _161_189 _161_188 _161_187))))
end else begin
()
end
in (
# 247 "FStar.SMTEncoding.ErrorReporting.fst"
let _77_423 = (let _161_191 = (FStar_All.pipe_right errs (FStar_List.map (fun _77_422 -> (match (_77_422) with
| (_77_419, x, y) -> begin
(x, y)
end))))
in (FStar_TypeChecker_Errors.add_errors env _161_191))
in if (FStar_ST.read FStar_Options.detail_errors) then begin
(Prims.raise (FStar_Syntax_Syntax.Err ("Detailed error report follows\n")))
end else begin
()
end)))))
in (
# 251 "FStar.SMTEncoding.ErrorReporting.fst"
let rec try_alt_configs = (fun prev_f p errs cfgs -> (
# 252 "FStar.SMTEncoding.ErrorReporting.fst"
let _77_431 = (set_minimum_workable_fuel prev_f errs)
in (match (cfgs) with
| [] -> begin
(report p errs)
end
| mi::[] -> begin
(match (errs) with
| [] -> begin
(let _161_204 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _161_204 (cb mi p [])))
end
| _77_438 -> begin
(
# 258 "FStar.SMTEncoding.ErrorReporting.fst"
let _77_439 = (set_minimum_workable_fuel prev_f errs)
in (report p errs))
end)
end
| mi::tl -> begin
(let _161_206 = (with_fuel [] p mi)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _161_206 (fun _77_446 -> (match (_77_446) with
| (ok, errs') -> begin
(match (errs) with
| [] -> begin
(cb mi p tl (ok, errs'))
end
| _77_449 -> begin
(cb mi p tl (ok, errs))
end)
end))))
end)))
and cb = (fun _77_452 p alt _77_457 -> (match ((_77_452, _77_457)) with
| ((prev_fuel, prev_ifuel), (ok, errs)) -> begin
if ok then begin
if (FStar_ST.read FStar_Options.print_fuels) then begin
(let _161_214 = (let _161_211 = (FStar_TypeChecker_Env.get_range env)
in (FStar_Range.string_of_range _161_211))
in (let _161_213 = (FStar_Util.string_of_int prev_fuel)
in (let _161_212 = (FStar_Util.string_of_int prev_ifuel)
in (FStar_Util.print3 "(%s) Query succeeded with fuel %s and ifuel %s\n" _161_214 _161_213 _161_212))))
end else begin
()
end
end else begin
(try_alt_configs (prev_fuel, prev_ifuel) p errs alt)
end
end))
in (let _161_215 = (with_fuel [] p initial_config)
in (FStar_SMTEncoding_Z3.ask use_fresh_z3_context all_labels _161_215 (cb initial_config p alt_configs))))))))
in (
# 283 "FStar.SMTEncoding.ErrorReporting.fst"
let process_query = (fun q -> if ((FStar_ST.read FStar_Options.split_cases) > 0) then begin
(
# 285 "FStar.SMTEncoding.ErrorReporting.fst"
let _77_462 = (let _161_221 = (FStar_ST.read FStar_Options.split_cases)
in (FStar_SMTEncoding_SplitQueryCases.can_handle_query _161_221 q))
in (match (_77_462) with
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




