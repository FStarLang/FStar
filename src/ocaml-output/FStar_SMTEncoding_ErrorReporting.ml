
open Prims
# 24 "FStar.SMTEncoding.ErrorReporting.fst"
type label =
(FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range)

# 25 "FStar.SMTEncoding.ErrorReporting.fst"
type labels =
label Prims.list

# 27 "FStar.SMTEncoding.ErrorReporting.fst"
type msg =
(Prims.string * FStar_Range.range)

# 28 "FStar.SMTEncoding.ErrorReporting.fst"
type ranges =
(Prims.string Prims.option * FStar_Range.range) Prims.list

# 30 "FStar.SMTEncoding.ErrorReporting.fst"
let fresh_label : ranges  ->  FStar_SMTEncoding_Term.term  ->  labels  ->  (FStar_SMTEncoding_Term.term * labels) = (
# 31 "FStar.SMTEncoding.ErrorReporting.fst"
let ctr = (FStar_ST.alloc 0)
in (fun rs t labs -> (
# 33 "FStar.SMTEncoding.ErrorReporting.fst"
let l = (
# 33 "FStar.SMTEncoding.ErrorReporting.fst"
let _76_5 = (FStar_Util.incr ctr)
in (let _160_8 = (let _160_7 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _160_7))
in (FStar_Util.format1 "label_%s" _160_8)))
in (
# 34 "FStar.SMTEncoding.ErrorReporting.fst"
let lvar = (l, FStar_SMTEncoding_Term.Bool_sort)
in (
# 35 "FStar.SMTEncoding.ErrorReporting.fst"
let _76_25 = (match (rs) with
| [] -> begin
(t.FStar_SMTEncoding_Term.hash, FStar_Range.dummyRange)
end
| (Some (reason), r)::_76_11 -> begin
(reason, r)
end
| (None, r)::_76_18 -> begin
("failed to prove a pre-condition", r)
end)
in (match (_76_25) with
| (message, range) -> begin
(
# 39 "FStar.SMTEncoding.ErrorReporting.fst"
let label = (lvar, message, range)
in (
# 40 "FStar.SMTEncoding.ErrorReporting.fst"
let lterm = (FStar_SMTEncoding_Term.mkFreeV lvar)
in (
# 41 "FStar.SMTEncoding.ErrorReporting.fst"
let lt = (FStar_SMTEncoding_Term.mkOr (lterm, t))
in (lt, (label)::labs))))
end))))))

# 51 "FStar.SMTEncoding.ErrorReporting.fst"
let label_goals : (Prims.unit  ->  Prims.string) Prims.option  ->  Prims.int64  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term * labels * ranges) = (fun use_env_msg r q -> (
# 52 "FStar.SMTEncoding.ErrorReporting.fst"
let _76_37 = (match (use_env_msg) with
| None -> begin
(false, "")
end
| Some (f) -> begin
(let _160_24 = (f ())
in (true, _160_24))
end)
in (match (_76_37) with
| (flag, msg_prefix) -> begin
(
# 55 "FStar.SMTEncoding.ErrorReporting.fst"
let fresh_label = (fun rs t labs -> (
# 56 "FStar.SMTEncoding.ErrorReporting.fst"
let rs' = if (not (flag)) then begin
rs
end else begin
(match (rs) with
| (Some (reason), _76_47)::_76_43 -> begin
((Some ((Prims.strcat "Failed to verify implicit argument: " reason)), r))::[]
end
| _76_51 -> begin
((Some ("Failed to verify implicit argument"), r))::[]
end)
end
in (
# 61 "FStar.SMTEncoding.ErrorReporting.fst"
let _76_55 = (fresh_label rs' t labs)
in (match (_76_55) with
| (lt, labs) -> begin
(lt, labs, rs)
end))))
in (
# 63 "FStar.SMTEncoding.ErrorReporting.fst"
let rec aux = (fun rs q labs -> (match (q.FStar_SMTEncoding_Term.tm) with
| (FStar_SMTEncoding_Term.BoundV (_)) | (FStar_SMTEncoding_Term.Integer (_)) -> begin
(q, labs, rs)
end
| FStar_SMTEncoding_Term.Labeled (_76_67, "push", r) -> begin
(FStar_SMTEncoding_Term.mkTrue, labs, ((None, r))::rs)
end
| FStar_SMTEncoding_Term.Labeled (_76_73, "pop", r) -> begin
(let _160_37 = (FStar_List.tl rs)
in (FStar_SMTEncoding_Term.mkTrue, labs, _160_37))
end
| FStar_SMTEncoding_Term.Labeled (arg, reason, r) -> begin
(
# 78 "FStar.SMTEncoding.ErrorReporting.fst"
let _76_86 = (aux (((Some (reason), r))::rs) arg labs)
in (match (_76_86) with
| (tm, labs, rs) -> begin
(let _160_38 = (FStar_List.tl rs)
in (tm, labs, _160_38))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, lhs::rhs::[]) -> begin
(
# 83 "FStar.SMTEncoding.ErrorReporting.fst"
let _76_96 = (aux rs rhs labs)
in (match (_76_96) with
| (rhs, labs, rs) -> begin
(let _160_39 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]))))
in (_160_39, labs, rs))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(
# 87 "FStar.SMTEncoding.ErrorReporting.fst"
let _76_113 = (FStar_List.fold_left (fun _76_104 c -> (match (_76_104) with
| (rs, cs, labs) -> begin
(
# 88 "FStar.SMTEncoding.ErrorReporting.fst"
let _76_109 = (aux rs c labs)
in (match (_76_109) with
| (c, labs, rs) -> begin
(rs, (c)::cs, labs)
end))
end)) (rs, [], labs) conjuncts)
in (match (_76_113) with
| (rs, conjuncts, labs) -> begin
(let _160_42 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.And, (FStar_List.rev conjuncts)))))
in (_160_42, labs, rs))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, hd::q1::q2::[]) -> begin
(
# 95 "FStar.SMTEncoding.ErrorReporting.fst"
let _76_125 = (aux rs q1 labs)
in (match (_76_125) with
| (q1, labs, _76_124) -> begin
(
# 96 "FStar.SMTEncoding.ErrorReporting.fst"
let _76_130 = (aux rs q2 labs)
in (match (_76_130) with
| (q2, labs, _76_129) -> begin
(let _160_43 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]))))
in (_160_43, labs, rs))
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
# 129 "FStar.SMTEncoding.ErrorReporting.fst"
let _76_252 = (aux rs body labs)
in (match (_76_252) with
| (body, labs, rs) -> begin
(let _160_44 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant ((FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body))))
in (_160_44, labs, rs))
end))
end))
in (aux [] q [])))
end)))




