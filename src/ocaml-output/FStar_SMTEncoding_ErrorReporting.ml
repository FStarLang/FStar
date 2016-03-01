
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
let fresh_label : ranges  ->  FStar_SMTEncoding_Term.term  ->  labels  ->  (FStar_SMTEncoding_Term.term * labels * ranges) = (
# 31 "FStar.SMTEncoding.ErrorReporting.fst"
let ctr = (FStar_ST.alloc 0)
in (fun rs t labs -> (
# 33 "FStar.SMTEncoding.ErrorReporting.fst"
let l = (
# 33 "FStar.SMTEncoding.ErrorReporting.fst"
let _73_5 = (FStar_Util.incr ctr)
in (let _154_8 = (let _154_7 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _154_7))
in (FStar_Util.format1 "label_%s" _154_8)))
in (
# 34 "FStar.SMTEncoding.ErrorReporting.fst"
let lvar = (l, FStar_SMTEncoding_Term.Bool_sort)
in (
# 35 "FStar.SMTEncoding.ErrorReporting.fst"
let _73_25 = (match (rs) with
| [] -> begin
(t.FStar_SMTEncoding_Term.hash, FStar_Range.dummyRange)
end
| (Some (reason), r)::_73_11 -> begin
(reason, r)
end
| (None, r)::_73_18 -> begin
("failed to prove a pre-condition", r)
end)
in (match (_73_25) with
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
in (lt, (label)::labs, rs))))
end))))))

# 51 "FStar.SMTEncoding.ErrorReporting.fst"
let rec label_goals : ranges  ->  FStar_SMTEncoding_Term.term  ->  labels  ->  (FStar_SMTEncoding_Term.term * labels * ranges) = (fun rs q labs -> (match (q.FStar_SMTEncoding_Term.tm) with
| (FStar_SMTEncoding_Term.BoundV (_)) | (FStar_SMTEncoding_Term.Integer (_)) -> begin
(q, labs, rs)
end
| FStar_SMTEncoding_Term.Labeled (_73_39, "push", r) -> begin
(FStar_SMTEncoding_Term.mkTrue, labs, ((None, r))::rs)
end
| FStar_SMTEncoding_Term.Labeled (_73_45, "pop", r) -> begin
(let _154_15 = (FStar_List.tl rs)
in (FStar_SMTEncoding_Term.mkTrue, labs, _154_15))
end
| FStar_SMTEncoding_Term.Labeled (arg, reason, r) -> begin
(
# 67 "FStar.SMTEncoding.ErrorReporting.fst"
let _73_58 = (label_goals (((Some (reason), r))::rs) arg labs)
in (match (_73_58) with
| (tm, labs, rs) -> begin
(let _154_16 = (FStar_List.tl rs)
in (tm, labs, _154_16))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, lhs::rhs::[]) -> begin
(
# 72 "FStar.SMTEncoding.ErrorReporting.fst"
let _73_68 = (label_goals rs rhs labs)
in (match (_73_68) with
| (rhs, labs, rs) -> begin
(let _154_17 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.Imp, (lhs)::(rhs)::[]))))
in (_154_17, labs, rs))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, conjuncts) -> begin
(
# 76 "FStar.SMTEncoding.ErrorReporting.fst"
let _73_85 = (FStar_List.fold_left (fun _73_76 c -> (match (_73_76) with
| (rs, cs, labs) -> begin
(
# 77 "FStar.SMTEncoding.ErrorReporting.fst"
let _73_81 = (label_goals rs c labs)
in (match (_73_81) with
| (c, labs, rs) -> begin
(rs, (c)::cs, labs)
end))
end)) (rs, [], labs) conjuncts)
in (match (_73_85) with
| (rs, conjuncts, labs) -> begin
(let _154_20 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.And, (FStar_List.rev conjuncts)))))
in (_154_20, labs, rs))
end))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, hd::q1::q2::[]) -> begin
(
# 84 "FStar.SMTEncoding.ErrorReporting.fst"
let _73_97 = (label_goals rs q1 labs)
in (match (_73_97) with
| (q1, labs, _73_96) -> begin
(
# 85 "FStar.SMTEncoding.ErrorReporting.fst"
let _73_102 = (label_goals rs q2 labs)
in (match (_73_102) with
| (q2, labs, _73_101) -> begin
(let _154_21 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.App ((FStar_SMTEncoding_Term.ITE, (hd)::(q1)::(q2)::[]))))
in (_154_21, labs, rs))
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
# 118 "FStar.SMTEncoding.ErrorReporting.fst"
let _73_224 = (label_goals rs body labs)
in (match (_73_224) with
| (body, labs, rs) -> begin
(let _154_22 = (FStar_SMTEncoding_Term.mk (FStar_SMTEncoding_Term.Quant ((FStar_SMTEncoding_Term.Forall, pats, iopt, sorts, body))))
in (_154_22, labs, rs))
end))
end))




