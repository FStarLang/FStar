
open Prims
# 10 "FStar.ToSMT.SplitQueryCases.fst"
let rec get_next_n_ite : Prims.int  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  (Prims.bool * FStar_ToSMT_Term.term * FStar_ToSMT_Term.term * FStar_ToSMT_Term.term) = (fun n t negs f -> if (n <= 0) then begin
(let _125_14 = (f FStar_ToSMT_Term.mkTrue)
in (true, _125_14, negs, t))
end else begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, g::t::e::_46_7) -> begin
(let _125_19 = (let _125_16 = (let _125_15 = (FStar_ToSMT_Term.mkNot g)
in (negs, _125_15))
in (FStar_ToSMT_Term.mkAnd _125_16))
in (get_next_n_ite (n - 1) e _125_19 (fun x -> (let _125_18 = (FStar_ToSMT_Term.mkITE (g, t, x))
in (f _125_18)))))
end
| FStar_ToSMT_Term.FreeV (_46_18) -> begin
(let _125_20 = (f FStar_ToSMT_Term.mkTrue)
in (true, _125_20, negs, t))
end
| _46_21 -> begin
(false, FStar_ToSMT_Term.mkFalse, FStar_ToSMT_Term.mkFalse, FStar_ToSMT_Term.mkFalse)
end)
end)

# 22 "FStar.ToSMT.SplitQueryCases.fst"
let rec is_ite_all_the_way : Prims.int  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term Prims.list  ->  (Prims.bool * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term) = (fun n t negs l -> if (n <= 0) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.FreeV (_46_27) -> begin
(let _125_31 = (let _125_30 = (let _125_29 = (FStar_ToSMT_Term.mkNot t)
in (negs, _125_29))
in (FStar_ToSMT_Term.mkAnd _125_30))
in (true, l, _125_31))
end
| _46_30 -> begin
(
# 29 "FStar.ToSMT.SplitQueryCases.fst"
let _46_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_46_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _125_34 = (let _125_33 = (FStar_ToSMT_Term.mkImp (negs, t))
in (_125_33)::l)
in (is_ite_all_the_way n rest negs' _125_34))
end else begin
(false, [], FStar_ToSMT_Term.mkFalse)
end
end))
end)
end)

# 36 "FStar.ToSMT.SplitQueryCases.fst"
let rec parse_query_for_split_cases : Prims.int  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  (Prims.bool * ((FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term) * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term)) = (fun n t f -> (match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.Quant (FStar_ToSMT_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _125_61 = (FStar_ToSMT_Term.mkForall'' (l, opt, l', x))
in (f _125_61))))
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Imp, t1::t2::_46_50) -> begin
(
# 41 "FStar.ToSMT.SplitQueryCases.fst"
let r = (match (t2.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.Quant (FStar_ToSMT_Term.Forall, _46_59, _46_61, _46_63, _46_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _125_69 = (FStar_ToSMT_Term.mkImp (t1, x))
in (f _125_69))))
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, _46_71) -> begin
(
# 47 "FStar.ToSMT.SplitQueryCases.fst"
let _46_77 = (is_ite_all_the_way n t2 FStar_ToSMT_Term.mkTrue [])
in (match (_46_77) with
| (b, l, negs) -> begin
(b, ((fun x -> (let _125_78 = (FStar_ToSMT_Term.mkImp (t1, x))
in (f _125_78))), l, negs))
end))
end
| _46_80 -> begin
(false, ((fun _46_81 -> FStar_ToSMT_Term.mkFalse), [], FStar_ToSMT_Term.mkFalse))
end)
in r)
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, _46_86) -> begin
(
# 55 "FStar.ToSMT.SplitQueryCases.fst"
let _46_92 = (is_ite_all_the_way n t FStar_ToSMT_Term.mkTrue [])
in (match (_46_92) with
| (b, l, negs) -> begin
(b, (f, l, negs))
end))
end
| _46_94 -> begin
(false, ((fun _46_95 -> FStar_ToSMT_Term.mkFalse), [], FStar_ToSMT_Term.mkFalse))
end))

# 60 "FStar.ToSMT.SplitQueryCases.fst"
let strip_not : FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term = (fun t -> (match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Not, hd::_46_100) -> begin
hd
end
| _46_106 -> begin
t
end))

# 64 "FStar.ToSMT.SplitQueryCases.fst"
let rec check_split_cases : (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  FStar_ToSMT_Term.term Prims.list  ->  (FStar_ToSMT_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _125_117 = (let _125_116 = (let _125_115 = (let _125_114 = (f t)
in (FStar_ToSMT_Term.mkNot _125_114))
in (_125_115, None))
in FStar_ToSMT_Term.Assume (_125_116))
in (check _125_117))) (FStar_List.rev l)))

# 67 "FStar.ToSMT.SplitQueryCases.fst"
let check_exhaustiveness : (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _125_138 = (let _125_137 = (let _125_136 = (let _125_135 = (let _125_134 = (FStar_ToSMT_Term.mkNot negs)
in (f _125_134))
in (FStar_ToSMT_Term.mkNot _125_135))
in (_125_136, None))
in FStar_ToSMT_Term.Assume (_125_137))
in (check _125_138)))

# 70 "FStar.ToSMT.SplitQueryCases.fst"
let can_handle_query : Prims.int  ->  FStar_ToSMT_Term.decl  ->  (Prims.bool * ((FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term) * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term)) = (fun n q -> (match (q) with
| FStar_ToSMT_Term.Assume (q', _46_118) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _46_123 -> begin
(false, ((fun x -> x), [], FStar_ToSMT_Term.mkFalse))
end))

# 75 "FStar.ToSMT.SplitQueryCases.fst"
let handle_query : ((FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term) * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term)  ->  (FStar_ToSMT_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _46_128 check -> (match (_46_128) with
| (f, l, negs) -> begin
(
# 76 "FStar.ToSMT.SplitQueryCases.fst"
let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))




