
open Prims
# 10 "splitcases.fs"
let rec get_next_n_ite : Prims.int  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  (Prims.bool * FStar_ToSMT_Term.term * FStar_ToSMT_Term.term * FStar_ToSMT_Term.term) = (fun n t negs f -> if (n <= 0) then begin
(let _159_14 = (f FStar_ToSMT_Term.mkTrue)
in (true, _159_14, negs, t))
end else begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, g::t::e::_57_7) -> begin
(let _159_19 = (let _159_16 = (let _159_15 = (FStar_ToSMT_Term.mkNot g)
in (negs, _159_15))
in (FStar_ToSMT_Term.mkAnd _159_16))
in (get_next_n_ite (n - 1) e _159_19 (fun x -> (let _159_18 = (FStar_ToSMT_Term.mkITE (g, t, x))
in (f _159_18)))))
end
| FStar_ToSMT_Term.FreeV (_57_18) -> begin
(let _159_20 = (f FStar_ToSMT_Term.mkTrue)
in (true, _159_20, negs, t))
end
| _57_21 -> begin
(false, FStar_ToSMT_Term.mkFalse, FStar_ToSMT_Term.mkFalse, FStar_ToSMT_Term.mkFalse)
end)
end)

# 22 "splitcases.fs"
let rec is_ite_all_the_way : Prims.int  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term Prims.list  ->  (Prims.bool * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term) = (fun n t negs l -> if (n <= 0) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.FreeV (_57_27) -> begin
(let _159_31 = (let _159_30 = (let _159_29 = (FStar_ToSMT_Term.mkNot t)
in (negs, _159_29))
in (FStar_ToSMT_Term.mkAnd _159_30))
in (true, l, _159_31))
end
| _57_30 -> begin
(let _57_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_57_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _159_34 = (let _159_33 = (FStar_ToSMT_Term.mkImp (negs, t))
in (_159_33)::l)
in (is_ite_all_the_way n rest negs' _159_34))
end else begin
(false, [], FStar_ToSMT_Term.mkFalse)
end
end))
end)
end)

# 36 "splitcases.fs"
let rec parse_query_for_split_cases : Prims.int  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  (Prims.bool * ((FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term) * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term)) = (fun n t f -> (match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.Quant (FStar_ToSMT_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _159_61 = (FStar_ToSMT_Term.mkForall'' (l, opt, l', x))
in (f _159_61))))
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Imp, t1::t2::_57_50) -> begin
(let r = (match (t2.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.Quant (FStar_ToSMT_Term.Forall, _57_59, _57_61, _57_63, _57_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _159_69 = (FStar_ToSMT_Term.mkImp (t1, x))
in (f _159_69))))
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, _57_71) -> begin
(let _57_77 = (is_ite_all_the_way n t2 FStar_ToSMT_Term.mkTrue [])
in (match (_57_77) with
| (b, l, negs) -> begin
(b, ((fun x -> (let _159_78 = (FStar_ToSMT_Term.mkImp (t1, x))
in (f _159_78))), l, negs))
end))
end
| _57_80 -> begin
(false, ((fun _57_81 -> FStar_ToSMT_Term.mkFalse), [], FStar_ToSMT_Term.mkFalse))
end)
in r)
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, _57_86) -> begin
(let _57_92 = (is_ite_all_the_way n t FStar_ToSMT_Term.mkTrue [])
in (match (_57_92) with
| (b, l, negs) -> begin
(b, (f, l, negs))
end))
end
| _57_94 -> begin
(false, ((fun _57_95 -> FStar_ToSMT_Term.mkFalse), [], FStar_ToSMT_Term.mkFalse))
end))

# 60 "splitcases.fs"
let strip_not : FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term = (fun t -> (match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Not, hd::_57_100) -> begin
hd
end
| _57_106 -> begin
t
end))

# 64 "splitcases.fs"
let rec check_split_cases : (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  FStar_ToSMT_Term.term Prims.list  ->  (FStar_ToSMT_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _159_117 = (let _159_116 = (let _159_115 = (let _159_114 = (f t)
in (FStar_ToSMT_Term.mkNot _159_114))
in (_159_115, None))
in FStar_ToSMT_Term.Assume (_159_116))
in (check _159_117))) (FStar_List.rev l)))

# 67 "splitcases.fs"
let check_exhaustiveness : (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _159_138 = (let _159_137 = (let _159_136 = (let _159_135 = (let _159_134 = (FStar_ToSMT_Term.mkNot negs)
in (f _159_134))
in (FStar_ToSMT_Term.mkNot _159_135))
in (_159_136, None))
in FStar_ToSMT_Term.Assume (_159_137))
in (check _159_138)))

# 70 "splitcases.fs"
let can_handle_query : Prims.int  ->  FStar_ToSMT_Term.decl  ->  (Prims.bool * ((FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term) * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term)) = (fun n q -> (match (q) with
| FStar_ToSMT_Term.Assume (q', _57_118) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _57_123 -> begin
(false, ((fun x -> x), [], FStar_ToSMT_Term.mkFalse))
end))

# 75 "splitcases.fs"
let handle_query : ((FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term) * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term)  ->  (FStar_ToSMT_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _57_128 check -> (match (_57_128) with
| (f, l, negs) -> begin
(let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))




