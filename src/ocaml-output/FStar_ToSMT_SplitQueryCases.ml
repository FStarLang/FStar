
open Prims
let rec get_next_n_ite : Prims.int  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  (Prims.bool * FStar_ToSMT_Term.term * FStar_ToSMT_Term.term * FStar_ToSMT_Term.term) = (fun n t negs f -> if (n <= 0) then begin
(let _161_14 = (f FStar_ToSMT_Term.mkTrue)
in (true, _161_14, negs, t))
end else begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, g::t::e::_58_7) -> begin
(let _161_19 = (let _161_16 = (let _161_15 = (FStar_ToSMT_Term.mkNot g)
in (negs, _161_15))
in (FStar_ToSMT_Term.mkAnd _161_16))
in (get_next_n_ite (n - 1) e _161_19 (fun x -> (let _161_18 = (FStar_ToSMT_Term.mkITE (g, t, x))
in (f _161_18)))))
end
| FStar_ToSMT_Term.FreeV (_58_18) -> begin
(let _161_20 = (f FStar_ToSMT_Term.mkTrue)
in (true, _161_20, negs, t))
end
| _58_21 -> begin
(false, FStar_ToSMT_Term.mkFalse, FStar_ToSMT_Term.mkFalse, FStar_ToSMT_Term.mkFalse)
end)
end)

let rec is_ite_all_the_way : Prims.int  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term Prims.list  ->  (Prims.bool * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term) = (fun n t negs l -> if (n <= 0) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.FreeV (_58_27) -> begin
(let _161_31 = (let _161_30 = (let _161_29 = (FStar_ToSMT_Term.mkNot t)
in (negs, _161_29))
in (FStar_ToSMT_Term.mkAnd _161_30))
in (true, l, _161_31))
end
| _58_30 -> begin
(let _58_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_58_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _161_34 = (let _161_33 = (FStar_ToSMT_Term.mkImp (negs, t))
in (_161_33)::l)
in (is_ite_all_the_way n rest negs' _161_34))
end else begin
(false, [], FStar_ToSMT_Term.mkFalse)
end
end))
end)
end)

let rec parse_query_for_split_cases : Prims.int  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  (Prims.bool * ((FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term) * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term)) = (fun n t f -> (match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.Quant (FStar_ToSMT_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _161_61 = (FStar_ToSMT_Term.mkForall'' (l, opt, l', x))
in (f _161_61))))
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Imp, t1::t2::_58_50) -> begin
(let r = (match (t2.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.Quant (FStar_ToSMT_Term.Forall, _58_59, _58_61, _58_63, _58_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _161_69 = (FStar_ToSMT_Term.mkImp (t1, x))
in (f _161_69))))
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, _58_71) -> begin
(let _58_77 = (is_ite_all_the_way n t2 FStar_ToSMT_Term.mkTrue [])
in (match (_58_77) with
| (b, l, negs) -> begin
(b, ((fun x -> (let _161_78 = (FStar_ToSMT_Term.mkImp (t1, x))
in (f _161_78))), l, negs))
end))
end
| _58_80 -> begin
(false, ((fun _58_81 -> FStar_ToSMT_Term.mkFalse), [], FStar_ToSMT_Term.mkFalse))
end)
in r)
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, _58_86) -> begin
(let _58_92 = (is_ite_all_the_way n t FStar_ToSMT_Term.mkTrue [])
in (match (_58_92) with
| (b, l, negs) -> begin
(b, (f, l, negs))
end))
end
| _58_94 -> begin
(false, ((fun _58_95 -> FStar_ToSMT_Term.mkFalse), [], FStar_ToSMT_Term.mkFalse))
end))

let strip_not : FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term = (fun t -> (match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Not, hd::_58_100) -> begin
hd
end
| _58_106 -> begin
t
end))

let rec check_split_cases : (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  FStar_ToSMT_Term.term Prims.list  ->  (FStar_ToSMT_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _161_117 = (let _161_116 = (let _161_115 = (let _161_114 = (f t)
in (FStar_ToSMT_Term.mkNot _161_114))
in (_161_115, None))
in FStar_ToSMT_Term.Assume (_161_116))
in (check _161_117))) (FStar_List.rev l)))

let check_exhaustiveness : (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _161_138 = (let _161_137 = (let _161_136 = (let _161_135 = (let _161_134 = (FStar_ToSMT_Term.mkNot negs)
in (f _161_134))
in (FStar_ToSMT_Term.mkNot _161_135))
in (_161_136, None))
in FStar_ToSMT_Term.Assume (_161_137))
in (check _161_138)))

let can_handle_query : Prims.int  ->  FStar_ToSMT_Term.decl  ->  (Prims.bool * ((FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term) * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term)) = (fun n q -> (match (q) with
| FStar_ToSMT_Term.Assume (q', _58_118) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _58_123 -> begin
(false, ((fun x -> x), [], FStar_ToSMT_Term.mkFalse))
end))

let handle_query : ((FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term) * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term)  ->  (FStar_ToSMT_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _58_128 check -> (match (_58_128) with
| (f, l, negs) -> begin
(let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))




