
open Prims
let rec get_next_n_ite : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) = (fun n t negs f -> if (n <= 0) then begin
(let _201_14 = (f FStar_SMTEncoding_Term.mkTrue)
in (true, _201_14, negs, t))
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, g::t::e::_98_7) -> begin
(let _201_19 = (let _201_16 = (let _201_15 = (FStar_SMTEncoding_Term.mkNot g)
in (negs, _201_15))
in (FStar_SMTEncoding_Term.mkAnd _201_16))
in (get_next_n_ite (n - 1) e _201_19 (fun x -> (let _201_18 = (FStar_SMTEncoding_Term.mkITE (g, t, x))
in (f _201_18)))))
end
| FStar_SMTEncoding_Term.FreeV (_98_18) -> begin
(let _201_20 = (f FStar_SMTEncoding_Term.mkTrue)
in (true, _201_20, negs, t))
end
| _98_21 -> begin
(false, FStar_SMTEncoding_Term.mkFalse, FStar_SMTEncoding_Term.mkFalse, FStar_SMTEncoding_Term.mkFalse)
end)
end)

let rec is_ite_all_the_way : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (Prims.bool * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term) = (fun n t negs l -> if (n <= 0) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (_98_27) -> begin
(let _201_31 = (let _201_30 = (let _201_29 = (FStar_SMTEncoding_Term.mkNot t)
in (negs, _201_29))
in (FStar_SMTEncoding_Term.mkAnd _201_30))
in (true, l, _201_31))
end
| _98_30 -> begin
(let _98_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_98_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _201_34 = (let _201_33 = (FStar_SMTEncoding_Term.mkImp (negs, t))
in (_201_33)::l)
in (is_ite_all_the_way n rest negs' _201_34))
end else begin
(false, [], FStar_SMTEncoding_Term.mkFalse)
end
end))
end)
end)

let rec parse_query_for_split_cases : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n t f -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _201_61 = (FStar_SMTEncoding_Term.mkForall'' (l, opt, l', x))
in (f _201_61))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, t1::t2::_98_50) -> begin
(let r = (match (t2.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, _98_59, _98_61, _98_63, _98_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _201_69 = (FStar_SMTEncoding_Term.mkImp (t1, x))
in (f _201_69))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _98_71) -> begin
(let _98_77 = (is_ite_all_the_way n t2 FStar_SMTEncoding_Term.mkTrue [])
in (match (_98_77) with
| (b, l, negs) -> begin
(b, ((fun x -> (let _201_78 = (FStar_SMTEncoding_Term.mkImp (t1, x))
in (f _201_78))), l, negs))
end))
end
| _98_80 -> begin
(false, ((fun _98_81 -> FStar_SMTEncoding_Term.mkFalse), [], FStar_SMTEncoding_Term.mkFalse))
end)
in r)
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _98_86) -> begin
(let _98_92 = (is_ite_all_the_way n t FStar_SMTEncoding_Term.mkTrue [])
in (match (_98_92) with
| (b, l, negs) -> begin
(b, (f, l, negs))
end))
end
| _98_94 -> begin
(false, ((fun _98_95 -> FStar_SMTEncoding_Term.mkFalse), [], FStar_SMTEncoding_Term.mkFalse))
end))

let strip_not : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, hd::_98_100) -> begin
hd
end
| _98_106 -> begin
t
end))

let rec check_split_cases : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _201_117 = (let _201_116 = (let _201_115 = (let _201_114 = (f t)
in (FStar_SMTEncoding_Term.mkNot _201_114))
in (_201_115, None))
in FStar_SMTEncoding_Term.Assume (_201_116))
in (check _201_117))) (FStar_List.rev l)))

let check_exhaustiveness : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _201_138 = (let _201_137 = (let _201_136 = (let _201_135 = (let _201_134 = (FStar_SMTEncoding_Term.mkNot negs)
in (f _201_134))
in (FStar_SMTEncoding_Term.mkNot _201_135))
in (_201_136, None))
in FStar_SMTEncoding_Term.Assume (_201_137))
in (check _201_138)))

let can_handle_query : Prims.int  ->  FStar_SMTEncoding_Term.decl  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n q -> (match (q) with
| FStar_SMTEncoding_Term.Assume (q', _98_118) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _98_123 -> begin
(false, ((fun x -> x), [], FStar_SMTEncoding_Term.mkFalse))
end))

let handle_query : ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _98_128 check -> (match (_98_128) with
| (f, l, negs) -> begin
(let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))




