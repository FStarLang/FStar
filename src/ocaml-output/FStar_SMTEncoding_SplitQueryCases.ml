
open Prims

let rec get_next_n_ite : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) = (fun n t negs f -> if (n <= (Prims.parse_int "0")) then begin
(let _181_14 = (f FStar_SMTEncoding_Util.mkTrue)
in ((true), (_181_14), (negs), (t)))
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (g)::(t)::(e)::_86_7) -> begin
(let _181_19 = (let _181_16 = (let _181_15 = (FStar_SMTEncoding_Util.mkNot g)
in ((negs), (_181_15)))
in (FStar_SMTEncoding_Util.mkAnd _181_16))
in (get_next_n_ite (n - (Prims.parse_int "1")) e _181_19 (fun x -> (let _181_18 = (FStar_SMTEncoding_Util.mkITE ((g), (t), (x)))
in (f _181_18)))))
end
| FStar_SMTEncoding_Term.FreeV (_86_18) -> begin
(let _181_20 = (f FStar_SMTEncoding_Util.mkTrue)
in ((true), (_181_20), (negs), (t)))
end
| _86_21 -> begin
((false), (FStar_SMTEncoding_Util.mkFalse), (FStar_SMTEncoding_Util.mkFalse), (FStar_SMTEncoding_Util.mkFalse))
end)
end)


let rec is_ite_all_the_way : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (Prims.bool * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term) = (fun n t negs l -> if (n <= (Prims.parse_int "0")) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (_86_27) -> begin
(let _181_31 = (let _181_30 = (let _181_29 = (FStar_SMTEncoding_Util.mkNot t)
in ((negs), (_181_29)))
in (FStar_SMTEncoding_Util.mkAnd _181_30))
in ((true), (l), (_181_31)))
end
| _86_30 -> begin
(

let _86_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_86_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _181_34 = (let _181_33 = (FStar_SMTEncoding_Util.mkImp ((negs), (t)))
in (_181_33)::l)
in (is_ite_all_the_way n rest negs' _181_34))
end else begin
((false), ([]), (FStar_SMTEncoding_Util.mkFalse))
end
end))
end)
end)


let rec parse_query_for_split_cases : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n t f -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _181_61 = (FStar_SMTEncoding_Util.mkForall'' ((l), (opt), (l'), (x)))
in (f _181_61))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (t1)::(t2)::_86_50) -> begin
(

let r = (match (t2.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, _86_59, _86_61, _86_63, _86_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _181_69 = (FStar_SMTEncoding_Util.mkImp ((t1), (x)))
in (f _181_69))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _86_71) -> begin
(

let _86_77 = (is_ite_all_the_way n t2 FStar_SMTEncoding_Util.mkTrue [])
in (match (_86_77) with
| (b, l, negs) -> begin
((b), ((((fun x -> (let _181_78 = (FStar_SMTEncoding_Util.mkImp ((t1), (x)))
in (f _181_78)))), (l), (negs))))
end))
end
| _86_80 -> begin
((false), ((((fun _86_81 -> FStar_SMTEncoding_Util.mkFalse)), ([]), (FStar_SMTEncoding_Util.mkFalse))))
end)
in r)
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _86_86) -> begin
(

let _86_92 = (is_ite_all_the_way n t FStar_SMTEncoding_Util.mkTrue [])
in (match (_86_92) with
| (b, l, negs) -> begin
((b), (((f), (l), (negs))))
end))
end
| _86_94 -> begin
((false), ((((fun _86_95 -> FStar_SMTEncoding_Util.mkFalse)), ([]), (FStar_SMTEncoding_Util.mkFalse))))
end))


let strip_not : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, (hd)::_86_100) -> begin
hd
end
| _86_106 -> begin
t
end))


let rec check_split_cases : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _181_117 = (let _181_116 = (let _181_115 = (let _181_114 = (f t)
in (FStar_SMTEncoding_Util.mkNot _181_114))
in ((_181_115), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_181_116))
in (check _181_117))) (FStar_List.rev l)))


let check_exhaustiveness : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _181_138 = (let _181_137 = (let _181_136 = (let _181_135 = (let _181_134 = (FStar_SMTEncoding_Util.mkNot negs)
in (f _181_134))
in (FStar_SMTEncoding_Util.mkNot _181_135))
in ((_181_136), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_181_137))
in (check _181_138)))


let can_handle_query : Prims.int  ->  FStar_SMTEncoding_Term.decl  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n q -> (match (q) with
| FStar_SMTEncoding_Term.Assume (q', _86_118, _86_120) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _86_125 -> begin
((false), ((((fun x -> x)), ([]), (FStar_SMTEncoding_Util.mkFalse))))
end))


let handle_query : ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _86_130 check -> (match (_86_130) with
| (f, l, negs) -> begin
(

let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))




