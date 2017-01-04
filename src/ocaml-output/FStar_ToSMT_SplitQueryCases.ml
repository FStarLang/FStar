
open Prims

let rec get_next_n_ite : Prims.int  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  (Prims.bool * FStar_ToSMT_Term.term * FStar_ToSMT_Term.term * FStar_ToSMT_Term.term) = (fun n t negs f -> if (n <= (Prims.parse_int "0")) then begin
(let _149_14 = (f FStar_ToSMT_Term.mkTrue)
in ((true), (_149_14), (negs), (t)))
end else begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, (g)::(t)::(e)::_51_7) -> begin
(let _149_19 = (let _149_16 = (let _149_15 = (FStar_ToSMT_Term.mkNot g)
in ((negs), (_149_15)))
in (FStar_ToSMT_Term.mkAnd _149_16))
in (get_next_n_ite (n - (Prims.parse_int "1")) e _149_19 (fun x -> (let _149_18 = (FStar_ToSMT_Term.mkITE ((g), (t), (x)))
in (f _149_18)))))
end
| FStar_ToSMT_Term.FreeV (_51_18) -> begin
(let _149_20 = (f FStar_ToSMT_Term.mkTrue)
in ((true), (_149_20), (negs), (t)))
end
| _51_21 -> begin
((false), (FStar_ToSMT_Term.mkFalse), (FStar_ToSMT_Term.mkFalse), (FStar_ToSMT_Term.mkFalse))
end)
end)


let rec is_ite_all_the_way : Prims.int  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term Prims.list  ->  (Prims.bool * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term) = (fun n t negs l -> if (n <= (Prims.parse_int "0")) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.FreeV (_51_27) -> begin
(let _149_31 = (let _149_30 = (let _149_29 = (FStar_ToSMT_Term.mkNot t)
in ((negs), (_149_29)))
in (FStar_ToSMT_Term.mkAnd _149_30))
in ((true), (l), (_149_31)))
end
| _51_30 -> begin
(

let _51_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_51_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _149_34 = (let _149_33 = (FStar_ToSMT_Term.mkImp ((negs), (t)))
in (_149_33)::l)
in (is_ite_all_the_way n rest negs' _149_34))
end else begin
((false), ([]), (FStar_ToSMT_Term.mkFalse))
end
end))
end)
end)


let rec parse_query_for_split_cases : Prims.int  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  (Prims.bool * ((FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term) * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term)) = (fun n t f -> (match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.Quant (FStar_ToSMT_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _149_61 = (FStar_ToSMT_Term.mkForall'' ((l), (opt), (l'), (x)))
in (f _149_61))))
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Imp, (t1)::(t2)::_51_50) -> begin
(

let r = (match (t2.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.Quant (FStar_ToSMT_Term.Forall, _51_59, _51_61, _51_63, _51_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _149_69 = (FStar_ToSMT_Term.mkImp ((t1), (x)))
in (f _149_69))))
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, _51_71) -> begin
(

let _51_77 = (is_ite_all_the_way n t2 FStar_ToSMT_Term.mkTrue [])
in (match (_51_77) with
| (b, l, negs) -> begin
((b), ((((fun x -> (let _149_78 = (FStar_ToSMT_Term.mkImp ((t1), (x)))
in (f _149_78)))), (l), (negs))))
end))
end
| _51_80 -> begin
((false), ((((fun _51_81 -> FStar_ToSMT_Term.mkFalse)), ([]), (FStar_ToSMT_Term.mkFalse))))
end)
in r)
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, _51_86) -> begin
(

let _51_92 = (is_ite_all_the_way n t FStar_ToSMT_Term.mkTrue [])
in (match (_51_92) with
| (b, l, negs) -> begin
((b), (((f), (l), (negs))))
end))
end
| _51_94 -> begin
((false), ((((fun _51_95 -> FStar_ToSMT_Term.mkFalse)), ([]), (FStar_ToSMT_Term.mkFalse))))
end))


let strip_not : FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term = (fun t -> (match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Not, (hd)::_51_100) -> begin
hd
end
| _51_106 -> begin
t
end))


let rec check_split_cases : (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  FStar_ToSMT_Term.term Prims.list  ->  (FStar_ToSMT_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _149_117 = (let _149_116 = (let _149_115 = (let _149_114 = (f t)
in (FStar_ToSMT_Term.mkNot _149_114))
in ((_149_115), (None)))
in FStar_ToSMT_Term.Assume (_149_116))
in (check _149_117))) (FStar_List.rev l)))


let check_exhaustiveness : (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _149_138 = (let _149_137 = (let _149_136 = (let _149_135 = (let _149_134 = (FStar_ToSMT_Term.mkNot negs)
in (f _149_134))
in (FStar_ToSMT_Term.mkNot _149_135))
in ((_149_136), (None)))
in FStar_ToSMT_Term.Assume (_149_137))
in (check _149_138)))


let can_handle_query : Prims.int  ->  FStar_ToSMT_Term.decl  ->  (Prims.bool * ((FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term) * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term)) = (fun n q -> (match (q) with
| FStar_ToSMT_Term.Assume (q', _51_118) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _51_123 -> begin
((false), ((((fun x -> x)), ([]), (FStar_ToSMT_Term.mkFalse))))
end))


let handle_query : ((FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term) * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term)  ->  (FStar_ToSMT_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _51_128 check -> (match (_51_128) with
| (f, l, negs) -> begin
(

let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))




