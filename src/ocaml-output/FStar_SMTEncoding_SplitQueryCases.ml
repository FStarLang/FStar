
open Prims

let rec get_next_n_ite : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) = (fun n t negs f -> if (n <= (Prims.parse_int "0")) then begin
(let _188_14 = (f FStar_SMTEncoding_Util.mkTrue)
in ((true), (_188_14), (negs), (t)))
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (g)::(t)::(e)::_89_7) -> begin
(let _188_19 = (let _188_16 = (let _188_15 = (FStar_SMTEncoding_Util.mkNot g)
in ((negs), (_188_15)))
in (FStar_SMTEncoding_Util.mkAnd _188_16))
in (get_next_n_ite (n - (Prims.parse_int "1")) e _188_19 (fun x -> (let _188_18 = (FStar_SMTEncoding_Util.mkITE ((g), (t), (x)))
in (f _188_18)))))
end
| FStar_SMTEncoding_Term.FreeV (_89_18) -> begin
(let _188_20 = (f FStar_SMTEncoding_Util.mkTrue)
in ((true), (_188_20), (negs), (t)))
end
| _89_21 -> begin
((false), (FStar_SMTEncoding_Util.mkFalse), (FStar_SMTEncoding_Util.mkFalse), (FStar_SMTEncoding_Util.mkFalse))
end)
end)


let rec is_ite_all_the_way : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (Prims.bool * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term) = (fun n t negs l -> if (n <= (Prims.parse_int "0")) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (_89_27) -> begin
(let _188_31 = (let _188_30 = (let _188_29 = (FStar_SMTEncoding_Util.mkNot t)
in ((negs), (_188_29)))
in (FStar_SMTEncoding_Util.mkAnd _188_30))
in ((true), (l), (_188_31)))
end
| _89_30 -> begin
(

let _89_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_89_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _188_34 = (let _188_33 = (FStar_SMTEncoding_Util.mkImp ((negs), (t)))
in (_188_33)::l)
in (is_ite_all_the_way n rest negs' _188_34))
end else begin
((false), ([]), (FStar_SMTEncoding_Util.mkFalse))
end
end))
end)
end)


let rec parse_query_for_split_cases : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n t f -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _188_61 = (FStar_SMTEncoding_Util.mkForall'' ((l), (opt), (l'), (x)))
in (f _188_61))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (t1)::(t2)::_89_50) -> begin
(

let r = (match (t2.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, _89_59, _89_61, _89_63, _89_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _188_69 = (FStar_SMTEncoding_Util.mkImp ((t1), (x)))
in (f _188_69))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _89_71) -> begin
(

let _89_77 = (is_ite_all_the_way n t2 FStar_SMTEncoding_Util.mkTrue [])
in (match (_89_77) with
| (b, l, negs) -> begin
((b), ((((fun x -> (let _188_78 = (FStar_SMTEncoding_Util.mkImp ((t1), (x)))
in (f _188_78)))), (l), (negs))))
end))
end
| _89_80 -> begin
((false), ((((fun _89_81 -> FStar_SMTEncoding_Util.mkFalse)), ([]), (FStar_SMTEncoding_Util.mkFalse))))
end)
in r)
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _89_86) -> begin
(

let _89_92 = (is_ite_all_the_way n t FStar_SMTEncoding_Util.mkTrue [])
in (match (_89_92) with
| (b, l, negs) -> begin
((b), (((f), (l), (negs))))
end))
end
| _89_94 -> begin
((false), ((((fun _89_95 -> FStar_SMTEncoding_Util.mkFalse)), ([]), (FStar_SMTEncoding_Util.mkFalse))))
end))


let strip_not : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, (hd)::_89_100) -> begin
hd
end
| _89_106 -> begin
t
end))


let rec check_split_cases : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _188_117 = (let _188_116 = (let _188_115 = (let _188_114 = (f t)
in (FStar_SMTEncoding_Util.mkNot _188_114))
in ((_188_115), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_188_116))
in (check _188_117))) (FStar_List.rev l)))


let check_exhaustiveness : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _188_138 = (let _188_137 = (let _188_136 = (let _188_135 = (let _188_134 = (FStar_SMTEncoding_Util.mkNot negs)
in (f _188_134))
in (FStar_SMTEncoding_Util.mkNot _188_135))
in ((_188_136), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_188_137))
in (check _188_138)))


let can_handle_query : Prims.int  ->  FStar_SMTEncoding_Term.decl  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n q -> (match (q) with
| FStar_SMTEncoding_Term.Assume (q', _89_118, _89_120) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _89_125 -> begin
((false), ((((fun x -> x)), ([]), (FStar_SMTEncoding_Util.mkFalse))))
end))


let handle_query : ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _89_130 check -> (match (_89_130) with
| (f, l, negs) -> begin
(

let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))




