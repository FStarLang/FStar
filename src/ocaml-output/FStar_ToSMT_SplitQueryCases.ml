
open Prims

let rec get_next_n_ite : Prims.int  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  (Prims.bool * FStar_ToSMT_Term.term * FStar_ToSMT_Term.term * FStar_ToSMT_Term.term) = (fun n t negs f -> if (n <= (Prims.parse_int "0")) then begin
(let _147_14 = (f FStar_ToSMT_Term.mkTrue)
in ((true), (_147_14), (negs), (t)))
end else begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, (g)::(t)::(e)::_50_7) -> begin
(let _147_19 = (let _147_16 = (let _147_15 = (FStar_ToSMT_Term.mkNot g)
in ((negs), (_147_15)))
in (FStar_ToSMT_Term.mkAnd _147_16))
in (get_next_n_ite (n - (Prims.parse_int "1")) e _147_19 (fun x -> (let _147_18 = (FStar_ToSMT_Term.mkITE ((g), (t), (x)))
in (f _147_18)))))
end
| FStar_ToSMT_Term.FreeV (_50_18) -> begin
(let _147_20 = (f FStar_ToSMT_Term.mkTrue)
in ((true), (_147_20), (negs), (t)))
end
| _50_21 -> begin
((false), (FStar_ToSMT_Term.mkFalse), (FStar_ToSMT_Term.mkFalse), (FStar_ToSMT_Term.mkFalse))
end)
end)


let rec is_ite_all_the_way : Prims.int  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term Prims.list  ->  (Prims.bool * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term) = (fun n t negs l -> if (n <= (Prims.parse_int "0")) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.FreeV (_50_27) -> begin
(let _147_31 = (let _147_30 = (let _147_29 = (FStar_ToSMT_Term.mkNot t)
in ((negs), (_147_29)))
in (FStar_ToSMT_Term.mkAnd _147_30))
in ((true), (l), (_147_31)))
end
| _50_30 -> begin
(

let _50_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_50_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _147_34 = (let _147_33 = (FStar_ToSMT_Term.mkImp ((negs), (t)))
in (_147_33)::l)
in (is_ite_all_the_way n rest negs' _147_34))
end else begin
((false), ([]), (FStar_ToSMT_Term.mkFalse))
end
end))
end)
end)


let rec parse_query_for_split_cases : Prims.int  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  (Prims.bool * ((FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term) * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term)) = (fun n t f -> (match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.Quant (FStar_ToSMT_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _147_61 = (FStar_ToSMT_Term.mkForall'' ((l), (opt), (l'), (x)))
in (f _147_61))))
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Imp, (t1)::(t2)::_50_50) -> begin
(

let r = (match (t2.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.Quant (FStar_ToSMT_Term.Forall, _50_59, _50_61, _50_63, _50_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _147_69 = (FStar_ToSMT_Term.mkImp ((t1), (x)))
in (f _147_69))))
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, _50_71) -> begin
(

let _50_77 = (is_ite_all_the_way n t2 FStar_ToSMT_Term.mkTrue [])
in (match (_50_77) with
| (b, l, negs) -> begin
((b), ((((fun x -> (let _147_78 = (FStar_ToSMT_Term.mkImp ((t1), (x)))
in (f _147_78)))), (l), (negs))))
end))
end
| _50_80 -> begin
((false), ((((fun _50_81 -> FStar_ToSMT_Term.mkFalse)), ([]), (FStar_ToSMT_Term.mkFalse))))
end)
in r)
end
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.ITE, _50_86) -> begin
(

let _50_92 = (is_ite_all_the_way n t FStar_ToSMT_Term.mkTrue [])
in (match (_50_92) with
| (b, l, negs) -> begin
((b), (((f), (l), (negs))))
end))
end
| _50_94 -> begin
((false), ((((fun _50_95 -> FStar_ToSMT_Term.mkFalse)), ([]), (FStar_ToSMT_Term.mkFalse))))
end))


let strip_not : FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term = (fun t -> (match (t.FStar_ToSMT_Term.tm) with
| FStar_ToSMT_Term.App (FStar_ToSMT_Term.Not, (hd)::_50_100) -> begin
hd
end
| _50_106 -> begin
t
end))


let rec check_split_cases : (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  FStar_ToSMT_Term.term Prims.list  ->  (FStar_ToSMT_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _147_117 = (let _147_116 = (let _147_115 = (let _147_114 = (f t)
in (FStar_ToSMT_Term.mkNot _147_114))
in ((_147_115), (None)))
in FStar_ToSMT_Term.Assume (_147_116))
in (check _147_117))) (FStar_List.rev l)))


let check_exhaustiveness : (FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term)  ->  FStar_ToSMT_Term.term  ->  (FStar_ToSMT_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _147_138 = (let _147_137 = (let _147_136 = (let _147_135 = (let _147_134 = (FStar_ToSMT_Term.mkNot negs)
in (f _147_134))
in (FStar_ToSMT_Term.mkNot _147_135))
in ((_147_136), (None)))
in FStar_ToSMT_Term.Assume (_147_137))
in (check _147_138)))


let can_handle_query : Prims.int  ->  FStar_ToSMT_Term.decl  ->  (Prims.bool * ((FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term) * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term)) = (fun n q -> (match (q) with
| FStar_ToSMT_Term.Assume (q', _50_118) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _50_123 -> begin
((false), ((((fun x -> x)), ([]), (FStar_ToSMT_Term.mkFalse))))
end))


let handle_query : ((FStar_ToSMT_Term.term  ->  FStar_ToSMT_Term.term) * FStar_ToSMT_Term.term Prims.list * FStar_ToSMT_Term.term)  ->  (FStar_ToSMT_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _50_128 check -> (match (_50_128) with
| (f, l, negs) -> begin
(

let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))




