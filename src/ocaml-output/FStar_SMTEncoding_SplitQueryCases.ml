
open Prims
open FStar_Pervasives

let rec get_next_n_ite : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) = (fun n1 t negs f -> (match ((n1 <= (Prims.parse_int "0"))) with
| true -> begin
(

let uu____34 = (f FStar_SMTEncoding_Util.mkTrue)
in ((true), (uu____34), (negs), (t)))
end
| uu____35 -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (g)::(t1)::(e)::uu____47) -> begin
(

let uu____52 = (

let uu____53 = (

let uu____58 = (FStar_SMTEncoding_Util.mkNot g)
in ((negs), (uu____58)))
in (FStar_SMTEncoding_Util.mkAnd uu____53))
in (get_next_n_ite (n1 - (Prims.parse_int "1")) e uu____52 (fun x -> (

let uu____62 = (FStar_SMTEncoding_Util.mkITE ((g), (t1), (x)))
in (f uu____62)))))
end
| FStar_SMTEncoding_Term.FreeV (uu____63) -> begin
(

let uu____68 = (f FStar_SMTEncoding_Util.mkTrue)
in ((true), (uu____68), (negs), (t)))
end
| uu____69 -> begin
((false), (FStar_SMTEncoding_Util.mkFalse), (FStar_SMTEncoding_Util.mkFalse), (FStar_SMTEncoding_Util.mkFalse))
end)
end))


let rec is_ite_all_the_way : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (Prims.bool * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term) = (fun n1 t negs l -> (match ((n1 <= (Prims.parse_int "0"))) with
| true -> begin
(FStar_Exn.raise FStar_Util.Impos)
end
| uu____110 -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (uu____119) -> begin
(

let uu____124 = (

let uu____125 = (

let uu____130 = (FStar_SMTEncoding_Util.mkNot t)
in ((negs), (uu____130)))
in (FStar_SMTEncoding_Util.mkAnd uu____125))
in ((true), (l), (uu____124)))
end
| uu____133 -> begin
(

let uu____134 = (get_next_n_ite n1 t negs (fun x -> x))
in (match (uu____134) with
| (b, t1, negs', rest) -> begin
(match (b) with
| true -> begin
(

let uu____165 = (

let uu____168 = (FStar_SMTEncoding_Util.mkImp ((negs), (t1)))
in (uu____168)::l)
in (is_ite_all_the_way n1 rest negs' uu____165))
end
| uu____169 -> begin
((false), ([]), (FStar_SMTEncoding_Util.mkFalse))
end)
end))
end)
end))


let rec parse_query_for_split_cases : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n1 t f -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, l, opt, l', t1) -> begin
(parse_query_for_split_cases n1 t1 (fun x -> (

let uu____237 = (FStar_SMTEncoding_Util.mkForall'' ((l), (opt), (l'), (x)))
in (f uu____237))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (t1)::(t2)::uu____248) -> begin
(

let r = (match (t2.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, uu____282, uu____283, uu____284, uu____285) -> begin
(parse_query_for_split_cases n1 t2 (fun x -> (

let uu____305 = (FStar_SMTEncoding_Util.mkImp ((t1), (x)))
in (f uu____305))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, uu____306) -> begin
(

let uu____311 = (is_ite_all_the_way n1 t2 FStar_SMTEncoding_Util.mkTrue [])
in (match (uu____311) with
| (b, l, negs) -> begin
((b), ((((fun x -> (

let uu____358 = (FStar_SMTEncoding_Util.mkImp ((t1), (x)))
in (f uu____358)))), (l), (negs))))
end))
end
| uu____359 -> begin
((false), ((((fun uu____375 -> (FStar_Util.return_all FStar_SMTEncoding_Util.mkFalse))), ([]), (FStar_SMTEncoding_Util.mkFalse))))
end)
in r)
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, uu____376) -> begin
(

let uu____381 = (is_ite_all_the_way n1 t FStar_SMTEncoding_Util.mkTrue [])
in (match (uu____381) with
| (b, l, negs) -> begin
((b), (((f), (l), (negs))))
end))
end
| uu____425 -> begin
((false), ((((fun uu____441 -> (FStar_Util.return_all FStar_SMTEncoding_Util.mkFalse))), ([]), (FStar_SMTEncoding_Util.mkFalse))))
end))


let strip_not : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, (hd1)::uu____446) -> begin
hd1
end
| uu____451 -> begin
t
end))


let handle_query : ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun uu____470 check1 -> (match (uu____470) with
| (f, l, negs) -> begin
(failwith "SplitQueryCases is not currently supported")
end))




