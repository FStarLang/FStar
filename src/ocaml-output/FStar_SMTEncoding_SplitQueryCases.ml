
open Prims
open FStar_Pervasives

let rec get_next_n_ite : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) = (fun n1 t negs f -> (match ((n1 <= (Prims.parse_int "0"))) with
| true -> begin
(

let uu____30 = (f FStar_SMTEncoding_Util.mkTrue)
in ((true), (uu____30), (negs), (t)))
end
| uu____31 -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (g)::(t1)::(e)::uu____39) -> begin
(

let uu____42 = (

let uu____43 = (

let uu____46 = (FStar_SMTEncoding_Util.mkNot g)
in ((negs), (uu____46)))
in (FStar_SMTEncoding_Util.mkAnd uu____43))
in (get_next_n_ite (n1 - (Prims.parse_int "1")) e uu____42 (fun x -> (

let uu____48 = (FStar_SMTEncoding_Util.mkITE ((g), (t1), (x)))
in (f uu____48)))))
end
| FStar_SMTEncoding_Term.FreeV (uu____49) -> begin
(

let uu____52 = (f FStar_SMTEncoding_Util.mkTrue)
in ((true), (uu____52), (negs), (t)))
end
| uu____53 -> begin
((false), (FStar_SMTEncoding_Util.mkFalse), (FStar_SMTEncoding_Util.mkFalse), (FStar_SMTEncoding_Util.mkFalse))
end)
end))


let rec is_ite_all_the_way : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (Prims.bool * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term) = (fun n1 t negs l -> (match ((n1 <= (Prims.parse_int "0"))) with
| true -> begin
(FStar_Pervasives.raise FStar_Util.Impos)
end
| uu____84 -> begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (uu____89) -> begin
(

let uu____92 = (

let uu____93 = (

let uu____96 = (FStar_SMTEncoding_Util.mkNot t)
in ((negs), (uu____96)))
in (FStar_SMTEncoding_Util.mkAnd uu____93))
in ((true), (l), (uu____92)))
end
| uu____98 -> begin
(

let uu____99 = (get_next_n_ite n1 t negs (fun x -> x))
in (match (uu____99) with
| (b, t1, negs', rest) -> begin
(match (b) with
| true -> begin
(

let uu____117 = (

let uu____119 = (FStar_SMTEncoding_Util.mkImp ((negs), (t1)))
in (uu____119)::l)
in (is_ite_all_the_way n1 rest negs' uu____117))
end
| uu____120 -> begin
((false), ([]), (FStar_SMTEncoding_Util.mkFalse))
end)
end))
end)
end))


let rec parse_query_for_split_cases : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n1 t f -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, l, opt, l', t1) -> begin
(parse_query_for_split_cases n1 t1 (fun x -> (

let uu____173 = (FStar_SMTEncoding_Util.mkForall'' ((l), (opt), (l'), (x)))
in (f uu____173))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (t1)::(t2)::uu____180) -> begin
(

let r = (match (t2.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, uu____200, uu____201, uu____202, uu____203) -> begin
(parse_query_for_split_cases n1 t2 (fun x -> (

let uu____213 = (FStar_SMTEncoding_Util.mkImp ((t1), (x)))
in (f uu____213))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, uu____214) -> begin
(

let uu____217 = (is_ite_all_the_way n1 t2 FStar_SMTEncoding_Util.mkTrue [])
in (match (uu____217) with
| (b, l, negs) -> begin
((b), ((((fun x -> (

let uu____245 = (FStar_SMTEncoding_Util.mkImp ((t1), (x)))
in (f uu____245)))), (l), (negs))))
end))
end
| uu____246 -> begin
((false), ((((fun uu____256 -> FStar_SMTEncoding_Util.mkFalse)), ([]), (FStar_SMTEncoding_Util.mkFalse))))
end)
in r)
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, uu____257) -> begin
(

let uu____260 = (is_ite_all_the_way n1 t FStar_SMTEncoding_Util.mkTrue [])
in (match (uu____260) with
| (b, l, negs) -> begin
((b), (((f), (l), (negs))))
end))
end
| uu____287 -> begin
((false), ((((fun uu____297 -> FStar_SMTEncoding_Util.mkFalse)), ([]), (FStar_SMTEncoding_Util.mkFalse))))
end))


let strip_not : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, (hd1)::uu____302) -> begin
hd1
end
| uu____305 -> begin
t
end))


let handle_query : ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun uu____320 check -> (match (uu____320) with
| (f, l, negs) -> begin
(failwith "SplitQueryCases is not currently supported")
end))




