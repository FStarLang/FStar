
open Prims
type doc =
| Doc of Prims.string


let uu___is_Doc : doc  ->  Prims.bool = (fun projectee -> true)


let __proj__Doc__item___0 : doc  ->  Prims.string = (fun projectee -> (match (projectee) with
| Doc (_0) -> begin
_0
end))


let empty : doc = Doc ("")


let hardline : doc = Doc ("\n")


let text : Prims.string  ->  doc = (fun s -> Doc (s))


let num : Prims.int  ->  doc = (fun i -> Doc ((Prims.string_of_int i)))


let break_ : Prims.int  ->  doc = (fun i -> Doc (""))


let break0 : doc = (break_ (Prims.parse_int "0"))


let break1 : doc = (text " ")


let enclose : doc  ->  doc  ->  doc  ->  doc = (fun uu____26 uu____27 uu____28 -> (match (((uu____26), (uu____27), (uu____28))) with
| (Doc (l), Doc (r), Doc (x)) -> begin
Doc ((Prims.strcat l (Prims.strcat x r)))
end))


let brackets : doc  ->  doc = (fun uu____34 -> (match (uu____34) with
| Doc (d) -> begin
(enclose (text "[") (text "]") (Doc (d)))
end))


let cbrackets : doc  ->  doc = (fun uu____38 -> (match (uu____38) with
| Doc (d) -> begin
(enclose (text "{") (text "}") (Doc (d)))
end))


let parens : doc  ->  doc = (fun uu____42 -> (match (uu____42) with
| Doc (d) -> begin
(enclose (text "(") (text ")") (Doc (d)))
end))


let cat : doc  ->  doc  ->  doc = (fun uu____48 uu____49 -> (match (((uu____48), (uu____49))) with
| (Doc (d1), Doc (d2)) -> begin
Doc ((Prims.strcat d1 d2))
end))


let reduce : doc Prims.list  ->  doc = (fun docs1 -> (FStar_List.fold_left cat empty docs1))


let group : doc  ->  doc = (fun uu____59 -> (match (uu____59) with
| Doc (d) -> begin
Doc (d)
end))


let groups : doc Prims.list  ->  doc = (fun docs1 -> (

let uu____66 = (reduce docs1)
in (group uu____66)))


let combine : doc  ->  doc Prims.list  ->  doc = (fun uu____72 docs1 -> (match (uu____72) with
| Doc (sep) -> begin
(

let select = (fun uu____80 -> (match (uu____80) with
| Doc (d) -> begin
(match ((d = "")) with
| true -> begin
None
end
| uu____84 -> begin
Some (d)
end)
end))
in (

let docs2 = (FStar_List.choose select docs1)
in Doc ((FStar_String.concat sep docs2))))
end))


let cat1 : doc  ->  doc  ->  doc = (fun d1 d2 -> (reduce ((d1)::(break1)::(d2)::[])))


let reduce1 : doc Prims.list  ->  doc = (fun docs1 -> (combine break1 docs1))


let nest : Prims.int  ->  doc  ->  doc = (fun i uu____103 -> (match (uu____103) with
| Doc (d) -> begin
Doc (d)
end))


let align : doc Prims.list  ->  doc = (fun docs1 -> (

let uu____110 = (combine hardline docs1)
in (match (uu____110) with
| Doc (doc1) -> begin
Doc (doc1)
end)))


let hbox : doc  ->  doc = (fun d -> d)


let pretty : Prims.int  ->  doc  ->  Prims.string = (fun sz uu____120 -> (match (uu____120) with
| Doc (doc1) -> begin
doc1
end))




