
open Prims

type doc =
| Doc of Prims.string


let is_Doc = (fun _discr_ -> (match (_discr_) with
| Doc (_) -> begin
true
end
| _ -> begin
false
end))


let ___Doc____0 = (fun projectee -> (match (projectee) with
| Doc (_28_2) -> begin
_28_2
end))


let empty : doc = Doc ("")


let hardline : doc = Doc ("\n")


let text : Prims.string  ->  doc = (fun s -> Doc (s))


let num : Prims.int  ->  doc = (fun i -> Doc ((Prims.string_of_int i)))


let break_ : Prims.int  ->  doc = (fun i -> Doc (""))


let break0 : doc = (break_ (Prims.parse_int "0"))


let break1 : doc = (text " ")


let enclose : doc  ->  doc  ->  doc  ->  doc = (fun _28_7 _28_9 _28_11 -> (match (((_28_7), (_28_9), (_28_11))) with
| (Doc (l), Doc (r), Doc (x)) -> begin
Doc ((Prims.strcat l (Prims.strcat x r)))
end))


let brackets : doc  ->  doc = (fun _28_13 -> (match (_28_13) with
| Doc (d) -> begin
(enclose (text "[") (text "]") (Doc (d)))
end))


let cbrackets : doc  ->  doc = (fun _28_15 -> (match (_28_15) with
| Doc (d) -> begin
(enclose (text "{") (text "}") (Doc (d)))
end))


let parens : doc  ->  doc = (fun _28_17 -> (match (_28_17) with
| Doc (d) -> begin
(enclose (text "(") (text ")") (Doc (d)))
end))


let cat : doc  ->  doc  ->  doc = (fun _28_19 _28_21 -> (match (((_28_19), (_28_21))) with
| (Doc (d1), Doc (d2)) -> begin
Doc ((Prims.strcat d1 d2))
end))


let reduce : doc Prims.list  ->  doc = (fun docs -> (FStar_List.fold_left cat empty docs))


let group : doc  ->  doc = (fun _28_24 -> (match (_28_24) with
| Doc (d) -> begin
Doc (d)
end))


let groups : doc Prims.list  ->  doc = (fun docs -> (let _125_35 = (reduce docs)
in (group _125_35)))


let combine : doc  ->  doc Prims.list  ->  doc = (fun _28_27 docs -> (match (_28_27) with
| Doc (sep) -> begin
(

let select = (fun _28_31 -> (match (_28_31) with
| Doc (d) -> begin
if (d = "") then begin
None
end else begin
Some (d)
end
end))
in (

let docs = (FStar_List.choose select docs)
in Doc ((FStar_String.concat sep docs))))
end))


let cat1 : doc  ->  doc  ->  doc = (fun d1 d2 -> (reduce ((d1)::(break1)::(d2)::[])))


let reduce1 : doc Prims.list  ->  doc = (fun docs -> (combine break1 docs))


let nest : Prims.int  ->  doc  ->  doc = (fun i _28_38 -> (match (_28_38) with
| Doc (d) -> begin
Doc (d)
end))


let align : doc Prims.list  ->  doc = (fun docs -> (

let _28_41 = (combine hardline docs)
in (match (_28_41) with
| Doc (doc) -> begin
Doc (doc)
end)))


let hbox : doc  ->  doc = (fun d -> d)


let pretty : Prims.int  ->  doc  ->  Prims.string = (fun sz _28_45 -> (match (_28_45) with
| Doc (doc) -> begin
doc
end))




