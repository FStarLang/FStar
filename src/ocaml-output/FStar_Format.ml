
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
| Doc (_29_2) -> begin
_29_2
end))


let empty : doc = Doc ("")


let hardline : doc = Doc ("\n")


let text : Prims.string  ->  doc = (fun s -> Doc (s))


let num : Prims.int  ->  doc = (fun i -> Doc ((Prims.string_of_int i)))


let break_ : Prims.int  ->  doc = (fun i -> Doc (""))


let break0 : doc = (break_ (Prims.parse_int "0"))


let break1 : doc = (text " ")


let enclose : doc  ->  doc  ->  doc  ->  doc = (fun _29_7 _29_9 _29_11 -> (match (((_29_7), (_29_9), (_29_11))) with
| (Doc (l), Doc (r), Doc (x)) -> begin
Doc ((Prims.strcat l (Prims.strcat x r)))
end))


let brackets : doc  ->  doc = (fun _29_13 -> (match (_29_13) with
| Doc (d) -> begin
(enclose (text "[") (text "]") (Doc (d)))
end))


let cbrackets : doc  ->  doc = (fun _29_15 -> (match (_29_15) with
| Doc (d) -> begin
(enclose (text "{") (text "}") (Doc (d)))
end))


let parens : doc  ->  doc = (fun _29_17 -> (match (_29_17) with
| Doc (d) -> begin
(enclose (text "(") (text ")") (Doc (d)))
end))


let cat : doc  ->  doc  ->  doc = (fun _29_19 _29_21 -> (match (((_29_19), (_29_21))) with
| (Doc (d1), Doc (d2)) -> begin
Doc ((Prims.strcat d1 d2))
end))


let reduce : doc Prims.list  ->  doc = (fun docs -> (FStar_List.fold_left cat empty docs))


let group : doc  ->  doc = (fun _29_24 -> (match (_29_24) with
| Doc (d) -> begin
Doc (d)
end))


let groups : doc Prims.list  ->  doc = (fun docs -> (let _130_35 = (reduce docs)
in (group _130_35)))


let combine : doc  ->  doc Prims.list  ->  doc = (fun _29_27 docs -> (match (_29_27) with
| Doc (sep) -> begin
(

let select = (fun _29_31 -> (match (_29_31) with
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


let nest : Prims.int  ->  doc  ->  doc = (fun i _29_38 -> (match (_29_38) with
| Doc (d) -> begin
Doc (d)
end))


let align : doc Prims.list  ->  doc = (fun docs -> (

let _29_41 = (combine hardline docs)
in (match (_29_41) with
| Doc (doc) -> begin
Doc (doc)
end)))


let hbox : doc  ->  doc = (fun d -> d)


let pretty : Prims.int  ->  doc  ->  Prims.string = (fun sz _29_45 -> (match (_29_45) with
| Doc (doc) -> begin
doc
end))




