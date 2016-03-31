
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
| Doc (_27_2) -> begin
_27_2
end))


let empty : doc = Doc ("")


let hardline : doc = Doc ("\n")


let text : Prims.string  ->  doc = (fun s -> Doc (s))


let num : Prims.int  ->  doc = (fun i -> Doc ((Prims.string_of_int i)))


let break_ : Prims.int  ->  doc = (fun i -> Doc (""))


let break0 : doc = (break_ 0)


let break1 : doc = (text " ")


let enclose : doc  ->  doc  ->  doc  ->  doc = (fun _27_7 _27_9 _27_11 -> (match ((_27_7, _27_9, _27_11)) with
| (Doc (l), Doc (r), Doc (x)) -> begin
Doc ((Prims.strcat (Prims.strcat l x) r))
end))


let brackets : doc  ->  doc = (fun _27_13 -> (match (_27_13) with
| Doc (d) -> begin
(let _116_22 = (text "[")
in (let _116_21 = (text "]")
in (enclose _116_22 _116_21 (Doc (d)))))
end))


let cbrackets : doc  ->  doc = (fun _27_15 -> (match (_27_15) with
| Doc (d) -> begin
(let _116_26 = (text "{")
in (let _116_25 = (text "}")
in (enclose _116_26 _116_25 (Doc (d)))))
end))


let parens : doc  ->  doc = (fun _27_17 -> (match (_27_17) with
| Doc (d) -> begin
(let _116_30 = (text "(")
in (let _116_29 = (text ")")
in (enclose _116_30 _116_29 (Doc (d)))))
end))


let cat : doc  ->  doc  ->  doc = (fun _27_19 _27_21 -> (match ((_27_19, _27_21)) with
| (Doc (d1), Doc (d2)) -> begin
Doc ((Prims.strcat d1 d2))
end))


let reduce : doc Prims.list  ->  doc = (fun docs -> (FStar_List.fold_left cat empty docs))


let group : doc  ->  doc = (fun _27_24 -> (match (_27_24) with
| Doc (d) -> begin
Doc (d)
end))


let groups : doc Prims.list  ->  doc = (fun docs -> (let _116_41 = (reduce docs)
in (group _116_41)))


let combine : doc  ->  doc Prims.list  ->  doc = (fun _27_27 docs -> (match (_27_27) with
| Doc (sep) -> begin
(

let select = (fun _27_31 -> (match (_27_31) with
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


let nest : Prims.int  ->  doc  ->  doc = (fun i _27_38 -> (match (_27_38) with
| Doc (d) -> begin
Doc (d)
end))


let align : doc Prims.list  ->  doc = (fun docs -> (

let _27_41 = (combine hardline docs)
in (match (_27_41) with
| Doc (doc) -> begin
Doc (doc)
end)))


let hbox : doc  ->  doc = (fun d -> d)


let pretty : Prims.int  ->  doc  ->  Prims.string = (fun sz _27_45 -> (match (_27_45) with
| Doc (doc) -> begin
doc
end))




