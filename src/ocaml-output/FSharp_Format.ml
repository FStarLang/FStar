
open Prims
type doc =
| Doc of Prims.string

let is_Doc : doc  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Doc (_) -> begin
true
end
| _ -> begin
false
end))

let ___Doc____0 : doc  ->  Prims.string = (fun projectee -> (match (projectee) with
| Doc (_24_2) -> begin
_24_2
end))

let empty : doc = Doc ("")

let hardline : doc = Doc ("\n")

let text : Prims.string  ->  doc = (fun s -> Doc (s))

let break_ : Prims.int  ->  doc = (fun i -> Doc (""))

let break0 : doc = (break_ 0)

let break1 : doc = (text " ")

let enclose : doc  ->  doc  ->  doc  ->  doc = (fun _24_6 _24_8 _24_10 -> (match ((_24_6, _24_8, _24_10)) with
| (Doc (l), Doc (r), Doc (x)) -> begin
Doc ((Prims.strcat (Prims.strcat l x) r))
end))

let brackets : doc  ->  doc = (fun _24_12 -> (match (_24_12) with
| Doc (d) -> begin
(let _126_20 = (text "[")
in (let _126_19 = (text "]")
in (enclose _126_20 _126_19 (Doc (d)))))
end))

let cbrackets : doc  ->  doc = (fun _24_14 -> (match (_24_14) with
| Doc (d) -> begin
(let _126_24 = (text "{")
in (let _126_23 = (text "}")
in (enclose _126_24 _126_23 (Doc (d)))))
end))

let parens : doc  ->  doc = (fun _24_16 -> (match (_24_16) with
| Doc (d) -> begin
(let _126_28 = (text "(")
in (let _126_27 = (text ")")
in (enclose _126_28 _126_27 (Doc (d)))))
end))

let cat : doc  ->  doc  ->  doc = (fun _24_18 _24_20 -> (match ((_24_18, _24_20)) with
| (Doc (d1), Doc (d2)) -> begin
Doc ((Prims.strcat d1 d2))
end))

let reduce : doc Prims.list  ->  doc = (fun docs -> (FStar_List.fold_left cat empty docs))

let group : doc  ->  doc = (fun _24_23 -> (match (_24_23) with
| Doc (d) -> begin
Doc (d)
end))

let groups : doc Prims.list  ->  doc = (fun docs -> (let _126_39 = (reduce docs)
in (group _126_39)))

let combine : doc  ->  doc Prims.list  ->  doc = (fun _24_26 docs -> (match (_24_26) with
| Doc (sep) -> begin
(let select = (fun _24_30 -> (match (_24_30) with
| Doc (d) -> begin
if (d = "") then begin
None
end else begin
Some (d)
end
end))
in (let docs = (FStar_List.choose select docs)
in Doc ((FStar_String.concat sep docs))))
end))

let cat1 : doc  ->  doc  ->  doc = (fun d1 d2 -> (reduce ((d1)::(break1)::(d2)::[])))

let reduce1 : doc Prims.list  ->  doc = (fun docs -> (combine break1 docs))

let nest : Prims.int  ->  doc  ->  doc = (fun i _24_37 -> (match (_24_37) with
| Doc (d) -> begin
Doc (d)
end))

let align : doc Prims.list  ->  doc = (fun docs -> (let _24_40 = (combine hardline docs)
in (match (_24_40) with
| Doc (doc) -> begin
Doc (doc)
end)))

let hbox : doc  ->  doc = (fun d -> d)

let pretty : Prims.int  ->  doc  ->  Prims.string = (fun sz _24_44 -> (match (_24_44) with
| Doc (doc) -> begin
doc
end))




