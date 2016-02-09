
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

let num : Prims.int  ->  doc = (fun i -> Doc ((Prims.string_of_int i)))

let break_ : Prims.int  ->  doc = (fun i -> Doc (""))

let break0 : doc = (break_ 0)

let break1 : doc = (text " ")

let enclose : doc  ->  doc  ->  doc  ->  doc = (fun _24_7 _24_9 _24_11 -> (match ((_24_7, _24_9, _24_11)) with
| (Doc (l), Doc (r), Doc (x)) -> begin
Doc ((Prims.strcat (Prims.strcat l x) r))
end))

let brackets : doc  ->  doc = (fun _24_13 -> (match (_24_13) with
| Doc (d) -> begin
(let _126_22 = (text "[")
in (let _126_21 = (text "]")
in (enclose _126_22 _126_21 (Doc (d)))))
end))

let cbrackets : doc  ->  doc = (fun _24_15 -> (match (_24_15) with
| Doc (d) -> begin
(let _126_26 = (text "{")
in (let _126_25 = (text "}")
in (enclose _126_26 _126_25 (Doc (d)))))
end))

let parens : doc  ->  doc = (fun _24_17 -> (match (_24_17) with
| Doc (d) -> begin
(let _126_30 = (text "(")
in (let _126_29 = (text ")")
in (enclose _126_30 _126_29 (Doc (d)))))
end))

let cat : doc  ->  doc  ->  doc = (fun _24_19 _24_21 -> (match ((_24_19, _24_21)) with
| (Doc (d1), Doc (d2)) -> begin
Doc ((Prims.strcat d1 d2))
end))

let reduce : doc Prims.list  ->  doc = (fun docs -> (FStar_List.fold_left cat empty docs))

let group : doc  ->  doc = (fun _24_24 -> (match (_24_24) with
| Doc (d) -> begin
Doc (d)
end))

let groups : doc Prims.list  ->  doc = (fun docs -> (let _126_41 = (reduce docs)
in (group _126_41)))

let combine : doc  ->  doc Prims.list  ->  doc = (fun _24_27 docs -> (match (_24_27) with
| Doc (sep) -> begin
(let select = (fun _24_31 -> (match (_24_31) with
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

let nest : Prims.int  ->  doc  ->  doc = (fun i _24_38 -> (match (_24_38) with
| Doc (d) -> begin
Doc (d)
end))

let align : doc Prims.list  ->  doc = (fun docs -> (let _24_41 = (combine hardline docs)
in (match (_24_41) with
| Doc (doc) -> begin
Doc (doc)
end)))

let hbox : doc  ->  doc = (fun d -> d)

let pretty : Prims.int  ->  doc  ->  Prims.string = (fun sz _24_45 -> (match (_24_45) with
| Doc (doc) -> begin
doc
end))




