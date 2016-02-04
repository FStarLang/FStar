
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
| Doc (_25_2) -> begin
_25_2
end))

let empty : doc = Doc ("")

let hardline : doc = Doc ("\n")

let text : Prims.string  ->  doc = (fun s -> Doc (s))

let break_ : Prims.int  ->  doc = (fun i -> Doc (""))

let break0 : doc = (break_ 0)

let break1 : doc = (text " ")

let enclose : doc  ->  doc  ->  doc  ->  doc = (fun _25_6 _25_8 _25_10 -> (match ((_25_6, _25_8, _25_10)) with
| (Doc (l), Doc (r), Doc (x)) -> begin
Doc ((Prims.strcat (Prims.strcat l x) r))
end))

let brackets : doc  ->  doc = (fun _25_12 -> (match (_25_12) with
| Doc (d) -> begin
(let _128_20 = (text "[")
in (let _128_19 = (text "]")
in (enclose _128_20 _128_19 (Doc (d)))))
end))

let cbrackets : doc  ->  doc = (fun _25_14 -> (match (_25_14) with
| Doc (d) -> begin
(let _128_24 = (text "{")
in (let _128_23 = (text "}")
in (enclose _128_24 _128_23 (Doc (d)))))
end))

let parens : doc  ->  doc = (fun _25_16 -> (match (_25_16) with
| Doc (d) -> begin
(let _128_28 = (text "(")
in (let _128_27 = (text ")")
in (enclose _128_28 _128_27 (Doc (d)))))
end))

let cat : doc  ->  doc  ->  doc = (fun _25_18 _25_20 -> (match ((_25_18, _25_20)) with
| (Doc (d1), Doc (d2)) -> begin
Doc ((Prims.strcat d1 d2))
end))

let reduce : doc Prims.list  ->  doc = (fun docs -> (FStar_List.fold_left cat empty docs))

let group : doc  ->  doc = (fun _25_23 -> (match (_25_23) with
| Doc (d) -> begin
Doc (d)
end))

let groups : doc Prims.list  ->  doc = (fun docs -> (let _128_39 = (reduce docs)
in (group _128_39)))

let combine : doc  ->  doc Prims.list  ->  doc = (fun _25_26 docs -> (match (_25_26) with
| Doc (sep) -> begin
(let select = (fun _25_30 -> (match (_25_30) with
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

let nest : Prims.int  ->  doc  ->  doc = (fun i _25_37 -> (match (_25_37) with
| Doc (d) -> begin
Doc (d)
end))

let align : doc Prims.list  ->  doc = (fun docs -> (let _25_40 = (combine hardline docs)
in (match (_25_40) with
| Doc (doc) -> begin
Doc (doc)
end)))

let hbox : doc  ->  doc = (fun d -> d)

let pretty : Prims.int  ->  doc  ->  Prims.string = (fun sz _25_44 -> (match (_25_44) with
| Doc (doc) -> begin
doc
end))




