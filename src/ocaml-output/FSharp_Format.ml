
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
| Doc (_55_2) -> begin
_55_2
end))

let empty = Doc ("")

let hardline = Doc ("\n")

let text = (fun s -> Doc (s))

let break_ = (fun i -> Doc (""))

let break0 = (break_ 0)

let break1 = (text " ")

let enclose = (fun _55_6 _55_8 _55_10 -> (match ((_55_6, _55_8, _55_10)) with
| (Doc (l), Doc (r), Doc (x)) -> begin
Doc ((Prims.strcat (Prims.strcat l x) r))
end))

let brackets = (fun _55_12 -> (match (_55_12) with
| Doc (d) -> begin
(let _120_20 = (text "[")
in (let _120_19 = (text "]")
in (enclose _120_20 _120_19 (Doc (d)))))
end))

let cbrackets = (fun _55_14 -> (match (_55_14) with
| Doc (d) -> begin
(let _120_24 = (text "{")
in (let _120_23 = (text "}")
in (enclose _120_24 _120_23 (Doc (d)))))
end))

let parens = (fun _55_16 -> (match (_55_16) with
| Doc (d) -> begin
(let _120_28 = (text "(")
in (let _120_27 = (text ")")
in (enclose _120_28 _120_27 (Doc (d)))))
end))

let cat = (fun _55_18 _55_20 -> (match ((_55_18, _55_20)) with
| (Doc (d1), Doc (d2)) -> begin
Doc ((Prims.strcat d1 d2))
end))

let reduce = (fun docs -> (FStar_List.fold_left cat empty docs))

let group = (fun _55_23 -> (match (_55_23) with
| Doc (d) -> begin
Doc (d)
end))

let groups = (fun docs -> (let _120_39 = (reduce docs)
in (group _120_39)))

let combine = (fun _55_26 docs -> (match (_55_26) with
| Doc (sep) -> begin
(let select = (fun _55_30 -> (match (_55_30) with
| Doc (d) -> begin
(match ((d = "")) with
| true -> begin
None
end
| false -> begin
Some (d)
end)
end))
in (let docs = (FStar_List.choose select docs)
in Doc ((FStar_String.concat sep docs))))
end))

let cat1 = (fun d1 d2 -> (reduce ((d1)::(break1)::(d2)::[])))

let reduce1 = (fun docs -> (combine break1 docs))

let nest = (fun i _55_37 -> (match (_55_37) with
| Doc (d) -> begin
Doc (d)
end))

let align = (fun docs -> (let _55_40 = (combine hardline docs)
in (match (_55_40) with
| Doc (doc) -> begin
Doc (doc)
end)))

let hbox = (fun d -> d)

let pretty = (fun sz _55_44 -> (match (_55_44) with
| Doc (doc) -> begin
doc
end))
