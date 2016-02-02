
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
| Doc (_25_2) -> begin
_25_2
end))

let empty = Doc ("")

let hardline = Doc ("\n")

let text = (fun s -> Doc (s))

let break_ = (fun i -> Doc (""))

let break0 = (break_ 0)

let break1 = (text " ")

let enclose = (fun _25_6 _25_8 _25_10 -> (match ((_25_6, _25_8, _25_10)) with
| (Doc (l), Doc (r), Doc (x)) -> begin
Doc ((Prims.strcat (Prims.strcat l x) r))
end))

let brackets = (fun _25_12 -> (match (_25_12) with
| Doc (d) -> begin
(let _102_20 = (text "[")
in (let _102_19 = (text "]")
in (enclose _102_20 _102_19 (Doc (d)))))
end))

let cbrackets = (fun _25_14 -> (match (_25_14) with
| Doc (d) -> begin
(let _102_24 = (text "{")
in (let _102_23 = (text "}")
in (enclose _102_24 _102_23 (Doc (d)))))
end))

let parens = (fun _25_16 -> (match (_25_16) with
| Doc (d) -> begin
(let _102_28 = (text "(")
in (let _102_27 = (text ")")
in (enclose _102_28 _102_27 (Doc (d)))))
end))

let cat = (fun _25_18 _25_20 -> (match ((_25_18, _25_20)) with
| (Doc (d1), Doc (d2)) -> begin
Doc ((Prims.strcat d1 d2))
end))

let reduce = (fun docs -> (FStar_List.fold_left cat empty docs))

let group = (fun _25_23 -> (match (_25_23) with
| Doc (d) -> begin
Doc (d)
end))

let groups = (fun docs -> (let _102_39 = (reduce docs)
in (group _102_39)))

let combine = (fun _25_26 docs -> (match (_25_26) with
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

let cat1 = (fun d1 d2 -> (reduce ((d1)::(break1)::(d2)::[])))

let reduce1 = (fun docs -> (combine break1 docs))

let nest = (fun i _25_37 -> (match (_25_37) with
| Doc (d) -> begin
Doc (d)
end))

let align = (fun docs -> (let _25_40 = (combine hardline docs)
in (match (_25_40) with
| Doc (doc) -> begin
Doc (doc)
end)))

let hbox = (fun d -> d)

let pretty = (fun sz _25_44 -> (match (_25_44) with
| Doc (doc) -> begin
doc
end))




