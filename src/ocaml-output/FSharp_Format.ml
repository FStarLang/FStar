
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
| Doc (_56_2) -> begin
_56_2
end))

let empty = Doc ("")

let hardline = Doc ("\n")

let text = (fun s -> Doc (s))

let break_ = (fun i -> Doc (""))

let break0 = (break_ 0)

let break1 = (text " ")

let enclose = (fun _56_6 _56_8 _56_10 -> (match ((_56_6, _56_8, _56_10)) with
| (Doc (l), Doc (r), Doc (x)) -> begin
Doc ((Prims.strcat (Prims.strcat l x) r))
end))

let brackets = (fun _56_12 -> (match (_56_12) with
| Doc (d) -> begin
(let _122_20 = (text "[")
in (let _122_19 = (text "]")
in (enclose _122_20 _122_19 (Doc (d)))))
end))

let cbrackets = (fun _56_14 -> (match (_56_14) with
| Doc (d) -> begin
(let _122_24 = (text "{")
in (let _122_23 = (text "}")
in (enclose _122_24 _122_23 (Doc (d)))))
end))

let parens = (fun _56_16 -> (match (_56_16) with
| Doc (d) -> begin
(let _122_28 = (text "(")
in (let _122_27 = (text ")")
in (enclose _122_28 _122_27 (Doc (d)))))
end))

let cat = (fun _56_18 _56_20 -> (match ((_56_18, _56_20)) with
| (Doc (d1), Doc (d2)) -> begin
Doc ((Prims.strcat d1 d2))
end))

let reduce = (fun docs -> (FStar_List.fold_left cat empty docs))

let group = (fun _56_23 -> (match (_56_23) with
| Doc (d) -> begin
Doc (d)
end))

let groups = (fun docs -> (let _122_39 = (reduce docs)
in (group _122_39)))

let combine = (fun _56_26 docs -> (match (_56_26) with
| Doc (sep) -> begin
(let select = (fun _56_30 -> (match (_56_30) with
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

let nest = (fun i _56_37 -> (match (_56_37) with
| Doc (d) -> begin
Doc (d)
end))

let align = (fun docs -> (let _56_40 = (combine hardline docs)
in (match (_56_40) with
| Doc (doc) -> begin
Doc (doc)
end)))

let hbox = (fun d -> d)

let pretty = (fun sz _56_44 -> (match (_56_44) with
| Doc (doc) -> begin
doc
end))




