
type doc =
| Doc of string

let empty = Doc ("")

let hardline = Doc ("\n")

let text = (fun s -> Doc (s))

let break_ = (fun i -> Doc (""))

let break0 = (break_ 0)

let break1 = (text " ")

let enclose = (fun _493427 _493429 _493431 -> (match ((_493427, _493429, _493431)) with
| (Doc (l), Doc (r), Doc (x)) -> begin
Doc ((Support.String.strcat (Support.String.strcat l x) r))
end))

let brackets = (fun _493433 -> (match (_493433) with
| Doc (d) -> begin
(enclose (text "[") (text "]") (Doc (d)))
end))

let cbrackets = (fun _493435 -> (match (_493435) with
| Doc (d) -> begin
(enclose (text "{") (text "}") (Doc (d)))
end))

let parens = (fun _493437 -> (match (_493437) with
| Doc (d) -> begin
(enclose (text "(") (text ")") (Doc (d)))
end))

let cat = (fun _493439 _493441 -> (match ((_493439, _493441)) with
| (Doc (d1), Doc (d2)) -> begin
Doc ((Support.String.strcat d1 d2))
end))

let reduce = (fun docs -> (Support.List.fold_left cat empty docs))

let group = (fun _493444 -> (match (_493444) with
| Doc (d) -> begin
Doc (d)
end))

let groups = (fun docs -> (group (reduce docs)))

let combine = (fun _493447 docs -> (match (_493447) with
| Doc (sep) -> begin
(let select = (fun _493451 -> (match (_493451) with
| Doc (d) -> begin
if (d = "") then begin
None
end else begin
Some (d)
end
end))
in (let docs = (Support.List.choose select docs)
in Doc ((Support.String.concat sep docs))))
end))

let cat1 = (fun d1 d2 -> (reduce ((d1)::(break1)::(d2)::[])))

let reduce1 = (fun docs -> (combine break1 docs))

let nest = (fun i _493458 -> (match (_493458) with
| Doc (d) -> begin
Doc (d)
end))

let align = (fun docs -> (let _493461 = (combine hardline docs)
in (match (_493461) with
| Doc (doc) -> begin
Doc (doc)
end)))

let hbox = (fun d -> d)

let pretty = (fun sz _493465 -> (match (_493465) with
| Doc (doc) -> begin
doc
end))




