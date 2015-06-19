
type doc =
| Doc of string

let empty = Doc ("")

let hardline = Doc ("\n")

let text = (fun s -> Doc (s))

let break_ = (fun i -> Doc (""))

let break0 = (break_ 0)

let break1 = (text " ")

let enclose = (fun _499262 _499264 _499266 -> (match ((_499262, _499264, _499266)) with
| (Doc (l), Doc (r), Doc (x)) -> begin
Doc ((Support.String.strcat (Support.String.strcat l x) r))
end))

let brackets = (fun _499268 -> (match (_499268) with
| Doc (d) -> begin
(enclose (text "[") (text "]") (Doc (d)))
end))

let cbrackets = (fun _499270 -> (match (_499270) with
| Doc (d) -> begin
(enclose (text "{") (text "}") (Doc (d)))
end))

let parens = (fun _499272 -> (match (_499272) with
| Doc (d) -> begin
(enclose (text "(") (text ")") (Doc (d)))
end))

let cat = (fun _499274 _499276 -> (match ((_499274, _499276)) with
| (Doc (d1), Doc (d2)) -> begin
Doc ((Support.String.strcat d1 d2))
end))

let reduce = (fun docs -> (Support.List.fold_left cat empty docs))

let group = (fun _499279 -> (match (_499279) with
| Doc (d) -> begin
Doc (d)
end))

let groups = (fun docs -> (group (reduce docs)))

let combine = (fun _499282 docs -> (match (_499282) with
| Doc (sep) -> begin
(let select = (fun _499286 -> (match (_499286) with
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

let nest = (fun i _499293 -> (match (_499293) with
| Doc (d) -> begin
Doc (d)
end))

let align = (fun docs -> (let _499296 = (combine hardline docs)
in (match (_499296) with
| Doc (doc) -> begin
Doc (doc)
end)))

let hbox = (fun d -> d)

let pretty = (fun sz _499300 -> (match (_499300) with
| Doc (doc) -> begin
doc
end))




