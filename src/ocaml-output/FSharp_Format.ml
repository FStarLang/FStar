
type doc =
| Doc of string

let empty = Doc ("")

let hardline = Doc ("\n")

let text = (fun s -> Doc (s))

let break_ = (fun i -> Doc (""))

let break0 = (break_ 0)

let break1 = (text " ")

let enclose = (fun _497171 _497173 _497175 -> (match ((_497171, _497173, _497175)) with
| (Doc (l), Doc (r), Doc (x)) -> begin
Doc ((Support.String.strcat (Support.String.strcat l x) r))
end))

let brackets = (fun _497177 -> (match (_497177) with
| Doc (d) -> begin
(enclose (text "[") (text "]") (Doc (d)))
end))

let cbrackets = (fun _497179 -> (match (_497179) with
| Doc (d) -> begin
(enclose (text "{") (text "}") (Doc (d)))
end))

let parens = (fun _497181 -> (match (_497181) with
| Doc (d) -> begin
(enclose (text "(") (text ")") (Doc (d)))
end))

let cat = (fun _497183 _497185 -> (match ((_497183, _497185)) with
| (Doc (d1), Doc (d2)) -> begin
Doc ((Support.String.strcat d1 d2))
end))

let reduce = (fun docs -> (Support.List.fold_left cat empty docs))

let group = (fun _497188 -> (match (_497188) with
| Doc (d) -> begin
Doc (d)
end))

let groups = (fun docs -> (group (reduce docs)))

let combine = (fun _497191 docs -> (match (_497191) with
| Doc (sep) -> begin
(let select = (fun _497195 -> (match (_497195) with
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

let nest = (fun i _497202 -> (match (_497202) with
| Doc (d) -> begin
Doc (d)
end))

let align = (fun docs -> (let _497205 = (combine hardline docs)
in (match (_497205) with
| Doc (doc) -> begin
Doc (doc)
end)))

let hbox = (fun d -> d)

let pretty = (fun sz _497209 -> (match (_497209) with
| Doc (doc) -> begin
doc
end))




