
type doc =
| Doc of string

let empty = Doc ("")

let hardline = Doc ("\n")

let text = (fun s -> Doc (s))

let break_ = (fun i -> Doc (""))

let break0 = (break_ 0)

let break1 = (text " ")

let enclose = (fun _493686 _493688 _493690 -> (match ((_493686, _493688, _493690)) with
| (Doc (l), Doc (r), Doc (x)) -> begin
Doc ((Support.String.strcat (Support.String.strcat l x) r))
end))

let brackets = (fun _493692 -> (match (_493692) with
| Doc (d) -> begin
(enclose (text "[") (text "]") (Doc (d)))
end))

let cbrackets = (fun _493694 -> (match (_493694) with
| Doc (d) -> begin
(enclose (text "{") (text "}") (Doc (d)))
end))

let parens = (fun _493696 -> (match (_493696) with
| Doc (d) -> begin
(enclose (text "(") (text ")") (Doc (d)))
end))

let cat = (fun _493698 _493700 -> (match ((_493698, _493700)) with
| (Doc (d1), Doc (d2)) -> begin
Doc ((Support.String.strcat d1 d2))
end))

let reduce = (fun docs -> (Support.List.fold_left cat empty docs))

let group = (fun _493703 -> (match (_493703) with
| Doc (d) -> begin
Doc (d)
end))

let groups = (fun docs -> (group (reduce docs)))

let combine = (fun _493706 docs -> (match (_493706) with
| Doc (sep) -> begin
(let select = (fun _493710 -> (match (_493710) with
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

let nest = (fun i _493717 -> (match (_493717) with
| Doc (d) -> begin
Doc (d)
end))

let align = (fun docs -> (let _493720 = (combine hardline docs)
in (match (_493720) with
| Doc (doc) -> begin
Doc (doc)
end)))

let hbox = (fun d -> d)

let pretty = (fun sz _493724 -> (match (_493724) with
| Doc (doc) -> begin
doc
end))




