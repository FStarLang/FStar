
type doc =
| Doc of string

let empty = Doc ("")

let hardline = Doc ("\n")

let text = (fun s -> Doc (s))

let break_ = (fun i -> Doc (""))

let break0 = (break_ 0)

let break1 = (text " ")

let enclose = (fun _493267 _493269 _493271 -> (match ((_493267, _493269, _493271)) with
| (Doc (l), Doc (r), Doc (x)) -> begin
Doc ((Support.String.strcat (Support.String.strcat l x) r))
end))

let brackets = (fun _493273 -> (match (_493273) with
| Doc (d) -> begin
(enclose (text "[") (text "]") (Doc (d)))
end))

let cbrackets = (fun _493275 -> (match (_493275) with
| Doc (d) -> begin
(enclose (text "{") (text "}") (Doc (d)))
end))

let parens = (fun _493277 -> (match (_493277) with
| Doc (d) -> begin
(enclose (text "(") (text ")") (Doc (d)))
end))

let cat = (fun _493279 _493281 -> (match ((_493279, _493281)) with
| (Doc (d1), Doc (d2)) -> begin
Doc ((Support.String.strcat d1 d2))
end))

let reduce = (fun docs -> (Support.List.fold_left cat empty docs))

let group = (fun _493284 -> (match (_493284) with
| Doc (d) -> begin
Doc (d)
end))

let groups = (fun docs -> (group (reduce docs)))

let combine = (fun _493287 docs -> (match (_493287) with
| Doc (sep) -> begin
(let select = (fun _493291 -> (match (_493291) with
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

let nest = (fun i _493298 -> (match (_493298) with
| Doc (d) -> begin
Doc (d)
end))

let align = (fun docs -> (let _493301 = (combine hardline docs)
in (match (_493301) with
| Doc (doc) -> begin
Doc (doc)
end)))

let hbox = (fun d -> d)

let pretty = (fun sz _493305 -> (match (_493305) with
| Doc (doc) -> begin
doc
end))




