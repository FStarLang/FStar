
type doc =
| Doc of string

let empty = Doc ("")

let hardline = Doc ("\n")

let text = (fun ( s ) -> Doc (s))

let break_ = (fun ( i ) -> Doc (""))

let break0 = (break_ 0)

let break1 = (text " ")

let enclose = (fun ( _47_5 ) ( _47_7 ) ( _47_9 ) -> (match ((_47_5, _47_7, _47_9)) with
| (Doc (l), Doc (r), Doc (x)) -> begin
Doc ((Support.String.strcat (Support.String.strcat l x) r))
end))

let brackets = (fun ( _47_11 ) -> (match (_47_11) with
| Doc (d) -> begin
(enclose (text "[") (text "]") (Doc (d)))
end))

let cbrackets = (fun ( _47_13 ) -> (match (_47_13) with
| Doc (d) -> begin
(enclose (text "{") (text "}") (Doc (d)))
end))

let parens = (fun ( _47_15 ) -> (match (_47_15) with
| Doc (d) -> begin
(enclose (text "(") (text ")") (Doc (d)))
end))

let cat = (fun ( _47_17 ) ( _47_19 ) -> (match ((_47_17, _47_19)) with
| (Doc (d1), Doc (d2)) -> begin
Doc ((Support.String.strcat d1 d2))
end))

let reduce = (fun ( docs ) -> (Support.List.fold_left cat empty docs))

let group = (fun ( _47_22 ) -> (match (_47_22) with
| Doc (d) -> begin
Doc (d)
end))

let groups = (fun ( docs ) -> (group (reduce docs)))

let combine = (fun ( _47_25 ) ( docs ) -> (match (_47_25) with
| Doc (sep) -> begin
(let select = (fun ( _47_29 ) -> (match (_47_29) with
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

let cat1 = (fun ( d1 ) ( d2 ) -> (reduce ((d1)::(break1)::(d2)::[])))

let reduce1 = (fun ( docs ) -> (combine break1 docs))

let nest = (fun ( i ) ( _47_36 ) -> (match (_47_36) with
| Doc (d) -> begin
Doc (d)
end))

let align = (fun ( docs ) -> (let _47_39 = (combine hardline docs)
in (match (_47_39) with
| Doc (doc) -> begin
Doc (doc)
end)))

let hbox = (fun ( d ) -> d)

let pretty = (fun ( sz ) ( _47_43 ) -> (match (_47_43) with
| Doc (doc) -> begin
doc
end))




