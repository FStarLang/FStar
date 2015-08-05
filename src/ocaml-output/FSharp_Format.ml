
type doc =
| Doc of string

let is_Doc = (fun ( _discr_ ) -> (match (_discr_) with
| Doc (_) -> begin
true
end
| _ -> begin
false
end))

let empty = Doc ("")

let hardline = Doc ("\n")

let text = (fun ( s ) -> Doc (s))

let break_ = (fun ( i ) -> Doc (""))

let break0 = (break_ 0)

let break1 = (text " ")

let enclose = (fun ( _52_5 ) ( _52_7 ) ( _52_9 ) -> (match ((_52_5, _52_7, _52_9)) with
| (Doc (l), Doc (r), Doc (x)) -> begin
Doc ((Support.String.strcat (Support.String.strcat l x) r))
end))

let brackets = (fun ( _52_11 ) -> (match (_52_11) with
| Doc (d) -> begin
(let _68_23667 = (text "[")
in (let _68_23666 = (text "]")
in (enclose _68_23667 _68_23666 (Doc (d)))))
end))

let cbrackets = (fun ( _52_13 ) -> (match (_52_13) with
| Doc (d) -> begin
(let _68_23671 = (text "{")
in (let _68_23670 = (text "}")
in (enclose _68_23671 _68_23670 (Doc (d)))))
end))

let parens = (fun ( _52_15 ) -> (match (_52_15) with
| Doc (d) -> begin
(let _68_23675 = (text "(")
in (let _68_23674 = (text ")")
in (enclose _68_23675 _68_23674 (Doc (d)))))
end))

let cat = (fun ( _52_17 ) ( _52_19 ) -> (match ((_52_17, _52_19)) with
| (Doc (d1), Doc (d2)) -> begin
Doc ((Support.String.strcat d1 d2))
end))

let reduce = (fun ( docs ) -> (Support.List.fold_left cat empty docs))

let group = (fun ( _52_22 ) -> (match (_52_22) with
| Doc (d) -> begin
Doc (d)
end))

let groups = (fun ( docs ) -> (let _68_23686 = (reduce docs)
in (group _68_23686)))

let combine = (fun ( _52_25 ) ( docs ) -> (match (_52_25) with
| Doc (sep) -> begin
(let select = (fun ( _52_29 ) -> (match (_52_29) with
| Doc (d) -> begin
(match ((d = "")) with
| true -> begin
None
end
| false -> begin
Some (d)
end)
end))
in (let docs = (Support.List.choose select docs)
in Doc ((Support.String.concat sep docs))))
end))

let cat1 = (fun ( d1 ) ( d2 ) -> (reduce ((d1)::(break1)::(d2)::[])))

let reduce1 = (fun ( docs ) -> (combine break1 docs))

let nest = (fun ( i ) ( _52_36 ) -> (match (_52_36) with
| Doc (d) -> begin
Doc (d)
end))

let align = (fun ( docs ) -> (let _52_39 = (combine hardline docs)
in (match (_52_39) with
| Doc (doc) -> begin
Doc (doc)
end)))

let hbox = (fun ( d ) -> d)

let pretty = (fun ( sz ) ( _52_43 ) -> (match (_52_43) with
| Doc (doc) -> begin
doc
end))




