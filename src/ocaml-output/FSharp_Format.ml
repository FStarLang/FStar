
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

let enclose = (fun ( _54_5 ) ( _54_7 ) ( _54_9 ) -> (match ((_54_5, _54_7, _54_9)) with
| (Doc (l), Doc (r), Doc (x)) -> begin
Doc ((Support.String.strcat (Support.String.strcat l x) r))
end))

let brackets = (fun ( _54_11 ) -> (match (_54_11) with
| Doc (d) -> begin
(let _70_23787 = (text "[")
in (let _70_23786 = (text "]")
in (enclose _70_23787 _70_23786 (Doc (d)))))
end))

let cbrackets = (fun ( _54_13 ) -> (match (_54_13) with
| Doc (d) -> begin
(let _70_23791 = (text "{")
in (let _70_23790 = (text "}")
in (enclose _70_23791 _70_23790 (Doc (d)))))
end))

let parens = (fun ( _54_15 ) -> (match (_54_15) with
| Doc (d) -> begin
(let _70_23795 = (text "(")
in (let _70_23794 = (text ")")
in (enclose _70_23795 _70_23794 (Doc (d)))))
end))

let cat = (fun ( _54_17 ) ( _54_19 ) -> (match ((_54_17, _54_19)) with
| (Doc (d1), Doc (d2)) -> begin
Doc ((Support.String.strcat d1 d2))
end))

let reduce = (fun ( docs ) -> (Support.List.fold_left cat empty docs))

let group = (fun ( _54_22 ) -> (match (_54_22) with
| Doc (d) -> begin
Doc (d)
end))

let groups = (fun ( docs ) -> (let _70_23806 = (reduce docs)
in (group _70_23806)))

let combine = (fun ( _54_25 ) ( docs ) -> (match (_54_25) with
| Doc (sep) -> begin
(let select = (fun ( _54_29 ) -> (match (_54_29) with
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

let nest = (fun ( i ) ( _54_36 ) -> (match (_54_36) with
| Doc (d) -> begin
Doc (d)
end))

let align = (fun ( docs ) -> (let _54_39 = (combine hardline docs)
in (match (_54_39) with
| Doc (doc) -> begin
Doc (doc)
end)))

let hbox = (fun ( d ) -> d)

let pretty = (fun ( sz ) ( _54_43 ) -> (match (_54_43) with
| Doc (doc) -> begin
doc
end))




