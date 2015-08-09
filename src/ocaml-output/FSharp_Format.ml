
type doc =
| Doc of string

let is_Doc = (fun ( _discr_ ) -> (match (_discr_) with
| Doc (_) -> begin
true
end
| _ -> begin
false
end))

let ___Doc____0 = (fun ( projectee ) -> (match (projectee) with
| Doc (_54_2) -> begin
_54_2
end))

let empty = Doc ("")

let hardline = Doc ("\n")

let text = (fun ( s ) -> Doc (s))

let break_ = (fun ( i ) -> Doc (""))

let break0 = (break_ 0)

let break1 = (text " ")

let enclose = (fun ( _54_6 ) ( _54_8 ) ( _54_10 ) -> (match ((_54_6, _54_8, _54_10)) with
| (Doc (l), Doc (r), Doc (x)) -> begin
Doc ((Support.String.strcat (Support.String.strcat l x) r))
end))

let brackets = (fun ( _54_12 ) -> (match (_54_12) with
| Doc (d) -> begin
(let _70_26323 = (text "[")
in (let _70_26322 = (text "]")
in (enclose _70_26323 _70_26322 (Doc (d)))))
end))

let cbrackets = (fun ( _54_14 ) -> (match (_54_14) with
| Doc (d) -> begin
(let _70_26327 = (text "{")
in (let _70_26326 = (text "}")
in (enclose _70_26327 _70_26326 (Doc (d)))))
end))

let parens = (fun ( _54_16 ) -> (match (_54_16) with
| Doc (d) -> begin
(let _70_26331 = (text "(")
in (let _70_26330 = (text ")")
in (enclose _70_26331 _70_26330 (Doc (d)))))
end))

let cat = (fun ( _54_18 ) ( _54_20 ) -> (match ((_54_18, _54_20)) with
| (Doc (d1), Doc (d2)) -> begin
Doc ((Support.String.strcat d1 d2))
end))

let reduce = (fun ( docs ) -> (Support.List.fold_left cat empty docs))

let group = (fun ( _54_23 ) -> (match (_54_23) with
| Doc (d) -> begin
Doc (d)
end))

let groups = (fun ( docs ) -> (let _70_26342 = (reduce docs)
in (group _70_26342)))

let combine = (fun ( _54_26 ) ( docs ) -> (match (_54_26) with
| Doc (sep) -> begin
(let select = (fun ( _54_30 ) -> (match (_54_30) with
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

let nest = (fun ( i ) ( _54_37 ) -> (match (_54_37) with
| Doc (d) -> begin
Doc (d)
end))

let align = (fun ( docs ) -> (let _54_40 = (combine hardline docs)
in (match (_54_40) with
| Doc (doc) -> begin
Doc (doc)
end)))

let hbox = (fun ( d ) -> d)

let pretty = (fun ( sz ) ( _54_44 ) -> (match (_54_44) with
| Doc (doc) -> begin
doc
end))




