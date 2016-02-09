
open Prims
# 8 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

type doc =
| Doc of Prims.string

# 8 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

let is_Doc : doc  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Doc (_) -> begin
true
end
| _ -> begin
false
end))

# 8 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

let ___Doc____0 : doc  ->  Prims.string = (fun projectee -> (match (projectee) with
| Doc (_24_2) -> begin
_24_2
end))

# 11 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

let empty : doc = Doc ("")

# 12 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

let hardline : doc = Doc ("\n")

# 15 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

let text : Prims.string  ->  doc = (fun s -> Doc (s))

# 16 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

let num : Prims.int  ->  doc = (fun i -> Doc ((Prims.string_of_int i)))

# 19 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

let break_ : Prims.int  ->  doc = (fun i -> Doc (""))

# 21 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

let break0 : doc = (break_ 0)

# 22 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

let break1 : doc = (text " ")

# 25 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

let enclose : doc  ->  doc  ->  doc  ->  doc = (fun _24_7 _24_9 _24_11 -> (match ((_24_7, _24_9, _24_11)) with
| (Doc (l), Doc (r), Doc (x)) -> begin
Doc ((Prims.strcat (Prims.strcat l x) r))
end))

# 28 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

let brackets : doc  ->  doc = (fun _24_13 -> (match (_24_13) with
| Doc (d) -> begin
(enclose (text "[") (text "]") (Doc (d)))
end))

# 29 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

let cbrackets : doc  ->  doc = (fun _24_15 -> (match (_24_15) with
| Doc (d) -> begin
(enclose (text "{") (text "}") (Doc (d)))
end))

# 30 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

let parens : doc  ->  doc = (fun _24_17 -> (match (_24_17) with
| Doc (d) -> begin
(enclose (text "(") (text ")") (Doc (d)))
end))

# 33 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

let cat : doc  ->  doc  ->  doc = (fun _24_19 _24_21 -> (match ((_24_19, _24_21)) with
| (Doc (d1), Doc (d2)) -> begin
Doc ((Prims.strcat d1 d2))
end))

# 36 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

let reduce : doc Prims.list  ->  doc = (fun docs -> (FStar_List.fold_left cat empty docs))

# 40 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

let group : doc  ->  doc = (fun _24_24 -> (match (_24_24) with
| Doc (d) -> begin
Doc (d)
end))

# 43 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

let groups : doc Prims.list  ->  doc = (fun docs -> (let _126_35 = (reduce docs)
in (group _126_35)))

# 47 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

let combine : doc  ->  doc Prims.list  ->  doc = (fun _24_27 docs -> (match (_24_27) with
| Doc (sep) -> begin
(let select = (fun _24_31 -> (match (_24_31) with
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

# 53 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

let cat1 : doc  ->  doc  ->  doc = (fun d1 d2 -> (reduce ((d1)::(break1)::(d2)::[])))

# 57 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

let reduce1 : doc Prims.list  ->  doc = (fun docs -> (combine break1 docs))

# 61 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

let nest : Prims.int  ->  doc  ->  doc = (fun i _24_38 -> (match (_24_38) with
| Doc (d) -> begin
Doc (d)
end))

# 65 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

let align : doc Prims.list  ->  doc = (fun docs -> (let _24_41 = (combine hardline docs)
in (match (_24_41) with
| Doc (doc) -> begin
Doc (doc)
end)))

# 70 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

let hbox : doc  ->  doc = (fun d -> d)

# 73 "D:\\workspace\\universes\\FStar\\src\\format\\formatml.fs"

let pretty : Prims.int  ->  doc  ->  Prims.string = (fun sz _24_45 -> (match (_24_45) with
| Doc (doc) -> begin
doc
end))




