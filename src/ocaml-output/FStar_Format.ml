
open Prims
# 8 "FStar.Format.fst"
type doc =
| Doc of Prims.string

# 8 "FStar.Format.fst"
let is_Doc = (fun _discr_ -> (match (_discr_) with
| Doc (_) -> begin
true
end
| _ -> begin
false
end))

# 8 "FStar.Format.fst"
let ___Doc____0 : doc  ->  Prims.string = (fun projectee -> (match (projectee) with
| Doc (_23_2) -> begin
_23_2
end))

# 34 "FStar.Format.fst"
let empty : doc = Doc ("")

# 35 "FStar.Format.fst"
let hardline : doc = Doc ("\n")

# 38 "FStar.Format.fst"
let text : Prims.string  ->  doc = (fun s -> Doc (s))

# 39 "FStar.Format.fst"
let num : Prims.int  ->  doc = (fun i -> Doc ((Prims.string_of_int i)))

# 42 "FStar.Format.fst"
let break_ : Prims.int  ->  doc = (fun i -> Doc (""))

# 44 "FStar.Format.fst"
let break0 : doc = (break_ 0)

# 45 "FStar.Format.fst"
let break1 : doc = (text " ")

# 48 "FStar.Format.fst"
let enclose : doc  ->  doc  ->  doc  ->  doc = (fun _23_7 _23_9 _23_11 -> (match ((_23_7, _23_9, _23_11)) with
| (Doc (l), Doc (r), Doc (x)) -> begin
Doc ((Prims.strcat (Prims.strcat l x) r))
end))

# 51 "FStar.Format.fst"
let brackets : doc  ->  doc = (fun _23_13 -> (match (_23_13) with
| Doc (d) -> begin
(let _104_22 = (text "[")
in (let _104_21 = (text "]")
in (enclose _104_22 _104_21 (Doc (d)))))
end))

# 52 "FStar.Format.fst"
let cbrackets : doc  ->  doc = (fun _23_15 -> (match (_23_15) with
| Doc (d) -> begin
(let _104_26 = (text "{")
in (let _104_25 = (text "}")
in (enclose _104_26 _104_25 (Doc (d)))))
end))

# 53 "FStar.Format.fst"
let parens : doc  ->  doc = (fun _23_17 -> (match (_23_17) with
| Doc (d) -> begin
(let _104_30 = (text "(")
in (let _104_29 = (text ")")
in (enclose _104_30 _104_29 (Doc (d)))))
end))

# 56 "FStar.Format.fst"
let cat : doc  ->  doc  ->  doc = (fun _23_19 _23_21 -> (match ((_23_19, _23_21)) with
| (Doc (d1), Doc (d2)) -> begin
Doc ((Prims.strcat d1 d2))
end))

# 59 "FStar.Format.fst"
let reduce : doc Prims.list  ->  doc = (fun docs -> (FStar_List.fold_left cat empty docs))

# 63 "FStar.Format.fst"
let group : doc  ->  doc = (fun _23_24 -> (match (_23_24) with
| Doc (d) -> begin
Doc (d)
end))

# 66 "FStar.Format.fst"
let groups : doc Prims.list  ->  doc = (fun docs -> (let _104_41 = (reduce docs)
in (group _104_41)))

# 70 "FStar.Format.fst"
let combine : doc  ->  doc Prims.list  ->  doc = (fun _23_27 docs -> (match (_23_27) with
| Doc (sep) -> begin
(
# 71 "FStar.Format.fst"
let select = (fun _23_31 -> (match (_23_31) with
| Doc (d) -> begin
if (d = "") then begin
None
end else begin
Some (d)
end
end))
in (
# 72 "FStar.Format.fst"
let docs = (FStar_List.choose select docs)
in Doc ((FStar_String.concat sep docs))))
end))

# 76 "FStar.Format.fst"
let cat1 : doc  ->  doc  ->  doc = (fun d1 d2 -> (reduce ((d1)::(break1)::(d2)::[])))

# 80 "FStar.Format.fst"
let reduce1 : doc Prims.list  ->  doc = (fun docs -> (combine break1 docs))

# 84 "FStar.Format.fst"
let nest : Prims.int  ->  doc  ->  doc = (fun i _23_38 -> (match (_23_38) with
| Doc (d) -> begin
Doc (d)
end))

# 88 "FStar.Format.fst"
let align : doc Prims.list  ->  doc = (fun docs -> (
# 89 "FStar.Format.fst"
let _23_41 = (combine hardline docs)
in (match (_23_41) with
| Doc (doc) -> begin
Doc (doc)
end)))

# 93 "FStar.Format.fst"
let hbox : doc  ->  doc = (fun d -> d)

# 96 "FStar.Format.fst"
let pretty : Prims.int  ->  doc  ->  Prims.string = (fun sz _23_45 -> (match (_23_45) with
| Doc (doc) -> begin
doc
end))




