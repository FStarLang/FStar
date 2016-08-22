
open Prims
# 5 "FStar.Format.fst"
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
let ___Doc____0 = (fun projectee -> (match (projectee) with
| Doc (_27_2) -> begin
_27_2
end))

# 8 "FStar.Format.fst"
let empty : doc = Doc ("")

# 13 "FStar.Format.fst"
let hardline : doc = Doc ("\n")

# 14 "FStar.Format.fst"
let text : Prims.string  ->  doc = (fun s -> Doc (s))

# 17 "FStar.Format.fst"
let num : Prims.int  ->  doc = (fun i -> Doc ((Prims.string_of_int i)))

# 18 "FStar.Format.fst"
let break_ : Prims.int  ->  doc = (fun i -> Doc (""))

# 21 "FStar.Format.fst"
let break0 : doc = (break_ 0)

# 23 "FStar.Format.fst"
let break1 : doc = (text " ")

# 24 "FStar.Format.fst"
let enclose : doc  ->  doc  ->  doc  ->  doc = (fun _27_7 _27_9 _27_11 -> (match (((_27_7), (_27_9), (_27_11))) with
| (Doc (l), Doc (r), Doc (x)) -> begin
Doc ((Prims.strcat l (Prims.strcat x r)))
end))

# 28 "FStar.Format.fst"
let brackets : doc  ->  doc = (fun _27_13 -> (match (_27_13) with
| Doc (d) -> begin
(enclose (text "[") (text "]") (Doc (d)))
end))

# 30 "FStar.Format.fst"
let cbrackets : doc  ->  doc = (fun _27_15 -> (match (_27_15) with
| Doc (d) -> begin
(enclose (text "{") (text "}") (Doc (d)))
end))

# 31 "FStar.Format.fst"
let parens : doc  ->  doc = (fun _27_17 -> (match (_27_17) with
| Doc (d) -> begin
(enclose (text "(") (text ")") (Doc (d)))
end))

# 32 "FStar.Format.fst"
let cat : doc  ->  doc  ->  doc = (fun _27_19 _27_21 -> (match (((_27_19), (_27_21))) with
| (Doc (d1), Doc (d2)) -> begin
Doc ((Prims.strcat d1 d2))
end))

# 35 "FStar.Format.fst"
let reduce : doc Prims.list  ->  doc = (fun docs -> (FStar_List.fold_left cat empty docs))

# 39 "FStar.Format.fst"
let group : doc  ->  doc = (fun _27_24 -> (match (_27_24) with
| Doc (d) -> begin
Doc (d)
end))

# 42 "FStar.Format.fst"
let groups : doc Prims.list  ->  doc = (fun docs -> (let _119_35 = (reduce docs)
in (group _119_35)))

# 46 "FStar.Format.fst"
let combine : doc  ->  doc Prims.list  ->  doc = (fun _27_27 docs -> (match (_27_27) with
| Doc (sep) -> begin
(
# 50 "FStar.Format.fst"
let select = (fun _27_31 -> (match (_27_31) with
| Doc (d) -> begin
if (d = "") then begin
None
end else begin
Some (d)
end
end))
in (
# 51 "FStar.Format.fst"
let docs = (FStar_List.choose select docs)
in Doc ((FStar_String.concat sep docs))))
end))

# 52 "FStar.Format.fst"
let cat1 : doc  ->  doc  ->  doc = (fun d1 d2 -> (reduce ((d1)::(break1)::(d2)::[])))

# 56 "FStar.Format.fst"
let reduce1 : doc Prims.list  ->  doc = (fun docs -> (combine break1 docs))

# 60 "FStar.Format.fst"
let nest : Prims.int  ->  doc  ->  doc = (fun i _27_38 -> (match (_27_38) with
| Doc (d) -> begin
Doc (d)
end))

# 64 "FStar.Format.fst"
let align : doc Prims.list  ->  doc = (fun docs -> (
# 68 "FStar.Format.fst"
let _27_41 = (combine hardline docs)
in (match (_27_41) with
| Doc (doc) -> begin
Doc (doc)
end)))

# 69 "FStar.Format.fst"
let hbox : doc  ->  doc = (fun d -> d)

# 72 "FStar.Format.fst"
let pretty : Prims.int  ->  doc  ->  Prims.string = (fun sz _27_45 -> (match (_27_45) with
| Doc (doc) -> begin
doc
end))




