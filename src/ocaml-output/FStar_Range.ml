
open Prims
open FStar_Pervasives

type file_name =
Prims.string

type pos =
{line : Prims.int; col : Prims.int}


let __proj__Mkpos__item__line : pos  ->  Prims.int = (fun projectee -> (match (projectee) with
| {line = __fname__line; col = __fname__col} -> begin
__fname__line
end))


let __proj__Mkpos__item__col : pos  ->  Prims.int = (fun projectee -> (match (projectee) with
| {line = __fname__line; col = __fname__col} -> begin
__fname__col
end))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun i j -> (match ((i < j)) with
| true -> begin
j
end
| uu____29 -> begin
i
end))


let pos_geq : pos  ->  pos  ->  Prims.bool = (fun p1 p2 -> ((p1.line >= p2.line) || ((Prims.op_Equality p1.line p2.line) && (p1.col >= p2.col))))

type rng =
{file_name : file_name; start_pos : pos; end_pos : pos}


let __proj__Mkrng__item__file_name : rng  ->  file_name = (fun projectee -> (match (projectee) with
| {file_name = __fname__file_name; start_pos = __fname__start_pos; end_pos = __fname__end_pos} -> begin
__fname__file_name
end))


let __proj__Mkrng__item__start_pos : rng  ->  pos = (fun projectee -> (match (projectee) with
| {file_name = __fname__file_name; start_pos = __fname__start_pos; end_pos = __fname__end_pos} -> begin
__fname__start_pos
end))


let __proj__Mkrng__item__end_pos : rng  ->  pos = (fun projectee -> (match (projectee) with
| {file_name = __fname__file_name; start_pos = __fname__start_pos; end_pos = __fname__end_pos} -> begin
__fname__end_pos
end))

type range =
{def_range : rng; use_range : rng}


let __proj__Mkrange__item__def_range : range  ->  rng = (fun projectee -> (match (projectee) with
| {def_range = __fname__def_range; use_range = __fname__use_range} -> begin
__fname__def_range
end))


let __proj__Mkrange__item__use_range : range  ->  rng = (fun projectee -> (match (projectee) with
| {def_range = __fname__def_range; use_range = __fname__use_range} -> begin
__fname__use_range
end))


let dummy_pos : pos = {line = (Prims.parse_int "0"); col = (Prims.parse_int "0")}


let dummy_rng : rng = {file_name = "<dummy>"; start_pos = dummy_pos; end_pos = dummy_pos}


let dummyRange : range = {def_range = dummy_rng; use_range = dummy_rng}


let use_range : range  ->  rng = (fun r -> r.use_range)


let def_range : range  ->  rng = (fun r -> r.def_range)


let range_of_rng : rng  ->  rng  ->  range = (fun d u -> {def_range = d; use_range = u})


let set_use_range : range  ->  rng  ->  range = (fun r2 use_rng -> (match ((Prims.op_disEquality use_rng dummy_rng)) with
| true -> begin
(

let uu___46_115 = r2
in {def_range = uu___46_115.def_range; use_range = use_rng})
end
| uu____116 -> begin
r2
end))


let set_def_range : range  ->  rng  ->  range = (fun r2 def_rng -> (match ((Prims.op_disEquality def_rng dummy_rng)) with
| true -> begin
(

let uu___47_125 = r2
in {def_range = def_rng; use_range = uu___47_125.use_range})
end
| uu____126 -> begin
r2
end))


let mk_pos : Prims.int  ->  Prims.int  ->  pos = (fun l c -> {line = (max (Prims.parse_int "0") l); col = (max (Prims.parse_int "0") c)})


let mk_rng : file_name  ->  pos  ->  pos  ->  rng = (fun file_name start_pos end_pos -> {file_name = file_name; start_pos = start_pos; end_pos = end_pos})


let mk_range : Prims.string  ->  pos  ->  pos  ->  range = (fun f b e -> (

let r = (mk_rng f b e)
in (range_of_rng r r)))


let union_rng : rng  ->  rng  ->  rng = (fun r1 r2 -> (match ((Prims.op_disEquality r1.file_name r2.file_name)) with
| true -> begin
r2
end
| uu____168 -> begin
(

let start_pos = (match ((pos_geq r1.start_pos r2.start_pos)) with
| true -> begin
r2.start_pos
end
| uu____170 -> begin
r1.start_pos
end)
in (

let end_pos = (match ((pos_geq r1.start_pos r2.start_pos)) with
| true -> begin
r1.start_pos
end
| uu____172 -> begin
r2.start_pos
end)
in (mk_rng r1.file_name start_pos end_pos)))
end))


let union_ranges : range  ->  range  ->  range = (fun r1 r2 -> {def_range = (union_rng r1.def_range r2.def_range); use_range = (union_rng r1.use_range r2.use_range)})


let string_of_pos : pos  ->  Prims.string = (fun pos -> (

let uu____185 = (FStar_Util.string_of_int pos.line)
in (

let uu____186 = (FStar_Util.string_of_int pos.col)
in (FStar_Util.format2 "%s,%s" uu____185 uu____186))))


let string_of_rng : rng  ->  Prims.string = (fun r -> (

let uu____191 = (string_of_pos r.start_pos)
in (

let uu____192 = (string_of_pos r.end_pos)
in (FStar_Util.format3 "%s(%s-%s)" r.file_name uu____191 uu____192))))


let string_of_def_range : range  ->  Prims.string = (fun r -> (string_of_rng r.def_range))


let string_of_use_range : range  ->  Prims.string = (fun r -> (string_of_rng r.use_range))


let string_of_range : range  ->  Prims.string = (fun r -> (string_of_def_range r))


let file_of_range : range  ->  Prims.string = (fun r -> r.def_range.file_name)


let start_of_range : range  ->  pos = (fun r -> r.def_range.start_pos)


let end_of_range : range  ->  pos = (fun r -> r.def_range.end_pos)


let file_of_use_range : range  ->  Prims.string = (fun r -> r.use_range.file_name)


let start_of_use_range : range  ->  pos = (fun r -> r.use_range.start_pos)


let end_of_use_range : range  ->  pos = (fun r -> r.use_range.end_pos)


let line_of_pos : pos  ->  Prims.int = (fun p -> p.line)


let col_of_pos : pos  ->  Prims.int = (fun p -> p.col)


let end_range : range  ->  range = (fun r -> (mk_range r.def_range.file_name r.def_range.end_pos r.def_range.end_pos))


let compare_rng : rng  ->  rng  ->  Prims.int = (fun r1 r2 -> (

let fcomp = (FStar_String.compare r1.file_name r2.file_name)
in (match ((Prims.op_Equality fcomp (Prims.parse_int "0"))) with
| true -> begin
(

let start1 = r1.start_pos
in (

let start2 = r2.start_pos
in (

let lcomp = (start1.line - start2.line)
in (match ((Prims.op_Equality lcomp (Prims.parse_int "0"))) with
| true -> begin
(start1.col - start2.col)
end
| uu____253 -> begin
lcomp
end))))
end
| uu____254 -> begin
fcomp
end)))


let compare : range  ->  range  ->  Prims.int = (fun r1 r2 -> (compare_rng r1.def_range r2.def_range))


let compare_use_range : range  ->  range  ->  Prims.int = (fun r1 r2 -> (compare_rng r1.use_range r2.use_range))


let range_before_pos : range  ->  pos  ->  Prims.bool = (fun m1 p -> (

let uu____279 = (end_of_range m1)
in (pos_geq p uu____279)))


let end_of_line : pos  ->  pos = (fun p -> (

let uu___48_284 = p
in {line = uu___48_284.line; col = FStar_Util.max_int}))


let extend_to_end_of_line : range  ->  range = (fun r -> (

let uu____289 = (file_of_range r)
in (

let uu____290 = (start_of_range r)
in (

let uu____291 = (

let uu____292 = (end_of_range r)
in (end_of_line uu____292))
in (mk_range uu____289 uu____290 uu____291)))))




