
open Prims
open FStar_Pervasives

type file_name =
Prims.string

type pos =
{line : Prims.int; col : Prims.int}


let __proj__Mkpos__item__line : pos  ->  Prims.int = (fun projectee -> (match (projectee) with
| {line = line; col = col} -> begin
line
end))


let __proj__Mkpos__item__col : pos  ->  Prims.int = (fun projectee -> (match (projectee) with
| {line = line; col = col} -> begin
col
end))


let max : Prims.int  ->  Prims.int  ->  Prims.int = (fun i j -> (match ((i < j)) with
| true -> begin
j
end
| uu____35 -> begin
i
end))


let pos_geq : pos  ->  pos  ->  Prims.bool = (fun p1 p2 -> ((p1.line > p2.line) || ((Prims.op_Equality p1.line p2.line) && (p1.col >= p2.col))))

type rng =
{file_name : file_name; start_pos : pos; end_pos : pos}


let __proj__Mkrng__item__file_name : rng  ->  file_name = (fun projectee -> (match (projectee) with
| {file_name = file_name; start_pos = start_pos; end_pos = end_pos} -> begin
file_name
end))


let __proj__Mkrng__item__start_pos : rng  ->  pos = (fun projectee -> (match (projectee) with
| {file_name = file_name; start_pos = start_pos; end_pos = end_pos} -> begin
start_pos
end))


let __proj__Mkrng__item__end_pos : rng  ->  pos = (fun projectee -> (match (projectee) with
| {file_name = file_name; start_pos = start_pos; end_pos = end_pos} -> begin
end_pos
end))

type range =
{def_range : rng; use_range : rng}


let __proj__Mkrange__item__def_range : range  ->  rng = (fun projectee -> (match (projectee) with
| {def_range = def_range; use_range = use_range} -> begin
def_range
end))


let __proj__Mkrange__item__use_range : range  ->  rng = (fun projectee -> (match (projectee) with
| {def_range = def_range; use_range = use_range} -> begin
use_range
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

let uu___80_139 = r2
in {def_range = uu___80_139.def_range; use_range = use_rng})
end
| uu____140 -> begin
r2
end))


let set_def_range : range  ->  rng  ->  range = (fun r2 def_rng -> (match ((Prims.op_disEquality def_rng dummy_rng)) with
| true -> begin
(

let uu___81_151 = r2
in {def_range = def_rng; use_range = uu___81_151.use_range})
end
| uu____152 -> begin
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
| uu____204 -> begin
(

let start_pos = (match ((pos_geq r1.start_pos r2.start_pos)) with
| true -> begin
r2.start_pos
end
| uu____206 -> begin
r1.start_pos
end)
in (

let end_pos = (match ((pos_geq r1.end_pos r2.end_pos)) with
| true -> begin
r1.end_pos
end
| uu____208 -> begin
r2.end_pos
end)
in (mk_rng r1.file_name start_pos end_pos)))
end))


let union_ranges : range  ->  range  ->  range = (fun r1 r2 -> {def_range = (union_rng r1.def_range r2.def_range); use_range = (union_rng r1.use_range r2.use_range)})


let rng_included : rng  ->  rng  ->  Prims.bool = (fun r1 r2 -> (match ((Prims.op_disEquality r1.file_name r2.file_name)) with
| true -> begin
false
end
| uu____229 -> begin
((pos_geq r1.start_pos r2.start_pos) && (pos_geq r2.end_pos r1.end_pos))
end))


let string_of_pos : pos  ->  Prims.string = (fun pos -> (

let uu____235 = (FStar_Util.string_of_int pos.line)
in (

let uu____236 = (FStar_Util.string_of_int pos.col)
in (FStar_Util.format2 "%s,%s" uu____235 uu____236))))


let string_of_file_name : Prims.string  ->  Prims.string = (fun f -> (

let uu____242 = (FStar_Options.ide ())
in (match (uu____242) with
| true -> begin
(FStar_All.try_with (fun uu___83_245 -> (match (()) with
| () -> begin
(

let uu____246 = (

let uu____249 = (FStar_Util.basename f)
in (FStar_Options.find_file uu____249))
in (match (uu____246) with
| FStar_Pervasives_Native.None -> begin
f
end
| FStar_Pervasives_Native.Some (absolute_path) -> begin
absolute_path
end))
end)) (fun uu___82_252 -> f))
end
| uu____253 -> begin
f
end)))


let file_of_range : range  ->  Prims.string = (fun r -> (

let f = r.def_range.file_name
in (string_of_file_name f)))


let set_file_of_range : range  ->  Prims.string  ->  range = (fun r f -> (

let uu___84_270 = r
in {def_range = (

let uu___85_273 = r.def_range
in {file_name = f; start_pos = uu___85_273.start_pos; end_pos = uu___85_273.end_pos}); use_range = uu___84_270.use_range}))


let string_of_rng : rng  ->  Prims.string = (fun r -> (

let uu____279 = (string_of_file_name r.file_name)
in (

let uu____280 = (string_of_pos r.start_pos)
in (

let uu____281 = (string_of_pos r.end_pos)
in (FStar_Util.format3 "%s(%s-%s)" uu____279 uu____280 uu____281)))))


let string_of_def_range : range  ->  Prims.string = (fun r -> (string_of_rng r.def_range))


let string_of_use_range : range  ->  Prims.string = (fun r -> (string_of_rng r.use_range))


let string_of_range : range  ->  Prims.string = (fun r -> (string_of_def_range r))


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
| uu____351 -> begin
lcomp
end))))
end
| uu____352 -> begin
fcomp
end)))


let compare : range  ->  range  ->  Prims.int = (fun r1 r2 -> (compare_rng r1.def_range r2.def_range))


let compare_use_range : range  ->  range  ->  Prims.int = (fun r1 r2 -> (compare_rng r1.use_range r2.use_range))


let range_before_pos : range  ->  pos  ->  Prims.bool = (fun m1 p -> (

let uu____383 = (end_of_range m1)
in (pos_geq p uu____383)))


let end_of_line : pos  ->  pos = (fun p -> (

let uu___86_389 = p
in {line = uu___86_389.line; col = FStar_Util.max_int}))


let extend_to_end_of_line : range  ->  range = (fun r -> (

let uu____395 = (file_of_range r)
in (

let uu____396 = (start_of_range r)
in (

let uu____397 = (

let uu____398 = (end_of_range r)
in (end_of_line uu____398))
in (mk_range uu____395 uu____396 uu____397)))))


let prims_to_fstar_range : ((Prims.string * (Prims.int * Prims.int) * (Prims.int * Prims.int)) * (Prims.string * (Prims.int * Prims.int) * (Prims.int * Prims.int)))  ->  range = (fun r -> (

let uu____468 = r
in (match (uu____468) with
| (r1, r2) -> begin
(

let uu____559 = r1
in (match (uu____559) with
| (f1, s1, e1) -> begin
(

let uu____593 = r2
in (match (uu____593) with
| (f2, s2, e2) -> begin
(

let s11 = (mk_pos (FStar_Pervasives_Native.fst s1) (FStar_Pervasives_Native.snd s1))
in (

let e11 = (mk_pos (FStar_Pervasives_Native.fst e1) (FStar_Pervasives_Native.snd e1))
in (

let s21 = (mk_pos (FStar_Pervasives_Native.fst s2) (FStar_Pervasives_Native.snd s2))
in (

let e21 = (mk_pos (FStar_Pervasives_Native.fst e2) (FStar_Pervasives_Native.snd e2))
in (

let r11 = (mk_rng f1 s11 e11)
in (

let r21 = (mk_rng f2 s21 e21)
in {def_range = r11; use_range = r21}))))))
end))
end))
end)))


let json_of_pos : pos  ->  FStar_Util.json = (fun pos -> (

let uu____638 = (

let uu____641 = (

let uu____642 = (line_of_pos pos)
in FStar_Util.JsonInt (uu____642))
in (

let uu____643 = (

let uu____646 = (

let uu____647 = (col_of_pos pos)
in FStar_Util.JsonInt (uu____647))
in (uu____646)::[])
in (uu____641)::uu____643))
in FStar_Util.JsonList (uu____638)))


let json_of_range_fields : Prims.string  ->  pos  ->  pos  ->  FStar_Util.json = (fun file b e -> (

let uu____663 = (

let uu____670 = (

let uu____677 = (

let uu____682 = (json_of_pos b)
in (("beg"), (uu____682)))
in (

let uu____683 = (

let uu____690 = (

let uu____695 = (json_of_pos e)
in (("end"), (uu____695)))
in (uu____690)::[])
in (uu____677)::uu____683))
in ((("fname"), (FStar_Util.JsonStr (file))))::uu____670)
in FStar_Util.JsonAssoc (uu____663)))


let json_of_use_range : range  ->  FStar_Util.json = (fun r -> (

let uu____717 = (file_of_use_range r)
in (

let uu____718 = (start_of_use_range r)
in (

let uu____719 = (end_of_use_range r)
in (json_of_range_fields uu____717 uu____718 uu____719)))))


let json_of_def_range : range  ->  FStar_Util.json = (fun r -> (

let uu____725 = (file_of_range r)
in (

let uu____726 = (start_of_range r)
in (

let uu____727 = (end_of_range r)
in (json_of_range_fields uu____725 uu____726 uu____727)))))




