
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
| uu____62 -> begin
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

let uu___35_192 = r2
in {def_range = uu___35_192.def_range; use_range = use_rng})
end
| uu____193 -> begin
r2
end))


let set_def_range : range  ->  rng  ->  range = (fun r2 def_rng -> (match ((Prims.op_disEquality def_rng dummy_rng)) with
| true -> begin
(

let uu___40_207 = r2
in {def_range = def_rng; use_range = uu___40_207.use_range})
end
| uu____208 -> begin
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
| uu____277 -> begin
(

let start_pos = (match ((pos_geq r1.start_pos r2.start_pos)) with
| true -> begin
r2.start_pos
end
| uu____281 -> begin
r1.start_pos
end)
in (

let end_pos = (match ((pos_geq r1.end_pos r2.end_pos)) with
| true -> begin
r1.end_pos
end
| uu____285 -> begin
r2.end_pos
end)
in (mk_rng r1.file_name start_pos end_pos)))
end))


let union_ranges : range  ->  range  ->  range = (fun r1 r2 -> {def_range = (union_rng r1.def_range r2.def_range); use_range = (union_rng r1.use_range r2.use_range)})


let rng_included : rng  ->  rng  ->  Prims.bool = (fun r1 r2 -> (match ((Prims.op_disEquality r1.file_name r2.file_name)) with
| true -> begin
false
end
| uu____314 -> begin
((pos_geq r1.start_pos r2.start_pos) && (pos_geq r2.end_pos r1.end_pos))
end))


let string_of_pos : pos  ->  Prims.string = (fun pos -> (

let uu____323 = (FStar_Util.string_of_int pos.line)
in (

let uu____325 = (FStar_Util.string_of_int pos.col)
in (FStar_Util.format2 "%s,%s" uu____323 uu____325))))


let string_of_file_name : Prims.string  ->  Prims.string = (fun f -> (

let uu____337 = (FStar_Options.ide ())
in (match (uu____337) with
| true -> begin
(FStar_All.try_with (fun uu___67_344 -> (match (()) with
| () -> begin
(

let uu____346 = (

let uu____350 = (FStar_Util.basename f)
in (FStar_Options.find_file uu____350))
in (match (uu____346) with
| FStar_Pervasives_Native.None -> begin
f
end
| FStar_Pervasives_Native.Some (absolute_path) -> begin
absolute_path
end))
end)) (fun uu___66_358 -> f))
end
| uu____360 -> begin
f
end)))


let file_of_range : range  ->  Prims.string = (fun r -> (

let f = r.def_range.file_name
in (string_of_file_name f)))


let set_file_of_range : range  ->  Prims.string  ->  range = (fun r f -> (

let uu___79_384 = r
in {def_range = (

let uu___81_387 = r.def_range
in {file_name = f; start_pos = uu___81_387.start_pos; end_pos = uu___81_387.end_pos}); use_range = uu___79_384.use_range}))


let string_of_rng : rng  ->  Prims.string = (fun r -> (

let uu____395 = (string_of_file_name r.file_name)
in (

let uu____397 = (string_of_pos r.start_pos)
in (

let uu____399 = (string_of_pos r.end_pos)
in (FStar_Util.format3 "%s(%s-%s)" uu____395 uu____397 uu____399)))))


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
| uu____500 -> begin
lcomp
end))))
end
| uu____502 -> begin
fcomp
end)))


let compare : range  ->  range  ->  Prims.int = (fun r1 r2 -> (compare_rng r1.def_range r2.def_range))


let compare_use_range : range  ->  range  ->  Prims.int = (fun r1 r2 -> (compare_rng r1.use_range r2.use_range))


let range_before_pos : range  ->  pos  ->  Prims.bool = (fun m1 p -> (

let uu____540 = (end_of_range m1)
in (pos_geq p uu____540)))


let end_of_line : pos  ->  pos = (fun p -> (

let uu___110_547 = p
in {line = uu___110_547.line; col = FStar_Util.max_int}))


let extend_to_end_of_line : range  ->  range = (fun r -> (

let uu____554 = (file_of_range r)
in (

let uu____556 = (start_of_range r)
in (

let uu____557 = (

let uu____558 = (end_of_range r)
in (end_of_line uu____558))
in (mk_range uu____554 uu____556 uu____557)))))


let prims_to_fstar_range : ((Prims.string * (Prims.int * Prims.int) * (Prims.int * Prims.int)) * (Prims.string * (Prims.int * Prims.int) * (Prims.int * Prims.int)))  ->  range = (fun r -> (

let uu____649 = r
in (match (uu____649) with
| (r1, r2) -> begin
(

let uu____770 = r1
in (match (uu____770) with
| (f1, s1, e1) -> begin
(

let uu____819 = r2
in (match (uu____819) with
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

let uu____896 = (

let uu____899 = (

let uu____900 = (line_of_pos pos)
in FStar_Util.JsonInt (uu____900))
in (

let uu____902 = (

let uu____905 = (

let uu____906 = (col_of_pos pos)
in FStar_Util.JsonInt (uu____906))
in (uu____905)::[])
in (uu____899)::uu____902))
in FStar_Util.JsonList (uu____896)))


let json_of_range_fields : Prims.string  ->  pos  ->  pos  ->  FStar_Util.json = (fun file b e -> (

let uu____926 = (

let uu____934 = (

let uu____942 = (

let uu____948 = (json_of_pos b)
in (("beg"), (uu____948)))
in (

let uu____951 = (

let uu____959 = (

let uu____965 = (json_of_pos e)
in (("end"), (uu____965)))
in (uu____959)::[])
in (uu____942)::uu____951))
in ((("fname"), (FStar_Util.JsonStr (file))))::uu____934)
in FStar_Util.JsonAssoc (uu____926)))


let json_of_use_range : range  ->  FStar_Util.json = (fun r -> (

let uu____996 = (file_of_use_range r)
in (

let uu____998 = (start_of_use_range r)
in (

let uu____999 = (end_of_use_range r)
in (json_of_range_fields uu____996 uu____998 uu____999)))))


let json_of_def_range : range  ->  FStar_Util.json = (fun r -> (

let uu____1006 = (file_of_range r)
in (

let uu____1008 = (start_of_range r)
in (

let uu____1009 = (end_of_range r)
in (json_of_range_fields uu____1006 uu____1008 uu____1009)))))




