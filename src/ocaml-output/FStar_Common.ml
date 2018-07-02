
open Prims
open FStar_Pervasives

let has_cygpath : Prims.bool = (FStar_All.try_with (fun uu___100_3 -> (match (()) with
| () -> begin
(

let t_out = (FStar_Util.run_process "has_cygpath" "which" (("cygpath")::[]) FStar_Pervasives_Native.None)
in (Prims.op_Equality (FStar_Util.trim_string t_out) "/usr/bin/cygpath"))
end)) (fun uu___99_7 -> (match (uu___99_7) with
| uu____8 -> begin
false
end)))


let try_convert_file_name_to_mixed : Prims.string  ->  Prims.string = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun s -> (match ((has_cygpath && (FStar_Util.starts_with s "/"))) with
| true -> begin
(

let uu____17 = (FStar_Util.smap_try_find cache s)
in (match (uu____17) with
| FStar_Pervasives_Native.Some (s1) -> begin
s1
end
| FStar_Pervasives_Native.None -> begin
(

let label = "try_convert_file_name_to_mixed"
in (

let out = (

let uu____23 = (FStar_Util.run_process label "cygpath" (("-m")::(s)::[]) FStar_Pervasives_Native.None)
in (FStar_All.pipe_right uu____23 FStar_Util.trim_string))
in ((FStar_Util.smap_add cache s out);
out;
)))
end))
end
| uu____25 -> begin
s
end)))


let snapshot : 'a 'b 'c . ('a  ->  'b)  ->  'c Prims.list FStar_ST.ref  ->  'a  ->  (Prims.int * 'b) = (fun push stackref arg -> (FStar_Util.atomically (fun uu____102 -> (

let len = (

let uu____104 = (FStar_ST.op_Bang stackref)
in (FStar_List.length uu____104))
in (

let arg' = (push arg)
in ((len), (arg')))))))


let rollback : 'a 'c . (unit  ->  'a)  ->  'c Prims.list FStar_ST.ref  ->  Prims.int FStar_Pervasives_Native.option  ->  'a = (fun pop stackref depth -> (

let rec aux = (fun n1 -> (match ((n1 <= (Prims.parse_int "0"))) with
| true -> begin
(failwith "Too many pops")
end
| uu____229 -> begin
(match ((Prims.op_Equality n1 (Prims.parse_int "1"))) with
| true -> begin
(pop ())
end
| uu____230 -> begin
((

let uu____232 = (pop ())
in ());
(aux (n1 - (Prims.parse_int "1")));
)
end)
end))
in (

let curdepth = (

let uu____234 = (FStar_ST.op_Bang stackref)
in (FStar_List.length uu____234))
in (

let n1 = (match (depth) with
| FStar_Pervasives_Native.Some (d) -> begin
(curdepth - d)
end
| FStar_Pervasives_Native.None -> begin
(Prims.parse_int "1")
end)
in (FStar_Util.atomically (fun uu____291 -> (aux n1)))))))


let raise_failed_assertion : 'Auu____296 . Prims.string  ->  'Auu____296 = (fun msg -> (

let uu____302 = (FStar_Util.format1 "Assertion failed: %s" msg)
in (failwith uu____302)))


let runtime_assert : Prims.bool  ->  Prims.string  ->  unit = (fun b msg -> (match ((not (b))) with
| true -> begin
(raise_failed_assertion msg)
end
| uu____313 -> begin
()
end))


let string_of_list : 'a . ('a  ->  Prims.string)  ->  'a Prims.list  ->  Prims.string = (fun f l -> (

let uu____340 = (

let uu____341 = (

let uu____342 = (FStar_List.map f l)
in (FStar_String.concat ", " uu____342))
in (Prims.strcat uu____341 "]"))
in (Prims.strcat "[" uu____340)))


type 'a thunk =
(unit  ->  'a, 'a) FStar_Util.either FStar_ST.ref


let mk_thunk : 'a . (unit  ->  'a)  ->  'a thunk = (fun f -> (FStar_Util.mk_ref (FStar_Util.Inl (f))))


let force_thunk : 'a . 'a thunk  ->  'a = (fun t -> (

let uu____479 = (FStar_ST.op_Bang t)
in (match (uu____479) with
| FStar_Util.Inr (a) -> begin
a
end
| FStar_Util.Inl (f) -> begin
(

let a = (f ())
in ((FStar_ST.op_Colon_Equals t (FStar_Util.Inr (a)));
a;
))
end)))


let tabulate : 'a . Prims.int  ->  (Prims.int  ->  'a)  ->  'a Prims.list = (fun n1 f -> (

let rec aux = (fun i -> (match ((i < n1)) with
| true -> begin
(

let uu____683 = (f i)
in (

let uu____684 = (aux (i + (Prims.parse_int "1")))
in (uu____683)::uu____684))
end
| uu____687 -> begin
[]
end))
in (aux (Prims.parse_int "0"))))




