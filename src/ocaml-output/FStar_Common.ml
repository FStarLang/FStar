
open Prims
open FStar_Pervasives

let has_cygpath : Prims.bool = (FStar_All.try_with (fun uu___68_5 -> (match (()) with
| () -> begin
(

let t_out = (FStar_Util.run_process "has_cygpath" "which" (("cygpath")::[]) FStar_Pervasives_Native.None)
in (Prims.op_Equality (FStar_Util.trim_string t_out) "/usr/bin/cygpath"))
end)) (fun uu___67_18 -> false))


let try_convert_file_name_to_mixed : Prims.string  ->  Prims.string = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun s -> (match ((has_cygpath && (FStar_Util.starts_with s "/"))) with
| true -> begin
(

let uu____39 = (FStar_Util.smap_try_find cache s)
in (match (uu____39) with
| FStar_Pervasives_Native.Some (s1) -> begin
s1
end
| FStar_Pervasives_Native.None -> begin
(

let label = "try_convert_file_name_to_mixed"
in (

let out = (

let uu____54 = (FStar_Util.run_process label "cygpath" (("-m")::(s)::[]) FStar_Pervasives_Native.None)
in (FStar_All.pipe_right uu____54 FStar_Util.trim_string))
in ((FStar_Util.smap_add cache s out);
out;
)))
end))
end
| uu____66 -> begin
s
end)))


let snapshot : 'a 'b 'c . ('a  ->  'b)  ->  'c Prims.list FStar_ST.ref  ->  'a  ->  (Prims.int * 'b) = (fun push stackref arg -> (FStar_Util.atomically (fun uu____146 -> (

let len = (

let uu____148 = (FStar_ST.op_Bang stackref)
in (FStar_List.length uu____148))
in (

let arg' = (push arg)
in ((len), (arg')))))))


let rollback : 'a 'c . (unit  ->  'a)  ->  'c Prims.list FStar_ST.ref  ->  Prims.int FStar_Pervasives_Native.option  ->  'a = (fun pop stackref depth -> (

let rec aux = (fun n1 -> (match ((n1 <= (Prims.parse_int "0"))) with
| true -> begin
(failwith "Too many pops")
end
| uu____281 -> begin
(match ((Prims.op_Equality n1 (Prims.parse_int "1"))) with
| true -> begin
(pop ())
end
| uu____286 -> begin
((

let uu____289 = (pop ())
in ());
(aux (n1 - (Prims.parse_int "1")));
)
end)
end))
in (

let curdepth = (

let uu____292 = (FStar_ST.op_Bang stackref)
in (FStar_List.length uu____292))
in (

let n1 = (match (depth) with
| FStar_Pervasives_Native.Some (d) -> begin
(curdepth - d)
end
| FStar_Pervasives_Native.None -> begin
(Prims.parse_int "1")
end)
in (FStar_Util.atomically (fun uu____355 -> (aux n1)))))))


let raise_failed_assertion : 'Auu____361 . Prims.string  ->  'Auu____361 = (fun msg -> (

let uu____369 = (FStar_Util.format1 "Assertion failed: %s" msg)
in (failwith uu____369)))


let runtime_assert : Prims.bool  ->  Prims.string  ->  unit = (fun b msg -> (match ((not (b))) with
| true -> begin
(raise_failed_assertion msg)
end
| uu____388 -> begin
()
end))


let string_of_list : 'a . ('a  ->  Prims.string)  ->  'a Prims.list  ->  Prims.string = (fun f l -> (

let uu____420 = (

let uu____422 = (

let uu____424 = (FStar_List.map f l)
in (FStar_String.concat ", " uu____424))
in (Prims.strcat uu____422 "]"))
in (Prims.strcat "[" uu____420)))


let list_of_option : 'a . 'a FStar_Pervasives_Native.option  ->  'a Prims.list = (fun o -> (match (o) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (x) -> begin
(x)::[]
end))


let string_of_option : 'Auu____459 . ('Auu____459  ->  Prims.string)  ->  'Auu____459 FStar_Pervasives_Native.option  ->  Prims.string = (fun f uu___66_476 -> (match (uu___66_476) with
| FStar_Pervasives_Native.None -> begin
"None"
end
| FStar_Pervasives_Native.Some (x) -> begin
(

let uu____484 = (f x)
in (Prims.strcat "Some " uu____484))
end))


type 'a thunk =
(unit  ->  'a, 'a) FStar_Util.either FStar_ST.ref


let mk_thunk : 'a . (unit  ->  'a)  ->  'a thunk = (fun f -> (FStar_Util.mk_ref (FStar_Util.Inl (f))))


let force_thunk : 'a . 'a thunk  ->  'a = (fun t -> (

let uu____623 = (FStar_ST.op_Bang t)
in (match (uu____623) with
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

let uu____835 = (f i)
in (

let uu____836 = (aux (i + (Prims.parse_int "1")))
in (uu____835)::uu____836))
end
| uu____840 -> begin
[]
end))
in (aux (Prims.parse_int "0"))))




