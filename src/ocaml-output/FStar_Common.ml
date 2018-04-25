
open Prims
open FStar_Pervasives

let has_cygpath : Prims.bool = (FStar_All.try_with (fun uu___29_3 -> (match (()) with
| () -> begin
(

let t_out = (FStar_Util.run_process "has_cygpath" "which" (("cygpath")::[]) FStar_Pervasives_Native.None)
in (Prims.op_Equality (FStar_Util.trim_string t_out) "/usr/bin/cygpath"))
end)) (fun uu___28_7 -> (match (uu___28_7) with
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




