
open Prims
open FStar_Pervasives

let has_cygpath : Prims.bool = (FStar_All.try_with (fun uu___29_6 -> (match (()) with
| () -> begin
(

let uu____7 = (FStar_Util.run_proc "which" "cygpath" "")
in (match (uu____7) with
| (uu____14, t_out, uu____16) -> begin
(Prims.op_Equality (FStar_Util.trim_string t_out) "/usr/bin/cygpath")
end))
end)) (fun uu___28_19 -> (match (uu___28_19) with
| uu____20 -> begin
false
end)))


let try_convert_file_name_to_mixed : Prims.string  ->  Prims.string = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun s -> (match ((has_cygpath && (FStar_Util.starts_with s "/"))) with
| true -> begin
(

let uu____29 = (FStar_Util.smap_try_find cache s)
in (match (uu____29) with
| FStar_Pervasives_Native.Some (s1) -> begin
s1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____33 = (FStar_Util.run_proc "cygpath" (Prims.strcat "-m " s) "")
in (match (uu____33) with
| (uu____40, out, uu____42) -> begin
(

let out1 = (FStar_Util.trim_string out)
in ((FStar_Util.smap_add cache s out1);
out1;
))
end))
end))
end
| uu____45 -> begin
s
end)))




