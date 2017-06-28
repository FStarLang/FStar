
open Prims
open FStar_Pervasives

let has_cygpath : Prims.bool = try
(match (()) with
| () -> begin
(

let uu____7 = (FStar_Util.run_proc "which" "cygpath" "")
in (match (uu____7) with
| (uu____11, t_out, uu____13) -> begin
((FStar_Util.trim_string t_out) = "/usr/bin/cygpath")
end))
end)
with
| uu____17 -> begin
false
end


let try_convert_file_name_to_mixed : Prims.string  ->  Prims.string = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun s -> (match (has_cygpath) with
| true -> begin
(

let uu____24 = (FStar_Util.smap_try_find cache s)
in (match (uu____24) with
| FStar_Pervasives_Native.Some (s1) -> begin
s1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____27 = (FStar_Util.run_proc "cygpath" (Prims.strcat "-m " s) "")
in (match (uu____27) with
| (uu____31, out, uu____33) -> begin
(

let out1 = (FStar_Util.trim_string out)
in ((FStar_Util.smap_add cache s out1);
out1;
))
end))
end))
end
| uu____36 -> begin
s
end)))




