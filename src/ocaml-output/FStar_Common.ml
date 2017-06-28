
open Prims
open FStar_Pervasives

let has_cygpath : Prims.bool = try
(match (()) with
| () -> begin
(

let uu____2 = (FStar_Util.run_proc "which" "cygpath" "")
in (match (uu____2) with
| (uu____6, t_out, uu____8) -> begin
((FStar_Util.trim_string t_out) = "/usr/bin/cygpath")
end))
end)
with
| uu____10 -> begin
false
end


let try_convert_file_name_to_mixed : Prims.string  ->  Prims.string = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun s -> (match (has_cygpath) with
| true -> begin
(

let uu____16 = (FStar_Util.smap_try_find cache s)
in (match (uu____16) with
| FStar_Pervasives_Native.Some (s1) -> begin
s1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____19 = (FStar_Util.run_proc "cygpath" (Prims.strcat "-m " s) "")
in (match (uu____19) with
| (uu____23, out, uu____25) -> begin
(

let out1 = (FStar_Util.trim_string out)
in ((FStar_Util.smap_add cache s out1);
out1;
))
end))
end))
end
| uu____28 -> begin
s
end)))




