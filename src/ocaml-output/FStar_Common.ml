
open Prims
open FStar_Pervasives

let has_cygpath : Prims.bool = (FStar_All.try_with (fun uu___45_6 -> (match (()) with
| () -> begin
(

let uu____7 = (FStar_Util.run_proc "which" "cygpath" "")
in (match (uu____7) with
| (uu____14, t_out, uu____16) -> begin
(Prims.op_Equality (FStar_Util.trim_string t_out) "/usr/bin/cygpath")
end))
end)) (fun uu___44_19 -> (match (uu___44_19) with
| uu____20 -> begin
false
end)))


let try_convert_file_name_to_mixed : Prims.string  ->  Prims.string = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun s -> (match (has_cygpath) with
| true -> begin
(

let uu____28 = (FStar_Util.smap_try_find cache s)
in (match (uu____28) with
| FStar_Pervasives_Native.Some (s1) -> begin
s1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____32 = (FStar_Util.run_proc "cygpath" (Prims.strcat "-m " s) "")
in (match (uu____32) with
| (uu____39, out, uu____41) -> begin
(

let out1 = (FStar_Util.trim_string out)
in ((FStar_Util.smap_add cache s out1);
out1;
))
end))
end))
end
| uu____44 -> begin
s
end)))




