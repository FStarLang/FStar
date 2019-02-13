
open Prims
open FStar_Pervasives
type printing_mode =
| ToTempFile
| FromTempToStdout
| FromTempToFile


let uu___is_ToTempFile : printing_mode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| ToTempFile -> begin
true
end
| uu____9 -> begin
false
end))


let uu___is_FromTempToStdout : printing_mode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FromTempToStdout -> begin
true
end
| uu____20 -> begin
false
end))


let uu___is_FromTempToFile : printing_mode  ->  Prims.bool = (fun projectee -> (match (projectee) with
| FromTempToFile -> begin
true
end
| uu____31 -> begin
false
end))


let temp_file_name : Prims.string  ->  Prims.string = (fun f -> (FStar_Util.format1 "%s.print_.fst" f))


let generate : printing_mode  ->  Prims.string Prims.list  ->  unit = (fun m filenames -> (

let parse_and_prettyprint = (fun m1 filename -> (

let uu____73 = (match (m1) with
| ToTempFile -> begin
(

let uu____88 = (

let uu____91 = (

let uu____92 = (temp_file_name filename)
in (FStar_Util.open_file_for_writing uu____92))
in FStar_Pervasives_Native.Some (uu____91))
in ((filename), (uu____88)))
end
| FromTempToFile -> begin
(

let uu____97 = (temp_file_name filename)
in (

let uu____99 = (

let uu____102 = (FStar_Util.open_file_for_writing filename)
in FStar_Pervasives_Native.Some (uu____102))
in ((uu____97), (uu____99))))
end
| FromTempToStdout -> begin
(

let uu____106 = (temp_file_name filename)
in ((uu____106), (FStar_Pervasives_Native.None)))
end)
in (match (uu____73) with
| (inf, outf) -> begin
(

let uu____119 = (FStar_Parser_Driver.parse_file inf)
in (match (uu____119) with
| (modul, comments) -> begin
(

let leftover_comments = (

let comments1 = (FStar_List.rev comments)
in (

let uu____168 = (FStar_Parser_ToDocument.modul_with_comments_to_document modul comments1)
in (match (uu____168) with
| (doc1, comments2) -> begin
((match (outf) with
| FStar_Pervasives_Native.Some (f) -> begin
(

let uu____205 = (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") doc1)
in (FStar_All.pipe_left (FStar_Util.append_to_file f) uu____205))
end
| FStar_Pervasives_Native.None -> begin
(FStar_Pprint.pretty_out_channel (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") doc1 FStar_Util.stdout)
end);
comments2;
)
end)))
in (

let left_over_doc = (match ((not ((FStar_List.isEmpty leftover_comments)))) with
| true -> begin
(

let uu____219 = (

let uu____222 = (

let uu____225 = (

let uu____228 = (FStar_Parser_ToDocument.comments_to_document leftover_comments)
in (uu____228)::[])
in (FStar_Pprint.hardline)::uu____225)
in (FStar_Pprint.hardline)::uu____222)
in (FStar_Pprint.concat uu____219))
end
| uu____229 -> begin
(match ((Prims.op_Equality m1 FromTempToStdout)) with
| true -> begin
(FStar_Pprint.concat ((FStar_Pprint.hardline)::(FStar_Pprint.hardline)::[]))
end
| uu____232 -> begin
FStar_Pprint.empty
end)
end)
in (match (outf) with
| FStar_Pervasives_Native.Some (f) -> begin
((

let uu____236 = (FStar_Pprint.pretty_string (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") left_over_doc)
in (FStar_All.pipe_left (FStar_Util.append_to_file f) uu____236));
(FStar_Util.close_file f);
)
end
| FStar_Pervasives_Native.None -> begin
(FStar_Pprint.pretty_out_channel (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") left_over_doc FStar_Util.stdout)
end)))
end))
end)))
in ((FStar_List.iter (parse_and_prettyprint m) filenames);
(match (m) with
| FromTempToFile -> begin
(FStar_List.iter (fun f -> (

let uu____250 = (temp_file_name f)
in (FStar_Util.delete_file uu____250))) filenames)
end
| FromTempToStdout -> begin
(FStar_List.iter (fun f -> (

let uu____257 = (temp_file_name f)
in (FStar_Util.delete_file uu____257))) filenames)
end
| ToTempFile -> begin
()
end);
)))




