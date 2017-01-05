
open Prims

let generate : FStar_Parser_ParseIt.filename Prims.list  ->  Prims.unit = (fun filenames -> (

let parse_and_indent = (fun filename -> (

let _97_6 = (FStar_Parser_Driver.parse_file filename)
in (match (_97_6) with
| (moduls, comments) -> begin
(

let leftover_comments = (FStar_List.fold_left (fun comments module_ -> (

let _97_11 = (FStar_Parser_ToDocument.modul_with_comments_to_document module_ comments)
in (match (_97_11) with
| (doc, comments) -> begin
(

let _97_12 = (FStar_Pprint.pretty_out_channel (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") doc FStar_Util.stdout)
in comments)
end))) (FStar_List.rev comments) moduls)
in (

let left_over_doc = (let _196_10 = (let _196_9 = (let _196_8 = (let _196_7 = (FStar_Parser_ToDocument.comments_to_document leftover_comments)
in (_196_7)::[])
in (FStar_Pprint.hardline)::_196_8)
in (FStar_Pprint.hardline)::_196_9)
in (FStar_Pprint.concat _196_10))
in (FStar_Pprint.pretty_out_channel (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") left_over_doc FStar_Util.stdout)))
end)))
in (FStar_List.iter parse_and_indent filenames)))




