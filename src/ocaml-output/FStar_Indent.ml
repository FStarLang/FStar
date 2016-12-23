
open Prims

let generate : FStar_Parser_ParseIt.filename Prims.list  ->  Prims.unit = (fun filenames -> (

let parse_and_indent = (fun filename -> (

let _96_6 = (FStar_Parser_Driver.parse_file filename)
in (match (_96_6) with
| (moduls, comments) -> begin
(

let leftover_comments = (FStar_List.fold_left (fun comments module_ -> (

let _96_11 = (FStar_Parser_ToDocument.modul_with_comments_to_document module_ comments)
in (match (_96_11) with
| (doc, comments) -> begin
(

let _96_12 = (FStar_Pprint.pretty_out_channel (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") doc FStar_Util.stdout)
in comments)
end))) (FStar_List.rev comments) moduls)
in (

let left_over_doc = (let _194_10 = (let _194_9 = (let _194_8 = (let _194_7 = (FStar_Parser_ToDocument.comments_to_document leftover_comments)
in (_194_7)::[])
in (FStar_Pprint.hardline)::_194_8)
in (FStar_Pprint.hardline)::_194_9)
in (FStar_Pprint.concat _194_10))
in (FStar_Pprint.pretty_out_channel (FStar_Util.float_of_string "1.0") (Prims.parse_int "100") left_over_doc FStar_Util.stdout)))
end)))
in (FStar_List.iter parse_and_indent filenames)))




