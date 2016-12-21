
open Prims

let generate : FStar_Parser_ParseIt.filename Prims.list  ->  Prims.unit = (fun filenames -> (

let modules = (FStar_List.collect (fun filename -> (FStar_Parser_Driver.parse_file filename)) filenames)
in (FStar_List.iter (fun module_ -> (let _194_5 = (FStar_Parser_ToDocument.modul_to_document module_)
in (FStar_Pprint.pretty_out_channel 1. (Prims.parse_int "100") _194_5 FStar_Util.stdout))) modules)))




