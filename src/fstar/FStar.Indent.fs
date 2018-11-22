#light "off"
module FStar.Indent
open FStar.ST
open FStar.All

open FStar.Util
open FStar.Parser.ToDocument

module D = FStar.Parser.Driver
module P = FStar.Pprint

let temp_file_name f = format1 ".%s.indent" f

let generate filenames =
    let parse_and_indent to_temp_file filename =
        let outf = if to_temp_file then Some (open_file_for_writing (temp_file_name filename)) else None in
        let modul, comments = D.parse_file filename in
        let leftover_comments =
            let comments = List.rev comments in
            let doc, comments = modul_with_comments_to_document modul comments in
                            (* TODO : some problem with the F# generated floats *)
            (match outf with
             | Some f -> append_to_file f <| P.pretty_string (float_of_string "1.0") 100 doc
             | None -> P.pretty_out_channel (float_of_string "1.0") 100 doc stdout);
            comments
        in
        if FStar.List.isEmpty comments then
          (* TODO : We could setup the leftover comments a little more nicely *)
          let left_over_doc =
             P.concat  [P.hardline ; P.hardline ; comments_to_document leftover_comments]
          in
          match outf with
          | Some f -> append_to_file f <| P.pretty_string (float_of_string "1.0") 100 left_over_doc
          | None -> P.pretty_out_channel (float_of_string "1.0") 100 left_over_doc stdout
        else ()
    in
    List.iter (parse_and_indent true) filenames;   //first pass reads from original file and outputs result to temp file
    List.iter (parse_and_indent false) filenames;  //second pass reads from temp file outputs result to stdout
    List.iter (fun f -> delete_file (temp_file_name f)) filenames
