#light "off"
module FStar.Indent
open FStar.ST
open FStar.All

open FStar.Util
open FStar.Parser.ToDocument

module D = FStar.Parser.Driver
module P = FStar.Pprint

let generate filenames =
    let parse_and_indent filename =
        let modul, comments = D.parse_file filename in
        // P.pretty_out_channel (float_of_string "1.0") 100 (comments_to_document comments) stdout ;
        let leftover_comments =
            let comments = List.rev comments in
            let doc, comments = modul_with_comments_to_document modul comments in
                            (* TODO : some problem with the F# generated floats *)
            P.pretty_out_channel (float_of_string "1.0") 100 doc stdout ;
            comments
        in
        (* TODO : We could setup the leftover comments a little more nicely *)
        let left_over_doc =
           P.concat  [P.hardline ; P.hardline ; comments_to_document leftover_comments]
        in
        P.pretty_out_channel (float_of_string "1.0") 100 left_over_doc stdout
    in List.iter parse_and_indent filenames
