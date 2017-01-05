module FStar.Indent

open FStar.Util
open FStar.Parser.ToDocument

module D = FStar.Parser.Driver
module P = FStar.Pprint

let generate filenames =
    let parse_and_indent filename =
        let moduls, comments = D.parse_file filename in
        // P.pretty_out_channel (float_of_string "1.0") 100 (comments_to_document comments) stdout ;
        let leftover_comments =
            List.fold_left (fun comments module_ ->
                            let doc, comments = modul_with_comments_to_document module_ comments in
                            (* TODO : some problem with the F# generated floats *)
                            P.pretty_out_channel (float_of_string "1.0") 100 doc stdout ;
                            comments)
                        (List.rev comments)
                        moduls
        in
        (* TODO : We could setup the leftover comments a little more nicely *)
        let left_over_doc =
           P.concat  [P.hardline ; P.hardline ; comments_to_document leftover_comments]
        in
        P.pretty_out_channel (float_of_string "1.0") 100 left_over_doc stdout
    in List.iter parse_and_indent filenames
