open Prims
let (generate : Prims.string Prims.list -> unit) =
  fun filenames  ->
    let parse_and_indent filename =
      let uu____20 = FStar_Parser_Driver.parse_file filename  in
      match uu____20 with
      | (modul,comments) ->
          let leftover_comments =
            let comments1 = FStar_List.rev comments  in
            let uu____69 =
              FStar_Parser_ToDocument.modul_with_comments_to_document modul
                comments1
               in
            match uu____69 with
            | (doc1,comments2) ->
                (FStar_Pprint.pretty_out_channel
                   (FStar_Util.float_of_string "1.0") (Prims.parse_int "100")
                   doc1 FStar_Util.stdout;
                 comments2)
             in
          let left_over_doc =
            let uu____108 =
              let uu____111 =
                let uu____114 =
                  let uu____117 =
                    FStar_Parser_ToDocument.comments_to_document
                      leftover_comments
                     in
                  [uu____117]  in
                FStar_Pprint.hardline :: uu____114  in
              FStar_Pprint.hardline :: uu____111  in
            FStar_Pprint.concat uu____108  in
          FStar_Pprint.pretty_out_channel (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") left_over_doc FStar_Util.stdout
       in
    FStar_List.iter parse_and_indent filenames
  