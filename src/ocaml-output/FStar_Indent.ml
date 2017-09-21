open Prims
let generate : FStar_Parser_ParseIt.filename Prims.list -> Prims.unit =
  fun filenames  ->
    let parse_and_indent filename =
      let uu____13 = FStar_Parser_Driver.parse_file filename  in
      match uu____13 with
      | (modul,comments) ->
          let leftover_comments =
            let comments1 = FStar_List.rev comments  in
            let uu____56 =
              FStar_Parser_ToDocument.modul_with_comments_to_document modul
                comments1
               in
            match uu____56 with
            | (doc1,comments2) ->
                (FStar_Pprint.pretty_out_channel
                   (FStar_Util.float_of_string "1.0") (Prims.parse_int "100")
                   doc1 FStar_Util.stdout;
                 comments2)
             in
          let left_over_doc =
            let uu____89 =
              let uu____92 =
                let uu____95 =
                  let uu____98 =
                    FStar_Parser_ToDocument.comments_to_document
                      leftover_comments
                     in
                  [uu____98]  in
                FStar_Pprint.hardline :: uu____95  in
              FStar_Pprint.hardline :: uu____92  in
            FStar_Pprint.concat uu____89  in
          FStar_Pprint.pretty_out_channel (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") left_over_doc FStar_Util.stdout
       in
    FStar_List.iter parse_and_indent filenames
  