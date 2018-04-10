open Prims
let (generate : FStar_Parser_ParseIt.filename Prims.list -> unit) =
  fun filenames  ->
    let parse_and_indent filename =
      let uu____15 = FStar_Parser_Driver.parse_file filename  in
      match uu____15 with
      | (modul,comments) ->
          let leftover_comments =
            let comments1 = FStar_List.rev comments  in
            let uu____58 =
              FStar_Parser_ToDocument.modul_with_comments_to_document modul
                comments1
               in
            match uu____58 with
            | (doc1,comments2) ->
                let uu____89 =
                  FStar_Pprint.pretty_out_channel
                    (FStar_Util.float_of_string "1.0")
                    (Prims.parse_int "100") doc1 FStar_Util.stdout
                   in
                comments2
             in
          let left_over_doc =
            let uu____91 =
              let uu____94 =
                let uu____97 =
                  let uu____100 =
                    FStar_Parser_ToDocument.comments_to_document
                      leftover_comments
                     in
                  [uu____100]  in
                FStar_Pprint.hardline :: uu____97  in
              FStar_Pprint.hardline :: uu____94  in
            FStar_Pprint.concat uu____91  in
          FStar_Pprint.pretty_out_channel (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") left_over_doc FStar_Util.stdout
       in
    FStar_List.iter parse_and_indent filenames
  