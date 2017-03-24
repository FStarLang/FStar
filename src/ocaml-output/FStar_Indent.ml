open Prims
let generate: FStar_Parser_ParseIt.filename Prims.list -> Prims.unit =
  fun filenames  ->
    let parse_and_indent filename =
      let uu____10 = FStar_Parser_Driver.parse_file filename in
      match uu____10 with
      | (moduls,comments) ->
          let leftover_comments =
            FStar_List.fold_left
              (fun comments1  ->
                 fun module_  ->
                   let uu____36 =
                     FStar_Parser_ToDocument.modul_with_comments_to_document
                       module_ comments1 in
                   match uu____36 with
                   | (doc1,comments2) ->
                       (FStar_Pprint.pretty_out_channel
                          (FStar_Util.float_of_string "1.0")
                          (Prims.parse_int "100") doc1 FStar_Util.stdout;
                        comments2)) (FStar_List.rev comments) moduls in
          let left_over_doc =
            let uu____57 =
              let uu____59 =
                let uu____61 =
                  let uu____63 =
                    FStar_Parser_ToDocument.comments_to_document
                      leftover_comments in
                  [uu____63] in
                FStar_Pprint.hardline :: uu____61 in
              FStar_Pprint.hardline :: uu____59 in
            FStar_Pprint.concat uu____57 in
          FStar_Pprint.pretty_out_channel (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") left_over_doc FStar_Util.stdout in
    FStar_List.iter parse_and_indent filenames