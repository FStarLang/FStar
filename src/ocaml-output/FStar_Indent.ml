open Prims
let generate: FStar_Parser_ParseIt.filename Prims.list -> Prims.unit =
  fun filenames  ->
    let parse_and_indent filename =
      let uu____12 = FStar_Parser_Driver.parse_file filename in
      match uu____12 with
      | (moduls,comments) ->
          let leftover_comments =
            FStar_List.fold_left
              (fun comments1  ->
                 fun module_  ->
                   let uu____58 =
                     FStar_Parser_ToDocument.modul_with_comments_to_document
                       module_ comments1 in
                   match uu____58 with
                   | (doc1,comments2) ->
                       (FStar_Pprint.pretty_out_channel
                          (FStar_Util.float_of_string "1.0")
                          (Prims.parse_int "100") doc1 FStar_Util.stdout;
                        comments2)) (FStar_List.rev comments) moduls in
          let left_over_doc =
            let uu____95 =
              let uu____98 =
                let uu____101 =
                  let uu____104 =
                    FStar_Parser_ToDocument.comments_to_document
                      leftover_comments in
                  [uu____104] in
                FStar_Pprint.hardline :: uu____101 in
              FStar_Pprint.hardline :: uu____98 in
            FStar_Pprint.concat uu____95 in
          FStar_Pprint.pretty_out_channel (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") left_over_doc FStar_Util.stdout in
    FStar_List.iter parse_and_indent filenames