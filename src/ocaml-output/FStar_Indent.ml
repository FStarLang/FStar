open Prims
let generate: FStar_Parser_ParseIt.filename Prims.list -> Prims.unit =
  fun filenames  ->
    let parse_and_indent filename =
      let uu____11 = FStar_Parser_Driver.parse_file filename in
      match uu____11 with
      | (moduls,comments) ->
          let leftover_comments =
            FStar_List.fold_left
              (fun comments1  ->
                 fun module_  ->
<<<<<<< HEAD
                   let uu____42 =
                     FStar_Parser_ToDocument.modul_with_comments_to_document
                       module_ comments1 in
                   match uu____42 with
=======
                   let uu____37 =
                     FStar_Parser_ToDocument.modul_with_comments_to_document
                       module_ comments1 in
                   match uu____37 with
>>>>>>> origin/guido_tactics
                   | (doc1,comments2) ->
                       (FStar_Pprint.pretty_out_channel
                          (FStar_Util.float_of_string "1.0")
                          (Prims.parse_int "100") doc1 FStar_Util.stdout;
                        comments2)) (FStar_List.rev comments) moduls in
          let left_over_doc =
<<<<<<< HEAD
            let uu____63 =
              let uu____65 =
                let uu____67 =
                  let uu____69 =
                    FStar_Parser_ToDocument.comments_to_document
                      leftover_comments in
                  [uu____69] in
                FStar_Pprint.hardline :: uu____67 in
              FStar_Pprint.hardline :: uu____65 in
            FStar_Pprint.concat uu____63 in
=======
            let uu____58 =
              let uu____60 =
                let uu____62 =
                  let uu____64 =
                    FStar_Parser_ToDocument.comments_to_document
                      leftover_comments in
                  [uu____64] in
                FStar_Pprint.hardline :: uu____62 in
              FStar_Pprint.hardline :: uu____60 in
            FStar_Pprint.concat uu____58 in
>>>>>>> origin/guido_tactics
          FStar_Pprint.pretty_out_channel (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") left_over_doc FStar_Util.stdout in
    FStar_List.iter parse_and_indent filenames