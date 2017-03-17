open Prims
let generate : FStar_Parser_ParseIt.filename Prims.list -> Prims.unit =
  fun filenames  ->
    let parse_and_indent filename =
      let uu____10 = FStar_Parser_Driver.parse_file filename  in
      match uu____10 with
      | (moduls,comments) ->
          let leftover_comments =
            FStar_List.fold_left
              (fun comments1  ->
                 fun module_  ->
                   let uu____36 =
                     FStar_Parser_ToDocument.modul_with_comments_to_document
                       module_ comments
                      in
                   match uu____36 with
                   | (doc1,comments2) ->
                       (FStar_Pprint.pretty_out_channel
                          (FStar_Util.float_of_string "1.0")
                          (Prims.parse_int "100") doc FStar_Util.stdout;
                        comments)) (FStar_List.rev comments) moduls
             in
          let left_over_doc =
            FStar_Pprint.concat
              (let _0_691 =
                 let _0_690 =
                   let _0_689 =
                     FStar_Parser_ToDocument.comments_to_document
                       leftover_comments
                      in
                   [_0_689]  in
                 FStar_Pprint.hardline :: _0_690  in
               FStar_Pprint.hardline :: _0_691)
             in
          FStar_Pprint.pretty_out_channel (FStar_Util.float_of_string "1.0")
            (Prims.parse_int "100") left_over_doc FStar_Util.stdout
       in
    FStar_List.iter parse_and_indent filenames
  