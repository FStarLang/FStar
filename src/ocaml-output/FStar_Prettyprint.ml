open Prims
type printing_mode =
  | ToTempFile 
  | FromTempToStdout 
  | FromTempToFile 
let (uu___is_ToTempFile : printing_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | ToTempFile  -> true | uu____46777 -> false
  
let (uu___is_FromTempToStdout : printing_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | FromTempToStdout  -> true | uu____46788 -> false
  
let (uu___is_FromTempToFile : printing_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | FromTempToFile  -> true | uu____46799 -> false
  
let (temp_file_name : Prims.string -> Prims.string) =
  fun f  -> FStar_Util.format1 "%s.print_.fst" f 
let (generate : printing_mode -> Prims.string Prims.list -> unit) =
  fun m  ->
    fun filenames  ->
      let parse_and_prettyprint m1 filename =
        let uu____46841 =
          match m1 with
          | ToTempFile  ->
              let uu____46856 =
                let uu____46859 =
                  let uu____46860 = temp_file_name filename  in
                  FStar_Util.open_file_for_writing uu____46860  in
                FStar_Pervasives_Native.Some uu____46859  in
              (filename, uu____46856)
          | FromTempToFile  ->
              let uu____46865 = temp_file_name filename  in
              let uu____46867 =
                let uu____46870 = FStar_Util.open_file_for_writing filename
                   in
                FStar_Pervasives_Native.Some uu____46870  in
              (uu____46865, uu____46867)
          | FromTempToStdout  ->
              let uu____46874 = temp_file_name filename  in
              (uu____46874, FStar_Pervasives_Native.None)
           in
        match uu____46841 with
        | (inf,outf) ->
            let uu____46887 = FStar_Parser_Driver.parse_file inf  in
            (match uu____46887 with
             | (modul,comments) ->
                 let leftover_comments =
                   let comments1 = FStar_List.rev comments  in
                   let uu____46936 =
                     FStar_Parser_ToDocument.modul_with_comments_to_document
                       modul comments1
                      in
                   match uu____46936 with
                   | (doc1,comments2) ->
                       ((match outf with
                         | FStar_Pervasives_Native.Some f ->
                             let uu____46973 =
                               FStar_Pprint.pretty_string
                                 (FStar_Util.float_of_string "1.0")
                                 (Prims.parse_int "100") doc1
                                in
                             FStar_All.pipe_left
                               (FStar_Util.append_to_file f) uu____46973
                         | FStar_Pervasives_Native.None  ->
                             FStar_Pprint.pretty_out_channel
                               (FStar_Util.float_of_string "1.0")
                               (Prims.parse_int "100") doc1 FStar_Util.stdout);
                        comments2)
                    in
                 let left_over_doc =
                   if
                     Prims.op_Negation (FStar_List.isEmpty leftover_comments)
                   then
                     let uu____46987 =
                       let uu____46990 =
                         let uu____46993 =
                           let uu____46996 =
                             FStar_Parser_ToDocument.comments_to_document
                               leftover_comments
                              in
                           [uu____46996]  in
                         FStar_Pprint.hardline :: uu____46993  in
                       FStar_Pprint.hardline :: uu____46990  in
                     FStar_Pprint.concat uu____46987
                   else
                     if m1 = FromTempToStdout
                     then
                       FStar_Pprint.concat
                         [FStar_Pprint.hardline; FStar_Pprint.hardline]
                     else FStar_Pprint.empty
                    in
                 (match outf with
                  | FStar_Pervasives_Native.Some f ->
                      ((let uu____47004 =
                          FStar_Pprint.pretty_string
                            (FStar_Util.float_of_string "1.0")
                            (Prims.parse_int "100") left_over_doc
                           in
                        FStar_All.pipe_left (FStar_Util.append_to_file f)
                          uu____47004);
                       FStar_Util.close_file f)
                  | FStar_Pervasives_Native.None  ->
                      FStar_Pprint.pretty_out_channel
                        (FStar_Util.float_of_string "1.0")
                        (Prims.parse_int "100") left_over_doc
                        FStar_Util.stdout))
         in
      FStar_List.iter (parse_and_prettyprint m) filenames;
      (match m with
       | FromTempToFile  ->
           FStar_List.iter
             (fun f  ->
                let uu____47018 = temp_file_name f  in
                FStar_Util.delete_file uu____47018) filenames
       | FromTempToStdout  ->
           FStar_List.iter
             (fun f  ->
                let uu____47025 = temp_file_name f  in
                FStar_Util.delete_file uu____47025) filenames
       | ToTempFile  -> ())
  