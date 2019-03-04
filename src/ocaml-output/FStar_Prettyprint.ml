open Prims
type printing_mode =
  | ToTempFile 
  | FromTempToStdout 
  | FromTempToFile 
let (uu___is_ToTempFile : printing_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | ToTempFile  -> true | uu____51344 -> false
  
let (uu___is_FromTempToStdout : printing_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | FromTempToStdout  -> true | uu____51355 -> false
  
let (uu___is_FromTempToFile : printing_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | FromTempToFile  -> true | uu____51366 -> false
  
let (temp_file_name : Prims.string -> Prims.string) =
  fun f  -> FStar_Util.format1 "%s.print_.fst" f 
let (generate : printing_mode -> Prims.string Prims.list -> unit) =
  fun m  ->
    fun filenames  ->
      let parse_and_prettyprint m1 filename =
        let uu____51408 =
          match m1 with
          | ToTempFile  ->
              let uu____51423 =
                let uu____51426 =
                  let uu____51427 = temp_file_name filename  in
                  FStar_Util.open_file_for_writing uu____51427  in
                FStar_Pervasives_Native.Some uu____51426  in
              (filename, uu____51423)
          | FromTempToFile  ->
              let uu____51432 = temp_file_name filename  in
              let uu____51434 =
                let uu____51437 = FStar_Util.open_file_for_writing filename
                   in
                FStar_Pervasives_Native.Some uu____51437  in
              (uu____51432, uu____51434)
          | FromTempToStdout  ->
              let uu____51441 = temp_file_name filename  in
              (uu____51441, FStar_Pervasives_Native.None)
           in
        match uu____51408 with
        | (inf,outf) ->
            let uu____51454 = FStar_Parser_Driver.parse_file inf  in
            (match uu____51454 with
             | (modul,comments) ->
                 let leftover_comments =
                   let comments1 = FStar_List.rev comments  in
                   let uu____51503 =
                     FStar_Parser_ToDocument.modul_with_comments_to_document
                       modul comments1
                      in
                   match uu____51503 with
                   | (doc1,comments2) ->
                       ((match outf with
                         | FStar_Pervasives_Native.Some f ->
                             let uu____51540 =
                               FStar_Pprint.pretty_string
                                 (FStar_Util.float_of_string "1.0")
                                 (Prims.parse_int "100") doc1
                                in
                             FStar_All.pipe_left
                               (FStar_Util.append_to_file f) uu____51540
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
                     let uu____51554 =
                       let uu____51557 =
                         let uu____51560 =
                           let uu____51563 =
                             FStar_Parser_ToDocument.comments_to_document
                               leftover_comments
                              in
                           [uu____51563]  in
                         FStar_Pprint.hardline :: uu____51560  in
                       FStar_Pprint.hardline :: uu____51557  in
                     FStar_Pprint.concat uu____51554
                   else
                     if m1 = FromTempToStdout
                     then
                       FStar_Pprint.concat
                         [FStar_Pprint.hardline; FStar_Pprint.hardline]
                     else FStar_Pprint.empty
                    in
                 (match outf with
                  | FStar_Pervasives_Native.Some f ->
                      ((let uu____51571 =
                          FStar_Pprint.pretty_string
                            (FStar_Util.float_of_string "1.0")
                            (Prims.parse_int "100") left_over_doc
                           in
                        FStar_All.pipe_left (FStar_Util.append_to_file f)
                          uu____51571);
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
                let uu____51585 = temp_file_name f  in
                FStar_Util.delete_file uu____51585) filenames
       | FromTempToStdout  ->
           FStar_List.iter
             (fun f  ->
                let uu____51592 = temp_file_name f  in
                FStar_Util.delete_file uu____51592) filenames
       | ToTempFile  -> ())
  