open Prims
type printing_mode =
  | ToTempFile 
  | FromTempToStdout 
  | FromTempToFile 
let (uu___is_ToTempFile : printing_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | ToTempFile  -> true | uu____51270 -> false
  
let (uu___is_FromTempToStdout : printing_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | FromTempToStdout  -> true | uu____51281 -> false
  
let (uu___is_FromTempToFile : printing_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | FromTempToFile  -> true | uu____51292 -> false
  
let (temp_file_name : Prims.string -> Prims.string) =
  fun f  -> FStar_Util.format1 "%s.print_.fst" f 
let (generate : printing_mode -> Prims.string Prims.list -> unit) =
  fun m  ->
    fun filenames  ->
      let parse_and_prettyprint m1 filename =
        let uu____51334 =
          match m1 with
          | ToTempFile  ->
              let uu____51349 =
                let uu____51352 =
                  let uu____51353 = temp_file_name filename  in
                  FStar_Util.open_file_for_writing uu____51353  in
                FStar_Pervasives_Native.Some uu____51352  in
              (filename, uu____51349)
          | FromTempToFile  ->
              let uu____51358 = temp_file_name filename  in
              let uu____51360 =
                let uu____51363 = FStar_Util.open_file_for_writing filename
                   in
                FStar_Pervasives_Native.Some uu____51363  in
              (uu____51358, uu____51360)
          | FromTempToStdout  ->
              let uu____51367 = temp_file_name filename  in
              (uu____51367, FStar_Pervasives_Native.None)
           in
        match uu____51334 with
        | (inf,outf) ->
            let uu____51380 = FStar_Parser_Driver.parse_file inf  in
            (match uu____51380 with
             | (modul,comments) ->
                 let leftover_comments =
                   let comments1 = FStar_List.rev comments  in
                   let uu____51429 =
                     FStar_Parser_ToDocument.modul_with_comments_to_document
                       modul comments1
                      in
                   match uu____51429 with
                   | (doc1,comments2) ->
                       ((match outf with
                         | FStar_Pervasives_Native.Some f ->
                             let uu____51466 =
                               FStar_Pprint.pretty_string
                                 (FStar_Util.float_of_string "1.0")
                                 (Prims.parse_int "100") doc1
                                in
                             FStar_All.pipe_left
                               (FStar_Util.append_to_file f) uu____51466
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
                     let uu____51480 =
                       let uu____51483 =
                         let uu____51486 =
                           let uu____51489 =
                             FStar_Parser_ToDocument.comments_to_document
                               leftover_comments
                              in
                           [uu____51489]  in
                         FStar_Pprint.hardline :: uu____51486  in
                       FStar_Pprint.hardline :: uu____51483  in
                     FStar_Pprint.concat uu____51480
                   else
                     if m1 = FromTempToStdout
                     then
                       FStar_Pprint.concat
                         [FStar_Pprint.hardline; FStar_Pprint.hardline]
                     else FStar_Pprint.empty
                    in
                 (match outf with
                  | FStar_Pervasives_Native.Some f ->
                      ((let uu____51497 =
                          FStar_Pprint.pretty_string
                            (FStar_Util.float_of_string "1.0")
                            (Prims.parse_int "100") left_over_doc
                           in
                        FStar_All.pipe_left (FStar_Util.append_to_file f)
                          uu____51497);
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
                let uu____51511 = temp_file_name f  in
                FStar_Util.delete_file uu____51511) filenames
       | FromTempToStdout  ->
           FStar_List.iter
             (fun f  ->
                let uu____51518 = temp_file_name f  in
                FStar_Util.delete_file uu____51518) filenames
       | ToTempFile  -> ())
  