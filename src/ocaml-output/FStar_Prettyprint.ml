open Prims
type printing_mode =
  | ToTempFile 
  | FromTempToStdout 
  | FromTempToFile 
let (uu___is_ToTempFile : printing_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | ToTempFile  -> true | uu____51339 -> false
  
let (uu___is_FromTempToStdout : printing_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | FromTempToStdout  -> true | uu____51350 -> false
  
let (uu___is_FromTempToFile : printing_mode -> Prims.bool) =
  fun projectee  ->
    match projectee with | FromTempToFile  -> true | uu____51361 -> false
  
let (temp_file_name : Prims.string -> Prims.string) =
  fun f  -> FStar_Util.format1 "%s.print_.fst" f 
let (generate : printing_mode -> Prims.string Prims.list -> unit) =
  fun m  ->
    fun filenames  ->
      let parse_and_prettyprint m1 filename =
        let uu____51403 =
          match m1 with
          | ToTempFile  ->
              let uu____51418 =
                let uu____51421 =
                  let uu____51422 = temp_file_name filename  in
                  FStar_Util.open_file_for_writing uu____51422  in
                FStar_Pervasives_Native.Some uu____51421  in
              (filename, uu____51418)
          | FromTempToFile  ->
              let uu____51427 = temp_file_name filename  in
              let uu____51429 =
                let uu____51432 = FStar_Util.open_file_for_writing filename
                   in
                FStar_Pervasives_Native.Some uu____51432  in
              (uu____51427, uu____51429)
          | FromTempToStdout  ->
              let uu____51436 = temp_file_name filename  in
              (uu____51436, FStar_Pervasives_Native.None)
           in
        match uu____51403 with
        | (inf,outf) ->
            let uu____51449 = FStar_Parser_Driver.parse_file inf  in
            (match uu____51449 with
             | (modul,comments) ->
                 let leftover_comments =
                   let comments1 = FStar_List.rev comments  in
                   let uu____51498 =
                     FStar_Parser_ToDocument.modul_with_comments_to_document
                       modul comments1
                      in
                   match uu____51498 with
                   | (doc1,comments2) ->
                       ((match outf with
                         | FStar_Pervasives_Native.Some f ->
                             let uu____51535 =
                               FStar_Pprint.pretty_string
                                 (FStar_Util.float_of_string "1.0")
                                 (Prims.parse_int "100") doc1
                                in
                             FStar_All.pipe_left
                               (FStar_Util.append_to_file f) uu____51535
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
                     let uu____51549 =
                       let uu____51552 =
                         let uu____51555 =
                           let uu____51558 =
                             FStar_Parser_ToDocument.comments_to_document
                               leftover_comments
                              in
                           [uu____51558]  in
                         FStar_Pprint.hardline :: uu____51555  in
                       FStar_Pprint.hardline :: uu____51552  in
                     FStar_Pprint.concat uu____51549
                   else
                     if m1 = FromTempToStdout
                     then
                       FStar_Pprint.concat
                         [FStar_Pprint.hardline; FStar_Pprint.hardline]
                     else FStar_Pprint.empty
                    in
                 (match outf with
                  | FStar_Pervasives_Native.Some f ->
                      ((let uu____51566 =
                          FStar_Pprint.pretty_string
                            (FStar_Util.float_of_string "1.0")
                            (Prims.parse_int "100") left_over_doc
                           in
                        FStar_All.pipe_left (FStar_Util.append_to_file f)
                          uu____51566);
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
                let uu____51580 = temp_file_name f  in
                FStar_Util.delete_file uu____51580) filenames
       | FromTempToStdout  ->
           FStar_List.iter
             (fun f  ->
                let uu____51587 = temp_file_name f  in
                FStar_Util.delete_file uu____51587) filenames
       | ToTempFile  -> ())
  